/*
 *
 * Copyright (c) 2001-2002,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

// ccuredlib.c
// runtime library for CCured programs; mostly libc wrappers

// The security model for these wrappers is that the programmer is the
// adversary, trying to break memory safety by any clever means,
// despite the program having been passed through the CCured
// translator.  However, this is (for the moment) an ideal; there are
// still a few holes in the wrappers.  We fix them when we notice them
// and the fix is not too onerous; we note below where we choose not
// to fix, with "UNSOUND".  Any unsoundness that is not marked as such
// is a bug.
//
// The security model we believe we enforce everywhere is that the
// programmer is not malicious, but perhaps forgetful.  Of course
// there is no formal model for this, but it means roughly we try to
// be very careful about off-by-one and other typical overflow
// scenarios, but do not (for example) guard against a
// carefully-constructed bogus argument to a FILE*-accepting function.
//
// One global unsoundness: threading.  This library is not
// thread-safe.  It only uses globals in a few places; that might be
// solvable.  But it extensively uses invariants which tie certain
// pieces of data together, and those invariants are, at times, false.
// In a threaded environment, another thread might access the data
// while the invariants are false (e.g. the tags are out of synch with
// data values).  Fixing this would require acquiring some kind of
// lock in almost all the code which manipulates tags...


#include <stdio.h>
#include <stdlib.h>      // malloc/free (?); dsw: getenv()
#include <setjmp.h>      // setjmp, jmp_buf
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <ctype.h>       // __ctype_b
#include <stdint.h>      // intptr_t, uintptr_t
#include <time.h>        // time, time_t
#include <stdarg.h>      // various varargs-related
#include <errno.h>

#ifdef _GNUCC
  #include <unistd.h>    /* struct stat, fd_set */
  #include <fcntl.h>     /* open; pulled up here to avoid implicit decl */
  #include <signal.h>    // signal
  #include <syslog.h>    // syslog, LOG_ERR(=3)
  #include <sys/times.h> // times, clock_t
  #include <sys/time.h>  // gettimeofday, struct timeval, struct timezone
  #include <sys/types.h> // size_t?   dsw:lets us use getpid()
  #include <sys/socket.h>// struct sockaddr, sendto
  #include <assert.h>    // __assert_fail
  #include <pthread.h>   // pthread_mutex_t, pthread_* functions
  #include <locale.h>    // setlocale
  #include <glob.h>      // glob, glob_t, GLOB_xxx codes
  #include <pwd.h>       // getpwnam
  #ifndef __CYGWIN__
    #include <execinfo.h>
    #define O_BINARY 0     /* doesn't exist in linux */
    #include <sys/mman.h>  // MAP_FAILED
  #endif
  #define _MAX_PATH 255  /* wouldn't begin to know where to properly find this */
#endif

// On MSVC some low-level functions have a leading underscore
#ifdef _MSVC
  #include <io.h>

  #define VSNPRINTF _vsnprintf
  #define SNPRINTF  _snprintf
  #define LSEEK _lseek
  #define READ  _read
  #define WRITE _write
  #define STAT  _stat
  #define OPEN  _open
  #define CLOSE _close
  #define FSTAT _fstat
  #define FILENO _fileno
  #define STRDUP _strdup
  #define UNLINK _unlink
#else
  #define VSNPRINTF vsnprintf
  #define SNPRINTF  snprintf
  #define LSEEK lseek
  #define READ  read
  #define WRITE write
  #define STAT  stat
  #define OPEN  open
  #define CLOSE close
  #define FSTAT fstat
  #define FILENO fileno
  #define STRDUP strdup
  #define UNLINK unlink
#endif


// sanity check
#if defined(_DEBUG) && defined(RELEASELIB)
  #error _DEBUG and RELEASELIB are inconsistent
#endif


// Add the checks as well
#include "ccuredcheck.h"


// ----------------- multi-word pointer templates -------------------
// the instrumented program will contain its own declarations of various
// multi-word pointers; but this library doesn't see that code, so we
// also declare these, and then the functions below use the names
// declared here; it's important to make sure that the pointer types
// used are consistent with the types implied by the mangled names,
// because *nothing* systematically checks this for consistency

// name mangling algorithm:
//   1. write down the type of the function on one line,
//      including return type; e.g.
//        int *foo(char *q, struct Bar *b, int y);
//
//   2. add safe/fseq/seq/wild qualifiers to pointer types, e.g.:
//        int * safe foo(char * fseq q, struct Bar * wild b, int y);
//
//   3. append an underscore to the function's name, e.g.:
//        foo_
//
//   4. read the qualifiers left to right, appending one character
//      for each qualifier, according to the following map:
//        safe    s
//        seq     q
//        seqN    Q    (null-terminated)
//        fseq    f
//        fseqN   F    (null-terminated)
//        wild    w
//      e.g.,
//        foo_sfw
//      Exception: nested qualifiers are read right to left; for example,
//        int getopt(int argc, char * SAFE * FSEQ argv, char *opts)
//      which accepts an FSEQ pointer to an array of SAFE pointers, is
//        getopt_fss
//
//   5. for the wrappers below, use the declared structures instead
//      of actual syntactic qualifiers, e.g.:
//        int *foo(fseqp_char q, wildp_void b, int y);
//      in this case, if the wrapper needed to access b's fields,
//      it would be necessary to declare a wildp_Bar (and possibly
//      also struct Bar), or at least cast the _p field on use
//
//   Notes:
//     - we currently do not dig inside structures and mangle names
//       according to qualifiers in there; this may be a mistake, but
//       it's how it currently (2/01/02) works
//     - I do not know how we mangle names where pointers to functions,
//       pointers to arrays, etc., are involved
//     - for historical reasons, wild pointers are typically called "fatp"
//       when naming the types..



typedef struct wildp_char {
  char * _p ;
  void * _b ;
} wildp_char;

typedef struct fseqp_char {
  char *_p;
  void *_e;
} fseqp_char;

typedef struct fseqcp_char {
  char *_p;
  void *_e;
  void *_z;
} fseqcp_char;

typedef struct wildp_char1 {
  char const  * _p ;
  void * _b ;
} wildp_char1;

typedef struct wildp_void {
  void *_p ;
  void *_b ;
} wildp_void;

typedef struct fseqp_void {  // for realloc_ff
  void *_p;
  void *_e;
} fseqp_void;

typedef struct fseqcp_void {
  void *_p;
  void *_e;
  void *_mp;
} fseqcp_void;

typedef struct indexp_void {
  void *_p;
  void *_b;
} indexp_void;



typedef struct seqp_void {
  void * _p ;
  void * _b ;
  void * _e ;
} seqp_void;

typedef struct seqcp_void {
  void * _p ;
  void * _b ;
  void * _e ;
  void * _mp ;
} seqcp_void;

typedef struct seqp_char {
  char * _p ;
  void * _b ;
  void * _e ;
} seqp_char;

typedef struct seqcp_char {
  char * _p ;
  void * _b ;
  void * _e ;
  void * _z;
} seqcp_char;

typedef struct seqp_int {
  int * _p ;
  void * _b ;
  void * _e ;
} seqp_int;

typedef struct safecp_void {
  void * _p;
  void * _mp;
} safecp_void;

typedef struct seqp_FILE {
  FILE * _p ;
  void * _b ;
  void * _e ;
} seqp_FILE;

typedef struct fseqp_FILE {
  FILE * _p ;
  void * _e ;
} fseqp_FILE;

typedef struct wildp_wildp_char {
  wildp_char * _p ;
  void * _b ;
} wildp_wildp_char;

typedef struct fseqp_wildp_char {
  wildp_char * _p ;
  void * _e ;
} fseqp_wildp_char;

typedef struct seq_wildp_char {
  wildp_char * _p ;
  void * _b ;
  void * _e;
} seq_wildp_char;

typedef struct wildp_FILE {
  FILE * _p ;
  void * _b ;
} wildp_FILE;

typedef struct wildp_struct__stat {
  struct _stat * _p ;
  void * _b ;
} wildp_struct__stat;

typedef struct wildp_time_t1 {
  time_t * _p ;
  void * _b ;
} wildp_time_t1;

#ifndef _MSVC
  typedef struct wildp_pthread_mutex_t {
    pthread_mutex_t * _p ;
    void * _b ;
  } wildp_pthread_mutex_t;
#endif
////////////////


#define __CCURED_ASSERT(what, code) \
  { if(! (what)) CCURED_FAIL(code FILE_AND_LINE); }

/* The value of this variable is set from the cured code. If this variable
 * is SET then the ccured_fail has the __NORETURN attribute, so it should
 * NOT RETURN !!! */
int __ccuredAlwaysStopOnError = 0;

/* If this variable is set then we should not look for the file and line
 * number arguments in ccured_fail functions */
int __ccuredFailIsTerse       = 0;


/* We use some variables to store the values of some environment variables
 * before the program messes with them ! */
static int __ccuredSleepOnError      = 0;
static int __ccuredContinueOnError   = 0;
static FILE* __ccuredErrorLog = NULL;

/* A variable that controls whether we have used strings in CCured. This
 * means tht we have null-termination issues */
int __ccuredUseStrings = 0;

int __ccuredDisableStoreCheck = 0;

void* __ccuredStackBottom = 0;

// sm: struct _stat doesn't exist in linux
#ifdef _GNUCC
#define _stat stat
#define __builtin_memset_ww memset_ww
#define __builtin_memset_ff memset_ff
#define __builtin_memset_qq memset_qq
#define __builtin_memset_sf memset_sf
#endif

// debugging print
#if 0
  #define DP(arg) printf arg
#else
  #define DP(arg)
#endif

// round a byte count up to the next word boundary
#define ALIGNBYTES(n) (((n) + sizeof(int) - 1) & ~(sizeof(int) - 1))

// round a byte count up to the next word boundary, and return
// the count in *words*
#define BYTESTOWORDS(n) (((n) + 3) >> 2)

// multiply two unsigned 32-bit values but check for overflow;
// this is to guard against the case where our wrapper only checks
// the product but libc does iteration internally; yes division is
// somewhat expensive, but this is usally called in a situation where
// a system call or even some I/O might happen, which certainly
// dominates the cost of integer division
unsigned __ccured_mult_u32(unsigned x, unsigned y)
{
  if (x==1 || y==1 || x==0 || y==0) {
    // can't overflow
  }
  else if (x > 0xFFFFFFFF / y) {
    CCURED_FAIL(FAIL_OVERFLOW  FILE_AND_LINE);
  }

  return x*y;
}


// --------------- garbage collector interface ---------------
// pull in declarations for garbage collector
#ifndef RELEASELIB
  #define GC_DEBUG
#endif
// See whether we pull in the GC or not
#ifdef CCURED_NO_GC
  #define GC_MALLOC(sz) malloc(sz)
  #define GC_REALLOC(p,sz) realloc(p,sz)
  #define GC_FREE(p)    free(p)
#else
  #include <gc/gc.h>
#endif

// 10/28/01: changed from defining 'malloc' etc to defining
// 'ccured_malloc', with a #define in ccured.h, because there
// was a problem with the former under cygwin: when libc calls
// malloc (twice) before main runs, it the call to GC_MALLOC
// below would always segfault.  we tried some hackery where
// our malloc would try to avoid handling the first 2 calls,
// but that didn't help.  so we decided to avoid linker tricks
// altogether and rely in the C preprocessor instead to intercept
// malloc/free


// if this is set to 1, we can emit a log of allocator traffic
#ifndef LOG_ALLOC_TRAFFIC
  // unfortunately, this DOES NOT WORK, because of problems
  // with the accuracy of GC_size() ...
  #define LOG_ALLOC_TRAFFIC 0
#endif
#if LOG_ALLOC_TRAFFIC
  FILE *allocTraffic = NULL;        // where to send allocator traffic
  long totalAllocated = 0;          // total bytes allocated
  long totalFreed = 0;              // total bytes in free'd blocks

  void reportAllocTraffic()
  {
    if (allocTraffic) {
      fprintf(allocTraffic, "%ld %ld %ld\n",
	      totalAllocated,
	      totalAllocated - totalFreed,      // size of heap with malloc/free
	      (long)GC_get_heap_size());        // size of heap with gc only
      fflush(allocTraffic);
    }
  }
#endif


#ifndef CCURED_NO_MALLOC
// cause references below to malloc/free/realloc to use
// the garbage collector's versions instead

// All of these functions must be __cdecl because they are replacement
// for malloc/free
void* __cdecl ccured_malloc(unsigned sz)
{
  void *ret;

  // 10/09/03: removed the 'sz++' since that was for our old
  // scheme for char* that turned out not to be very useful

  ret = GC_MALLOC(sz);
  DP(("malloc(%d) yielded %p\n", sz, ret));

  #if LOG_ALLOC_TRAFFIC
    totalAllocated += GC_size(ret);     // might be a little bigger than 'sz'
    reportAllocTraffic();
  #endif

  return ret;
}

void* __cdecl ccured_calloc(size_t x, size_t y)
{
  // ccured_malloc already zeroes, because GC_malloc does
  return ccured_malloc(x*y);
}

void __cdecl ccured_free(void *p)
{
  DP(("free(%p)\n", p));

  #if LOG_ALLOC_TRAFFIC
    totalFreed += GC_size(p);
    reportAllocTraffic();
  #endif

  #ifdef GC_DEBUG
    // in debug mode, this checks for things like double-free, but
    // the memory remains allocated, so there is no unsoundness
    GC_FREE(p);
  #else
    // sm: 9/26/03: It turns out that the TOPLAS reviewer was right!
    // When GC_DEBUG is not defined, GC_FREE does indeed free the
    // memory, which leads to unsoundness of course.  So, when we're
    // in release mode, do not free.

    //GC_FREE(p);     // sm: temporarily testing the effect of adding this back
  #endif
}

void* ccured_realloc(void *p, unsigned int sz)
{
  // we can't call GC_REALLOC for same reason can't call GC_FREE above;
  // so, implement this in terms of the functionality we already have

  // except, GC_size doesn't accurately report the amount of memory
  // that was zeroed during allocation (I'm not sure if GC_size is
  // just wrong or what), so instead I've modified GC_realloc so it
  // does not call GC_free internally

  void *ret = GC_REALLOC(p, sz);
  DP(("realloc(%p, %d) yielded %p\n", p, sz, (unsigned int)ret));
  return ret;
}

// I intend to call this from user code to invoke
// the garbage collector, and verify it has accomplished
// some useful work; returns # of bytes freed
int ccured_explicit_gc()
{
#ifdef CCURED_NO_GC
  return 0;
#else
  int before = GC_get_free_bytes();
  GC_gcollect();
  return GC_get_free_bytes() - before;
#endif
}

#endif

// the GC has been instrumented (optionally) to call this function
// every time a block is noticed to be reachable; the idea is I will
// add code to detect if the programmer freed this block, in which
// case I might take some additional action (like warn the user?)
void noticedReachable(void *block, size_t size)
{
  //printf("noticedReachable: %p, sz=%d\n", block, size);
}

void noticedUnreachable(void *block, size_t size)
{
  //printf("noticedUnreachable: %p, sz=%d\n", block, size);
}

void noticedContiguousUnreachable(void *block, size_t size, size_t arraySize)
{
  //printf("noticedContiguousUnreachable: %p, sz=%d, arraySize=%d (ratio: %d)\n",
  //       block, size, arraySize, arraySize/size);
}


// sm: these duplicate things in ccuredcheck.h, which gets #included above
// via ccured.h; however, #defining NO_CHECKS would disable that inclusion,
// and I don't understand when NO_CHECKS is used, so I leave this for now..
#ifdef _MSVC
  #define I32 int
#endif
#ifdef _GNUCC
  #define I32 int
#endif
#define U32 unsigned I32

#ifndef MIN
  #define MIN(x,y) (((x) < (y)) ? (x) : (y))
#endif


// --------------------- error reporting / aborting ---------------
// line these up with ccuredannot.h codes to verify correspondence
struct failMessageData
{   char *name, *msg;
} failMessages[] = {
  { "BELOW_SP", "Returning a local stack address"},       // 0
  { "STORE_SP", "Storing stack address"},
  { "LBOUND", "Lbound"},
  { "UBOUND", "Ubound"},
  { "INVFUNC", "Function pointer"},
  { "DECFSEQ", "Decrement FSEQ"},                   // 5
  { "NULL", "Null pointer"},
  { "NULLSTR", "Null string"},
  { "LONGSTR", "Non-terminated string"},
  { "ALIGN", "Unaligned pointer"},
  { "MALLOC", "Malloc"},                           // 10
  { "REALLOC", "Realloc"},
  { "FREE", "Free with ptr!=base"},
  { "REALLOCLESS", "Realloc (shrink)"},
  { "REALLOCMORE", "Realloc (grow)"},
  { "NONPTR", "Non-pointer"},                      // 15
  { "SCALAR", "Scalar log"},
  { "NULLSTRLEN", "Null string in strlen"},
  { "VARARG", "variable argument"},
  { "NOVA_START", "call to va_arg without call to va_start"},
  { "VARARGMANY", "too many calls to va_arg"},         // 20
  { "VARARGBADTYPE","type mismatch between caller and use of va_arg function"},
  { "VARARGFORMAT", "unrecognized format character"},
  { "OVERFLOW", "Integer arithmetic overflow"},
  { "READTAMPERED", "Reading a pointer that has been tampered with"}, // 24
  { "BADRTTI", "Casting to invalid RTTI"}, // 25
  { "TOOSMALL", "Not enough room for one element"}, // 26
  { "ALIGNSEQ", "Creating an unaligned sequence"}, // 27
  { "WRONGFIELD", "Reading the wrong union field"}, // 28
  { "STACKOVERFLOW", "Stack overflow"}, // 29
  { "CUSTOM", ""}, // 30
};

//matth: if needed, break_env could be implemented for Windows using Sleep()
//  instead of sleep() and GetCurrentProcessId() instead of getpid()
#ifndef _MSVC

// dsw: Break if a specified environment variable is set.
void break_env(const char *env_var_name) {
  if (getenv(env_var_name)) {
    volatile int stopped = 1; // 3) in the debugger, set this to 0 to jump out
    // dsw: To allow debugging of multithreaded code, we use Ben
    // Liblit's trick.
    printf("**************** break_env on name '%s', my pid is %d\n", env_var_name, getpid());
    while (stopped) {
      sleep(1);           // 1) will stop here when attached.
    }
  } else {
    printf("**************** skipping break_env on name '%s', (pid %d), since name not set\n",
	   env_var_name, getpid());
  }
  // 2) set breakpoint here.
}
#endif //ndef MSVC

/* If CCured fails, it checks to see if you have specified special handling
 * for this failed check */
enum handlerKind {
  HANDLE_DEFAULT, // no handler specified
  HANDLE_IGNORE,// ignore
  HANDLE_STOP,  // warn and stop
  HANDLE_WARN,  // warn but do not stop
  HANDLE_SLEEP, // start the debugger
};
struct handler {
  enum handlerKind   knd;
  int                line; // 0 if match any
  char              *file; // NULL if match any
  char              *function; // NULL if match any
  struct handler    *next; // next one
};
// We keep an array of handlers
static int handlersInitialized = 0; // If this was initialized
static struct handler * errorHandlers[NUM_FAIL_CODES];

__inline
enum handlerKind checkHandler(int code,
			      char const *file, int line, char const *function)
{
  struct handler *h = errorHandlers[code];
  while(h) { // See if it matches
    while(1) {
      if(h->line && h->line != line) break;
      if(h->file && strcmp(h->file, file)) break;
      if(h->function && strcmp(h->function, function)) break;
      // We found a match
      return h->knd;
    }
    h = h->next;
  }
  return HANDLE_DEFAULT;
}

#ifndef CCURED_NO_ERROR_HANDLERS_FILE
/* Now initialize the handlers from a file */
void initErrorHandlers(char *fname) {
  FILE *f = fopen(fname, "r");
  int  line = 0;
  char buffer[1024];
  int i;
  struct handler *h;
  if(!f) {
    SNPRINTF(buffer, sizeof(buffer), "Cannot open error handler file \"%s\"",
	     fname);
    CCURED_FAIL_STR(buffer FILE_AND_LINE);
    abort();
  }
  // Read a line
  while(fgets(buffer, sizeof(buffer), f)) {
    char *token, *theEnd, *why = "unknown";
    int code;

    line ++;
    // Is this an empty line
    if(! *buffer || *buffer == '\n') continue;
    // Start to parse the line
    token = strtok(buffer, " \n");
    if(! token || *token == '\n') continue; // empty line
    // Prepare a new handler
    h = (struct handler*)malloc(sizeof(*h));
    if(! h) {
      CCURED_FAIL_STR("Cannot allocated memory for error handlers"
		      FILE_AND_LINE);
      abort();
    }
    // Must be one of our friends: ignore, stop, warn
    // we check only the first character
    switch(*token) {
    case 'i': h->knd = HANDLE_IGNORE; break;
    case 'w': h->knd = HANDLE_WARN; break;
    case 's':
      switch(*(token + 1)) {
      case 't' : h->knd = HANDLE_STOP; break;
      case 'l' : h->knd = HANDLE_SLEEP; break;
      default: why = "no instruction"; goto parseError;
      }
      break;
    default:
      why = "no instruction";
      goto parseError;
    }
    // Now get the error code
    token = strtok(NULL, " \n");
    if(! token) { why = "no code"; goto parseError; }
    // Search for the token in our table
    code = 0;
    while(code < NUM_FAIL_CODES) {
      if(! strcmp(failMessages[code].name, token)) break;
      code ++;
    }
    if(code == NUM_FAIL_CODES) {
      if(*token == '*') { // This is a message for all codes
	code = -1;
      } else {
	why = " invalid code";
	goto parseError;
      }
    }
    // Prepare for the defaults
    h->file = h->function = NULL; h->line = 0;

    // Now skip the "at" and get the
    token = strtok(NULL, " :\n");
    if(! token) { // We are done. Keep the defaults
      goto finishedLine;
    }
    if(*token != 'a') {
      why = "no \"at\""; goto parseError;
    }
    token = strtok(NULL, " :\n");
    if(! token) {
      why = "no file name after \"at\""; goto parseError;
    }
    h->file = *token == '*' ? NULL : STRDUP(token);
    // Get the line number
    token = strtok(NULL, " :\n");
    if(! token) goto finishedLine;
    if(*token != '*') {
      h->line = strtol(token, &theEnd, 10);
      if(*theEnd) { why = "no line"; goto parseError; }
    }
    // get the function name
    token = strtok(NULL, " :(\n");
    if(! token) goto finishedLine;
    if(*token != '*') {
      h->function = STRDUP(token);
    }
    // Now link it in
 finishedLine:
    // Maybe we need to link it in all codes
    if(code == -1) {
      int i;
      for(i=0;i<NUM_FAIL_CODES;i++) {
	struct handler *copy;
	h->next = errorHandlers[i];
	errorHandlers[i] = h;
	// Make a copy for the next one
	copy = (struct handler*)malloc(sizeof(*copy));
	memcpy(copy, h, sizeof(*copy));
	h = copy;
      }
    } else {
      h->next = errorHandlers[code];
      errorHandlers[code] = h;
    }
    continue;

  parseError:
    SNPRINTF(buffer, sizeof(buffer),
	     "Error parsing error handler file %s:%d (%s)\n",
	     fname, line, why);
    CCURED_FAIL_STR(buffer FILE_AND_LINE); // go on
    continue;
  }
  fclose(f);
  // Now we must reverse all lists (to ensure that we
  for(i = 0; i < NUM_FAIL_CODES; i ++) {
    struct handler * prev = NULL; // The head of the reversed prefix
    struct handler *current = errorHandlers[i];
    while(current) {
      struct handler *t = current->next;
      current->next = prev;
      prev = current;
      current = t;
    }
    errorHandlers[i] = prev;
  }
  // See if we must dump the handlers
  if(getenv("CCURED_DUMP_HANDLERS")) {
    fprintf(stderr, "The CCured error handlers are:\n");
    for(i = 0; i < NUM_FAIL_CODES; i ++) {
      struct handler * h = errorHandlers[i];
      if(! h) continue;
      fprintf(stderr, " %s:\n", failMessages[i].name);
      while(h) {
	char *action = NULL;
	switch(h->knd) {
	case HANDLE_DEFAULT: action = "default"; break;
	case HANDLE_STOP: action = "stop"; break;
	case HANDLE_WARN: action = "warn"; break;
	case HANDLE_IGNORE: action = "ignore"; break;
	case HANDLE_SLEEP: action = "sleep"; break;
	}
	fprintf(stderr, "   %s at %s:%d: %s()\n",
		action,
		(h->file ? h->file : "*"),
		(h->line ? h->line : 0),
		(h->function ? h->function : "*"));
	h = h->next;
      }
    }
  }
  handlersInitialized = 1;
}
#endif // CCURED_NO_ERROR_HANDLER_FILE

// Remember here the last error that was encountered
static int ccured_last_error = FAIL_CUSTOM;

#define MSGFMT "Failure %s at %s:%d: %s(): %s"

void ccured_fail_str(char const *str  CCURED_FAIL_EXTRA_PARAMS)  {
  int code = ccured_last_error;
  char *codename = failMessages[code].name;
  enum handlerKind how;

  // And reset it, in case we come next time directly here
  // without going through ccured_fail
  ccured_last_error = FAIL_CUSTOM;

  if(file == NULL) { // This means we are called from a terse version
    file = "<unknown>";
    line = 0;
    function = "<unknown>";
  }

  how = handlersInitialized ?
    checkHandler(code, file, line, function) : HANDLE_DEFAULT;

  if(!__ccuredAlwaysStopOnError && how == HANDLE_IGNORE) return;

  // obscure C: juxtaposed string constants are implicitly concatenated
  fprintf(stderr, MSGFMT "\n", codename CCURED_FAIL_EXTRA_ARGS, str);
  fflush(stderr);
  if (__ccuredErrorLog != 0){
#ifndef CCURED_NO_CTIME
    time_t t = time(NULL);
#endif
    fprintf(__ccuredErrorLog,
#ifndef CCURED_NO_CTIME
	    "%s" MSGFMT "\n\n",
	    ctime(&t),
#else
	    MSGFMT "\n\n",
#endif
	    codename CCURED_FAIL_EXTRA_ARGS, str);
    fflush(__ccuredErrorLog);
  }

#if defined(_GNUCC)
  if(getenv("CCURED_SYSLOGFAIL")) {
    syslog(LOG_ERR, MSGFMT,  codename CCURED_FAIL_EXTRA_ARGS, str);
  }
#endif

  if(!__ccuredAlwaysStopOnError && how == HANDLE_WARN) return;

  // See if we should fall asleep to allow the user to connect
  // to use using gdb
  if(__ccuredSleepOnError || how == HANDLE_SLEEP) {
#if defined(_MSVC)
    // On windows this will fire the just-in=time debugger
    _asm { int 3 }
#else
    // dsw: To allow debugging of multithreaded code, we use Ben
    // Liblit's trick.
    if (__ccuredSleepOnError) {
      volatile int stopped = 1; // 3) in the debugger,set this to 0 to jump out
      printf("**************** ccured_fail_str, my pid is %d\n", getpid());
      while (stopped) {
	sleep(1);               // 1) will stop here when attached.
      }
				// 2) set breakpoint here.
      stopped ++; // Just a place to put a breakpoint after we awake
    }
#endif
  }

  // Now we must stop
  if(__ccuredAlwaysStopOnError ||
     how == HANDLE_STOP  ||
     ! __ccuredContinueOnError) {
    // We must STOP !!! This function was compiled with attribute((noreturn))
    if(__ccuredAlwaysStopOnError &&
       (how != HANDLE_STOP || __ccuredContinueOnError)) {
      // We'll stop no matter what they say
      fprintf(stderr, "Will abort because you said --alwaysStopOnError\n");
      fflush(stderr);
    }

    if (getenv("CCURED_NO_SIGABRT")) {
      //The user asks that we not use the SIGABRT signal.
      //So call exit instead of abort()
      exit(-1);
    } else {
#if defined(_MSVC) && defined(_DEBUG)
      // on windows a debug trap is desired in debug mode
      _asm { int 3 }
#else
#if ! defined(__CYGWIN__) && defined(_DEBUG)
      { // Try to print a backtrace. At the moment, not very useful
	#define SIZE_BACKTRACE 128
	void * backtrace_buffer[SIZE_BACKTRACE];
	int much = backtrace(backtrace_buffer, SIZE_BACKTRACE);
	backtrace_symbols_fd(backtrace_buffer, much, 2);
      }
#endif
      abort();
#endif
    }
  }
#undef MSGFMT
}

void ccured_fail_str_terse(char const *str) {
  ccured_fail_str(str, NULL, 0, NULL);
}

// This might return
void ccured_fail(int msgId  CCURED_FAIL_EXTRA_PARAMS)
{
  ccured_last_error = msgId;
  ccured_fail_str(failMessages[msgId].msg  CCURED_FAIL_EXTRA_ARGS);
}
void ccured_fail_terse(int msgId) {
  ccured_fail(msgId, NULL, 0, NULL);
}

void lbound_or_ubound_fail(void *base,
			   void *p  CCURED_FAIL_EXTRA_PARAMS) {
    //what kind of failure was this?
  if (p < base){
    CCURED_FAIL(FAIL_LBOUND CCURED_FAIL_EXTRA_ARGS);
  } else {
    CCURED_FAIL(FAIL_UBOUND CCURED_FAIL_EXTRA_ARGS);
  }
}
void lbound_or_ubound_fail_terse(void *base, void *p) {
  lbound_or_ubound_fail(base, p, NULL, 0, NULL);
}


// out-of-line ubound failure analysis; we don't want this in the
// main check because that gets inlined everywhere
// use this as a replacement for ccured_fail
void ubound_or_non_pointer_fail(void *p,
				void *bend  CCURED_FAIL_EXTRA_PARAMS) {
  if (bend == 0) {
    // sm: George wants this to be classified as non-pointer (which is
    // a better description), so we'll special-case it
    NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
  }
  else {
    // valid 'end' field means it's an upper-bounds failure
    CCURED_FAIL(FAIL_UBOUND  CCURED_FAIL_EXTRA_ARGS);
  }
}
void ubound_or_non_pointer_fail_terse(void *base, void *p) {
  ubound_or_non_pointer_fail(base, p, NULL, 0, NULL);
}


  //we need this for wrappers when INFERBOX=wild
void ccured_fail_ww(int msgId, wildp_char file,
		     int line, wildp_char function) {
  ccured_fail(msgId, file._p, line, function._p);
}

// ------------------- general-purpose: fatp ---------------------
// this section has some general purpose queries and checkers for
// various kinds of pointers, which are then shared by the wrappers

// possible TODO: these don't do the best thing with CCURED_FAIL_IS_VERBOSE

// given a fat pointer, return the # of bytes legal to read/write
// starting from its _p field.  Also do a bounds check.
__inline static int wildp_length(wildp_char ptr)
{
  unsigned nwords = CHECK_FETCHLENGTH(ptr._p, ptr._b,0);
  __CCURED_ASSERT((void*)ptr._p >= ptr._b, FAIL_LBOUND);
  __CCURED_ASSERT((void*)ptr._p < CHECK_FETCH_WILD_END(ptr._p, ptr._b, 0),
		  FAIL_UBOUND);

  // the code that was in memset_ww had a -1, but I think that's
  // wrong now that strings are handled orthogonally
  return (int)(nwords << 2) - (ptr._p - (char*)ptr._b);
}

// fail unless there are >=n bytes read/writable after ptr
// Also does a bounds check (via wildp_length)
__inline static void wildp_verify_atleast(wildp_char ptr, int n)
{
#ifndef NO_CHECKS
  if (n < 0) {
    CCURED_FAIL(FAIL_LBOUND FILE_AND_LINE);
  }
  if (n > wildp_length(ptr)) {
    CCURED_FAIL(FAIL_UBOUND FILE_AND_LINE);
  }
#endif //NO_CHECKS
}


// clear the tags for the 'n' bytes starting at ptr
__inline static void wildp_clear_tags(wildp_char ptr, int n)
{
  // no-op when NO_TAGS
  CHECK_ZEROTAGS(ptr._b, CHECK_FETCHLENGTH(ptr._p, ptr._b,0),
		 ptr._p, n/*, 0*/);
}

// copy the tags for the 'n' bytes starting at 'src' to the
// tags for the 'n' bytes starting at 'dest'; tries to handle
// overlapping memory areas properly, because we do not trust
// the programmer to respect e.g. memcpy's requirement of non-
// overlapping areas
__inline static void wildp_copy_tags(wildp_char dest, wildp_char src, int n)
{
  unsigned int srclen = CHECK_FETCHLENGTH(src._p, src._b, 0);
  unsigned int destlen = CHECK_FETCHLENGTH(dest._p, dest._b, 0);

  if (dest._p < src._p) {
    // in the old memmove_www, the forward copy was used when it
    // appeared that src and dest don't overlap; that check was
    // wrong because the *tags* might have overlapped anway; but it
    // suggests forward may be preferred for performance reasons, so
    // a possible micro-optimization is to do a more careful check
    // for nonoverlapping and use forward in that case
    CHECK_COPYTAGSFORW(src._b, srclen, src._p,
		       dest._b, destlen, dest._p, n);
  }
  else if (dest._p > src._p) {
    CHECK_COPYTAGSBACK(src._b, srclen, src._p,
		       dest._b, destlen, dest._p, n);
  }
  else {
    // dest and src are the same place; nothing to do
  }
}


// verify the memory is writable, and then clear the tags
// Also does a bounds check (via wildp_verify_at_least)
__inline static void wildp_write_atleast(wildp_char ptr, int n)
{
  wildp_verify_atleast(ptr, n);
  wildp_clear_tags(ptr, n);
}

// verify_nul, for wild pointers
// Also does a bounds check (via wildp_length)
__inline static void wildp_verify_nul(wildp_char ptr)
{
  ccured_verify_nul(ptr._p, wildp_length(ptr));
}


// ------------------- general-purpose: seqp ---------------------
// similar section to the above, but for sequence pointers

// given a seq pointer, return the # of bytes legal to read/write
// starting from its _p field
__inline static int seqp_length(seqp_char ptr)
{
  return (intptr_t)ptr._e - (intptr_t)ptr._p;
}

// fail unless there are >=n bytes read/writable after ptr
__inline static void seqp_verify_atleast(seqp_char ptr, int n)
{
  if (n < 0) {
    CCURED_FAIL(FAIL_LBOUND FILE_AND_LINE);
  }
  if (n > seqp_length(ptr)) {
    CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
  }
}

// I'm not consistent is using this for seq/fseq, but I may as well
// keep the ones I have
#define seqp_write_atleast(ptr, n) seqp_verify_atleast(ptr, n)


// ------------------- general-purpose: fseqp ---------------------
// similar section to the above, but for forward-sequence pointers

// given an fseq pointer, return the # of bytes legal to read/write
// starting from its _p field
__inline static int fseqp_length(fseqp_char ptr)
{
  return (intptr_t)ptr._e - (intptr_t)ptr._p;
}

// same for a meta-fseq
__inline static int fseqcp_length(fseqcp_char ptr)
{
  return (intptr_t)ptr._e - (intptr_t)ptr._p;
}

// fail unless there are >=n bytes read/writable after ptr
__inline static void fseqp_verify_atleast(fseqp_char ptr, int n)
{
  if (n < 0) {
    CCURED_FAIL(FAIL_LBOUND  FILE_AND_LINE);
  }
  if (n > fseqp_length(ptr)) {
    CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
  }
}

#define fseqp_write_atleast(ptr, n) fseqp_verify_atleast(ptr, n)


// ---------------- tag manipulation ------------------
#ifndef NO_TAGS
/* Copy the tags going forward. Call this in conjuction with any memory
 * copy. The psrc and pdst and size should be _exactly_ as passed to memcpy.
 * NOTE THAT THIS MIGHT NOT WORK PROPERLY IN CASE OF OVERLAPPING AREAS
 * (since the bits are read first and then written as a block. To model
 * overlapping correctly we need to copy one tag at a time.) Note that this
 * is used in a somewhat unusual way in realloc.  */
void CHECK_COPYTAGSFORW(void *bsrc, /* base of src */
			unsigned int lensrc, /* len of src */
			char* psrc, /* pointer of src */
			void *bdst, /* base of dest */
			unsigned int lendst, /* words in dest*/
			char* pdst, /* pointer of dest */
			unsigned int size /* Size in bytes
					   * of the memory
					   * being copied */)
{
  TAGADDR stag, dtag;
  // Word starting address
  char    *alignSrc      = (char*)((uintptr_t)psrc & (~ 3));
  char    *alignDest     = (char*)((uintptr_t)pdst & (~ 3));
  char    *nextDestByte  = pdst + size; // Byte after the last copied
  int     bitsToCopy     = CHECK_NRTAGBITS(psrc, psrc + size);
  U32     srcTags   = 0;  // Keep some srcTags in here (always at LSB)
  int     nrSrcTags = 0;  // How many live bits we have in srcTags
  int     first = 1;      // A marker that says that we are copying the first

  /* If the alignment of the destination is different from that of the
   * source then we just zero out all of the destination tags  */
  if(((uintptr_t)psrc ^ (uintptr_t)pdst) & 3) {
    CHECK_ZEROTAGS(bdst, lendst, pdst, size/*, 0*/);
    return;
  }
  // Assume for now the we are copying whole words always
  stag  = CHECK_FETCHTAGADDR(bsrc, lensrc, alignSrc);
  dtag  = CHECK_FETCHTAGADDR(bdst, lendst, alignDest);
  // While there are some more bits in the source
  while(bitsToCopy) {
    // See if we need to refill srcTags
    if(nrSrcTags == 0) {
      srcTags = (*stag.word) >> stag.bit;
      nrSrcTags = MIN(32 - stag.bit, bitsToCopy);
      if(first) { // The first batch of bits
	first = 0;
	// If we are doing partial word read and write
	if(((uintptr_t)pdst & 3)) {
	  // We know that source and destination have the same alignment
	  srcTags &= (~ TAGBITSMASK); // Zero out the tag for the first word
	}
	/* gn: this is not necessary anymore */
//        if(! (srcTags & TAGBITSMASK) || (void*)alignDest > bdst) {
//           /* We are starting the write with a tag 0. Must zero the previous
//            * tag as well */
//          // Pretend we have started behind with src
//          stag.bit -= TAGBITS;
//          if(stag.bit == - TAGBITS) {
//            stag.word --;
//            stag.bit  += 32;
//          }
//          dtag.bit -= TAGBITS;
//          if(dtag.bit == - TAGBITS) {
//            dtag.word --;
//            dtag.bit += 32;
//          }
//          srcTags <<= TAGBITS; // Insert a 0 tag
//          bitsToCopy += TAGBITS;
//        }
      }
      if(bitsToCopy == nrSrcTags) { // This is the last batch
	if(((uintptr_t)nextDestByte & 3)  ||
	   // We are ending the copy with the first half of a fat pointer
	   ((srcTags >> (nrSrcTags - TAGBITS)) & TAGBITSMASK)) {
	  // Zero out the tag for the last word
	  srcTags &= (~ (TAGBITSMASK << (nrSrcTags - TAGBITS)));
	}
      }
      stag.bit  += nrSrcTags;
      if(stag.bit >= 32) {
	stag.word ++;
	stag.bit -= 32;
      }
    }
    // Put some tags in the destination
    {
      int tocopy  = MIN(nrSrcTags, 32 - dtag.bit);
      U32 mask    = tocopy < 32 ? (1 << tocopy) - 1 : (U32)-1;
      U32 towrite = (srcTags & mask) << dtag.bit;
      *dtag.word  = (*dtag.word & (~ (mask << dtag.bit))) | towrite;
      // Advance bit pointers
      nrSrcTags   -= tocopy;
      bitsToCopy  -= tocopy;
      srcTags     >>= tocopy;
      dtag.bit    += tocopy;
      if(dtag.bit == 32) { // Move on to the next destination pointer
	dtag.word ++;
	dtag.bit  = 0;
      }
    }
  }
}

/* Copy the tags going backward. The psrc, pdst and size arguments should be
 * exactly as passed to memcpy. The copying is done going backwards from the
 * last word. NOTE THAT THIS MIGHT NOT WORK PROPERLY IN CASE OF OVERLAPPING
 * AREAS (since the bits are read first and then written as a block. To
 * model overlapping correctly we need to copy one tag at a time.) Note that
 * this is used in a somewhat unusual way in realloc.  */
void CHECK_COPYTAGSBACK(void *bsrc, /* base of src */
			unsigned int lensrc, /* len of src */
			char* psrc, /* pointer of src */
			void *bdst, /* base of dest */
			unsigned int lendst, /* words in dest*/
			char* pdst, /* pointer of dest */
			unsigned int size)
{
  TAGADDR stag, dtag;
  // Word starting address
  //  char    *alignSrc      = (char*)((U32)psrc & (~ 3));
  char    *nextSrcByte   = psrc + size; // Byte after the last copied
  char    *nextSrcWord   = (char*)((uintptr_t)(nextSrcByte + 3) & (~ 3));
  //char    *alignDest     = (char*)((U32)pdst & (~ 3));
  char    *nextDestByte  = pdst + size; // Byte after the last copied
  char    *nextDestWord  = (char*)((uintptr_t)(nextDestByte + 3) & (~ 3));
  int     bitsToCopy     = CHECK_NRTAGBITS(psrc, psrc + size);
  U32     srcTags   = 0;  // Keep some srcTags in here (always at LSB)
  int     nrSrcTags = 0;  // How many live bits we have in srcTags
  int     first = 1;      // A marker that says that we are copying the first

  /* If the alignment of the destination is different from that of the
   * source then we just zero out all of the destination tags  */
  if(((uintptr_t)psrc ^ (uintptr_t)pdst) & 3) {
    CHECK_ZEROTAGS(bdst, lendst, pdst, size/*, 0*/);
    return;
  }
  // Assume for now the we are copying whole words always
  stag  = CHECK_FETCHTAGADDR(bsrc, lensrc, nextSrcWord - 4);
  dtag  = CHECK_FETCHTAGADDR(bdst, lendst, nextDestWord - 4);
  // While there are some more bits in the source
  while(bitsToCopy > 0) {
    // See if we need to refill srcTags
    if(nrSrcTags == 0) {
      srcTags = (*stag.word);
      // Maybe all the source tags fit into one word
      nrSrcTags = stag.bit + TAGBITS;
      if(nrSrcTags > bitsToCopy) {
	srcTags >>= (nrSrcTags - bitsToCopy);
	nrSrcTags = bitsToCopy;
      }
      if(first) { // The first batch. Meaning the bits at highest addresses
	first = 0;
	// If partial word write
//        if(((U32)nextDestByte & 3) ||
//           // We end the copy with the first half of a fat pointer
//           ((srcTags >> (nrSrcTags - TAGBITS)) & TAGBITSMASK)) {
//          // Zero out the last tag
//          srcTags &= (~ (TAGBITSMASK << (nrSrcTags - TAGBITS)));
//        }
      }
      if(nrSrcTags == bitsToCopy) {
	// Last batch. Meaning the bits at lowest addr
	// If partial word write, zero out the tag
//        if(((U32)pdst & 3)) {
//          srcTags &= (~ TAGBITSMASK);
//        }
      }
      stag.bit  = 32 - TAGBITS;
      stag.word --;
    }
    // Put some tags in the destination
    {
      int tocopy;
      int doff;
      U32 mask, towrite;
    //WriteToDest:
      if(nrSrcTags < dtag.bit + TAGBITS) {
	tocopy = nrSrcTags;
	doff   = dtag.bit + TAGBITS - nrSrcTags;
      } else {
	tocopy = dtag.bit + TAGBITS;
	doff   = 0;
      }
      mask    = tocopy < 32 ? (1 << tocopy) - 1 : (U32)-1;
      towrite = ((srcTags >> (nrSrcTags - tocopy)) & mask) << doff;
      *dtag.word  = (*dtag.word & (~ (mask << doff))) | towrite;
      // Advance bit pointers
      nrSrcTags   -= tocopy;
      dtag.bit   -= tocopy;
      bitsToCopy  -= tocopy;
      if(dtag.bit < 0) { // Move on to the next destination pointer
	dtag.word --;
	dtag.bit  = 32 - TAGBITS;
      }
//      // If we have just copied the tag at the lowest address
//      // And the first tag is 0, then we must zero the previous tag as well
//      if(bitsToCopy == 0 && (! (srcTags & TAGBITSMASK)) &&
//         (void*)alignDest > bdst) {
//        tocopy = TAGBITS;
//        srcTags = 0;
//        nrSrcTags = TAGBITS;
//        goto WriteToDest;
//      }
    }
  }
}
#endif // !NO_TAGS

#ifndef CCURED_NO_WILD_WRAPPERS
// ------------------- malloc -------------------------
// malloc, returning a wild pointer; has to allocate and initialize
// the extra bookkeeping info for wild areas
wildp_void malloc_w(unsigned int size)
{
  wildp_void res;
  int  nrWords    = BYTESTOWORDS(size);       // align the size
  int  nrTagWords = CHECK_NRTAGWORDS(nrWords);

  // allocate: one word for the length, nrWords for data, nrTagWords for tags
  int  newSize    = ((1 + nrWords + nrTagWords) << 2);

  U32  *alloc     = (U32*)malloc(newSize);
  if(! alloc) {
    CCURED_FAIL(FAIL_MALLOC  FILE_AND_LINE);
    abort(); // If we continue after failure
  }

  *(alloc++)   = nrWords;   // Write the length.
  res._p = (void*)alloc;    // This is the start of the data
  res._b = (void*)alloc;
  alloc += nrWords;         // Skip the data section

  for (; nrTagWords; nrTagWords--) { // Clear the tags
    *(alloc++) = 0;
  }

  return res;
}
#endif

#ifndef CCURED_NO_MALLOC
// allocate, yield fseq
// (sm: why isn't this called malloc_f?)
fseqp_void malloc_fseq_f(unsigned size)
{
  fseqp_void res;

  // align size; fseq's e field needs to be aligned (?) so it can only
  // express boundaries that are aligned (theoretical bugfix: we used
  // to align 'e' without aligning size, leaving potentially three
  // bytes unprotected)
  size = ALIGNBYTES(size);

  res._p = (void*)malloc(size);
  res._e = ((char*)res._p) + size;      // first inaccessible word

  return res;
}

// ----------------------- free ----------------------
// note: when the GC is enabled, calls to free are no-ops anyway;
// the below is for the case where we disable the GC and just
// trust the programmer to call free correctly, as a way to measure
// the GC's performance impact

// Use wrapperFree if you need this
// void free_safe(void *x)
// {
//   free(x);
// }

#ifndef CCURED_NO_WILD_WRAPPERS
void free_w(wildp_void x)
{
  U32 *p = (U32*)x._p;
  if(! x._b || x._b != p) {
    CCURED_FAIL(FAIL_FREE  FILE_AND_LINE);
  }

  // Now find the real start
  // (sm: there's been some debate about whether this -1
  // should be here.. but for now I think it should..)
  free((void*)(p-1));
}
#endif

void free_f(fseqp_void x)
{
  // Wes had a comment here basically pointing out the unsoundness of
  // believing the program's use of free(); as I've (now) noted above,
  // these wrappers are effectively no-ops in the "official" CCured
  free(x._p);
}

void free_F(fseqp_void x) { free_f(x); }

// sm: I find it strange that we have free_q but not malloc_q ...
void free_q(seqp_void x)
{
  // sm: we used to fail when x._b was null, but calling free()
  // on a NULL pointer *is* legal according to my man pages, and
  // STLport does so in ios_base::~ios_base (ios.cc:297)
  if (x._b != x._p) {
    CCURED_FAIL(FAIL_FREE  FILE_AND_LINE);
  }
  free(x._b);
}
void free_Q(seqp_void x) { free_q(x); }

void free_ms(safecp_void x)
{
  free(x._p);
}

void free_mf(fseqcp_void x)
{
  free(x._p);
}

void free_mq(seqcp_void x)
{
  if (x._b != x._p) {
    CCURED_FAIL(FAIL_FREE  FILE_AND_LINE);
  }
  free(x._b);
}
void free_mQ(seqcp_void x) { free_mq(x); }

#ifndef CCURED_NO_WILD_WRAPPERS
void free_i(wildp_void x)
{
  free_w(x);
}
#endif

void free_rs(void * p, struct RTTI_ELEMENT * m )
{
  free(p);
}


#ifndef CCURED_NO_WILD_WRAPPERS
// -------------------- calloc ----------------------
wildp_void calloc_w(unsigned int count, unsigned int osize)
{
  // the unchecked multiply here is ok, because our bookkeeping info
  // only ever stores the product, so if that ends up smaller than
  // what the programmer thought we'll catch it later in a bounds check
  unsigned size = ALIGNBYTES(osize * count);

  // let's just call malloc; it simplifies the code and fixes a bug I noticed
  // (holdover from the two-bits tags days)
  wildp_void res = malloc_w(size);

  // ccured_malloc clears the area, but in case we're not using the gc..
  // (malloc_w set length and zeroed tags already; we just zero data)
  memset(res._p, 0, size);

  return res;
}
#endif // CCURED_NO_WILD_WRAPPERS

// sm: why isn't this called calloc_f?
fseqp_void calloc_fseq_f(unsigned int count,
			unsigned int osize)
{
  unsigned size = ALIGNBYTES(osize * count);
  fseqp_void res = malloc_fseq_f(size);
  memset(res._p, 0, size);
  return res;
}


// sm: where did this **bizarre** nonsense come from?
//void *calloc_rbnode(unsigned int nrelem, unsigned int osize)
//{
//  char *res = (char*)calloc(nrelem, osize);
//  char *where = res + 5 * 4;
//  int i;
//  //  printf("Allocating %d RBNode's, each of size %d (24 + %d)\n",
//  //         nrelem, osize, osize - 24);
//  for(i=0; i<(int)nrelem; i++, where += osize) {
//    *((int*)where) = osize - 5 * 4;
//  }
//  return (void*)res;
//}

#ifndef CCURED_NO_WILD_WRAPPERS
// ------------------------- realloc ------------------------
wildp_void realloc_ww(wildp_void orig, unsigned int newsz)
{
  int  nrWords    = BYTESTOWORDS(newsz);
  int  nrTagWords = CHECK_NRTAGWORDS(nrWords);            // 0 if NO_TAGS #defined
  int  newSize    = ((1 + nrWords + nrTagWords) << 2);    // length/data/tags
  int  origNrWords;
  //U32  *origbase  = (U32*)orig._b;
  U32  *alloc;

  if (orig._b != orig._p) {
    CCURED_FAIL(FAIL_REALLOC  FILE_AND_LINE);
  }

  if (!orig._p) {        // NULL argument. A straight malloc
    return malloc_w(newsz);
  }

  if (newsz == 0) {      // A free operation. Pass it along.
    free_w(orig);
    orig._p = NULL;
    orig._b = NULL;
    return orig;
  }

  // The old number of words
  origNrWords = CHECK_FETCHLENGTH(orig._p, orig._b, 0);
  if(origNrWords == nrWords) {
    return orig; // No change
  }

  if (nrWords < origNrWords) {
    // Shrinking. Move the tags to lower addresses before we realloc.
    // copy left to right for proper overlapping behavior
    CHECK_COPYTAGSFORW(orig._b, origNrWords, (char*)orig._b,
		       orig._b, nrWords, (char*)orig._b,
		       nrWords << 2);

    // Now realloc. The (old) length, data and the surviving tags will be copied
    alloc = (U32*)realloc((U32*)orig._b - 1, newSize);
    if (!alloc) {
      CCURED_FAIL(FAIL_REALLOC_SHRINK  FILE_AND_LINE);
    }
  }
  else {
    // Growing. Realloc first and then move the tags to higher addresses
    alloc = (U32*)realloc((U32*)orig._b - 1, newSize);
    if (!alloc) {
      CCURED_FAIL(FAIL_REALLOC_GROW  FILE_AND_LINE);
    }
    // Move the tags from last to first for proper overlapping behavior
    CHECK_COPYTAGSBACK(alloc + 1, origNrWords, (char*)(alloc + 1),
		       alloc + 1, nrWords, (char*)(alloc + 1),
		       origNrWords << 2);

    // sm: bugfix: need to zero out the cleared space, otherwise the tags
    // left behind lead to bad stuff; alternatively, clearing the tags for
    // the left-behind memory should also be adequate
    memset(alloc+1+origNrWords, 0, (nrWords-origNrWords) * 4);
  }

  // Set the new length
  *alloc = nrWords;
  alloc ++;  // Skip the length
  orig._p = (void*)alloc;
  orig._b = (void*)alloc;
  return orig;
}
#endif


// sm: our current implementation actually can't hit this, because we don't
// treat realloc polymorphically; this was from experimenting with James'
// options to do inference unsoundly
fseqp_void realloc_ff(fseqp_void ptr, size_t newsize)
{
  // I can't be sure 'ptr' really is the start of a memory block, so I'll
  // play it safe; GC should clean up after me
  fseqp_void ret;

  size_t oldsize = (intptr_t)ptr._e - (intptr_t)ptr._p;
  if (oldsize >= newsize) {
    // just give them back the same pointer, and don't release any memory
    ret._p = ptr._p;
    ret._e = (void*)( (intptr_t)(ptr._p) + newsize );
    return ret;
  }

  // allocate some new space
  ret._p = (void*)malloc(newsize);
  if (!ret._p) {
    CCURED_FAIL(FAIL_MALLOC  FILE_AND_LINE);
    abort(); // If we continue after failureq
  }
  ret._e = (void*)( (intptr_t)(ret._p) + newsize );

  // copy the original data into this new buffer
  memcpy(ret._p, ptr._p, oldsize);

  // zero out the remainder
  memset((void*)( (intptr_t)(ret._p) + oldsize ), 0, newsize-oldsize);

  // finally give back this pointer
  return ret;
}

// jc: this function isn't actually correct; we need to move the metadata
// around in the reallocated chunk to make it correct.  this is difficult
// because we don't know the size of the chunk.  even then, we might be
// breaking external pointers to that metadata.  for now, this stub is
// here for reallocs that don't involve metadata.
fseqcp_void realloc_mfmf(fseqcp_void ptr, size_t newsize)
{
  fseqcp_void ret;
  ret._p = ccured_realloc(ptr._p, newsize);
  ret._e = (void*)((char*)ret._p + newsize);
  ret._mp = 0; // TODO
  return ret;
}

// sm: I don't know why I wrote the above wrapper to be so complicated,
// when I think this simple one will do ..
fseqp_char realloc_fs(char *ptr, size_t newsize)
{
  fseqp_char ret;
  ret._p = (void*)ccured_realloc(ptr, newsize);
  ret._e = ret._p + newsize;
  return ret;
}

seqp_char realloc_qq(seqp_char ptr, size_t newsize)
{
  seqp_char ret;
  long oldsize = (long)ptr._e - (long)ptr._b;
  if (ptr._p != ptr._b || oldsize < 0)
  {
    CCURED_FAIL(FAIL_REALLOC  FILE_AND_LINE);
  }
  ret._p = (void*)ccured_realloc(ptr._p, newsize);
  ret._e = ret._p == NULL? NULL : ret._p + newsize;
  ret._b = ret._p;

  //if we're growing, zero the new memory (in case it contains pointers.)
  if (ret._p != NULL && (size_t)newsize > (size_t)oldsize)
  {
    //the first oldsize bytes were initialized in realloc.
    memset(ret._p + oldsize, '\0', newsize - oldsize);
  }
  return ret;
}

seqp_char realloc_QQ(seqp_char ptr, size_t newsize)
{
  seqp_char ret;
  if (newsize == 0)
  {
    ret._p = NULL;
    ret._e = NULL;
    ret._b = NULL;
    free(ptr._p);
    return ret;
  }

  //The buffer should be null-terminated.
  //  So add one to the buffer size,
  ret = realloc_qq(ptr, newsize+1);
  if (ret._p != 0)
  {
    //  set that new byte to 0,
    (ret._p)[newsize] = '\0';
    //  and don't let the program touch it.
    ret._e = (char*)ret._e - 1;
  }
  return ret;
}

seqp_char realloc_Qq(seqp_char ptr, size_t newsize)
{
  return realloc_QQ(ptr, newsize);
}


// weimer, copied from scott's realloc_fs
unsigned long realloc_q(seqp_void ptr, size_t newsize)
{

  return (unsigned long)ccured_realloc(ptr._p,newsize);
}
#endif

#ifndef CCURED_NO_WILD_WRAPPERS
// ------------------------ fopen ------------------------
wildp_FILE fopen_wss(char* fname, char* mode)
{
  wildp_FILE res;
  res._p = fopen(fname, mode);

  // this little trick helps ensure the program treats FILE* opaquely
  res._b = (void*)0;       // We should not be reading from here !!!

  return res;
}

// --------------- accesses to stdin/stdout/stderr ------------------
 //#ifdef _MSVC
 //// A major hack to intercept accesses to _iob on MSVC
 //void * get_iob(int n) {
 //  return (void*)& _iob[n];
 //}
 //wildp_void get_iob_w(int n) {
 //  wildp_void res;
 //  res._p = (void*)& _iob[n];
 //  res._b = (void*)0;
 //  return res;
 //}
 //

// all uses of stdin/stdout/stderr in the program are translated
// into get_stdin()/get_stdout()/get_stderr()
wildp_void get_stdin_w()
{
  wildp_void res;
  res._p = (void*)stdin;
  res._b = 0;
  return res;
}
wildp_void get_stdout_w()
{
  wildp_void res;
  res._p = (void*)stdout;
  res._b = 0;
  return res;
}
wildp_void get_stderr_w()
{
  wildp_void res;
  res._p = (void*)stderr;
  res._b = 0;
  return res;
}
#endif // CCURED_NO_WILD_WRAPPERS

FILE *get_stdin() {
  return stdin;
}
FILE *get_stdout() {
  return stdout;
}
FILE *get_stderr() {
  return stderr;
}

// matth: OpenSSL needs these.  FILE*s are put into SEQR nodes, so we need
// bounds.
seqp_FILE get_stdin_q()
{
  seqp_FILE res;
  res._p = (FILE*)stdin;
  res._b = res._p;
  res._e = res._p + 1;
  return res;
}
seqp_FILE get_stdout_q()
{
  seqp_FILE res;
  res._p = (FILE*)stdout;
  res._b = res._p;
  res._e = res._p + 1;
  return res;
}
seqp_FILE get_stderr_q()
{
  seqp_FILE res;
  res._p = (FILE*)stderr;
  res._b = res._p;
  res._e = res._p + 1;
  return res;
}

fseqp_FILE get_stdin_f()
{
  fseqp_FILE res;
  res._p = (FILE*)stdin;
  res._e = res._p + 1;
  return res;
}
fseqp_FILE get_stdout_f()
{
  fseqp_FILE res;
  res._p = (FILE*)stdout;
  res._e = res._p + 1;
  return res;
}
fseqp_FILE get_stderr_f()
{
  fseqp_FILE res;
  res._p = (FILE*)stderr;
  res._e = res._p + 1;
  return res;
}

#ifndef CCURED_NO_WILD_WRAPPERS


// --------------- misc FILE* functions ----------------
// sm: UNSOUND: I think these are a security hole for a malicious
// program: we let the programmer pass any value at all to fflush
// (etc.), so if the programmer *does* know how libc behaves and what
// the structure of FILE* is, a carefully-crafted bogus FILE could
// break memory safety

int fflush_w(wildp_FILE f)
{
  return fflush(f._p);
}

int fclose_w(wildp_FILE f)
{
  return fclose(f._p);
}

#ifdef _GNUCC
  /* Appears in putc for GCC */
  #ifdef __CYGWIN__
    int __swbuf_w(int c, wildp_void fl) {
      return __swbuf(c, (FILE*)fl._p);
    }
    /* Appears in getc for GCC */
    int __srget_w(wildp_void fl) {
      return __srget((FILE*)fl._p);
    }
  #endif // __CYGWIN__

  // sm: internally, my putc uses _IO_putc
  // see /usr/include/features.h to find glibc version numbers
  #if defined(__GLIBC__) && __GLIBC__ == 2
    int _IO_putc_w(int c, wildp_void fl) {
      return _IO_putc(c, (FILE*)fl._p);
    }

    int _IO_getc_w(wildp_void fl) {
      return _IO_getc((FILE*)fl._p);
    }
  #endif
#endif // _GNUCC

int putc_w(int c, wildp_void fl) {
  return putc(c, (FILE*)fl._p);
}

int getc_w(wildp_void fl) {
  return getc((FILE*)fl._p);
}

// sm: similar (no error checking..) wrappers for scott/putc
int fputc_w(int c, wildp_void fl) {
  return fputc(c, (FILE*)fl._p);
}

int fgetc_w(wildp_void fl) {
  return fgetc((FILE*)fl._p);
}

int puts_w(wildp_char s) {
  return puts((char*)s._p);
}

int fileno_w(wildp_FILE f) {
  return FILENO(f._p);
}

int ferror_w(wildp_FILE fp) {
  return ferror(fp._p);
}

int fseek_w(wildp_FILE fp, long offset, int whence)
{
  return fseek(fp._p, offset, whence);
}

void clearerr_w(wildp_FILE fp)
{
  clearerr(fp._p);
}


// ---------------------- fread ------------------------
size_t fread_ws(wildp_char buff, size_t size, size_t count, FILE *fl)
{
  size_t requested = __ccured_mult_u32(size, count);
  size_t res;
  wildp_write_atleast(buff, requested);
  res = fread(buff._p, size, count, fl);
  return res;
}

size_t fread_ww(wildp_char buff, size_t size, size_t count, wildp_FILE fl)
{
  return fread_ws(buff, size, count, fl._p);
}

// ------------------------- fwrite -----------------------
size_t fwrite_ws(wildp_char buff, size_t size, size_t count, FILE *fl)
{
  size_t requested = __ccured_mult_u32(size, count);
  size_t res;
  wildp_verify_atleast(buff, requested);
  res = fwrite(buff._p, size, count, fl);
  return res;
}

size_t fwrite_ww(wildp_char buff, size_t size, size_t count, wildp_FILE fl)
{
  return fwrite_ws(buff, size, count, fl._p);
}

// -------------------------- fgets -----------------------
wildp_char fgets_wws(wildp_char buffer, int size, FILE *stream)
{
  wildp_char res;
  wildp_write_atleast(buffer, size);
  res._p = fgets(buffer._p, size, stream);
  res._b = buffer._b;
  return res;
}

/* fgets and gets have different behavior concerning \n. Since we want gets
 * to use fgets, we write a separate version of fgets which replaces the \n
 * with \0, as gets would do */
wildp_char fgets_nonewline_wws(wildp_char buffer, int size, FILE *stream)
{
  wildp_char res = fgets_wws(buffer, size, stream);

  char *tmp = res._p;
  while (*tmp != '\n' && *tmp != '\0') tmp++;     // find newline or nul
  *tmp ='\0';

  return res;
}

/* It is unsound to use gets, so we turn it into a fgets */
wildp_char gets_ww(wildp_char buffer)
{
  return fgets_nonewline_wws(buffer, wildp_length(buffer), stdin);
}

wildp_char fgets_www(wildp_char buffer, int size, wildp_FILE stream)
{
  return fgets_wws(buffer, size, stream._p);
}



// -------------------- read ----------------------
int read_w(int fid, wildp_char buff, unsigned int size)
{
  wildp_write_atleast(buff, size);
  return READ(fid, buff._p, size);
}

int read_q(int fid, seqp_char buff, unsigned int size)
{
  seqp_write_atleast(buff, size);
  return READ(fid, buff._p, size);
}

int read_f(int fid, fseqp_char buff, unsigned int size)
{
  fseqp_write_atleast(buff, size);
  return READ(fid, buff._p, size);
}

// --------------------- write -------------------
int write_w(int fid, wildp_char buff, unsigned int size)
{
  wildp_verify_atleast(buff, size);
  return WRITE(fid, buff._p, size);
}

int write_q(int fid, seqp_char buff, unsigned int size)
{
  seqp_verify_atleast(buff, size);
  return WRITE(fid, buff._p, size);
}

// ---------------- misc file-descriptor funcs -----------------
#ifdef _MSVC
# define __STAT   struct _stat
#else
# define __STAT   struct stat
#endif

int fstat_w(int fid, wildp_char buff)
{
  wildp_write_atleast(buff, sizeof(__STAT));
  return FSTAT(fid, (__STAT *)buff._p);
}

int stat_ww(wildp_char path, wildp_char buff)
{
  wildp_write_atleast(buff, sizeof(__STAT));
  wildp_verify_nul(path);
  return STAT(path._p, (__STAT *)buff._p);
}
#undef __STAT

int open_w(wildp_char path, int oflag, int pmode)
{
  wildp_verify_nul(path);
  return OPEN(path._p, oflag, pmode);
}

int unlink_w(wildp_char path)
{
  wildp_verify_nul(path);
  return UNLINK(path._p);
}

#endif

#ifndef CCURED_NO_OPEN
/* We introduce this function sometimes for the three argument open,
   used only when curetype=wild. */
int open_with_mode(char *file, int flags, int mode) {
  return OPEN(file, flags, mode);
}
#endif

// ----------------- setjmp/longjmp --------------------
// allowing the programmer to call longjmp is UNSOUND because
// the jmp_buf could be filled with arbitrary trash, which
// then gets copied into the processor registers; for the safe/seq
// world one possible solution is to use the patcher to make
// the jmp_buf type opaque, so the programmer can't touch it;
// but then there's still the problem of calling longjmp after
// the setjmp's caller has returned, which I don't know how to
// solve

// I want to cast, but jmp_buf is defined as an array type..
struct jmp_buf_wrapper {
  jmp_buf buf;
};

// given a fat pointer, make it look like a jmp_buf
#define AS_JMP_BUF(ptr) ((struct jmp_buf_wrapper*)ptr._p)->buf

#if 0   // no wrappers for setjmp
  // TODO: you can't wrap setjmp!  once the wrapper returns, that
  // means setjmp's caller has returned, so the context to which
  // longjmp wants to return is gone!

  int setjmp_w(wildp_char jbuf)
  {
    wildp_write_atleast(jbuf, sizeof(jmp_buf));
    return setjmp(AS_JMP_BUF(jbuf));
  }

  // (glibc-ism) the leading underscore means it does not save
  // the signal context
  int _setjmp_w(wildp_char jbuf)
  {
    return setjmp_w(jbuf);
  }

  #if defined(_GNUCC) && !defined(__CYGWIN__)
    // sm: isn't this wrong?  I mean, sigsetjmp takes a buffer
    // which is larger than a simple jmp_buf, right?
    // update: no, at least on glibc 2, the two structures are the same,
    // and it contains a flag inside it to tell whether the signal
    // mask was saved
    int __sigsetjmp_w(wildp_char jbuf, int __savemask)
    {
      wildp_write_atleast(jbuf, sizeof(jmp_buf));
      return __sigsetjmp(AS_JMP_BUF(jbuf), __savemask);
    }
  #endif

  // sm 4/01/02: in the seq/fseq case, box.ml inserts the checks
  // directly (!), so there seems to be no way to provoke a need for
  // setjmp_q
  int setjmp_q(seqp_char jbuf)
  {
    seqp_verify_atleast(jbuf, sizeof(jmp_buf));
    return setjmp(AS_JMP_BUF(jbuf));
  }

  int _setjmp_q(seqp_char jbuf)
  {
    return setjmp_q(jbuf);
  }

  #if defined(_GNUCC) && !defined(__CYGWIN__)
    int __sigsetjmp_q(seqp_char jbuf, int __savemask)
    {
      seqp_verify_atleast(jbuf, sizeof(jmp_buf));
      return __sigsetjmp(AS_JMP_BUF(jbuf), __savemask);
    }
  #endif
#endif // 0


void longjmp_w(wildp_char jbuf, int res)
{
  wildp_verify_atleast(jbuf, sizeof(jmp_buf));
  longjmp(AS_JMP_BUF(jbuf), res);
}
void longjmp_q(seqp_char jbuf, int res)
{
  seqp_verify_atleast(jbuf, sizeof(jmp_buf));
  longjmp(AS_JMP_BUF(jbuf), res);
}


// ---------------- string-to-number conversions ---------------
#ifndef CCURED_NO_WILD_WRAPPERS
double atof_w(wildp_char str)
{
  wildp_verify_nul(str);
  return atof(str._p);
}

int atoi_w(wildp_char str)
{
  wildp_verify_nul(str);
  return atoi(str._p);
}

long atol_w(wildp_char str)
{
  wildp_verify_nul(str);
  return atol(str._p);
}
#endif


// --------------------- qsort -----------------
#ifndef NO_TAGS
// return 1 if:
//   - 'base' is aligned to a word boundary
//   - 'size' is aligned to a word boundary
//   - the tags corresponding to each element of size 'size' are
//     identical to every other element, in the range 'base' up to
//     'base + nelts*size'
// otherwise return 0
int qsort_regular_tags(wildp_char base, size_t nelts, size_t size)
{
  unsigned word, elt;     // iterators for loops below
  unsigned areaSize = CHECK_FETCHLENGTH(base._b, base._p, 0);

  // pointer to the first word of the first element
  U32 *firstElt = (U32*)base._p;

  // do this check after declaring the variables...
  if (((intptr_t)base._p & 3) || (size & 3)) {
    return 0;   // unaligned
  }

  // now size is in WORDS (was in bytes)
  size >>= 2;

  // iterate over the words in an element
  for (word=0; word<size; word++) {
    // what is the first element's tag for this word?
    unsigned firstTag = CHECK_FETCHTAGBIT(base._b, areaSize, firstElt);

    // iterate over all elements beyond the first
    U32 *otherElt = firstElt + size;
    for (elt=1; elt<nelts; elt++) {
      // is the tag for this elt/word equal to the corresponding tag
      // for the first elt?
      if (firstTag != CHECK_FETCHTAGBIT(base._b, areaSize, otherElt)) {
	// they differ; we fail
	return 0;
      }

      // advance to next element
      otherElt += size;
    }

    // advance to next word in the first element
    firstElt++;
  }

  // every element matched the first
  return 1;
}
#else
  #define qsort_regular_tags(b,n,s) 1
#endif


void qsort_zero_tags_w(wildp_char base, size_t nelts, size_t size)
{
  // zero the tags, *unless* they happen to be such that sorting
  // cannot change them
  if (qsort_regular_tags(base, nelts, size)) {
    // every element's tags are the same!  sorting cannot affect them
    wildp_verify_atleast(base, __ccured_mult_u32(nelts, size));
  }
  else {
    // tags not the same, conservatively clear them
    wildp_write_atleast(base, __ccured_mult_u32(nelts, size));
  }
}

//if it's not wild, don't do anything:
void qsort_zero_tags_f(wildp_char base, size_t nelts, size_t size) {}
void qsort_zero_tags_q(wildp_char base, size_t nelts, size_t size) {}
void qsort_zero_tags_F(wildp_char base, size_t nelts, size_t size) {}
void qsort_zero_tags_Q(wildp_char base, size_t nelts, size_t size) {}
void qsort_zero_tags_mf(wildp_char base, size_t nelts, size_t size) {}
void qsort_zero_tags_mq(wildp_char base, size_t nelts, size_t size) {}

#ifndef CCURED_NO_WILD_WRAPPERS

// ---------------- str* functions -------------------
// throughout this section, I make the simplifying assumption that
// there are no pointers stored in regions pointed-to by the
// arguments; it would be a really strange program which had pointers
// in these areas but somehow knew their representations did not
// contain 0 bytes

//matth:  leave these here for INFERBOX=wild test cases
int strncmp_ww(wildp_char s1,
	       wildp_char s2,  unsigned int size)
{
  // sm: we used to have some code here which worried about
  // nul-termination, but that's irrelevant since strncmp
  // itself agrees not to look beyond 'size' bytes under
  // any circumstances

  wildp_verify_atleast(s1, size);
  wildp_verify_atleast(s2, size);
  return strncmp(s1._p, s2._p, size);
}

int strcmp_ww(wildp_char s1, wildp_char s2)
{
  // sm: then this code called strncmp_ww with a large length..
  // that seems to not be what we want..

  wildp_verify_nul(s1);
  wildp_verify_nul(s2);
  return strcmp(s1._p, s2._p);
}
char * strcpy_sww(wildp_char dest, wildp_char src)
{
  // the old code copied the tags; I'm going to assume if you're
  // using strcpy there aren't any pointers in this area, and
  // just clear the tags (if I'm wrong, pull from CVS around 2/01/02
  // to get the tag-copying version)
  wildp_verify_nul(src);
  wildp_write_atleast(dest, strlen(src._p)+1);
  strcpy(dest._p, src._p);
  return NULL;
}

wildp_char strcpy_www(wildp_char dest, wildp_char src)
{
  // the old code copied the tags; I'm going to assume if you're
  // using strcpy there aren't any pointers in this area, and
  // just clear the tags (if I'm wrong, pull from CVS around 2/01/02
  // to get the tag-copying version)
  wildp_verify_nul(src);
  wildp_write_atleast(dest, strlen(src._p)+1);
  strcpy(dest._p, src._p);
  return dest;
}
unsigned int strlen_w(wildp_char s)
{
  wildp_verify_nul(s);
  return strlen(s._p);
}

wildp_char strchr_ww(wildp_char s, int chr)
{
  wildp_char res;
  wildp_verify_nul(s);
  res._b = s._b;
  res._p = strchr(s._p, chr);
  return res;
}


wildp_char fattenstring(char *s)
{
  wildp_char ret;
  wildp_void res = malloc_w(1 + strlen(s));
  strcpy(res._p, s);
  ret._p = (char *)res._p;
  ret._b = res._b;
  return ret;
}


// sm: how can this work?  shouldn't our printf be checking that
// the passed base fields are valid?  possibly UNSOUND somewhere

// matth:  yes, this function is broken -- you can't print (or do anything
// else with) the return value.  I'm not sure how to fix this ... we could
// use fattenstring, but that would be a memory leak if "--nogc" is used, right?

wildp_char strerror_w(int errno)
{
  wildp_char res;
  res._p = strerror(errno);
  res._b = (void*)0;  // !!! No tags or length in there !
  return res;
}


// ----------------------- mem* functions ---------------------
int memcmp_ww(wildp_char dest, wildp_char src, unsigned int size)
{
  wildp_verify_atleast(dest, size);
  wildp_verify_atleast(src, size);
  return memcmp(dest._p, src._p, size);
}

#ifdef _MSVC
  void* memcpy(void *, void const *, unsigned int);
#endif

wildp_char memcpy_www(wildp_char dest, wildp_char src, unsigned int size)
{
  wildp_verify_atleast(dest, size);
  wildp_verify_atleast(src, size);
  wildp_copy_tags(dest, src, size);
  memcpy(dest._p, src._p, size);
  return dest;
}

wildp_char memmove_www(wildp_char dest, wildp_char src, unsigned int size)
{
  wildp_verify_atleast(dest, size);
  wildp_verify_atleast(src, size);
  wildp_copy_tags(dest, src, size);
  memmove(dest._p, src._p, size);
  return dest;
}


wildp_char memset_ww(wildp_char buffer, int c, size_t size)
{
  wildp_write_atleast(buffer, size);
  memset(buffer._p, c, size);
  return buffer;
}


// ------------------- time ------------------
time_t time_w(wildp_char timer)
{
  if (timer._p) {   // time accepts a NULL argument
    wildp_write_atleast(timer, sizeof(time_t));
  }
  return time((time_t*)timer._p);
}

#ifdef _GNUCC
  clock_t times_w(wildp_char tms)
  {
    wildp_write_atleast(tms, sizeof(struct tms));
    return times((struct tms*)tms._p);
  }


  // int gettimeofday(struct timeval *tv, struct timezone *tz);
  int gettimeofday_ws(wildp_char tv, struct timezone *tz)
  {
    wildp_write_atleast(tv, sizeof(struct timeval));
    return gettimeofday((struct timeval *)tv._p, tz);
  }
#endif

#endif // CCURED_NO_WILD_WRAPPERS

// ----------------- pointer cast log --------------------
// the idea here is, when a program fails with a non-pointer error,
// it's often not obvious where this non-pointer arose.  so,
// optionally, every time a non-pointer is created, we can log the
// source location where that happened.  then when the pointer failure
// happens, we may be able to report the source line that produced the
// bad value.

// does this mean we've *always* been doing this??
// no, it has to be enabled in box.ml

#define MIN_POINTER 0x100000U
#define MAX_POINTER (0xFFFFFFFFU - MIN_POINTER)
#if defined(_MSVC) && defined(_DEBUG)
//  wildp_void _CrtSetReportFile_ww(int reportMode, wildp_void f) {
//    _CrtSetReportFile(reportMode, f._p);
//    return f;
//  }
#endif /* _MSVC && _DEBUG */


typedef struct {
  unsigned long l;
  unsigned int id;
} LOG_ENTRY;
#define LOG_SIZE   (1 << 16)
LOG_ENTRY logBuffer[LOG_SIZE];
int logBufferP = 0; // Next free entry
int logFid = -1;
#include <fcntl.h>

int __ccuredLogNonPointers = 0;

#ifndef CCURED_NOLOG_NONPOINTERS

// Flush the log to a file
int flushLog()
{
  // See if we need to open the log file
  int toWrite = logBufferP * sizeof(LOG_ENTRY);
  if(toWrite <= 0)
    return 0;

  if(logFid < 0) {
    logFid = OPEN("__ccured_scalar.log",
		  O_CREAT  | O_TRUNC | O_RDWR | O_BINARY,
		  0777);
    if(logFid < 0) {
      CCURED_FAIL(FAIL_SCALARLOG  FILE_AND_LINE);
    }
  }
  if(toWrite != WRITE(logFid, & logBuffer[0], toWrite)) {
    CCURED_FAIL(FAIL_SCALARLOG  FILE_AND_LINE);
  }
  logBufferP = 0;
  return 0;
}

void __logScalar(int id, unsigned long l)  {
  // printf("Logging scalar %ld at ID=%d\n", l, id);
  if(l >= MIN_POINTER && l <= MAX_POINTER) {
    LOG_ENTRY *le = & logBuffer[logBufferP ++];
    le->l = l;
    le->id = id;
    // See if we need to dump the log out
    if(logBufferP == LOG_SIZE) {
      flushLog();
    }
  }
}


/* Scan the log and apply the given function to all entries. Stop when the
 * log is over or when the match function returns true. Scan log returns
 * true if it terminated because match returned true  */
int scanLog(int (*match)(uintptr_t, LOG_ENTRY *), uintptr_t closure) {
  flushLog();
  if(logFid < 0) {
    // Log is empty
    return 0;
  }
  {
    LOG_ENTRY *le = & logBuffer[0];
    int toGo = LSEEK(logFid, 0, SEEK_END);
    int i = LOG_SIZE;  // Pretend we are at the end of the buffer

    LSEEK(logFid, 0, SEEK_SET); // Go to start
    while(toGo > 0) {
      if(i >= LOG_SIZE) {
	int toRead = sizeof(logBuffer);
	if(toRead > toGo) toRead = toGo;
	if(toRead != READ(logFid, & logBuffer[0], toRead)) {
	  CCURED_FAIL(FAIL_SCALARLOG  FILE_AND_LINE);
	}
	i = 0;
	le = & logBuffer[i];
      }
      if((*match)(closure, le)) {
	return 1;
      }
      i ++;
      le ++;
      toGo -= sizeof(LOG_ENTRY);
    }
  }
  return 0; // Not found
}

int foundOne = 0;
int printMatches(uintptr_t tomatch, LOG_ENTRY *le) {
  if(le->l == (unsigned)tomatch) {
    foundOne = 1;
    fprintf(stderr, "\tSame value as at ID=%d in the scalar log\n",
	    le->id);
  }
  return 0; // Want all matches
}

// Print the contents of the log
int printAll(uintptr_t where, LOG_ENTRY *le) {
  fprintf((FILE*)where, "0x%08lx  %d\n",
	  le->l, le->id);
  return 0;
}


// And a function to scan the logs and find the matching
void non_pointer_fail(unsigned long p  CCURED_FAIL_EXTRA_PARAMS)
{
  if(__ccuredLogNonPointers && p >= MIN_POINTER && p <= MAX_POINTER) {
    fprintf(stderr, "Dereferencing a non-pointer (0x%08lx)\n", p);
    foundOne = 0;
    scanLog(& printMatches, (uintptr_t)p);
    if(! foundOne) {
      // Dump the entire log to a file
      char *theFileName = "__ccured_scalar.log";
      FILE *txtLog = fopen(theFileName, "w");
#ifdef _MSVC
      char fullPath[_MAX_PATH];
      theFileName = _fullpath(fullPath, theFileName, _MAX_PATH);
#endif
      fprintf(stderr,
	      "Cannot find the cast in log. Dumping the entire log to %s\n",
	      theFileName);
      scanLog(& printAll, (uintptr_t)txtLog);
      fclose(txtLog);
    } else {
      fflush(stderr);
    }
  }
  ccured_fail((p ? FAIL_NONPOINTER : FAIL_NULL) CCURED_FAIL_EXTRA_ARGS);
}
#else  // CCURED_NOLOG_NONPOINTERS
// And a function to scan the logs and find the matching
void non_pointer_fail(unsigned long p  CCURED_FAIL_EXTRA_PARAMS)
{
  ccured_fail((p ? FAIL_NONPOINTER : FAIL_NULL) CCURED_FAIL_EXTRA_ARGS);
}
#endif

void non_pointer_fail_terse(unsigned long l) {
  non_pointer_fail(l, NULL, 0, NULL);
}

/* ------------- wrappers for main (matth: mostly obsolete) ----------- */
// when the arguments to main become non-safe (as they almost always
// do if they're used), then we need to glue the loader's call to main
// with the program's now-mangled main (which gets renamed to trueMain)

// fwd decl
void __ccured_test_ccuredlib();

// an initializer for all our CCured stuff
static void __ccuredInitHelper(void);
void __ccuredInit()
{
  int volatile bottomOfStack = 0;
  /* Set the stack bottom here. This is called from main, which means that
   * the entire stack frame of main is at higher addresses, and nothing
   * more. We add 4 bytes, just to be sure. */
  __ccuredStackBottom = (void*)(&bottomOfStack + 1);
  /* Do everything else in some other helper function, to ensure that the
   * stack frame of this function is as small as possible, and thus we are
   * getting a value for the __ccuredStackBottom as high as possible */
  __ccuredInitHelper();
}

static void __ccuredInitHelper(void) {
  char* logFileName = NULL;

  if (sizeof(failMessages)/sizeof(failMessages[0]) != NUM_FAIL_CODES) {
    CCURED_FAIL_STR("NUM_FAIL_CODES doesn't agree with failMessages[]"
		    FILE_AND_LINE);
  }
#ifndef CCURED_NO_ERROR_HANDLERS_FILE
  // Now see if we must initialize the failure handlers
  {
    char *fname = getenv("CCURED_ERROR_HANDLERS");
    if(fname) {
      initErrorHandlers(fname);
    }
  }
#endif
  __ccured_test_ccuredlib();
  /* Read some environment variables, before the program messes with them */
#ifndef CCURED_NO_GETENV
  __ccuredContinueOnError = (0 != getenv("CCURED_CONTINUE_ON_ERROR"));
  __ccuredSleepOnError = (0 != getenv("CCURED_SLEEP_ON_ERROR"));
  logFileName = getenv("CCURED_ERROR_LOG");

  if (logFileName != 0)
  {
    FILE* tmp = fopen(logFileName, "a");
    if (tmp == NULL){
      fprintf(stderr, "Unable to open log file \"%s\": %s.\n",
	      logFileName, strerror(errno) );
      CCURED_FAIL_STR("Unable to open log file." FILE_AND_LINE);
    }
    else {
      time_t t = time(NULL);
      __ccuredErrorLog = tmp;
      fprintf(tmp, "\n================================================\n"
	      "Entered program at %s\n", ctime(&t) );
      fflush(tmp);
    }
  }

#else
  __ccuredContinueOnError = 0;
  __ccuredSleepOnError = 0;
  logFileName = 0;

  #ifndef _DEBUG
    if(__ccuredSleepOnError) {
      fprintf(stderr, "You said CCURED_SLEEP_ON_ERROR but you have linked with the non-debug library!\n");
    }
  #endif

  #if LOG_ALLOC_TRAFFIC
  {
    char const *fname = getenv("CCURED_ALLOC_LOG");
    if (fname) {
      allocTraffic = fopen(fname, "w");
      if (!allocTraffic) {
	perror("open");
	abort();
      }
    }
  }
  #endif

#endif   // CCURED_NO_GETENV

  return;
}

typedef struct {
  char * * _p;
  void * _e;
} fseqp_p_char;

typedef struct {
  fseqp_char *_p;
  void *_e;
} fseqp_fseqp_char;



// --------------------- misc. wrappers ----------------
#ifdef __CYGWIN__
  int _get_ctype_p1(unsigned int chr) {
    if (!( (unsigned)chr < 256 )) {
      CCURED_FAIL_STR("Bad character index for ctype."  FILE_AND_LINE);
      return 0;
    }
    return (_ctype_+1)[chr];
  }
#endif

#if defined(__GLIBC__) && __GLIBC__ == 2
  /// For brooksie
  // sm: glibc 2.0 and 2.1 both have this; so I removed check for minor number
  int _get__ctype_b(int chr) {
    if (!( (unsigned)chr < 256 )) {
      fprintf(stderr, "Bad character index to _get__ctype_b: %d\n", chr);
      abort();
    }
#if __GLIBC_MINOR__ >= 3
    return (*__ctype_b_loc())[chr];
#else
    return __ctype_b[chr];
#endif
  }
#endif


// sm: I don't have __assert ... we need an #ifdef here
// which identifies the machine which has this ...
// gn: who has this anyway?
#if !defined(__GLIBC__) && !defined(_MSVC) && !defined(__FreeBSD__)
  extern void __assert(const char *, int, const char *);
  void __assert_ww(wildp_char file, int line, wildp_char a2)
  {
    wildp_verify_nul(file);
    wildp_verify_nul(a2);
    __assert(file._p, line, a2._b);
  }
#endif

// sm: I don't know if this is a problem on msvc, but I suspect it is
#ifdef _GNUCC
/*  // sm: for m88k
  typedef void (*sig_fn)(int);
  typedef struct fseq_sig_fn {
    sig_fn fn;
    void *_e;
  } fseq_sig_fn;
  fseq_sig_fn signal_ff(int signum, fseq_sig_fn f)
  {
    // UNSOUND (why? don't remember)
    fseq_sig_fn ret;
    ret.fn = signal(signum, f.fn);
    ret._e = 0;     // people don't call handlers directly (right?)
    return ret;
  }
*/
// gn (9/8/02) removed because now we have a wrapper for getopt
//
//  // workaround for m88k getopt thing (bug in our tool)
//  int m88k_getopt(int argc, seqp_char *argv, char *argdesc)
//  {
//    char **argv2;
//    int i;
//    int retval;
//
//    // construct a new array
//    argv2 = (char**)malloc((argc+1) * sizeof(char*));
//
//    // copy the string pointers into it; no bounds checking
//    for (i=0; i<argc+1; i++) {
//      argv2[i] = argv[i]._p;    // last will be NULL (we hope)
//    }
//
//    // call the real getopt
//    retval = getopt(argc, argv2, argdesc);
//
//    // free the array
//    free(argv2);
//
//    return retval;
//  }

// gn (9/5/02) Removed this because I added wrappers
//  // extern char *optarg;
//  // int getopt(int argc, char * SAFE const * FSEQ argv, const char * SAFE optstring);
//  fseqp_char optarg_f;
//  int getopt_fss(int argc, fseqp_p_char argv, char const *optstring)
//  {
//    int ret;
//
//    if ((char**)argv._e - argv._p < argc) {
//      // not enough entries in the argv array; should be at least argc many
//      ccured_fail_str("getopt called with too-small argv array"  FILE_AND_LINE);
//    }
//
//    ret = getopt(argc, argv._p, optstring);
//
//    // make optarg available as optarg_f
//    optarg_f._p = optarg;
//    optarg_f._e = optarg? optarg + strlen(optarg) : NULL;
//
//    return ret;
//  }


// For getopt
extern char* optarg;

// sm: the optarg wrapper calls this to get libc's optarg; we should
// *not* make mangled versions of this function
char* ccured_get_optarg(void)
{ return optarg; }

// sm: place for the program to read the value of optarg, after
// the wrapper (unistd_wrappers.h) has copied it there
fseqp_char optarg_F;
fseqp_char optarg_f;
seqp_char optarg_Q;
seqp_char optarg_q;


#endif // _GNUCC


// --------------------- varargs stuff --------------------
// Define our version of va_start

// sm: I already defined this myself, calling it ALIGNBYTES
//#define OUR_ROUND(size) ((size + sizeof(int) - 1) & ~(sizeof(int) - 1))

#ifdef _GNUCC
  /* On GCC we do not take the address of the last local because if we do that
   * gcc will give us the address of a copy of the local. */
  #define getPNextArg(lastarg) __builtin_next_arg(lastarg)
#else
  #define getPNextArg(lastarg) ((char*)(&(lastarg)) + ALIGNBYTES(sizeof(lastarg)))
#endif
#define our_advance_va_arg(ap,size) ap = (va_list)((char*)ap + ALIGNBYTES(size))

int __ccured_va_count = 0;
int __ccured_va_tags[32];
typedef struct __ccured_va_localinfo {
   int next ;
   int count ;
   unsigned int tags[32] ;
   va_list nextp ;
} CCURED_VAINFO;


//Initialize a CCURED_VAINFO struct using the global vars.
//This must be the first command in the function, in case other vararg calls
// overwrite the globals before va_start is called.
void __ccured_va_init_vs(CCURED_VAINFO *vainfo) {
  vainfo->count = __ccured_va_count;
  memcpy(vainfo->tags, __ccured_va_tags, sizeof(__ccured_va_tags));

  vainfo->next  = -1;
  // FIX_VARARGS: vainfo->nextp = (va_list)0;
}

//Calls to va_start are replaced by this.  The vainfo should already have been
//initialized by __ccured_va_init_vs
void __ccured_va_start_vs(CCURED_VAINFO *vainfo,
			  void *pNextArg) {
  vainfo->next  = 0;
  // FIX_VARARGS: vainfo->nextp = (va_list)pNextArg;
}

void __ccured_va_end_vs(CCURED_VAINFO *vainfo) {
  vainfo->next = -1;
}

#ifndef CCURED_NO_VA_COPY
CCURED_VAINFO * __ccured_va_copy_vsvs(CCURED_VAINFO *src) {
  //matth: copy the structure.  (va_copy allows programmers to iterate
  //through a va_list more than once by duplicating the next/nextp fields)
  CCURED_VAINFO * dest;
  if(src->next == -1) {
    CCURED_FAIL(FAIL_VA_NOSTART  FILE_AND_LINE);
  }
  dest = malloc(sizeof(CCURED_VAINFO));
  memcpy(dest, src, sizeof(CCURED_VAINFO));
  return dest;
}
#endif // CCURED_NO_VA_COPY

#define GET_VA_TAG(tags, idx) ((tags[idx >> 2] >> ((idx & 0x3) << 3)) & 0xFF)

void *__ccured_va_arg_svs(CCURED_VAINFO *vainfo,
			  unsigned int thisTypeSize,
			  int thisTypeIndex) {
  void* lastp = NULL; // FIX_VARARGS: vainfo->nextp;

  if(vainfo->next == -1) {
    CCURED_FAIL(FAIL_VA_NOSTART  FILE_AND_LINE);
  }
  if(vainfo->next >= vainfo->count) {
    CCURED_FAIL(FAIL_VA_MANY  FILE_AND_LINE);
  }
  // Grab the stored tag
  {
    int tag = GET_VA_TAG(vainfo->tags, vainfo->next);
    if(tag != thisTypeIndex) {
      CCURED_FAIL(FAIL_VA_BADTYPE  FILE_AND_LINE);
    }
  }
  // FIX_VARARGS: our_advance_va_arg(vainfo->nextp, thisTypeSize);

  vainfo->next ++;
  return lastp;
}

// varargs merge but don't cure start ****************

// dsw: These are for merging with CCURED=1 but then not curing.  They
// are identical to the above, but they don't do any checking.

void __ccured_va_start(CCURED_VAINFO *vainfo,
		       void *pNextArg) {
//    vainfo->next  = 0;
//    vainfo->count = __ccured_va_count;
//    memcpy(vainfo->tags, __ccured_va_tags, sizeof(__ccured_va_tags));

  // FIX_VARARGS: vainfo->nextp = (va_list)pNextArg;
  return;
}

void __ccured_va_end(CCURED_VAINFO *vainfo) {
//    vainfo->next = -1;
}

//  #define GET_VA_TAG(tags, idx) ((tags[idx >> 2] >> ((idx & 0x3) << 3)) & 0xFF)

void *__ccured_va_arg(CCURED_VAINFO *vainfo,
			  unsigned int thisTypeSize,
			  int thisTypeIndex) {
  void* lastp = NULL;  // FIX_VARARGS: vainfo->nextp;

//    if(vainfo->next == -1) {
//      CCURED_FAIL(FAIL_VA_NOSTART);
//    }
//    if(vainfo->next >= vainfo->count) {
//      CCURED_FAIL(FAIL_VA_MANY);
//    }
//    // Grab the stored tag
//    {
//      int tag = GET_VA_TAG(vainfo->tags, vainfo->next);
//      if(tag != thisTypeIndex) {
//        CCURED_FAIL(FAIL_VA_BADTYPE);
//      }
//    }
  // FIX_VARARGS: our_advance_va_arg(vainfo->nextp, thisTypeSize);

//    vainfo->next ++;
  return lastp;
}

// varargs merge but don't cure stop ****************

//makes sure the ith argument to a printf-like function has type "type".
__inline static
void DO_CHECK(int i, int type)
{
  if(i >= __ccured_va_count) {
    CCURED_FAIL(FAIL_VA_MANY  FILE_AND_LINE);
  }
  if(type != GET_VA_TAG(__ccured_va_tags, i)) {
    CCURED_FAIL(FAIL_VA_BADTYPE  FILE_AND_LINE);
  }
}

// NOTE: these codes for __ccured_va_tags are determined by the
// order of the fields in printf_arguments, which is defined
// in ccured/vararg.ml and fixup.h
#define INT_TYPE 0
#define DOUBLE_TYPE 1
#define STRING_TYPE 2
#define LONGLONG_TYPE 3

// parse a printf-like format string
void CHECK_FORMATARGS(const char *format) {
  int i = 0;
  if(! format) {
    CCURED_FAIL(FAIL_NULL  FILE_AND_LINE);
  }
  if(__ccured_va_count == -1) return; // Was checked already
  while(*format) {
    if(*format == '%')
    {
      format ++;
    KeepLooking:
      switch(*format) {
      case '%': format ++; continue;
      case 's': DO_CHECK(i, STRING_TYPE); i++; continue;
      case 'f': DO_CHECK(i, DOUBLE_TYPE); i++; continue;
      case 'd': case 'c': case 'x': case 'u':
	   DO_CHECK(i, INT_TYPE); i++; continue;
      case 'l': case '-': case '.': format ++; goto KeepLooking;
      case '*': //a format specifier whose value is an argument.
	DO_CHECK(i, INT_TYPE);
	i++;
	format++;
	goto KeepLooking;
      default:
	if(*format >= '0' && *format <= '9') {
	  format ++; goto KeepLooking;
	}
	// printf("**************** unrecognized format char '%c'\n", *format);
	CCURED_FAIL(FAIL_UNRECOGNIZEDFORMAT  FILE_AND_LINE);
      }  // '%'
    }
    format ++;
  }
  __ccured_va_count = -1; // Was checked already. this will prevent the use
  // of va_arg but that would be unsafe anyway for printf-like functions
}



// some functions that we need to link with whenever we
// merge wrappers.c but don't then cure (which ordinarily
// throws away wrapper functions for SAFE pointers)
void __verify_nul(char *ptr) {}
void __write_at_least(void *ptr, unsigned int n) {}
void __read_at_least(void *ptr, unsigned int n) {}
void __copytags(void *dest, void* src, unsigned int n) {}

// Forward decl
void __verify_nul_w(wildp_char);
void CHECK_FORMATARGS_w(wildp_char format) {
  __verify_nul_w(format);
  CHECK_FORMATARGS(format._p);
}


// ---------------------- socket functions ----------------
#ifdef _GNUCC

#if 0
//matth: do we need these for INFERBOX=wild tests?
  // the user simply has to pass a buffer in 'optval' that is at least
  // 'optlen' bytes long
  // int setsockopt(int s, int level, int optname, void const *optval, int optlen);
  int setsockopt_w(int s, int level, int optname, wildp_char optval, int optlen)
  {
    wildp_verify_atleast(optval, optlen);
    return setsockopt(s, level, optname, optval._p, optlen);
  }

  // same deal for bind
  // int bind(int sockfd, struct sockaddr *my_addr, int addrlen);
  int bind_w(int sockfd, wildp_char my_addr, int addrlen)
  {
    wildp_verify_atleast(my_addr, addrlen);
    return bind(sockfd, (struct sockaddr*)my_addr._p, addrlen);
  }

  // connect is just like bind
  // int connect(int sockfd, struct sockaddr *my_addr, int addrlen);
  int connect_w(int sockfd, wildp_char my_addr, int addrlen)
  {
    wildp_verify_atleast(my_addr, addrlen);
    return connect(sockfd, (struct sockaddr*)my_addr._p, addrlen);
  }

#endif

  //gn: I don't have getnameinfo on cygwin
  #if !defined(__CYGWIN__)
    // not a socket function, but specific to unix, so I'll put it here
    //void *mmap(void *start, int length, int prot, int flags, int fd, int offset);
    seqp_void mmap_qs(void *start, int length, int prot, int flags, int fd, int offset)
    {
      seqp_void ret;

      // the only way it makes sense for 'start' to be safe is if it's null
      if (start != NULL) {
	CCURED_FAIL_STR("expected NULL start to mmap"  FILE_AND_LINE);
      }

      ret._p = mmap(start, length, prot, flags, fd, offset);
      if (ret._p == MAP_FAILED) {
	ret._b = ret._e = NULL;
      }
      else {
	ret._b = ret._p;
	ret._e = ((char*)ret._p) + length;    // ptr to first *invalid* byte
      }

      return ret;
    }

    int munmap_q(seqp_void start, int length)
    {
      CHECK_NULL(start._p);
      if (start._p != start._b) {
	CCURED_FAIL_STR("must pass pointer to start of the region"
			FILE_AND_LINE);
      }
      if ((char*)start._e - (char*)start._b  != length) {
	CCURED_FAIL_STR("must pass correct length to munmap"  FILE_AND_LINE);
      }

      // fixme?  this could leave dangling pointers.. it's a form
      // of explicit deallocation.. (UNSOUND)
      return munmap(start._p, length);
    }
  #endif // !defined(__CYGWIN__)
#endif // _GNUCC


// sm: removed the glob wrapper since I've now got a better
// one in include/glob_wrappers.h


// ----------------- misc for EDG -------------------
// sm: putting this back, since I don't see how to use #pragma ccuredwrapper
void abort_w()
{
  abort();
}


typedef struct wildp_func {
  void (*_p)();
  void *_b;
} wildp_func;

#ifndef _MSVC
  int atexit_w(wildp_func f)
  {
    CHECK_FUNCTIONPOINTER(f._p, f._b, 0);
    return atexit(f._p);
  }
#endif


#ifdef __GLIBC__
void __assert_fail_www(wildp_char assertion, wildp_char file,
		       unsigned int line, wildp_char function)
{
  wildp_verify_nul(assertion);
  wildp_verify_nul(file);
  wildp_verify_nul(function);
  __assert_fail(assertion._p, file._p, line, function._p);
}
#endif // __GLIBC__


// ------------------ startof, endof, ptrof, stringof, mkptr  ------------------


// Similar to verify_nul, but returns the length of the string
// (excluding the NUL).
//   __ccured_strlen(start, end) <= (end - start - 1)
//Called by the various (polymorphic) __strlen implementations
__inline static int __ccured_strlen(const char *start, const char *end)
{
  const char * current = start;
  int max = (intptr_t)end - (intptr_t)start;

  for(; max > 0; max--) {
    if (*current == 0) {
      // ok
      return current - start;
    }
    current++;
  }

  // didn't find a nul in the accessible area
  CCURED_FAIL(FAIL_STRINGBOUND  FILE_AND_LINE);
  return 0;     // silence warning
}


// like the above, except if 'start+n' is less than end, and we
// don't find a nul in the first 'n' bytes, return 'n'
//   __ccured_strlen_n(start, end) <= (end - start - 1)
//Called by the various (polymorphic) __strlen_n implementations
__inline static int __ccured_strlen_n(const char *start, const char *end, int n)
{
  const char * current = start;
  int max = (intptr_t)end - (intptr_t)start;
  if (n < max) { max = n; }

  for(; max > 0; max--) {
    if (*current == 0) {
      // ok
      return current - start;
    }
    current++;
  }

  if (current == start+n) {
    // didn't find a nul in the first 'n' bytes, but we hit the
    // 'n' limit, so that's ok
    return n;
  }

  // didn't find a nul in the accessible area
  CCURED_FAIL(FAIL_STRINGBOUND  FILE_AND_LINE);
  return 0;     // silence warning
}


// -- TODO: make all of these functions inline, and put them in ccuredcheck.h:

//
//safe
//
# if 0
//matth: moved to ccuredcheck.h for performance.
void* __ptrof(void* p){
  return p;
}
#endif //0
char* __stringof(char *p) {
  __verify_nul(p);
  return p;
}
void* __ptrof_nocheck(void* p){
  return p;
}
FILE* __ptrof_file(FILE* p){
  return p;
}
void* __mkptr(void* ptr, void* phome){
  return ptr;
}
void* __mkptr_int(unsigned long ptr, void* phome){
  return (void*)ptr;
}
//  void* __mksafeptr_int(unsigned long ptr){
//    return (void*)ptr;
//  }
void* __mkptr_ssf(void* ptr, fseqp_void phome){
  return ptr;
}
void* __mkptr_ssq(void* ptr, seqp_void phome){
  return ptr;
}
void* __mkptr_ssF(void* ptr, fseqp_void phome){
  return ptr;
}
void* __mkptr_ssQ(void* ptr, seqp_void phome){
  return ptr;
}
void* __mkptr_int_sf(unsigned long ptr, fseqp_void phome){
  return (void*)ptr;
}
void* __mkptr_int_sF(unsigned long ptr, fseqp_void phome){
  return (void*)ptr;
}
void* __mkptr_int_sq(unsigned long ptr, seqp_void phome){
  return (void*)ptr;
}
void* __mkptr_int_sQ(unsigned long ptr, seqp_void phome){
  return (void*)ptr;
}
void* __mkptr_size(void* ptr, unsigned int len){
  return ptr;
}
FILE* __mkptr_file(FILE* f){
  return f;
}
void* __mkptr_string(void* ptr){
  return ptr;
}

int __strlen(char* s) {
  __CCURED_ASSERT(s != NULL, FAIL_NULL);
  return strlen(s);
}

//The semantics of this are the same as strnlen, but not all systems define
// strnlen.
int __strlen_n(char* s, int n) {
  char* string_end;
  __CCURED_ASSERT(s != NULL, FAIL_NULL);

  //look up to n characters away for the nul.
  string_end = memchr(s, '\0', n);

  return string_end == NULL
    ? n // the string is more than n bytes long (if it is a string).  Return n.
    : string_end - s;
}


void *__endof(void *ptr) {
  // This function is only used in wrappers.  If the program has been
  // cured, then any use of __endof will turn into __endof_q or whatever.
  // If this program has not been cured, then the wrappers should never
  // be called.
  ccured_fail_str("cannot call __endof in non-cured program"  FILE_AND_LINE);
  return NULL;
}

//
//wild
//

//helper for other *_w functions.  Fails if NULL or out of bounds.
void __bounds_check_w(wildp_void p){
  __CCURED_ASSERT(p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT(p._p < CHECK_FETCH_WILD_END(p._p, p._b, 0), FAIL_UBOUND);
}
void* __ptrof_sw(wildp_void p){
  if (p._p != 0){ //allow p to be null
    __bounds_check_w(p);
  }
  return p._p;
}
char* __stringof_sw(wildp_char p){
  __verify_nul_w(p);
  return p._p;
}
char* __stringof_ornull_sw(wildp_char p){
  if (p._p) {__verify_nul_w(p);}
  return p._p;
}
// In the all_wild mode we need this one as well
wildp_char __stringof_ww(wildp_char p){
  __verify_nul_w(p);
  return p;
}
wildp_char __stringof_ornull_ww(wildp_char p){
  if (p._p) {__verify_nul_w(p);}
  return p;
}
void* __ptrof_nocheck_sw(wildp_void p){
  return p._p;
}
FILE* __ptrof_file_sw(wildp_FILE p){
  return p._p;
}
void* __startof_sw(wildp_void p){
  return p._b;
}
void* __endof_sw(wildp_void p){
  if(p._b == 0)
    return 0;
  else
    return CHECK_FETCH_WILD_END(p._p, p._b, 0);
}
wildp_void __mkptr_wsw(void* ptr, wildp_void phome)
{
  wildp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : phome._b;
  return res;
}
// This should only be necessary in BOX all mode.
wildp_void __mkptr_string_ww(wildp_void x) {
  return x;
}

//  __mkptr_size_ws isn't possible
wildp_FILE __mkptr_file_ws(FILE* f){
  //see fopen_wrapper
  wildp_FILE res;
  res._p = f;
  res._b = 0;
  return res;
}
int __strlen_w(wildp_void p){
  __bounds_check_w(p);
  return __ccured_strlen(p._p, __endof_sw(p));
}
int __strlen_n_w(wildp_void p, int n){
  __bounds_check_w(p);
  return __ccured_strlen_n(p._p, __endof_sw(p), n);
}
void __verify_nul_w(wildp_char p){
  //matth: this needs to be fixed for performance.  We compute the end of the
  // buffer twice.
  wildp_void p1;
  p1._p = p._p;
  p1._b = p._b;
  __bounds_check_w(p1);
  ccured_verify_nul(p1._p,
		    (unsigned long)__endof_sw(p1) - (unsigned long)p1._p);
}
void __write_at_least_w(wildp_char ptr, unsigned int n){
  wildp_write_atleast(ptr, n);
}
void __read_at_least_w(wildp_char ptr, unsigned int n){
  wildp_verify_atleast(ptr, n);
}
void __copytags_ww(wildp_char dest, wildp_char src, unsigned int n){
  __CCURED_ASSERT(n <= (unsigned int)wildp_length(src), FAIL_UBOUND); // checks that src is not an integer.
  __CCURED_ASSERT(n <= (unsigned int)wildp_length(dest), FAIL_UBOUND); // checks that dest is not an integer.
  wildp_copy_tags(dest, src, n);
}


/* When we use the WILD solver we might need strange versions of these
 * wrappers */
wildp_void __ptrof_ww(wildp_void x) {
  if (x._p != 0){ //allow x to be null
    __bounds_check_w(x);
  }
  return x;
}
wildp_void __ptrof_nocheck_ww(wildp_void x) {
  return x;
}
wildp_FILE __ptrof_file_ww(wildp_FILE x) {
  return x;
}
wildp_void __endof_ww(wildp_void x) {
  return __mkptr_wsw(__endof_sw(x), x);
}
wildp_void __mkptr_www(wildp_void ptr, wildp_void phome)
{
  wildp_void res;
  res._p = ptr._p;
  res._b = ptr._p == 0 ? 0 : phome._b;
  return res;
}
wildp_FILE __mkptr_file_ww(wildp_FILE f){
  return f;
}

//
//seq
//

//helper for other *_q functions.  Fails if NULL or out of bounds.
void __bounds_check_q(seqp_void p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT(p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT(p._p < p._e, FAIL_UBOUND);
}

void* __startof_sq(seqp_void p){
  return p._b;
}
void* __endof_sq(seqp_void p){
  return p._e;
}
void* __ptrof_sq(seqp_void p){
  if (p._p != 0){ //allow p to be null
    __bounds_check_q(p);
  }
  return p._p;
}
void* __ptrof_nocheck_sq(seqp_void p){
  return p._p;
}
void * __ptrof_size_sq(seqp_void ptr, unsigned int n) {
  if(n > 0) { __bounds_check_q(ptr); }
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
  return ptr._p;
}
void* __ptrof_file_sq(seqp_void p){
  return __ptrof_sq(p);
}
seqp_void __mkptr_qsq(void* ptr, seqp_void phome)
{
  seqp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : phome._b;
  res._e = ptr == 0 ? 0 : phome._e;
  return res;
}
seqp_void __mkptr_qsQ(void* ptr, seqp_void phome)
{
  return __mkptr_qsq(ptr, phome);
}
seqp_void __mkptr_int_qq(unsigned long ptr, seqp_void phome)
{
  return __mkptr_qsq((void*)ptr, phome);
}
seqp_void __mkptr_int_qQ(unsigned long ptr, seqp_void phome)
{
  return __mkptr_qsq((void*)ptr, phome);
}
seqp_void __mkptr_size_qs(void* ptr, unsigned int len)
{
  //matth: should we check alignment?
  seqp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + len);
  return res;
}
// note that the NULL is part of the area
seqp_void __mkptr_string_qs(char* ptr)
{
  seqp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + strlen(ptr)
				  + (__ccuredUseStrings ? 0 : 1));
  return res;
}
seqp_void __mkptr_file_qs(FILE* f){
  return __mkptr_size_qs(f, sizeof(FILE));
}

void __verify_nul_q(seqp_char p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT((void*)p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT((void*)p._p < p._e, FAIL_UBOUND);
  ccured_verify_nul(p._p, seqp_length(p));
}
void __verify_nul_Q(seqp_char p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT((void*)p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT((void*)p._p <= p._e, FAIL_UBOUND); // We may point to NULL
  // We know we have a NULL
}
int __strlen_q(seqp_void p){
  __bounds_check_q(p);
  return __ccured_strlen(p._p, p._e);
}
int __strlen_n_q(seqp_void p, int n){
  __bounds_check_q(p);
  return __ccured_strlen_n(p._p, p._e, n);
}
char* __stringof_sq(seqp_char p){
  __verify_nul_q(p);
  return p._p;
}
char* __stringof_sQ(seqp_char p){
  __verify_nul_Q(p);
  return p._p;
}
char* __stringof_ornull_sq(seqp_char p){
  if (p._p) {__verify_nul_q(p);}
  return p._p;
}

void __read_at_least_q(seqp_void ptr, unsigned int n){
  if(n > 0) { __bounds_check_q(ptr); }
  //n is treated as an unsigned number so that we fail if it's negative
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
}
void __write_at_least_q(seqp_void ptr, unsigned int n){
  __read_at_least_q(ptr, n);
}
void __copytags_qq(seqp_void dest, seqp_void src, unsigned int n){
  __read_at_least_q(dest, n);
  __read_at_least_q(src, n);
}
void __copytags_qQ(seqp_void dest, seqp_void src, unsigned int n){
  __copytags_qq(dest, src, n);
}
void __copytags_Qq(seqp_void dest, seqp_void src, unsigned int n){
  __copytags_qq(dest, src, n);
}


//
//fseq
//

//helper for other *_f functions.  Fails if NULL or out of bounds.
void __bounds_check_f(fseqp_void p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT(p._p < p._e, FAIL_UBOUND);
}
void* __endof_sf(fseqp_void p){
  return p._e;
}
void* __ptrof_sf(fseqp_void p){
  if (p._e != 0){ //allow p to be null
    __bounds_check_f(p);
  }
  return p._p;
}
void * __ptrof_size_sf(fseqp_void ptr, unsigned int n) {
  if(n > 0) { __bounds_check_f(ptr); }
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
  return ptr._p;
}
void * __ptrof_size_sF(fseqp_void ptr, unsigned int n) {
  return __ptrof_size_sf(ptr, n);
}
void* __ptrof_nocheck_sf(fseqp_void p){
  return p._p;
}
void* __ptrof_file_sf(fseqp_void p){
  return __ptrof_sf(p);
}

fseqp_void __mkptr_fsf(void* ptr, fseqp_void phome)
{
  fseqp_void res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : phome._e;
  return res;
}
fseqp_void __mkptr_fsF(void* ptr, fseqp_void phome)
{
  return __mkptr_fsf(ptr, phome);
}
fseqp_void __mkptr_fsq(void* ptr, seqp_void phome)
{
  fseqp_void res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : phome._e;
  return res;
}
fseqp_void __mkptr_fsQ(void* ptr, seqp_void phome)
{
  return __mkptr_fsq(ptr, phome);
}

fseqp_void __mkptr_int_ff(unsigned long ptr, fseqp_void phome)
{
  return __mkptr_fsf((void*)ptr, phome);
}
fseqp_void __mkptr_int_fF(unsigned long ptr, fseqp_void phome)
{
  return __mkptr_fsf((void*)ptr, phome);
}

fseqp_void __mkptr_size_fs(void* ptr, unsigned int len)
{
  fseqp_void res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + len);
  return res;
}
// The null is part of the area
fseqp_void __mkptr_string_fs(char* ptr)
{
  fseqp_void res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + strlen(ptr)
				  + (__ccuredUseStrings ? 0 : 1));
  return res;
}
fseqp_void __mkptr_file_fs(FILE* f){
  return __mkptr_size_fs(f, sizeof(FILE));
}

void __verify_nul_f(fseqp_char p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT((void*)p._p < p._e, FAIL_UBOUND);
  ccured_verify_nul(p._p, fseqp_length(p));
}

void __verify_nul_F(fseqp_char p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT((void*)p._p <= p._e, FAIL_UBOUND); // We may pointto NULL
  // We know we have a NULL
}

char* __stringof_sf(fseqp_char p){
  __verify_nul_f(p);
  return p._p;
}
char* __stringof_sF(fseqp_char p){
  __verify_nul_F(p);
  return p._p;
}
char* __stringof_ornull_sf(fseqp_char p){
  if (p._p) {__verify_nul_f(p);}
  return p._p;
}

int __strlen_f(fseqp_void p){
  __bounds_check_f(p);
  return __ccured_strlen(p._p, p._e);
}
int __strlen_n_f(fseqp_void p, int n){
  __bounds_check_f(p);
  return __ccured_strlen_n(p._p, p._e, n);
}

void __read_at_least_f(fseqp_void ptr, unsigned int n){
  if(n > 0) { __bounds_check_f(ptr); }
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
}
void __write_at_least_f(fseqp_void ptr, unsigned int n){
  __read_at_least_f(ptr, n);
}
void __copytags_ff(fseqp_void dest, fseqp_void src, unsigned int n){
  __read_at_least_f(dest, n);
  __read_at_least_f(src, n);
}
void __copytags_fF(fseqp_void dest, fseqp_void src, unsigned int n){
  __copytags_ff(dest, src, n);
}
void __copytags_Ff(fseqp_void dest, fseqp_void src, unsigned int n){
  __copytags_ff(dest, src, n);
}
void __copytags_fq(fseqp_void dest, seqp_void src, unsigned int n){
  __read_at_least_f(dest, n);
  __read_at_least_q(src, n);
}
void __copytags_qf(seqp_void dest, fseqp_void src, unsigned int n){
  __read_at_least_q(dest, n);
  __read_at_least_f(src, n);
}
void __copytags_qF(seqp_void dest, fseqp_void src, unsigned int n){
  __copytags_qf(dest, src, n);
}
void __copytags_Qf(seqp_void dest, fseqp_void src, unsigned int n){
  __copytags_qf(dest, src, n);
}
void __copytags_QF(seqp_void dest, fseqp_void src, unsigned int n){
  __copytags_qf(dest, src, n);
}


//
//seqN
//
void* __startof_sQ(seqp_void p){
  return p._b;
}
void* __endof_sQ(seqp_void p){
  return p._e;
}
void* __ptrof_sQ(seqp_void p){
  if (p._b != 0){ //allow p to be null
    __bounds_check_q(p);
  }
  return p._p;
}
void* __ptrof_nocheck_sQ(seqp_void p){
  return p._p;
}
seqp_void __mkptr_QsQ(void* ptr, seqp_void phome){
  return __mkptr_qsq(ptr, phome);
}
seqp_void __mkptr_size_Qs(void* ptr, unsigned int len)
{
  seqp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : ptr;
  if (ptr != 0) {
    char* end = (void*)((char*)ptr + len);
    __CCURED_ASSERT(len > 0, FAIL_UBOUND);
    // GN: trust the user here
    //    *(end - 1) = 0;
    res._e = end;
  }
  else {
    res._e = 0;
  }
  return res;
}
seqp_void __mkptr_string_Qs(char* ptr)
{
  seqp_void res;
  res._p = ptr;
  res._b = ptr ? ptr : 0;
  // Do not count the NULL byte because it is required
  // except if we are not using strings
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + strlen(ptr)
				  + (__ccuredUseStrings ? 0 : 1));
  return res;
}
//matth: added 1 to p._e because when dealing with FSeqN/SeqN, we're allowed
// to look one character beyond the official end to read a nul.
int __strlen_Q(seqp_void p){
  __bounds_check_q(p);
  return __ccured_strlen(p._p, (char*)p._e + 1);
}
int __strlen_n_Q(seqp_void p, int n){
  __bounds_check_q(p);
  return __ccured_strlen_n(p._p, (char*)p._e + 1, n);
}
void __write_at_least_Q(seqp_void ptr, unsigned int n){
  __write_at_least_q(ptr, n);
}
void __read_at_least_Q(seqp_void ptr, unsigned int n){
  __read_at_least_q(ptr, n - 1); // Subtract 1 to account for the NULL
}
void __copytags_QQ(seqp_void dest, seqp_void src, unsigned int n){
  __copytags_qq(dest, src, n - 1);
}
void __copytags_FQ(fseqp_void dest, seqp_void src, unsigned int n){
  __copytags_fq(dest, src, n - 1);
}
void __copytags_fQ(fseqp_void dest, seqp_void src, unsigned int n){
  __copytags_fq(dest, src, n - 1);
}


//
//fseqN
//
void* __endof_sF(fseqp_void p){
  return p._e;
}
void* __ptrof_sF(fseqp_void p){
  if (p._e != 0){ //allow p to be null
    __bounds_check_f(p);
  }
  return p._p;
}
void* __ptrof_nocheck_sF(fseqp_void p){
  return p._p;
}
fseqp_void __mkptr_FsF(void* ptr, fseqp_void phome){
  return __mkptr_fsf(ptr, phome);
}
fseqp_void __mkptr_FsQ(void* ptr, seqp_void phome){
  return __mkptr_fsq(ptr, phome);
}
fseqp_void __mkptr_size_Fs(void* ptr, unsigned int len)
{
  fseqp_void res;
  res._p = ptr;
  if (ptr != 0) {
    char* end = (void*)((char*)ptr + len);
    __CCURED_ASSERT(len > 0, FAIL_UBOUND);
    // GN: true the use here?
    //    *(end - 1) = 0;
    res._e = end;
  }
  else {
    res._e = 0;
  }
  return res;
}
// sm: we were returning seqp here, that's wrong..
fseqp_void __mkptr_string_Fs(char* ptr)
{
  fseqp_void res;
  res._p = ptr;
  // Do not count the NULL byte because it is required
  // except if we are not using strings
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + strlen(ptr)
				  + (__ccuredUseStrings ? 0 : 1));
  return res;
}
//matth: added 1 to p._e because when dealing with FSeqN/SeqN, we're allowed
// to look one character beyond the official end to read a nul.
int __strlen_F(fseqp_void p){
  __bounds_check_f(p);
  return __ccured_strlen(p._p, (char*)p._e + 1);
}
int __strlen_n_F(fseqp_void p, int n){
  __bounds_check_f(p);
  return __ccured_strlen_n(p._p, (char*)p._e + 1, n);
}
void __write_at_least_F(fseqp_void ptr, unsigned int n){
  __write_at_least_f(ptr, n - 1); //account for the NULL
}
void __read_at_least_F(fseqp_void ptr, unsigned int n){
  __read_at_least_f(ptr, n - 1); // account for the NULL
}
void __copytags_FF(fseqp_void dest, fseqp_void src, unsigned int n){
  __copytags_ff(dest, src, n - 1); // account for the NULL
}

//
// RTTI
//
void* __ptrof_srs(void * p , struct RTTI_ELEMENT *m){
  return p;
}
void* __ptrof_srf(fseqp_void p, struct RTTI_ELEMENT *m){
  return __ptrof_sf(p);
}
void* __ptrof_srq(seqp_void p, struct RTTI_ELEMENT *m){
  return __ptrof_sq(p);
}
void* __ptrof_nocheck_srs(void * p , struct RTTI_ELEMENT *m){
  return p;
}
void* __ptrof_nocheck_srf(fseqp_void p, struct RTTI_ELEMENT *m){
  return __ptrof_nocheck_sf(p);
}
void* __ptrof_nocheck_srq(seqp_void p, struct RTTI_ELEMENT *m){
  return __ptrof_nocheck_sq(p);
}



// index
//helper for other *_i functions.  Fails if NULL or out of bounds.
void __bounds_check_i(indexp_void p){
  __CCURED_ASSERT(p._b != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT(p._p < CHECK_FETCH_INDEX_END(p._p, p._b, 0), FAIL_UBOUND);
}


//
// safec
//
void* __ptrof_sms(safecp_void p){
  return p._p;
}
safecp_void __ptrof_nocheck_msms(safecp_void p){
  return p;
}
safecp_void __mkptr_mssms(void* ptr, safecp_void phome){
  safecp_void res;
  res._p = ptr;
  res._mp = ptr == 0 ? 0 : phome._mp;
  return res;
}
safecp_void __mkptr_mssmf(void* ptr, fseqcp_void phome){
  safecp_void res;
  res._p = ptr;
  res._mp = ptr == 0 ? 0 : phome._mp;
  return res;
}


//
// seqc
//
void __bounds_check_mq(seqcp_void p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT(p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT(p._p < p._e, FAIL_UBOUND);
}

void* __startof_smq(seqcp_void p){
  return p._b;
}
void* __endof_smq(seqcp_void p){
  return p._e;
}
void* __ptrof_smq(seqcp_void p){
  if (p._p != 0){ //allow p to be null
    __bounds_check_mq(p);
  }
  return p._p;
}
void* __ptrof_nocheck_smq(seqcp_void p){
  return p._p;
}
seqcp_void __mkptr_mqsmq(void* ptr, seqcp_void phome)
{
  seqcp_void res;
  res._p = ptr;
  res._b = ptr == 0 ? 0 : phome._b;
  res._e = ptr == 0 ? 0 : phome._e;
  res._mp = ptr == 0 ? 0 : phome._mp;
  return res;
}

void __read_at_least_mq(seqcp_void ptr, unsigned int n){
  if(n > 0) { __bounds_check_mq(ptr); }
  //n is treated as an unsigned number so that we fail if it's negative
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
}
void __write_at_least_mq(seqcp_void ptr, unsigned int n){
  __read_at_least_mq(ptr, n);
}
void __copytags_mqq(seqcp_void dest, seqp_void src, unsigned int n){
  __read_at_least_mq(dest, n);
  __read_at_least_q(src, n);
}
void __copytags_mqmq(seqcp_void dest, seqcp_void src, unsigned int n){
  __read_at_least_mq(dest, n);
  __read_at_least_mq(src, n);
}
void __copytags_qmq(seqp_void dest, seqcp_void src, unsigned int n){
  __read_at_least_q(dest, n);
  __read_at_least_mq(src, n);
}


//
// fseqc
//
void __bounds_check_mf(fseqcp_void p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT(p._p < p._e, FAIL_UBOUND);
}
void* __endof_smf(fseqcp_void p){
  return p._e;
}
void* __ptrof_smf(fseqcp_void p){
  if (p._e != 0){ //allow p to be null
    __bounds_check_mf(p);
  }
  return p._p;
}
void* __ptrof_nocheck_smf(fseqcp_void p){
  return p._p;
}
void* __ptrof_file_smf(fseqcp_void p){
  return __ptrof_smf(p);
}
fseqcp_void __mkptr_size_mfs(void* ptr, unsigned int len)
{
  fseqcp_void res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + len);
  res._mp = 0; // TODO
  return res;
}
// The null is part of the area
fseqcp_char __mkptr_string_mfs(char* ptr)
{
  fseqcp_char res;
  res._p = ptr;
  res._e = ptr == 0 ? 0 : (void*)((char*)ptr + strlen(ptr)
				  + (__ccuredUseStrings ? 0 : 1));
  res._z = 0; // TODO
  return res;
}
fseqcp_void __mkptr_file_mfs(FILE* f){
  return __mkptr_size_mfs(f, sizeof(FILE));
}

void __verify_nul_mf(fseqcp_char p){
  __CCURED_ASSERT(p._e != 0, (p._p ? FAIL_NONPOINTER : FAIL_NULL));
  __CCURED_ASSERT((void*)p._p < p._e, FAIL_UBOUND);
  ccured_verify_nul(p._p, fseqcp_length(p));
}

void __read_at_least_mf(fseqcp_void ptr, unsigned int n){
  if(n > 0) { __bounds_check_mf(ptr); }
  __CCURED_ASSERT(n <= (uintptr_t)ptr._e - (uintptr_t)ptr._p, FAIL_UBOUND);
}
void __write_at_least_mf(fseqcp_void ptr, unsigned int n){
  __read_at_least_mf(ptr, n);
}

int __strlen_mf(fseqcp_void p){
  __bounds_check_mf(p);
  return __ccured_strlen(p._p, p._e);
}
int __strlen_n_mf(fseqcp_void p, int n){
  __bounds_check_mf(p);
  return __ccured_strlen_n(p._p, p._e, n);
}

void __copytags_mff(fseqcp_void dest, fseqp_void src, unsigned int n){
  __read_at_least_mf(dest, n);
  __read_at_least_f(src, n);
}
void __copytags_mfmf(fseqcp_void dest, fseqcp_void src, unsigned int n){
  __read_at_least_mf(dest, n);
  __read_at_least_mf(src, n);
}
void __copytags_mfmq(fseqcp_void dest, seqcp_void src, unsigned int n){
  __read_at_least_mf(dest, n);
  __read_at_least_mq(src, n);
}
void __copytags_fmq(fseqp_void dest, seqcp_void src, unsigned int n){
  __read_at_least_f(dest, n);
  __read_at_least_mq(src, n);
}


void* __startof_si(indexp_void p){
  return p._b;
}

void* __endof_si(indexp_void p){
  if(p._b == 0)
    return 0;
  else
    return CHECK_FETCH_INDEX_END(p._p, p._b, 0);
}

void* __ptrof_si(indexp_void p){
  __CCURED_ASSERT(p._p >= p._b, FAIL_LBOUND);
  __CCURED_ASSERT(!p._p || (p._p < CHECK_FETCH_INDEX_END(p._p, p._b, 0)),
		  FAIL_UBOUND);  //allow p to be null
  return p._p;
}

void* __ptrof_nocheck_si(indexp_void p){
  return p._p;
}
void* __ptrof_file_si(indexp_void p){
  return __ptrof_si(p);
}


void __write_at_least_i(indexp_void ptr, unsigned int n){
  __bounds_check_i(ptr);
  //n is treated as an unsigned number so that we fail if it's negative
  __CCURED_ASSERT(n <= (uintptr_t)__endof_si(ptr) - (uintptr_t)ptr._p, FAIL_UBOUND);
}


// ------------------- vsprintf -----------------------

// Doesn't check the size of buffer; should only be called by
// trusted wrappers (e.g. vsprintf_fsvs below and sprintf_wrapper.)
int __ccured_vsnprintf_ssvs(char* buffer, int size, const char *format,
			    CCURED_VAINFO *args)
{
  CHECK_FORMATARGS(format);
  return VSNPRINTF(buffer, size, format, args->nextp);
}

// __ccured_vsnprintf for the all-wild solver.
int __ccured_vsnprintf_wsvs(wildp_char buffer, int size, char* format,
			    CCURED_VAINFO *args)
{
  return __ccured_vsnprintf_ssvs(buffer._p, size, format, args);
}

int vsprintf_fsvs(fseqp_char buffer, const char *format,
		  CCURED_VAINFO *args)
{
  int res;
  //matth: This used to be "(int)buffer._e - (int)buffer._p - 1".  Why?
  int size = (intptr_t)buffer._e - (intptr_t)buffer._p;
  if(!buffer._e || (void*)buffer._p >= buffer._e) {
    CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
  }

  res = __ccured_vsnprintf_ssvs(buffer._p, size, format, args);
  if(res < 0 || res >= ((intptr_t)buffer._e - (intptr_t)buffer._p)) {
    //If vsnprintf tries to write more than size bytes, it will either
    //return -1 or the number of bytes it tried to write, depending on the
    //version of glibc.
    CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
  }
  return res;
}

int vsprintf_qsvs(seqp_char buffer, const char *format,
		  CCURED_VAINFO *args)
{
  fseqp_char buffer_f;
  CHECK_SEQ2FSEQ(buffer._b, buffer._e, buffer._p);
  buffer_f._p = buffer._p;
  buffer_f._e = buffer._e;
  return vsprintf_fsvs(buffer_f, format, args);
}


#ifndef CCURED_NO_PRINTF
// --------------------- vfprintf -------------------
int vfprintf_ssvs(FILE * stream, const char *format, CCURED_VAINFO *args)
{
  int res;
  CHECK_NULL(stream);
  CHECK_NULL((char*)format);

  CHECK_FORMATARGS(format);
  res = vfprintf(stream, format, args->nextp);
  return res;
}

int vfprintf_sFvs(FILE * stream, fseqp_char format, CCURED_VAINFO *args)
{
  int res;
  CHECK_NULL(stream);
  __verify_nul_F(format);

  CHECK_FORMATARGS(format._p);
  res = vfprintf(stream, format._p, args->nextp);
  return res;
}


int vfprintf_wwvs(wildp_void stream, wildp_char format, CCURED_VAINFO *args)
{
  wildp_verify_nul(format);
  return vfprintf_ssvs(stream._p, format._p, args);
}

int vfprintf_swvs(void* stream, wildp_char format, CCURED_VAINFO *args)
{
  wildp_verify_nul(format);
  return vfprintf_ssvs(stream, format._p, args);
}

int vfprintf_wsvs(wildp_void stream, char *format, CCURED_VAINFO *args)
{
  // Do not check the FILE*
  return vfprintf_ssvs(stream._p, format, args);
}


// ---------------------- fprintf ----------------------
int fprintf_wws(wildp_void stream, wildp_char format, ...)
{
  CCURED_VAINFO args;
  int res;
  wildp_verify_nul(format);

  __ccured_va_start_vs(&args, getPNextArg(format));
  res = vfprintf_ssvs(stream._p, format._p, &args);
  __ccured_va_end_vs(&args);
  return res;
}

int fprintf_sws(FILE *stream, wildp_char format, ...)
{
  CCURED_VAINFO args;
  int res;
  wildp_verify_nul(format);

  __ccured_va_start_vs(&args, getPNextArg(format));
  res = vfprintf_ssvs(stream, format._p, &args);
  __ccured_va_end_vs(&args);
  return res;
}

int fprintf_wss(wildp_void stream, char *format, ...)
{
  CCURED_VAINFO args;
  int res;

  __ccured_va_start_vs(&args, getPNextArg(format));
  res = vfprintf_ssvs(stream._p, format, &args);
  __ccured_va_end_vs(&args);
  return res;
}


// ------------------- [v]printf -------------------
int vprintf_svs(char const *format, CCURED_VAINFO *args)
{
  return vfprintf_ssvs(stdout, format, args);
}

// sm 2/14/02: this used to be called printf_sf .. ??  the mangling
// algorithm gives this function the name printf_fs ..
int printf_fs(fseqp_char format, ...) // weimer
{
  CCURED_VAINFO args;
  int res;
  ccured_verify_nul(format._p,
		    (unsigned long)format._e - (unsigned long)format._p);

  __ccured_va_start_vs(&args, getPNextArg(format));
  res = vfprintf_ssvs(stdout, format._p, &args);
  __ccured_va_end_vs(&args);
  return res;
}

int printf_ws(wildp_char format, ...)
{
  CCURED_VAINFO args;
  int res;
  wildp_verify_nul(format);

  __ccured_va_start_vs(&args, getPNextArg(format));
  res = vfprintf_ssvs(stdout, format._p, &args);
  __ccured_va_end_vs(&args);
  return res;
}


// sm: trying vsyslog too! (conditional on linux to not interfere on cygwin)
#ifdef __linux__
  extern void vsyslog_svs(int pri, char const *format, CCURED_VAINFO *args)
  {
    CHECK_FORMATARGS(format);              // check
    vsyslog(pri, format, args->nextp);     // pass
  }
#endif // __linux__
#endif


//
// void ccured_fscanf_string_ssw(FILE *stream, char* what, wildp_char buffer) {
//   fseqp_char buffer_f;
//   int buff_wrds = CHECK_FETCHLENGTH(buffer._p, buffer._b, 0);
//   buffer_f._p = buffer._p;
//   buffer_f._e = buffer._p + (buff_wrds << 2);
//   // Now call the above
//   ccured_fscanf_string_ssf(stream, what, buffer_f);
//   // Now fix the tags !
//   // For the entire buffer to be sure
//   CHECK_ZEROTAGS(buffer._b, buff_wrds, buffer._p, buff_wrds << 2/*, 0*/);
// }

#ifndef CCURED_NO_WILD_WRAPPERS
//when using INFERBOX=wild, the fscanf functions in stdio_wrappers.h
//need WILD wrappers for fscanf.
int  fscanf_wswwwww(wildp_void stream, wildp_char format, wildp_void data){
  //the real wrappers have already done whatever checks are needed.
  return fscanf((FILE*)stream._p, format._p, data._p);
}

#endif

// ---------------------- scanf and friends -----------------------
#ifndef CCURED_NO_SCANF
int ccured_scanf_count;
FILE *ccured_sscanf_file = NULL;
void resetScanfCount(void) {
  ccured_scanf_count = 0;
}

// Call this function for sscanf
void resetSScanfCount(char *str) {
  resetScanfCount();

  if(! str) {
    CCURED_FAIL(FAIL_NULL_STRING  FILE_AND_LINE);
  }
  if(ccured_sscanf_file) {
    fprintf(stderr, "Must call getScanfCount after resetSScanfCount");
    exit(2);
  }
  ccured_sscanf_file = tmpfile();
  if(!ccured_sscanf_file) {
    fprintf(stderr, "CCured error: Cannot open sscanf temp file because: %s\n",
	    strerror(errno));
    exit(1);
  }
  fputs(str, ccured_sscanf_file);
  fseek(ccured_sscanf_file, 0L, SEEK_SET);
}

void resetSScanfCount_w(wildp_char str)
{
  wildp_verify_nul(str);
  resetSScanfCount(str._p);
}
void resetSScanfCount_F(fseqp_char str)
{
  __verify_nul_F(str);
  resetSScanfCount(str._p);
}

int getScanfCount() {
  if(ccured_sscanf_file) {
    fclose(ccured_sscanf_file);
    ccured_sscanf_file = 0;
  }
  return ccured_scanf_count;
}

void ccured_fscanf_string_len(FILE *stream, char* what,
			      char *buffer,
			      long bufflen) {
  char *mybuff;
  int orig_pos, read, scanned;

  if(!buffer) {
    CCURED_FAIL(FAIL_NULL  FILE_AND_LINE);
  }
  if(bufflen <= 0) {
    CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
  }
  // Now create a buffer
  mybuff = (char*)malloc(bufflen);
  if(!mybuff) {
    fprintf(stderr, "Cannot allocate buffer for fscanf_string");
    exit(2);
  }
  // Now remember the positon in the stream
  orig_pos = ftell(stream);
  // Now read that many characters from the stream in the buffer
  read = fread(mybuff, 1, bufflen - 1, stream);
  if(read == bufflen - 1) {
    //matth: This silently truncates strings if scanf would have read more
    //than bufflen-1 bytes.  It would be nice if we could report a buffer
    //overrun in this case.
    FILE *myfile = fopen("sscanf_string", "w+b");
    if(! myfile) {
      fprintf(stderr, "Cannot create file for fscanf_string.\n");
      exit(2);
    }
    // Write them out to the new file
    if (fwrite(mybuff, read, 1, myfile) != 1)
      fprintf(stderr, "write truncated for fscanf_string.\n");

    // Rewind
    fseek(myfile, 0L, SEEK_SET);
    // And scan
    scanned = fscanf(myfile, what, buffer);
    // Find out how much we have advanced. This is misleading if we
    // are openin text mode on Win and we skipped newlines !
    orig_pos += ftell(myfile);
    fseek(stream, orig_pos, SEEK_SET);
    fclose(myfile);
    if(scanned == EOF) {
      CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
    }
  } else {
    // The file is shorter than the buffer. Go ahead and scan
    fseek(stream, orig_pos, SEEK_SET);
    scanned = fscanf(stream, what, buffer);
  }
  if(scanned == EOF) {
    if (ccured_scanf_count == 0){
      //If the input ends before the first match, getScanfCount returns EOF
      ccured_scanf_count = EOF;
    } else {
      //else the count is however many items have been matched so far
      //(ccured_scanf_count is unchanged)
    }
  } else {
    ccured_scanf_count += scanned;
  }
}

#endif // CCURED_NO_SCANF


// ------------------------ stuff needed for structs+edg+stl :dsw ------------------
#ifndef CCURED_NO_WILD_WRAPPERS
// These are not tested, as Scott is still writing the wrappers for
// them. --dsw ****************

// NOTE: I just implemented the dang thing.  It was simpler than
// figuring out how to check for the correct arguments to the real
// thing.
wildp_char strncat_www(wildp_char dest, wildp_char src, size_t n) {
    // NOTE: I don't verify the assumtion that src and dest don't
    // overlap.  However, if this were violated, it would not
    // technically constitute a violation of memory safty in the sense
    // of ccured.  Scott told me so --dsw.
    int destwildlen = wildp_length(dest);
    int srcwildlen = wildp_length(src);
    int i;
    int j;
    // Find the end of dest.
    for (i=0; i<destwildlen && dest._p[i]!='\0'; ++i) {
    }
    for (j=0;
	 i<destwildlen && (size_t)j<n && j<srcwildlen && src._p[i]!='\0';
	 ++i, ++j) { // We can't go off the end of dest nor src nor past n.
	dest._p[i] = src._p[j];
    }
    // Stick on terminating nul character.
    if (i<destwildlen) {
	dest._p[i] = '\0';
    } else {
	ccured_fail(FAIL_STRINGBOUND  FILE_AND_LINE);
    }
    return dest;
}

// NOTE: I just implemented the dang thing.  It was simpler than
// figuring out how to check for the correct arguments to the real
// thing.
wildp_char strncpy_www(wildp_char dest, wildp_char src, size_t n) {
    int destwildlen = wildp_length(dest);
    int srcwildlen = wildp_length(src);
    int i;
    for (i=0; (size_t)i<n && i<srcwildlen; ++i) { // We can't go off the end of src nor past n.
	if (src._p[i]!='\0') {  // If there is something to copy,
	    if (i<destwildlen) { // and somewhere to put it
		dest._p[i] = src._p[i]; // copy it.
	    } else {
		ccured_fail(FAIL_STRINGBOUND  FILE_AND_LINE); // otherwise, fail.
	    }
	}
    }
    // Pad the rest of dest with nuls.
    for (; i<destwildlen; ++i) dest._p[i] = '\0';
    return dest;
}

// These are tested. ****************

int feof_w(wildp_FILE __stream) {
    return feof(__stream._p);
}

int fgetpos_ws(wildp_FILE __stream, fpos_t *__pos) {
    return fgetpos(__stream._p, __pos);
}

int fsetpos_ws(wildp_FILE __stream, const fpos_t *__pos) {
    return fsetpos(__stream._p, __pos);
}

long ftell_w(wildp_FILE __stream) {
    return ftell(__stream._p);
}

//  wildp_void mmap_ws(void *start, size_t length, int prot, int flags, int fd, off_t offset) {
//      // Its legal for start to not be zero, but our implementation is
//      // not guaranteed.  Scott told me to do this :dsw.
//      assert(start == 0);
//  }

// This should work, but its commented out for symmetry with mmap
// above, which is not implemented.
//  int munmap_w(wildp_void start, size_t length) {
//      return munmap(start._p, length);
//  }

#ifndef _MSVC

  int pthread_mutex_destroy_w(wildp_pthread_mutex_t mutex) {
      return pthread_mutex_destroy(mutex._p);
  }

  int pthread_mutex_init_ws(wildp_pthread_mutex_t mutex,
			    pthread_mutexattr_t *mutexattr) {
      return pthread_mutex_init(mutex._p, mutexattr);
  }

  char *setlocale_sw(int category, wildp_char locale) {
      if (locale._p != NULL) wildp_verify_nul(locale);
      return setlocale(category, locale._p);
  }

#endif

int setvbuf_ww(wildp_FILE __stream, wildp_char __buf, int __mode, unsigned int __n) {
    if (__buf._p != NULL) wildp_write_atleast(__buf, __n);
    return setvbuf(__stream._p, __buf._p, __mode, __n);
}

int ungetc_w(int __c, wildp_FILE __stream) {
    return ungetc(__c, __stream._p);
}

#endif // CCURED_NO_WILD_WRAPPERS

// ------------------------ kind_of ------------------
// sm: what is this for?
// gn: to build test cases in which we can ask about the kind of a pointer
// gn: we intercept these calls in box.ml
//
//char* ccured_kind_of() {
//  return "SAFE";
//}
//char* ccured_kind_of_sq() {
//  return "SEQ";
//}
//char* ccured_kind_of_sQ() {
//  return "SEQN";
//}
//char* ccured_kind_of_sf() {
//  return "FSEQ";
//}
//char* ccured_kind_of_sF() {
//  return "FSEQN";
//}
//char* ccured_kind_of_sw() {
//  return "WILD";
//}

//struct {
//  int len;
//  char data[8];
//  int tags;
//} theWild = { 2, "WILD", 0 };
//
//wildp_char ccured_kind_of_ww() {
//  wildp_char res;
//  res._p = theWild.data;
//  res._b = res._p;
//  return res;
//}


// ---------------------- test code ------------------------
// sm: I want to be able to test the internal interfaces
void __ccured_test_ccuredlib()
{
#if !defined(RELEASELIB) && defined(_GNUCC)
  char s[10] = "hello";
  assert(__ccured_strlen_n(s, s+10, 20) == 5);
  assert(__ccured_strlen_n(s, s+10, 3) == 3);
  assert(__ccured_strlen_n(s, s+10, 4) == 4);
  assert(__ccured_strlen_n(s, s+10, 5) == 5);
  assert(__ccured_strlen_n(s, s+10, 6) == 5);
  assert(__ccured_strlen_n(s, s+10, 7) == 5);
  assert(__ccured_strlen_n(s, s+6, 4) == 4);
  assert(__ccured_strlen_n(s, s+5, 4) == 4);
  assert(__ccured_strlen_n(s, s+4, 4) == 4);
  // I'd like to drop 's' one more, but that requires catching
  // signals etc, so for now I'll skip it
#endif // !defined(RELEASELIB) && defined(_GNUCC)
}


// ****************
// dsw: make a way to chop down the home area of an sequence pointer
// so we don't get "Creating an unaligned sequence" error.

// this one is a no-op in case we put one in where not needed
void* __align_seq(void *p, size_t size) {
  return p;
}

//matth: cast to char* to avoid "arithmetic on void*" errors.
seqp_void __align_seq_qq(seqp_void p, size_t size) {
  seqp_void res;
  if (p._e == 0) return p;
  // take the floor of the length wrt size being the unit value
  res._p = p._p;
  res._b = p._b;
  res._e = (void*)((char*)p._e -
		   ((uintptr_t)p._e - (uintptr_t)p._p) % size);
  return res;
}

fseqp_void __align_seq_ff(fseqp_void p, size_t size) {
  fseqp_void res;
  if (p._e == 0) return p;
  // take the floor of the length wrt size being the unit value
  res._p = p._p;
  res._e = (void*)((char*)p._e -
		   ((uintptr_t)p._e - (uintptr_t)p._p) % size);
  return res;
}


// ****************

// similarly for __mkptr, which also appears explicitly in our
// modified versions of STLport


#if defined(_GNUCC) && !defined(__CYGWIN__)
// sm: wrapper for signal; accepts FSEQ because I call it with SIG_IGN,
// which is a number of some kind (the number 1)
struct some_fseqp_fun {
   void (*  _p)(int  ) ;
   void *_e ;
};
void (*__sysv_signal_sf(int signum, struct some_fseqp_fun fun))(int n )
{
  if ((unsigned long)fun._p != (unsigned long)fun._e &&
      (unsigned long)fun._p > 16) {
    // user has passed an invalid FSEQ that isn't one of the low addresses
    // we know to be encoded special values; complain
    ccured_fail_str("__sysv_signal called with a strange pointer\n"  FILE_AND_LINE);
  }
#if defined(__FreeBSD__)
  return signal(signum, fun._p);
#else
  return __sysv_signal(signum, fun._p);
#endif
}
#endif // defined(_GNUCC) && !defined(__CYGWIN__)

#if defined(_GNUCC)

#if 0 //matth: we shouldn't need these true_ functions anymore:

// wrapper for gethostbyname_r
#include <netdb.h>
struct hostent* true_gethostbyname(const char * name) {
    return gethostbyname(name);
}
struct servent* true_getservbyname(const char * name, const char * proto) {
    return getservbyname(name, proto);
}
struct hostent *true_gethostbyaddr(const char *addr, int len, int type) {
    return gethostbyaddr(addr, len, type);
}

# if !defined(__CYGWIN__)
struct hostent* true_gethostent(void) {
    return gethostent();
}
int true_gethostbyname_r (__const char *__restrict __name,
			  struct hostent *__restrict __result_buf,
			  char *__restrict __buf, size_t __buflen,
			  struct hostent **__restrict __result,
			  int *__restrict __h_errnop) __THROW {
  return gethostbyname_r(__name, __result_buf,
			 __buf, __buflen, __result, __h_errnop);
}
int true_getservbyname_r (__const char *__restrict __name,
			  __const char *__restrict __proto,
			  struct servent *__restrict __result_buf,
			  char *__restrict __buf, size_t __buflen,
			  struct servent **__restrict __result) __THROW {
  return getservbyname_r(__name, __proto, __result_buf,
			 __buf, __buflen, __result);
}
int true_gethostent_r (struct hostent *__restrict __result_buf,
		       char *__restrict __buf, size_t __buflen,
		       struct hostent **__restrict __result,
		       int *__restrict __h_errnop) __THROW {
  return gethostent_r (__result_buf, __buf, __buflen, __result, __h_errnop);
}

int true_gethostbyaddr_r (__const void *__restrict __addr, __socklen_t __len,
			  int __type,
			  struct hostent *__restrict __result_buf,
			  char *__restrict __buf, size_t __buflen,
			  struct hostent **__restrict __result,
			  int *__restrict __h_errnop) __THROW {
  return gethostbyaddr_r (__addr, __len, __type,__result_buf,__buf,
			  __buflen,__result,__h_errnop);
}
#endif //!CYGWIN
#endif //0

# if !defined(__CYGWIN__)
#  include <netdb.h>
// sm: similar for getaddrinfo
int true_getaddrinfo(
  const char *node, const char *service,
  const struct addrinfo *hints, struct addrinfo **res)
{
  return getaddrinfo(node, service, hints, res);
}

void true_freeaddrinfo(struct addrinfo *res)
{
  return freeaddrinfo(res);
}

#endif //CYGWIN
#endif //GNUCC

#if defined(_GNUCC)
// helpers for readv_wrapper and writev_wrapper
#include <sys/uio.h>
int true_readv(int fd, const struct iovec* vec, int count)
{
  return readv(fd, vec, count);
}

int true_writev(int fd, const struct iovec* vec, int count)
{
  return writev(fd, vec, count);
}
#endif

#if defined _GNUCC //&& ! defined __CYGWIN__
void check_glob_size(int pglob_size)
{
  if (sizeof(glob_t) != pglob_size) {
    // see include/functions/glob.h
    ccured_fail_str("glob_t size mismatch; something is wrong\n"  FILE_AND_LINE);
  }
}

// sm: the usual.. but with a size check
int true_glob(const char *pattern, int flags,
	      int errfunc(const char *epath, int eerrno),
	      glob_t *pglob, int pglob_size)
{
  check_glob_size(pglob_size);
  return glob(pattern, flags, errfunc, pglob);
}

void true_globfree(glob_t *pglob, int pglob_size)
{
  check_glob_size(pglob_size);
  globfree(pglob);
}

struct passwd *true_getpwnam(const char *name)
{
  return getpwnam(name);
}

#endif // GNUCC


unsigned long ___stack_threshhold;
unsigned long  ___compute_stack_threshhold(void) {
  int a_local;
  unsigned long maxSize = 24 * 65536UL;
  unsigned long sp = (unsigned long)&a_local;
  if(sp < maxSize) {
    unsigned long res = 0x1000;
    fprintf(stderr,
	    "SP=0x%08lx, which is smaller than the maximum stack size. Will set a stack theshhold of 0x%lx\n",
	    sp, res);
    return res;
  }
  return sp - maxSize;
}

void ___stack_overflow(void) {
  // int a_local;
  // printf("SP = %08lx. Threshhold=0x%08lx\n",
  //       (unsigned long)&a_local, ___stack_threshhold);
  ccured_fail(FAIL_STACK_OVERFLOW  FILE_AND_LINE);
}

void CHECK_FORMATARGS_f(fseqp_char format) {
  __verify_nul_f(format);
  CHECK_FORMATARGS(format._p);
}

#ifndef CCURED_NO_MALLOC
uintptr_t wrapperAlloc(unsigned int sz) {
  return (uintptr_t)malloc(sz);
}
void  wrapperFree(void* x) { free(x); }
char* wrapperStrdup(char *str) {
  if(str) {
    return STRDUP(str);
  } else {
    return 0;
  }
}
#endif


void abort_deepcopy(char *fieldname) {
  ccured_fail_str(fieldname FILE_AND_LINE);
}
