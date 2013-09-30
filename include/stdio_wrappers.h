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

// sm: There's a subtle problem: stdio.h gets #included in some strange
// ways by some files.  For example, pwd.h says (line 69)
//   #define __need_FILE
//   #include <stdio.h>
// which causes stdio.h to provide the typedef for FILE, but omit
// everything else (like the #definition of EOF).  But then these wrappers
// get pulled in, expecting EOF, and we fail.  So I've now made this
// stuff conditional upon EOF being #defined, and hope that will ensure
// the code below is only seen during "normal" processing of stdio.h.
#if defined(CCURED) && defined(EOF) && ! defined(STDIO_WRAPPERS_INCLUDED)
#define STDIO_WRAPPERS_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif
  
// __mkptr_file is defined in ccuredlib.c.  Usually, it is implemented
// as __mkptr_size(f, sizeof(FILE)).  But for WILDS this isn't possible, so 
// it is implemented as __mkptr(f, NULL) instead.  This prevents programs
// from accessing the data in a FILE* __WILD, which is necessary since the
// buffer returned by fopen has no WILD tags.
extern FILE* __mkptr_file(FILE* __SAFE f);
#pragma ccuredpoly("__mkptr_file");

// __ptrof_file is also defined in ccuredlib.c.  Usually, it is the same
// as __ptrof, but for WILDs it is the same as ptrof_nocheck.  This is needed
// because mkptr_file creates wild pointers using NULL home areas.
extern FILE* __SAFE __ptrof_file(FILE* f);
#pragma ccuredpoly("__ptrof_file");


#pragma ccuredvararg("printf", printf(1))
#pragma ccuredvararg("fprintf", printf(2))
#pragma ccuredvararg("snprintf", printf(3))
#pragma ccuredvararg("syslog", printf(2))
#pragma ccuredvararg("sprintf", printf(2))
#pragma ccuredvararg("vsprintf", printf(2))
#pragma ccuredvararg("vfprintf", printf(2))
#pragma ccuredvararg("vprintf", printf(1))     // sm: for ftpd
#pragma ccuredvararg("vsyslog", printf(2))     // sm: for ftpd
void * __endof(void *ptr);
#pragma ccuredpoly("__endof")


extern void   resetScanfCount(void);
extern void   resetSScanfCount(const char*);
extern int    getScanfCount(void);
extern FILE*  ccured_sscanf_file;

extern void   ccured_fscanf_string(FILE *, char *format, char *buffer);
extern void   ccured_fscanf_string_len(FILE *, char *format, char *buffer,
                                       long bufflen);
#pragma ccuredpoly("ccured_fscanf_string")

// Provide a wrapper  what requires the string to be valid
#pragma ccuredwrapper("ccured_fscanf_string_wrapper", of("ccured_fscanf_string"))
__inline static   
void   ccured_fscanf_string_wrapper(FILE * f, char *format, char *buffer) {
  long bufflen = (long)__endof(buffer) - (long)buffer;
  __verify_nul(format);
  ccured_fscanf_string_len(__ptrof(f), __ptrof(format), __ptrof(buffer),
                           bufflen);
}
  

// sm: adding this for wu-ftpd, where there are lots of calls
// to {s,f}scanf, but in all cases it's a simple type being read,
// not a string, so we should be ok letting things go unchecked
struct scanf_format {
  int *p_int;
  double *p_double;
  long *p_long;
  unsigned int *p_uint;
  unsigned long *p_ulong;
  // sm: if someone wants to add char* here, a wrapper should
  // be written, I think
  char *p_char;
  short *p_short;
  long long *p_longlong;
  unsigned long long *p_ulonglong;
};

#pragma ccuredvararg("sscanf", sizeof(struct scanf_format))
#pragma ccuredvararg("fscanf", sizeof(struct scanf_format))
#ifdef __cplusplus
  }
#endif
  
#pragma ccuredwrapper("fgets_wrapper", of("fgets"));
__inline static
char * fgets_wrapper (char *buf, int size, FILE *fp)  { 
  char * res;
  __write_at_least(buf, size);
  res = fgets((char*)__ptrof(buf), size, (FILE*)__ptrof_file(fp));
  return (char*)__mkptr(res, buf);
}

#pragma ccuredwrapper("fopen_wrapper", of("fopen"));
__inline static
FILE* fopen_wrapper(const char* fname, const  char * mode)
{
  return __mkptr_file(fopen(__stringof(fname), __stringof(mode)));
}

#pragma ccuredwrapper("fdopen_wrapper", of("fdopen"));
__inline static
FILE* fdopen_wrapper(int filedes, const  char * mode)
{
  return __mkptr_file(fdopen(filedes, __stringof(mode)));
}

#pragma ccuredwrapper("fflush_wrapper", of("fflush"));
__inline static
int fflush_wrapper(FILE* f)
{
  return fflush((FILE*)__ptrof_file(f));
}
#pragma ccuredwrapper("fclose_wrapper", of("fclose"));
__inline static
int fclose_wrapper(FILE* f)
{
  return fclose((FILE*)__ptrof_file(f));
}


#ifdef _GNUCC
  /* Appears in putc for GCC */
  #ifdef __CYGWIN__
    #pragma ccuredwrapper("__swbuf_wrapper", of("__swbuf"));
    __inline static
    int __swbuf_wrapper(int c, void* fl) {
      return __swbuf(c, (FILE*)__ptrof_file(fl));
    }
    /* Appears in getc for GCC */
    #pragma ccuredwrapper("__srget_wrapper", of("__srget"));
    __inline static
    int __srget_wrapper(void* fl) {
      return __srget((FILE*)__ptrof_file(fl));
    }
  #endif // __CYGWIN__

  // sm: internally, my putc uses _IO_putc
  // see /usr/include/features.h to find glibc version numbers
  #if defined(__GLIBC__) && __GLIBC__ == 2
    #pragma ccuredwrapper("_IO_putc_wrapper", of("_IO_putc"));
    __inline static
    int _IO_putc_wrapper(int c, FILE* fl) {
      return _IO_putc(c, (FILE*)__ptrof_file(fl));
    }

    #pragma ccuredwrapper("_IO_getc_wrapper", of("_IO_getc"));
    __inline static
    int _IO_getc_wrapper(FILE* fl) {
      return _IO_getc((FILE*)__ptrof_file(fl));
    }
  #endif
#endif // _GNUCC

#if defined(_MSVC) || defined(__CYGWIN__)
  //putc and getc are macros in some systems.
  #pragma ccuredwrapper("putc_wrapper", of("putc"));
  __inline static
  int putc_wrapper(int c, FILE* fl) {
    return putc(c, (FILE*)__ptrof_file(fl));
  }

  #pragma ccuredwrapper("getc_wrapper", of("getc"));
  __inline static
  int getc_wrapper(FILE* fl) {
    return getc((FILE*)__ptrof_file(fl));
  }
#endif


// sm: similar (no error checking..) wrappers for scott/putc
#pragma ccuredwrapper("fputc_wrapper", of("fputc"));
__inline static
int fputc_wrapper(int c, FILE* fl) {
  return fputc(c, (FILE*)__ptrof_file(fl));
}

#pragma ccuredwrapper("fputs_wrapper", of("fputs"));
__inline static
int fputs_wrapper(const char *s, FILE* fl) {
  return fputs(__stringof(s), (FILE*)__ptrof_file(fl));
}

#pragma ccuredwrapper("fgetc_wrapper", of("fgetc"));
__inline static
int fgetc_wrapper(FILE* fl) {
  return fgetc((FILE*)__ptrof_file(fl));
}

#pragma ccuredwrapper("puts_wrapper", of("puts"));
__inline static
int puts_wrapper(char* s) {
  return puts((char*)__ptrof(s));
}

#pragma ccuredwrapper("fileno_wrapper", of("fileno"));
__inline static
int fileno_wrapper(FILE* f) {
  return fileno((FILE*)__ptrof(f));
}

#pragma ccuredwrapper("ferror_wrapper", of("ferror"));
__inline static
int ferror_wrapper(FILE* f) {
  return ferror((FILE*)__ptrof(f));
}

#pragma ccuredwrapper("fseek_wrapper", of("fseek"));
__inline static
int fseek_wrapper(FILE* fp, long offset, int whence)
{
  return fseek((FILE*)__ptrof_file(fp), offset, whence);
}

#pragma ccuredwrapper("clearerr_wrapper", of("clearerr"));
__inline static
void clearerr_wrapper(FILE* fp)
{
  clearerr((FILE*)__ptrof_file(fp));
}


// multiply two unsigned 32-bit values but check for overflow;
extern unsigned __ccured_mult_u32(unsigned x, unsigned y);

#pragma ccuredwrapper("fread_wrapper", of("fread"));
__inline static
size_t fread_wrapper(char* buff, size_t size, size_t count, FILE *fl)
{
  size_t requested = __ccured_mult_u32(size, count);
  size_t res;
  __write_at_least(buff, requested);
  res = fread(__ptrof(buff), size, count, (FILE*)__ptrof_file(fl));
  return res;
}

#pragma ccuredwrapper("fwrite_wrapper", of("fwrite"));
__inline static
size_t fwrite_wrapper(char* buff, size_t size, size_t count, FILE *fl)
{
  size_t requested = __ccured_mult_u32(size, count);
  size_t res;
  __write_at_least(buff, requested);
  res = fwrite(__ptrof(buff), size, count, (FILE*)__ptrof_file(fl));
  return res;
}


// It is unsound to use gets, so we turn it into a fgets
#pragma ccuredwrapper("gets_wrapper", of("gets"));
__inline static
char* gets_wrapper(char* buffer)
{
  char* res = fgets_wrapper(buffer, __LENGTH(buffer), stdin);

  if (res != NULL) {  //if res != NULL:
    char *tmp = res;
    while (*tmp != '\n' 
      && *tmp != '\0') {
      tmp++;     // find newline or nul
    }
    *tmp ='\0';
  }
  return res;
}

#include <stdarg.h>

//In ccuredlib.c.  Calls vsnprintf after checking that the format string
// matches the arguments.  Doesn't check the length of the buffer.
extern int __ccured_vsnprintf(char* __SAFE buffer, int size, 
			      const char * __SAFE format,
			      va_list args);


#pragma ccuredvararg("vsnprintf_wrapper", printf(3))
#pragma ccuredwrapper("vsnprintf_wrapper", of("vsnprintf"))
__inline static
int vsnprintf_wrapper(char *buf, size_t n, const char * format, va_list ap){
  __write_at_least(buf, n);
  return __ccured_vsnprintf(__ptrof(buf),n,__stringof(format),ap);
} 

#pragma ccuredvararg("vsprintf_wrapper", printf(2))
#pragma ccuredwrapper("vsprintf_wrapper", of("vsprintf"));
__inline static
int vsprintf_wrapper(char *buf, const char * format, va_list ap) {
  int n = (char*)__endof(buf) - buf;
  return vsnprintf_wrapper(buf, n, format, ap);
} 

#pragma ccuredvararg("snprintf_wrapper", printf(3))
#pragma ccuredwrapper("snprintf_wrapper", of("snprintf"));
__inline static
int snprintf_wrapper(char *buf, size_t n, const char * format, ...){
  va_list ap;
  int res;
  __write_at_least(buf, n);
  va_start(ap, format);
  res = __ccured_vsnprintf(__ptrof(buf),n,__stringof(format),ap); 
  va_end(ap);
  return res;
}

#pragma ccuredvararg("sprintf_wrapper", printf(2))
#pragma ccuredwrapper("sprintf_wrapper", of("sprintf"));
__inline static
int sprintf_wrapper(char *buf, const char * format, ...){
  va_list ap;
  int res;
  int size = __LENGTH(buf);
  __write_at_least(buf, size); //fails if size < 0
  va_start(ap, format);
  res = __ccured_vsnprintf(__ptrof(buf),size,__stringof(format),ap);
  va_end(ap);
  if (res < 0 || res >= size){
    //If vsnprintf tries to write more than size bytes, it will either
    //return -1 or the number of bytes it tried to write, depending on the
    //version of glibc.
    CCURED_FAIL(FAIL_UBOUND FILE_AND_LINE);
  }
  return res;
}


extern int ccured_scanf_count;

#pragma ccuredpoly("ccured_fscanf_double");
__inline static
double ccured_fscanf_double(FILE *stream, char *format) {
  double d = 0.0;
  if(ccured_scanf_count != EOF) {
    int res = fscanf((FILE*)__ptrof_file(stream),
                     (char*)__stringof(format), &d);
    if(res == EOF) {
      ccured_scanf_count = EOF;
    } else {
      ccured_scanf_count += res;
    }
  }
  return d;
}                                                                   

#pragma ccuredpoly("ccured_fscanf_int");
__inline static
int ccured_fscanf_int(FILE *stream, char *format) {
  int i = 0;
  if(ccured_scanf_count != EOF) {
    int res = fscanf((FILE*)__ptrof_file(stream),
                     (char*)__stringof(format), &i);
    if(res == EOF) {
      ccured_scanf_count = EOF;
    } else {
      ccured_scanf_count += res;
    }
  }
  return i;
}                                                                   

#pragma ccuredpoly("ccured_fscanf_nothing");
__inline static
void ccured_fscanf_nothing(FILE *stream, char *format) {
  // just advance the pointer and match
  if(EOF == fscanf((FILE*)__ptrof_file(stream),
                   (char*)__stringof(format)))
    ccured_scanf_count = EOF;
}                                                                   

/* matth: if we enable this wrapper here, we'll have to add char* to the
 * list of legal fscanf arguments, which unforunately would also let the
 * user use fscanf unsafely.
 */
#if 0
#pragma ccuredpoly("ccured_fscanf_string");
void ccured_fscanf_string(FILE *stream, char* format, char* buffer) {
  size_t bufflen = __LENGTH(buffer);
  char *mybuff;
  long orig_pos;
  size_t read;
  int scanned;
  FILE* __SAFE stream_safe = __ptrof_file(stream);

  if(!__valid(buffer)) {
    CCURED_FAIL(FAIL_NONPOINTER  FILE_AND_LINE);
  }
  // Now create a buffer
  mybuff = (char*)malloc(bufflen);
  if(!mybuff) {
    fprintf(stderr, "Cannot allocate buffer for fscanf_string");
    exit(2);
  }
  // Now remember the positon in the stream
  orig_pos = ftell(stream_safe);
  // Now read that many characters from the stream in the buffer
  read = fread(mybuff, 1, bufflen - 1, stream_safe);
  if(read == bufflen - 1) {
    FILE *myfile = fopen("sscanf_string", "rwb");
    if(! myfile) {
      fprintf(stderr, "Cannot create file for fscanf_string");
      exit(2);
    }
    // Write them out to the new file
    fwrite(mybuff, read, 1, myfile);
    // Rewind
    fseek(myfile, 0L, SEEK_SET);
    // And scan
    scanned = fscanf(myfile, format, __ptrof(buffer));
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
    scanned = fscanf(stream, format, (char *)__ptrof(buffer));
  }
  if(scanned == EOF) {
    ccured_scanf_count = EOF;
  } else {
    ccured_scanf_count += scanned;
  }
  __write_at_least(buffer, bufflen);//clear all tags.
}
#endif

#pragma ccuredwrapper("perror_wrapper", of("perror"));
void perror_wrapper(const char *s) {
  perror(__stringof(s));
}


#ifdef __cplusplus
}
#endif // __cplusplus
#endif // CCURED

