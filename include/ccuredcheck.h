/* See licence and copyright notice at the end of this file */

// This file is included:
// - after CCured (with CCURED_POST) defined
// - in the library

#include <stdint.h>
#include <sys/types.h>

// Grab the annotations. If we are after CCured this will define them away
#include "ccuredannot.h"

//
//   RUN-TIME CHECKS
//


#ifndef CCURED_NO_GC
/* We use the preprocessor to replace the calls to the allocation functions
 * with our own versions. Note that this happens after curing. */
  #define malloc      ccured_malloc
  #define calloc      ccured_calloc
  #define realloc     ccured_realloc
  #define free        ccured_free
  #define explicit_gc ccured_explicit_gc

#endif

// Define some prototypes for functions used by boxing
extern void* allocInternal(unsigned int);
extern void  freeInternal(void *);
extern void  freeInternalMinus4(void *);

// We declare this as unsigned int because allocators are made like that
extern void* wrapperAlloc(unsigned int);
extern void wrapperFree(void*);
extern char* wrapperStrdup(char *);

/* weimer. GN: Wes, Wes! I spent so much time trying to fix a bug due to this
 * define. __cdecl on Windows is a keyword not a macro. You made it
 * disappear and functions were going nowhere. */
#if !defined(_MSVC) && !defined(__cdecl)
  #define __cdecl
#endif
#ifndef NULL
  #define NULL 0
#endif

void *   __scalar2pointer(unsigned long  l , int  fid , int  lid ) ;


//
//
// WRAPPERS
//
//
//#if defined(CCURED) && defined(_MSVC)
//#define memcpy _memcpy
//#endif

// sm: struct _stat doesn't exist in linux
#ifdef _GNUCC
#define _stat stat
#define __builtin_memset_ww memset_ww
#define __builtin_memset_ff memset_ff
#define __builtin_memset_qq memset_qq
#define __builtin_memset_sf memset_sf
#endif


/* It's not possible to write a setjmp wrapper per se, because you'd be
 * seting the wrong context: the saved context is invalidated when the
 * wrapper returns. So, instead we define some macros. */
// GN: changed to account for splitting the arguments of functions
#ifdef CCURED_SPLIT_ARGUMENTS
 #define _setjmp_w(fatpbuf_p, fatpbuf_b)                                    \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf_p, fatpbuf_b, sizeof(jmp_buf)),    \
     _setjmp(fatpbuf_p) )

 // similar versions for setjmp and __sigsetjmp
 // (at this time, untested)
 #define setjmp_w(fatpbuf_p, fatpbuf_b)                                   \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf_p, fatpbuf_b, sizeof(jmp_buf)),   \
     setjmp(fatpbuf_p) )
 #define __sigsetjmp_w(fatpbuf_p, fatpbuf_b, savemask)                      \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf_p, fatpbuf_b, sizeof(jmp_buf)),    \
     __sigsetjmp(fatpbuf_p, savemask) )
#else
 #define _setjmp_w(fatpbuf)                                                \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf._p, fatpbuf._b, sizeof(jmp_buf)),    \
     _setjmp(fatpbuf._p) )

 // similar versions for setjmp and __sigsetjmp
 // (at this time, untested)
 #define setjmp_w(fatpbuf)                                                \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf._p, fatpbuf._b, sizeof(jmp_buf)),   \
     setjmp(fatpbuf._p) )
 #define __sigsetjmp_w(fatpbuf, savemask)                                  \
   ( CHECK_WILDP_WRITE_ATLEAST(fatpbuf._p, fatpbuf._b, sizeof(jmp_buf)),    \
     __sigsetjmp(fatpbuf._p, savemask) )
#endif

// defines to fix the 32-bit assumption below, for x86_64 only currently.
#if defined __x86_64__
# define CC_64_BIT
# define CC_BYTES_PER_WORD       8
# define CC_LOG_BYTES_PER_WORD   3
#else
# define CC_32_BIT
# define CC_BYTES_PER_WORD       4
# define CC_LOG_BYTES_PER_WORD   2
#endif

#define CC_LOG_BITS_PER_WORD    (CC_BYTES_PER_WORD + 3)
#define CC_BITS_PER_WORD        (8 * CC_BYTES_PER_WORD)
#define CC_ALIGNED_PTR_MASK     ((0x1 << CC_LOG_BYTES_PER_WORD) - 1)

// a lot of CCured's implementation was dependent on the assumption
// that pointers are represented in 32 bits.  We leave these defines
// here for now.
#define I32 int
#define U32 unsigned I32

#ifndef MIN
  #define MIN(x,y) (((x) < (y)) ? (x) : (y))
#endif


/* Define this if you want to omit the null checks. Note that this is not
 * safe because the null check is sometimes used to prevent you from
 * obtaining a safe pointer as follows: & 0[some_number]. Use it for
 * experimentation only */
// #define OMIT_NULL_CHECK


/* Define this if you want to omit *all* checks.  Obviously this is
 * even more wildly unsafe then omitting null checks.  It can be
 * useful, though, if we want to measure the cost of runtime checks as
 * distinguished from the cost of the changed representation of
 * data. */
// #define NO_CHECKS

#ifdef NO_CHECKS
#  define CCURED_CHECK(check)
#else  /* perform standard runtime checks */
#  define CCURED_CHECK(check)  check
#endif /* perform standard runtime checks */


// libc prototypes (we avoid pulling in entire headers; sm: I no longer
// remember why)
extern size_t strlen(const char *);

// ---------------- check function return value --------------
// CHECK_GETFRAME: return the frame pointer of the current function;
// we assume (for stacks growing towards 0) that all local variables
// (those on the stack, anyway) are at addresses less-or-equal this value
#if defined(_MSVC)
  #define CHECK_GETFRAME(putwhere) { \
     char *__bpVal; \
     _asm { mov __bpVal, ebp }; \
     (putwhere) = __bpVal; }
#elif defined(_GNUCC)
  // sm: gcc doesn't inline functions unless the optimizer is turned
  // on, but I really want to be able to test our system without the
  // optimizer; so I'm turning this into a macro, so we get the frame
  // of the *caller*, not the callee
  #define CHECK_GETFRAME(putwhere) (putwhere) = __builtin_frame_address(0);
#endif

// given a value being returned from a function call, verify it is
// not a pointer to this function's locals (so, transitively, we
// should never be able to return a pointer to a deallocated frame);
// The pointer passed to this function should be the _b or _e component
// of a pointer, not the _p component because that one can be
// adjusted through arithmetic. In each case pass the component
// that is NULL if the pointer is an integer (_e for FSEQ and
// _b for all others).
//#define CHECK_RETURNPTR(p)  __CHECK_RETURNPTR(p  FILE_AND_LINE)

// sm: as for CHECK_GETFRAME itself, I'm changing this to a macro
// to ensure inline expansion even when optimization is turned off

/* gn: If gcc inlines the function containing the CHECK_RETURNPTR then
 * CHECK_GETFRAME will obtain the frame address of the wrong function. To
 * prevent this I have changed box.ml to add a special volatile temporary
 * first in the argument list and use its address as the frame address */
#define CHECK_RETURNPTR(p, pTopOfFrame) CCURED_CHECK(__CHECK_RETURNPTR(p, pTopOfFrame))
#ifdef _MSVC
  #define __CHECK_RETURNPTR(p, pTopOfFrame)                      \
  {                                                              \
    char* bpVal;                                                 \
    /*CHECK_GETFRAME(bpVal);*/                                   \
    bpVal = (char*)pTopOfFrame;                                  \
    /* _MSVC seems to put the stack at lowest addresses */       \
    if (p && (char*)p <= bpVal) {                                \
      CCURED_FAIL(FAIL_BELOW_STACK_ADDRESS FILE_AND_LINE);       \
    }                                                            \
  }
#else
  #define __CHECK_RETURNPTR(p, pTopOfFrame)                                 \
  {                                                                         \
    char* bpVal;                                                            \
    /*CHECK_GETFRAME(bpVal);*/                                              \
    bpVal = (char*)pTopOfFrame;                                             \
                                                                            \
    /* Others (gcc) put the stack up. Check only the first 2M to avoid */   \
    /* rejecting pointers that are really into the heap                */   \
    if (p && ! ((bpVal - (char*)p) >> 21)) {                                \
      CCURED_FAIL(FAIL_BELOW_STACK_ADDRESS FILE_AND_LINE);                  \
    }                                                                       \
  }
#endif

// ----------------- writing pointers through pointers or to globals --------
// given an address the user is writing through a pointer, verify
// it is not a pointer into the stack; the 'where' argument is the
// address of the pointer whose value will *change*, i.e. this is
// checking something like ``*where = p''
//
// pTopOfFrame is either the caller's frame pointer or the address of
// the firstlocal.
#define CHECK_STOREPTR(where, p, pTopOfFrame) \
		CCURED_CHECK(__CHECK_STOREPTR(where, p, (void*)(pTopOfFrame)  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_STOREPTR(void **where,
		      void *p,
		      void* pTopOfFrame
		      CCURED_FAIL_EXTRA_PARAMS)
{
  #if defined _GNUCC || defined _MSVC
  // the following check assumes the stack grows towards smaller
  // addresses; that's an ABI feature not a compiler issue, but
  // we're pretending it is anyway
    if ((uintptr_t)p - (uintptr_t)where < 0x100000U) {
      // sm: if the check below fails, it means that 'p'
      // is a stack address; however, since 'where' is only a little
      // (<1M) smaller than 'p', it too must be a stack address;
      // moreover, it's in a warmer frame, so it will go away before
      // 'p' will, so this should be ok
      //
      // I've implemented this extra check as a way to try to allow
      // EDG's exception-handling code to work
      return;
    }

    // matth: If where is less than and within a stone's throw of the frame
    // pointer, then it is in the current stack frame.  Allow all writes.
    if ((uintptr_t)pTopOfFrame - (uintptr_t)where < 0x100000U) {
      return;
    }

  #endif // _GNUCC || _MSVC

  if (p) {
    char* bpVal;
    int   delta;
    bpVal = (char*)pTopOfFrame;
    delta = (bpVal - (char*)p);

    if(__ccuredDisableStoreCheck) {
      return;
    }
    // If this is an address in main or above, let it alone
    if(p >= __ccuredStackBottom) return;

    #ifndef DISABLE_HEAPIFY
      // the usual code
      delta >>= 20;  // Look +- 1MB from the frame (UNSOUND). We need a better way to do this
      if(delta == 0 || delta == -1) {  // Catch 0 or 1
        CCURED_FAIL(FAIL_STORE_STACK_ADDRESS  CCURED_FAIL_EXTRA_ARGS);
      }
    #else
      // some code which should have the same performance effect
      // as the above code where the 'if' condition is always false
      delta <<= 4;
      if (delta == 1 || delta == -1) { // never true (does the compiler know this?)
        CCURED_FAIL(FAIL_STORE_STACK_ADDRESS  CCURED_FAIL_EXTRA_ARGS);
      }
    #endif
  }
}

/********************************************************************
 **
 **  FUNCTION DESCRIPTORS
 **
 **  Deprecated (?) Try to use the RTTI pointer kind instead!
 **
 ****************************************************************** */
// This is the type of a function descriptor
struct __functionDescriptor {
  unsigned int _len ; // Always 0
  void (* _pfun)() ; // Pointer to a function
  unsigned int _nrargs ; // The number of arguments
};

// And a macro to initialize the function descriptor
#define DEFINE_CCURED_FUNCTIONDESCRIPTOR(f, nrargs) \
 struct __functionDescriptor f ## __descriptor={ 0, (void (*)())(f), (nrargs)};

// ---------------- usage checks for b,p fat pointers ---------------
// given a b,p fat pointer to a function, and 'n' the number of arguments
// actually passed, verify that b,p is actually a function pointer, and that
// 'n' is enough arguments
#define CHECK_FUNCTIONPOINTER(p,b,n) \
        CCURED_CHECK(__CHECK_FUNCTIONPOINTER(p, b, n  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_FUNCTIONPOINTER(void *p, void *b, int nrActualArgs
                             CCURED_FAIL_EXTRA_PARAMS)
{
  // non-pointer check
  if (!b) {
    NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
    return; // If we do not stop
  }

  // the check below allows 'nrActualArgs' to exceed the number of args
  // the function accepts, because the usual calling convention will
  // harmlessly ignore extra arguments (and our type system has no notion
  // of obligated use)
  if( ((U32*)b)[-1] != 0              ||      // length field is 0 for fn pointers
      ((U32*)b)[ 0] != (uintptr_t)p   ||      // first word is actual code pointer
      ((U32*)b)[+1] > (U32)nrActualArgs ) {   // second word is # args fn requires
    CCURED_FAIL(FAIL_FUNCTIONPOINTER  CCURED_FAIL_EXTRA_ARGS);
  }
}

/***************************************************************
 **
 **   BOUNDS CHECKING
 **
 ************************************************************** */

/* Use this instead of ccured_fail. */
MAYBE_NORETURN
void ubound_or_non_pointer_fail(void *p, void *bend,
                                CCURED_FAIL_VERBOSE_PARAMS);
MAYBE_NORETURN
void ubound_or_non_pointer_fail_terse(void *p, void *bend);
#ifdef CCURED_FAIL_IS_TERSE
 #define UBOUND_OR_NON_POINTER_FAIL ubound_or_non_pointer_fail_terse
#else
 #define UBOUND_OR_NON_POINTER_FAIL ubound_or_non_pointer_fail
#endif

/* Use this instead of ccured_fail. */
MAYBE_NORETURN
void lbound_or_ubound_fail(void *base, void *p,
                           CCURED_FAIL_VERBOSE_PARAMS);
void lbound_or_ubound_fail_terse(void *base, void *p);
#ifdef CCURED_FAIL_IS_TERSE
 #define LBOUND_OR_UBOUND_FAIL lbound_or_ubound_fail_terse
#else
 #define LBOUND_OR_UBOUND_FAIL lbound_or_ubound_fail
#endif

// bend - either NULL or the byte past the accessible area
// p    - the pointer being tested.
// plen - the sizeof the type being accessed
// foraccess - true if this check is done for a memory access, false if
//             it is for a cast or address-of. In the latter case allow
//             the NULL pointer to sneak by
// noint - if true then bend is known to be non NULL

/*** FSEQ Invariants *** */
// bend - is either NULL or else the byte past an accessible area
// p    - If bend is not NULL then p >= beginning of the home area

#define CHECK_FSEQ2SAFE(bend,p,srcl,plen,foraccess,noint) \
      CCURED_CHECK(__CHECK_FSEQ2SAFE(bend,p,srcl,plen,foraccess,noint  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_FSEQ2SAFE(void *bend, void *p,
                       unsigned int src_element_len,
                       unsigned int destlen,
                       int foraccess,
                       int nonnull __UNUSED
                       CCURED_FAIL_EXTRA_PARAMS)
{
  // A new check with only two conditionals
  // Note that now we do not allow casting of a non-pointer FSEQ into
  // SAFE, unless this is not an access and the value is NULL
  // Unsatisfying that we need two upper bounds checks
  if(p >= bend) { // ensure p < bend, always fails for bend = 0
    if(destlen == 0 && p == bend) { /* If we try to access an empty struct. */
      return;
    } else if(!foraccess && !p) { // If foraccess, this conditional goes away
      return; // Ok, allow a 0 if not for access
    } else {
      UBOUND_OR_NON_POINTER_FAIL(p, bend CCURED_FAIL_EXTRA_ARGS);
    }
  } else {
#if ! defined(CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE)
    // We know that bend is not zero and bend - p is a multiple of
    // src_element_len.
    // Since p < bend it must be that p <= bend - src_element_len
    if(src_element_len >= destlen) { // This will be optimized in most cases
      return;
    }
#endif
    // bend - p does not underflow because of previous check
    if(((uintptr_t)bend - (uintptr_t)p) < destlen) {
      CCURED_FAIL(FAIL_UBOUND CCURED_FAIL_EXTRA_ARGS);
    }
  }
}

// Check that we create an aligned sequence
#if ! defined(CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE)
#define CHECK_FSEQALIGN(sz,p,bend) \
      CCURED_CHECK(__CHECK_FSEQALIGN(sz,p,bend FILE_AND_LINE))
#else
#define CHECK_FSEQALIGN(sz,p,bend)
#endif

INLINE_STATIC_CHECK
void __CHECK_FSEQALIGN(unsigned int sz,
                       void* p, void *bend
                       CCURED_FAIL_EXTRA_PARAMS) {
  long diff = (long)bend - (long)p;
  if(bend && (diff / sz) * sz != diff) {
    CCURED_FAIL(FAIL_SEQUENCE_ALIGN CCURED_FAIL_EXTRA_ARGS);
  }
}


// Check that we create an aligned sequence
#if ! defined(CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE)
#define CHECK_SEQALIGN(sz,p,base,bend) \
      CCURED_CHECK(__CHECK_SEQALIGN(sz,p,base,bend FILE_AND_LINE))
#else
#define CHECK_SEQALIGN(sz,p,base,bend)
#endif

//Check that a sequence is aligned after doing arithmetic.  We need this if
//sz is not a power of two, to guard against wraparounds.  This is the same
//check that CHECK_SEQALIGN does for casts, but we need this even if
//CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE is defined.
#define CHECK_SEQARITH(sz,p,base,bend) \
      CCURED_CHECK(__CHECK_SEQALIGN(sz,p,base,bend FILE_AND_LINE))

INLINE_STATIC_CHECK
void __CHECK_SEQALIGN(unsigned int sz,
                      void* p, void *base, void *bend CCURED_FAIL_EXTRA_PARAMS) {
  // Take a look at the SEQ2SAFE check to see that we only need that
  // end - p is a multiple of sz
  long diff = (long)bend - (long)p;
  if(bend && (diff / sz) * sz != diff) {
    CCURED_FAIL(FAIL_SEQUENCE_ALIGN CCURED_FAIL_EXTRA_ARGS);
  }
}


// base - if bend is not NULL then the beginning of the home area
// bend - either NULL or the byte past the accessible area
// p    - the pointer being tested.
// plen - the sizeof the type being accessed
// foraccess - true if this check is done for a memory access, false if
//             it is for a cast or address-of. In the latter case allow
//             the NULL pointer to sneak by
// noint - if true then bend is known to be non NULL

#define CHECK_SEQ2SAFE(base,bend,p,srclen,plen,foraccess,noint) \
      CCURED_CHECK(__CHECK_SEQ2SAFE(base,bend,p,srclen,plen,foraccess,noint  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_SEQ2SAFE(void *base, void *bend,
                      void *p,
                      unsigned int src_element_len,
                      unsigned int destlen,
                      int foraccess,
                      int noint
                      CCURED_FAIL_EXTRA_PARAMS) {
  // A new way to check SEQ2SAFE with only 3 conditionals
  // Note that now we do not allow casting of a non-pointer SEQ into
  // SAFE, unless this is not an access and the value is NULL
  uintptr_t pmb = (uintptr_t)p - (uintptr_t)base;

  // We know the bend >= base always, so no overflow here
  uintptr_t emb = (uintptr_t)bend - (uintptr_t)base;

#ifndef OMIT_NULL_CHECK // Unsafe. For experimentation only
  if(!noint && ! bend) { // bend != 0
    if(!foraccess && !p) { // If foraccess=1 this conditional goes away !
      return; // Allow the 0 to go through, if not in a memory access
    } else {
      NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
    }
  }
#endif
  // At this point we know bend <> 0,
  // emb = bend - base is > 0
#if ! defined(CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE)
  // We know that end - p is a multiple of src_element_len
  if(pmb >= emb) {// ensure p - base < end - base
    //This could be either a lbound or a ubound failure
    // We define a separate function because otherwise gcc will not inline this
    LBOUND_OR_UBOUND_FAIL(base, p CCURED_FAIL_EXTRA_ARGS);
  }
  // Now we know that p >= base and p < e, thus p + src_element_len <= e
  if(src_element_len < destlen) { // This is a constant!!
    // We know p < e, so no overflow
    if(((uintptr_t)bend - (uintptr_t)p) < destlen) {
      LBOUND_OR_UBOUND_FAIL(base, p CCURED_FAIL_EXTRA_ARGS);
    }
  }
#else
  if(emb < destlen) { // Ensure bend - base >= destlen
    CCURED_FAIL(FAIL_UBOUND CCURED_FAIL_EXTRA_ARGS);
  }
  // ensure p - base <= bend - base - destlen
  if(pmb > (unsigned int)(emb - destlen)) {
    // This could be either a lbound or a ubound failure
    // We define a separate function because otherwise gcc will not inline this
    LBOUND_OR_UBOUND_FAIL(base, p CCURED_FAIL_EXTRA_ARGS);
  }
#endif
}

/* //Read a string:  Allow access to the terminating NULL */
/* //(also require dest_len=src_len, so we don't have to reason about casts) */
/* #define CHECK_SEQN_READ(base,bend,p,len,noint) \ */
/*       CCURED_CHECK(__CHECK_SEQ2SAFE(base,((unsigned long)bend)+(len),p,len,len,1,noint  FILE_AND_LINE)) */

/* #define CHECK_FSEQN_READ(bend,p,len,noint) \ */
/*       CCURED_CHECK(__CHECK_FSEQ2SAFE(((unsigned long)bend)+(len),p,len,len,1,noint  FILE_AND_LINE)) */

//Write a string:  Allow access to the terminating NUL iff we
// are writing 0
//(we also require dest_len=src_len, so we don't have to reason about casts)
#define CHECK_SEQN_WRITE(base,bend,p,len,noint,isnul) \
      CCURED_CHECK(__CHECK_SEQN_WRITE(base,bend,p,len,noint, isnul  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_SEQN_WRITE(void *base, void *bend,
                        void *p,
                        unsigned int len,
                        int noint,
                        int isnul  // true only iff we are writing a 0.
                      CCURED_FAIL_EXTRA_PARAMS)
{
  // It's okay to write a 0 when p == bend.
  // But p==bend could also be caused by p == NULL, so check for that.
  if (isnul
      && p == bend
      && (noint || bend)) {
    return;
  }
  __CHECK_SEQ2SAFE(base,bend,p,
                   len,len,  //src_len = dest_len
                   1, // foraccess = 1, since this is a write.
                   noint CCURED_FAIL_EXTRA_ARGS);
}

#define CHECK_FSEQN_WRITE(bend,p,len,noint,isnul) \
      CCURED_CHECK(__CHECK_FSEQN_WRITE(bend,p,len,noint, isnul  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_FSEQN_WRITE(void *bend,
                         void *p,
                         unsigned int len,
                         int noint,
                         int isnul
                      CCURED_FAIL_EXTRA_PARAMS)
{
  // It's okay to write a 0 when p == bend.
  // But p==bend could also be caused by p == NULL, so check for that.
  if (isnul
      && p == bend
      && (noint || bend)) {
    return;
  }
  __CHECK_FSEQ2SAFE(bend,p,
                    len,len,  //src_len = dest_len
                    1, // foraccess = 1, since this is a write.
                    noint CCURED_FAIL_EXTRA_ARGS);
}

//A write to the an address that has type __STRING.
//This is safe if *p <> 0 (i.e. length is >=1), or the new value == 0
//Note: only works for char*.
#define CHECK_STRING_WRITE(p,isnul) \
      CCURED_CHECK(__CHECK_STRING_WRITE(p,isnul  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_STRING_WRITE(void *p,
                          int isnul
                          CCURED_FAIL_EXTRA_PARAMS)
{
  if (!p) {
    NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
  }
  if(!isnul
     && (*((char*)p) == 0)) {
    CCURED_FAIL(FAIL_UBOUND CCURED_FAIL_EXTRA_ARGS);
  }
}


// like CHECK_SAFE2SEQ except we're given the length of the accessible
// area in words, instead of a pointer to just beyond that area
// We know that the home area is valid (we tested that when we fetched the length)
// And we also know this is for an access.
#define CHECK_BOUNDS_LEN(base,bwords,p,srcl,plen) \
      CCURED_CHECK(__CHECK_BOUNDS_LEN(base,bwords,p,srcl,plen  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_BOUNDS_LEN(void *base,
                        unsigned int bwords,
                        void *p,
                        unsigned int src_element_len,
                        unsigned int plen  CCURED_FAIL_EXTRA_PARAMS)
{
  __CHECK_SEQ2SAFE(base, (char*)base + (bwords << CC_LOG_BYTES_PER_WORD),      // compute end
                   p, src_element_len,
                   plen, 1, 1  CCURED_FAIL_EXTRA_ARGS);
}


// ---------------- queries on b,p fat pointers -----------------
// given a b,p fat pointer that's going to be dereferenced, retrieve
// the length field; the length is the number of platform (32-bit or
// 64-bit) words the program is allowed to read/write
#define CHECK_FETCHLENGTH(p,b,noint) \
      __CHECK_FETCHLENGTH(p,b,noint  FILE_AND_LINE)
INLINE_STATIC_CHECK
unsigned int __CHECK_FETCHLENGTH(void *p, void *b,
                                 int noint CCURED_FAIL_EXTRA_PARAMS)
{
  // if the 'b' field is null, we fail
  if (!noint && !b) {
    NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
    return 0; // If we do not stop
  }

  // length is stored just before the first word of user-accessible area
  return (unsigned int)(* (((U32*)b) - 1));
}

// given a b,p fat pointer, return a pointer to the word just beyond the
// last one the user is allowed to read/write
#define CHECK_FETCH_WILD_END(p,b,noint) \
      __CHECK_FETCH_WILD_END(p,b,noint  FILE_AND_LINE)
INLINE_STATIC_CHECK
void * __CHECK_FETCH_WILD_END(void *p, void *b,
                              int noint CCURED_FAIL_EXTRA_PARAMS)
{
  unsigned int len = __CHECK_FETCHLENGTH(p, b, noint  CCURED_FAIL_EXTRA_ARGS);
  return (void*)((char*)b + (len << CC_LOG_BYTES_PER_WORD));
}

#define CHECK_FETCH_INDEX_END(p,b,noint) \
      __CHECK_FETCH_INDEX_END(p,b,noint FILE_AND_LINE)
INLINE_STATIC_CHECK
void * __CHECK_FETCH_INDEX_END(void *p, void *b,
                               int noint CCURED_FAIL_EXTRA_PARAMS)
{
  unsigned int len = __CHECK_FETCHLENGTH(p, b, noint  CCURED_FAIL_EXTRA_ARGS);
  return (void*)((char*)b + (len << CC_LOG_BYTES_PER_WORD));
}

// Check that we create an aligned sequence
#if ! defined(CCURED_ALLOW_PARTIAL_ELEMENTS_IN_SEQUENCE)
#define CHECK_INDEXALIGN(sz,p,base) \
      CCURED_CHECK(__CHECK_INDEXALIGN(sz,p,base FILE_AND_LINE))
#else
#define CHECK_INDEXALIGN(sz,p,base)
#endif

INLINE_STATIC_CHECK
void __CHECK_INDEXALIGN(unsigned int sz,
                        void* p, void *base CCURED_FAIL_EXTRA_PARAMS) {
  if(base) {
    unsigned int nrWords =
      __CHECK_FETCHLENGTH(p, base, 1  CCURED_FAIL_EXTRA_ARGS);
    long diff = (long)base + (nrWords << CC_LOG_BYTES_PER_WORD) - (long)p;
    if((diff / sz) * sz != diff) {
      CCURED_FAIL(FAIL_SEQUENCE_ALIGN CCURED_FAIL_EXTRA_ARGS);
    }
  }
}




// Check unsigned >=. Used by the optimized for some bounds checks
#define CHECK_GEU(e1,e2) CCURED_CHECK(__CHECK_GEU(e1,e2  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_GEU(unsigned long e1, unsigned long e2  CCURED_FAIL_EXTRA_PARAMS)
{
  if(! (e1 >= e2)) {
    CCURED_FAIL(FAIL_UBOUND  CCURED_FAIL_EXTRA_ARGS);
  }
}

// ----------------------- misc? ------------------------
// checks associated with casting a seq to an fseq
#define CHECK_SEQ2FSEQ(b,e,p) CCURED_CHECK(__CHECK_SEQ2FSEQ(b, e, p  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_SEQ2FSEQ(void *b, void *e, void *p CCURED_FAIL_EXTRA_PARAMS)
{
// Check the lower bound
//   base - pointer to the first byte the user is allowed to read/write
//   p    - pointer the user is using to read/write
  if (p < b) {
    CCURED_FAIL(FAIL_LBOUND  CCURED_FAIL_EXTRA_ARGS);
  } else {
    // ok
  }
}

// verify that 'x' is nonnegative
#define CHECK_POSITIVE(x) CCURED_CHECK(__CHECK_POSITIVE(x  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_POSITIVE(int x  CCURED_FAIL_EXTRA_PARAMS)
{
  if (x < 0) {
    CCURED_FAIL(FAIL_DECR_FSEQ  CCURED_FAIL_EXTRA_ARGS);
  }
}

// verify that computing 'p+x' does not overflow
#define CHECK_FSEQARITH(p, plen, p_x, bend, checkAlign) \
      CCURED_CHECK(__CHECK_FSEQARITH(p, plen, p_x, bend, checkAlign FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_FSEQARITH(void *p,
                       unsigned int plen,  //element size
                       void *p_x,
                       void *bend,
                       int checkAlign
                       CCURED_FAIL_EXTRA_PARAMS)
{
  if ((uintptr_t)p_x < (uintptr_t)p) {
    CCURED_FAIL(FAIL_DECR_FSEQ  CCURED_FAIL_EXTRA_ARGS);
  }
  //Even if p_x > p, we still could have wrapped around.  Recheck the alignment
  if (checkAlign) {  //compile-time constant
    __CHECK_FSEQALIGN(plen,p_x,bend  CCURED_FAIL_EXTRA_ARGS);
  }
}

// A combination of FSEQARITH and FSEQ2SAFE
//
//
#define CHECK_FSEQARITH2SAFE(p,bend,ppi,srclen,plen,foraccess,noint,checkAlign) \
      CCURED_CHECK(__CHECK_FSEQARITH2SAFE(p,bend,ppi,srclen,plen,foraccess,noint,checkAlign  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_FSEQARITH2SAFE(void *p, void *bend,
                            void *ppi, /* p + i */
                            unsigned int src_element_len,
                            unsigned int plen,
                            int foraccess,
                            int noint,
                            int checkAlign
                            CCURED_FAIL_EXTRA_PARAMS) {
  __CHECK_FSEQARITH(p, plen, ppi, bend, checkAlign  CCURED_FAIL_EXTRA_ARGS);
  __CHECK_FSEQ2SAFE(bend, ppi, src_element_len, plen,
                    foraccess, noint CCURED_FAIL_EXTRA_ARGS);
}

// Called for a conversion of SAFE to FSEQ or SEQ. We pass the SAFE
// pointer 'p' and the tentative end ('p+1'). We must check
// whether 'p' is zero or not.
#define CHECK_SAFE_END(p, end) __CHECK_SAFE_END(p, end  FILE_AND_LINE)
INLINE_STATIC_CHECK
void* __CHECK_SAFE_END(void *p, void *end  CCURED_FAIL_EXTRA_PARAMS)
{
  return p ? end : (void*)0;
}


// we can turn off the null check to improve performance;
// sm: for reasons still unclear to me, George wants to explicitly check,
// so this remains commented-out..
// #define OMIT_NULL_CHECK
// George: sometimes the check is used on a pointer that is no going to be
// dereferenced:
//    BIG_STRUCT * p = 0;
//    int * x = & (p->farField); // here we much check if p is NULL
//                               // of else we can manufacture any pointer
//                               // that way
#define CHECK_NULL(p) CCURED_CHECK(__CHECK_NULL(p  FILE_AND_LINE))
#ifdef OMIT_NULL_CHECK
  #define __CHECK_NULL(p)
#else
  INLINE_STATIC_CHECK
  void __CHECK_NULL(void *p  CCURED_FAIL_EXTRA_PARAMS)
  {
    if (!p) {
      CCURED_FAIL(FAIL_NULL  CCURED_FAIL_EXTRA_ARGS);
    }
  }
#endif

#define LOG_SCALAR(p,id) __LOG_SCALAR(p, id)
INLINE_STATIC_CHECK
void __LOG_SCALAR(unsigned long p, int id)
{
  __logScalar(p, id);
}

// --------------------- strings -------------------
// given a string pointer, return a pointer to the 0 byte which
// terminates it; the RWSTRING-qualified pointers are *not* allowed
// to overwrite this 0 byte
// Except if we are not usings strings. In that case the NULL is part of the
// area. However, in that case this function will never be called !
#if defined(CCURED_USE_STRINGS)
#define CHECK_FETCHNULLTERMEND1(p) __CHECK_FETCHNULLTERMEND1(p  FILE_AND_LINE)
INLINE_STATIC_CHECK void * __CHECK_FETCHNULLTERMEND1(char *p CCURED_FAIL_EXTRA_PARAMS)
{
  unsigned int len;
  if (!p) {
    CCURED_FAIL(FAIL_NULLSTRING  CCURED_FAIL_EXTRA_ARGS);
    return NULL; // If we do not stop
  }


  len = strlen(p);
  return p + len;
}

#define CHECK_FETCHNULLTERMEND2(p) __CHECK_FETCHNULLTERMEND2(p FILE_AND_LINE)
INLINE_STATIC_CHECK void * __CHECK_FETCHNULLTERMEND2(void *p CCURED_FAIL_EXTRA_PARAMS)
{
  short *ps = p;
  if (!ps) {
    CCURED_FAIL(FAIL_NULLSTRING  CCURED_FAIL_EXTRA_ARGS);
    return NULL; // If we do not stop
  }

  while(*ps) { ps ++; }
  return (void*)ps;
}

#define CHECK_FETCHNULLTERMEND4(p) __CHECK_FETCHNULLTERMEND4(p FILE_AND_LINE)
INLINE_STATIC_CHECK void * __CHECK_FETCHNULLTERMEND4(void *p CCURED_FAIL_EXTRA_PARAMS)
{
  long *ps = p;
  if (!ps) {
    CCURED_FAIL(FAIL_NULLSTRING  CCURED_FAIL_EXTRA_ARGS);
    return NULL; // If we do not stop
  }

  while(*ps) { ps ++; }
  return (void*)ps;
}

#define CHECK_FETCHNULLTERMEND_GEN(p,sz) __CHECK_FETCHNULLTERMEND_GEN(p, sz FILE_AND_LINE)
INLINE_STATIC_CHECK void * __CHECK_FETCHNULLTERMEND_GEN(void *p, int sz CCURED_FAIL_EXTRA_PARAMS)
{
  char *ps = (char*)p;
  if (!ps) {
    CCURED_FAIL(FAIL_NULLSTRING  CCURED_FAIL_EXTRA_ARGS);
    return NULL; // If we do not stop
  }

  while(1) {
    // See if the bytes from ps to ps + sz - 1 are all zero
    char *t;
    for(t=ps;t<ps+sz;t++) {
      if(*t != 0) break;
    }
    if(t == ps+sz) {
      // All zero, we have found our null termination. We return the pointer
      // to the null object
      return ps;
    }
    ps = ps + sz;
  }
}

#endif // CCURED_USE_STRINGS

// verify that we are casting correctly
/* The RTTI is the address of an entry in an array of integers. Each integer
 * is the offset of the parent's entry from the current one, or zero for
 * void (the root of the class hierarchy) */

struct RTTI_ELEMENT {
  int index; /* The index within the RTTI_ARRAY of this entry */
  char *name; /* The name of the type */
  int parentDelta; /* The difference between the index of the parent's entry
                      and the current entry. This is the only field that
                      matters */
};

//helper for __CHECK_RTTICAST. Also used for CCURED_HASUNIONTAG
//Note: the caller should check whether the pointer is NULL.  If so, don't
// call this, since it's safe to cast it to any pointer type.
static
int __CHECK_HASRTTITYPE(struct RTTI_ELEMENT *srtti,
                        struct RTTI_ELEMENT *drtti)
{
  if (srtti == drtti) {
    return 1;
  }
  if(! srtti || ! srtti->parentDelta) {
    return 0;
  }
  return __CHECK_HASRTTITYPE(srtti + srtti->parentDelta, drtti);
}

//Three different error messages for the same check:
//  (rtti, vararg, unions)
#define CHECK_RTTICAST(srtti, drtti) \
      CCURED_CHECK(__CHECK_RTTICAST(srtti, drtti, FAIL_RTTICAST \
                                    FILE_AND_LINE))
#define CHECK_VACAST(srtti, drtti) \
      CCURED_CHECK(__CHECK_RTTICAST(srtti, drtti, FAIL_VA_BADTYPE \
                                    FILE_AND_LINE))
#define CHECK_RTTIUNIONTAG(srtti, drtti) \
      CCURED_CHECK(__CHECK_RTTICAST(srtti, drtti, FAIL_UNIONTAG \
                                    FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_RTTICAST(struct RTTI_ELEMENT *srtti,
                      struct RTTI_ELEMENT *drtti,
                      int msgId
                      CCURED_FAIL_EXTRA_PARAMS)
{
  if (!__CHECK_HASRTTITYPE(srtti, drtti)) {
    CCURED_FAIL(msgId  CCURED_FAIL_EXTRA_ARGS);
  }
}


// context: box.ml
//   This function is used by box.ml when casting from wild or index to
//   String.  I think we should disallow mixing of wild and string, but
//   that's somewhat of a different issue.  In any event, in box.ml, the
//   expected semantics of this are:
//     Given a b,p pointer, verify that p points to one of the bytes
//     in the memory area denoted by b (failing with STRINGBOUND
//     instead of {U,L}BOUND on failure..).
// context: ccuredlib.c
//   I have now removed all uses of this function from ccuredlib.c, preferring
//   instead fatp_verify_nul, which has simpler semantics and usage.
#define CHECK_STRINGMAX(p,b) __CHECK_STRINGMAX(p, b  FILE_AND_LINE)
INLINE_STATIC_CHECK
unsigned int __CHECK_STRINGMAX(void *p, void* b  CCURED_FAIL_EXTRA_PARAMS)
{
  int nrWords;
  int max;
  //  U32 *addr = (U32*)p;
  if(! b) {
    NON_POINTER_FAIL((unsigned long)p  CCURED_FAIL_EXTRA_ARGS);
    return 0; // If we do not stop
  }
#ifndef NO_CHECKS
  if(p < b) {
    CCURED_FAIL(FAIL_LBOUND  CCURED_FAIL_EXTRA_ARGS);
  }
#endif /* NO_CHECKS */
  nrWords = *(((U32*)b) - 1);
  max     =  ((char*)b - (char*)p) + (nrWords << CC_LOG_BYTES_PER_WORD);
#ifndef NO_CHECKS
  if(max <= 0) {
    CCURED_FAIL(FAIL_STRINGBOUND  CCURED_FAIL_EXTRA_ARGS);
  }
#endif /* NO_CHECKS */
  return (unsigned int)max;
}

/* Check the tag of a discriminated union */
#define CHECK_UNIONTAG(t) __CHECK_UNIONTAG(t FILE_AND_LINE)
INLINE_STATIC_CHECK
void __CHECK_UNIONTAG(int tag CCURED_FAIL_EXTRA_PARAMS) {
  if(! tag) {
    CCURED_FAIL(FAIL_UNIONTAG CCURED_FAIL_EXTRA_ARGS);
  }
}

/* We are writing to part of a tagged union field.
   If this field is currently selected, do nothing.
   Otherwise, zero the whole union before setting the new tag or data values.*/
INLINE_STATIC_CHECK
void CHECK_INITUNIONFIELD(int selected, void* p, unsigned int size) {
  if (!selected) {
    __builtin_memset(p, 0, size);
  }
}

/************** TAG MANIPULATION ************** */

/* We have one tag bit per aligned data word. The tag bit value is 1 if the
 * data word contains a _b component of a WILD pointer (i.e. the second word
 * of a WILD pointer) and 0 if it contains an integer or the _p component of
 * a WILD pointer. A very important invariant is that a tag bit sequence
 * "01" denotes two data words that contain a WILD pointer (with the fields
 * _p and _b in that order). To maintain this invariant we have to write the
 * bits "01" whenever we write a pointer and we have to clear the tag bit
 * for word "w" when we write an integer in the word "w". Note that this
 * means that we might be overwriting the _p field of a stored pointer and
 * we would not notice. This might mask some programming errors but it is
 * not unsound because the _p field will be checked against the _b field
 * next time it is used. All we need for soundness is to know that the _b
 * fields are intact. */
/* The way we write the tags is to first clear the tags for all the words we
 * are writing. Then, if some of the words contain pointers (such as when
 * writing structures containing pointers and non-pointers) we just set
 * those particular bits. An exception is made when we write just pointers.*/
/* Bits are counted from 0 starting with the least-significant bit in the
 * first tag word. The tag words (4 or 8 bytes each) are written in little-endian
 * notation. So, if I have a block of memory containing one fat pointer, with
 * a valid base and ptr, it looks like: */
/*
 *  <-- word -><-- word -><-- word -><-------------- word -------------------->
 *  +---------+----------+----------+-----------------------------------------+
 *  | size: 2 |    ptr   |   base   | 0000 0000 0000 0000 0000 0000 0000 0010 |
 *  +---------+----------+----------+-----------------------------------------+
 *                                                                         ^^
 */
/* The last "1" and "0" are the "01" combination referred to above. */

// Note:  In this section, several chunks of code are controlled by the NO_TAGS
// #define.  The purpose of NO_TAGS is to measure the performance impact of
// tag manipulations -- the system is unsound when NO_TAGS is defined.

// The number of tags bits per data word
#define TAGBITS          1
#define TAGBITSMASK      ((1 << TAGBITS) - 1)                       // 1

// How many tags fit into a  word                                      32-bit, 64-bit
#define TAGSPERWORD_LOG  (CC_LOG_BITS_PER_WORD - TAGBITS + 1)       // 5     , 6
#define TAGSPERWORD      (1 << TAGSPERWORD_LOG)                     // 0x20  , 0x40

// The tags for a fat pointer
#define WILDPTR_TAG       2  // a 0 followed by a 1
#define WILDPTR_MASK      (TAGBITSMASK | (TAGBITSMASK << TAGBITS))  // 3


typedef struct tagAddr
{
  U32 *word;                  /* This is the address of the word in which
                               * the tag lives */
  int bit;                    /* This is the index of the bit where the tag
                               * starts. 0 means the LSB. Will always be
                               * less or equal WORDSIZE - TAGBITS (at least one
                               * tag still fits)  */
} TAGADDR;


// given a TAGADDR, retrieve either a 0 or 1
#define READ_TAG(addr) ((*((addr).word) >> (addr).bit) & 1)


// first, we give definitions for the tag functions in the normal
// case where tags are in effect
#ifndef NO_TAGS

// given the number of data words, return the number of tag words that
// must be allocated to track the types in the data
INLINE_STATIC_CHECK
int CHECK_NRTAGWORDS(unsigned int nrDataWords)
{
  return (nrDataWords + TAGSPERWORD - 1) >> TAGSPERWORD_LOG;
}


/* Compute the address of the tag for a given word. Both the base and p must
 * be aligned on word boundary */
#define CHECK_FETCHTAGADDR(b,bw,p) __CHECK_FETCHTAGADDR(b,bw,p FILE_AND_LINE)
INLINE_STATIC_CHECK
TAGADDR __CHECK_FETCHTAGADDR(void *base,            // Base
                             unsigned int bwords,   // words in area
                             void *p                // the pointer
                             CCURED_FAIL_EXTRA_PARAMS)
{
  TAGADDR res;
  int wrdIdx    = ((char*)p - (char*)base) >> CC_LOG_BYTES_PER_WORD;
  res.word      = (U32*)base + bwords + (wrdIdx >> TAGSPERWORD_LOG);
  res.bit       = TAGBITS * (wrdIdx & (TAGSPERWORD - 1));
  return res;
}

// read the tag bit for the given word; if 'p' is not aligned, we get the
// tag for the word whose interior it's pointing at (as if we aligned it first)
INLINE_STATIC_CHECK
unsigned CHECK_FETCHTAGBIT(void *base,            // start of memory area.
                                                  // Always aligned
                           unsigned int bwords,   /* # of words in the memory
                                                   * area */
                           void *p)               /* pointer to word we're
                                                   * interested in  */
{
  // composition of READ_TAG and CHECK_FETCHTAGADDR, above
  int wrdIdx    = ((char*)p - (char*)base) >> CC_LOG_BYTES_PER_WORD;
  U32 *word     = (U32*)base + bwords + (wrdIdx >> TAGSPERWORD_LOG);
  int bit       = TAGBITS * (wrdIdx & (TAGSPERWORD - 1));
  return (*word >> bit) & 1;
}


/* Compute the number of bits that correspond to the number of words covered
 * by the range given. nextAddr is 1 past the last address in the range */
INLINE_STATIC_CHECK
int CHECK_NRTAGBITS(char* startAddr, char* nextAddr)
{
  int startWord = ((intptr_t)startAddr) >> CC_LOG_BYTES_PER_WORD;   // Round down
  int nextWord  = (((intptr_t)nextAddr + (CC_BYTES_PER_WORD - 1))
		   >> CC_LOG_BYTES_PER_WORD);                       // Round up
  return (nextWord - startWord) * TAGBITS;
}

/* Zero out the tags for a written memory area. Later we'll come and fix the
 * tags for the words that contain pointers. */
INLINE_STATIC_CHECK
void CHECK_ZEROTAGS(void *base,  /* The base of the tagged area */
                    unsigned int nrbwords, // Number of data words in the area
                    void *where, /* The address of the first word whose tag
                                    must be cleared */
                    unsigned int size /* The size in bytes of the memory
                                       * range for which we must clear the
                                       * tag */
                    )
{
  char *wherec = (char*)where;


  // Adjust for the offset. Not necessary anymore.
  // wherec += offset;
  // size  -= offset;
//  if((void*)wherec > base) { // Adjust for the preceeding word
//    wherec -= 4;
//    size  += 4;
//  }

  {
    TAGADDR stag    = CHECK_FETCHTAGADDR(base, nrbwords, wherec);
    int nrBits      = CHECK_NRTAGBITS(wherec, wherec + size);

    if(stag.bit > 0) { // First tag word is only partially written
      if(stag.bit + nrBits < CC_BITS_PER_WORD) { // Don't zero to the end
        *(stag.word++) &= (~ (((1 << nrBits) - 1) << stag.bit));
        nrBits = 0;
      } else { // First tag word is written to the end
        *(stag.word++) &= (~ ((0 - 1) << stag.bit));
        nrBits -= (CC_BITS_PER_WORD - stag.bit);
      }
    }
    while(nrBits >= CC_BITS_PER_WORD) {
      *(stag.word++) = (U32)0;
      nrBits -= CC_BITS_PER_WORD;
    }
    if(nrBits > 0) { // Some leftover in the last word
      *stag.word &= (~ ((1 << nrBits) - 1));
    }
  }
}

/* Copy the tags going forward. Call this in conjuction with any memory
 * copy. The psrc and pdst and size should be _exactly_ as passed to memcpy.
 * NOTE THAT THIS MIGHT NOT WORK PROPERLY IN CASE OF OVERLAPPING AREAS
 * (since the bits are read first and then written as a block. To model
 * overlapping correctly we need to copy one tag at a time.) Note that this
 * is used in a somewhat unusual way in realloc.  */
void CHECK_COPYTAGSFORW(void *bsrc, /* base of src */
                        unsigned int lensrc, /* len of src (in words) */
                        char* psrc, /* pointer of src */
                        void *bdst, /* base of dest */
                        unsigned int lendst, /* words in dest*/
                        char* pdst, /* pointer of dest */
                        unsigned int size /* Size in bytes
                                           * of the memory
                                           * being copied */);

/* Copy the tags going backward. The psrc, pdst and size arguments should be
 * exactly as passed to memcpy. The copying is done going backwards from the
 * last word. NOTE THAT THIS MIGHT NOT WORK PROPERLY IN CASE OF OVERLAPPING
 * AREAS (since the bits are read first and then written as a block. To
 * model overlapping correctly we need to copy one tag at a time.) Note that
 * this is used in a somewhat unusual way in realloc.  */
void CHECK_COPYTAGSBACK(void *bsrc, /* base of src */
                        unsigned int lensrc, /* len of src (in words) */
                        char* psrc, /* pointer of src */
                        void *bdst, /* base of dest */
                        unsigned int lendst, /* words in dest*/
                        char* pdst, /* pointer of dest */
                        unsigned int size);


/* This function is called before a pointer is read from a tagged area. */
#define CHECK_WILDPOINTERREAD(b,n,w) CCURED_CHECK(__CHECK_WILDPOINTERREAD(b,n,w  FILE_AND_LINE))
INLINE_STATIC_CHECK
void __CHECK_WILDPOINTERREAD(void *base, /* The base of the tagged area */
                             unsigned int nrWords, /* No of words in the
                                                    * area*/
                             void *where /* The address in the area from
                                          * where the pointer will be read */
                             CCURED_FAIL_EXTRA_PARAMS)
{
  // Check only the tag bit for the _b field. This is in the next word
  U32 * where_b = 1 + (U32*)where;
  TAGADDR tag;
  U32 memTag;

  // We do not support unaligned reads of pointers
  if((uintptr_t)where_b & CC_ALIGNED_PTR_MASK) {
    CCURED_FAIL(FAIL_UNALIGNED  CCURED_FAIL_EXTRA_ARGS);
  }

  tag = CHECK_FETCHTAGADDR(base, nrWords, (void*)where_b);


  // Read the tag for the _b word to be read
  memTag  = (* tag.word) >> tag.bit;
  if(memTag & TAGBITSMASK) { // If the tag for the _b field is 1, Ok
    return;
  }
  // Houston, we have a problem! Somebody messed with our pointers.

  // We give it one more chance. Maybe the word that would be read for base
  // is 0, in which case everything is still safe. This will handle the case
  // when an area has been initialized with 0 and the tags are all 0
  if(* where_b == (U32)0) {
    return;
  }
  CCURED_FAIL(FAIL_READINVALIDPTR CCURED_FAIL_EXTRA_ARGS);
}


/* We are writing (changing the value of) a fat pointer
 * which, itself, lives inside a tagged block of memory */
// this first version does not check for writing stack pointers
#define CHECK_WILDPOINTERWRITE_NOSTACKCHECK(b,n,w,x,y) \
        __CHECK_WILDPOINTERWRITE_NOSTACKCHECK(b,n,w,x,y  FILE_AND_LINE)
INLINE_STATIC_CHECK
void __CHECK_WILDPOINTERWRITE_NOSTACKCHECK(
  // the base of the block in which the fat pointer lives
  // (the byte just after the length)
  void *base,

  // the number of words in the block containing
  // the fat pointer
  unsigned int nrWords,

  // the address of the fat pointer itself; this will
  // point to the '_p' field, since it is first
  void **where,

  // 'whatbase' is the value we want the fat pointer's
  // '_b' (base) field to become
  void *whatbase,

  // and this is what we want its '_p' field to become
  void *whatp

  CCURED_FAIL_EXTRA_PARAMS)
{
  // compute bit address of tag bit
  TAGADDR tag  = CHECK_FETCHTAGADDR(base, nrWords, where);

#ifndef NO_CHECKS
  // sm: maybe this alignment check should go first?
  if((uintptr_t)where & CC_ALIGNED_PTR_MASK) {
    CCURED_FAIL(FAIL_UNALIGNED  CCURED_FAIL_EXTRA_ARGS);
  }
#endif /* NO_CHECKS */

  // mask out the existing tag bits, and OR in the "10"
  // for a valid fat pointer
  *tag.word = (* tag.word & (~ (WILDPTR_MASK << tag.bit))) |
                  (WILDPTR_TAG << tag.bit);

  #if 0     // testing (forgot gdb was showing me values in decimal!)
  {
    U32 data = *(tag.word);                // read tags word
    data &= ~(WILDPTR_MASK << tag.bit);     // strip existing tag pair
    data |= WILDPTR_TAG << tag.bit;         // add "01" bitpattern
    *(tag.word) = data;                    // write it back
  }
  #endif // 0

  if (tag.bit < CC_BITS_PER_WORD - TAGBITS) {
    // Both fit in the same word
  }
  else {
    // sm: I'm able to verify that the following lines do have
    // a good effect; scott/arraytags will fail if these lines
    // are removed

    // the tag bits straddle a word boundary, so the second half didn't
    // actually get written above (left-shift just discards
    // extra bits); so we now write that last half into the
    // next tag word
    tag.word ++;
    *tag.word = (*tag.word & (~ (WILDPTR_MASK >> TAGBITS))) |
                   (WILDPTR_TAG >> TAGBITS);
  }
}


// same as the above check, but also check for writing stack pointers
#define CHECK_WILDPOINTERWRITE(b,n,w,x,y,f) __CHECK_WILDPOINTERWRITE(b,n,w,x,y,f  FILE_AND_LINE)
INLINE_STATIC_CHECK
void __CHECK_WILDPOINTERWRITE(
  void *base, unsigned int nrWords, void **where,
  void *whatbase, void *whatp, void *pTopOfFrame
  CCURED_FAIL_EXTRA_PARAMS)
{
  __CHECK_WILDPOINTERWRITE_NOSTACKCHECK(base, nrWords, where, whatbase,
                                       whatp  CCURED_FAIL_EXTRA_ARGS);

  // this is the stack pointer check
  if (whatbase) {
    CHECK_STOREPTR(where, whatp, pTopOfFrame);
  }
}


// now, we give stub definitions for when tags are disabled
#else     // NO_TAGS
  // for query functions, sometimes we can answer sensibly, but sometimes
  // the query is invalid
  #define CHECK_NRTAGWORDS(datawords) 0
  #define CHECK_FETCHTAGADDR(b,bw,p) ERROR_NO_TAGS_IS_DEFINED
  #define CHECK_FETCHTAGBIT(b,bw,p) ERROR_NO_TAGS_IS_DEFINED
  #define CHECK_NRTAGBITS(start, next) 0

  // for tag manipulations, make them no-ops
  #define CHECK_ZEROTAGS(b,bw,w,s/*,o*/)
  #define CHECK_COPYTAGSFORW(bs,ls,ps,bd,ld,pd,sz)
  #define CHECK_COPYTAGSBACK(bs,ls,ps,bd,ld,pd,sz)
  #define CHECK_WILDPOINTERREAD(b,n,w)

  // even without tags there's a small check to perform on pointer write
  #define CHECK_WILDPOINTERWRITE(b,n,w,x,y,f) \
                        __CHECK_WILDPOINTERWRITE(b,n,w,x,y,f  FILE_AND_LINE)
  INLINE_STATIC_CHECK
  void __CHECK_WILDPOINTERWRITE(
    // see above for interpretation of these fields
    void *base, unsigned int nrWords, void **where,
    void *whatbase, void *whatp, void *pTopOfFrame
    CCURED_FAIL_EXTRA_PARAMS)
  {
    if (whatbase) {
      CHECK_STOREPTR(where, whatp, pTopOfFrame);
    }
  }
#endif    // NO_TAGS


// sm: I need this for the _setjmp_w macro; it does the same thing
// as fatp_write_atleast() in ccuredlib.c
#define CHECK_WILDP_WRITE_ATLEAST(p, b, n) \
        __CHECK_WILDP_WRITE_ATLEAST(p, b, n  FILE_AND_LINE)
INLINE_STATIC_CHECK
void __CHECK_WILDP_WRITE_ATLEAST(
  void *p,    // pointer to first byte to write
  void *b,    // base of the home area to be written
  int n       // number of bytes to write
  CCURED_FAIL_EXTRA_PARAMS)
{
  // words in the home area
  unsigned nwords = CHECK_FETCHLENGTH(p, b, 0);

#ifndef NO_CHECKS
  if (n < 0) {
    CCURED_FAIL(FAIL_LBOUND CCURED_FAIL_EXTRA_ARGS);
  }
  {
    // bytes available between 'p' and the end
    int nbytes = (int)(nwords << CC_LOG_BYTES_PER_WORD) - ((char*)p - (char*)b);

    if (n > nbytes)
      CCURED_FAIL(FAIL_UBOUND CCURED_FAIL_EXTRA_ARGS);
  }
#endif /* NO_CHECKS */

  CHECK_ZEROTAGS(b, nwords, p, n/*, 0*/);
}


// ---------------- "table" pointers and splay tree access -----------
// sm: this stuff is largely defunct now, mainly because the
// splay tree turned out to be *much* too slow a data structure

/* weimer: our hooks into the splay tree data structure */
#include "splay.h"

// here, 'end' is the last+1 byte
INLINE_STATIC_CHECK
void CHECK_REGISTERAREA(int kind, void *base, void *end)
{
  if (kind == registerTagged || kind == registerSized) {
      end = CHECK_FETCH_WILD_END(base,base,0);
  }
  splayInsertInterval(kind, base, (char*)end - (char*)base);
  //splayPrintTree(&__global_tree[kind]);
  return;
}


// sm: changed this to a macro, so that unregistering works in gcc
// even when optimization is turned off
#define CHECK_UNREGISTERFRAME()                                \
{                                                              \
  char* thisf;                                                 \
  CHECK_GETFRAME(thisf);                                       \
  splayRemoveKindBelow(MR_STACK, registerTagged, thisf);       \
  splayRemoveKindBelow(MR_STACK, registerSized, thisf);        \
  splayRemoveKindBelow(MR_STACK, registerSeq, thisf);          \
}


INLINE_STATIC_CHECK
void * CHECK_FINDHOME(int kind, void *p)
{
  return splayFindHome(kind, p);
}

INLINE_STATIC_CHECK
void * CHECK_FINDHOMEEND(int kind, void *p, void **e)
{
  return splayFindHomeEnd(kind, p, e);
}


// verify there is a nul value between ptr and the end of its buffer;
// typically the context is we're about to pass a char* to libc which
// will interpret it as a nul-terminated string, so we want to make
// sure it will only access (read) bytes within the valid memory area;
// returns 'len'
// (terminology: nul is ASCII 0; null is a pointer value)
#define ccured_verify_nul(p, len)  CCURED_CHECK(__ccured_verify_nul(p, len))
INLINE_STATIC_CHECK void  __ccured_verify_nul(char const *p, int len)
{
  while (len) {
    if (*p == 0) {
      // ok
      return;
    }
    len--;
    p++;
  }

  // didn't find a nul in the accessible area
  CCURED_FAIL(FAIL_STRINGBOUND  FILE_AND_LINE);
}

//matth: put __ptrof here so it can be inlined.  (The versions of __ptrof
//that operate on non-safe arguments are still in ccuredlib.c)

INLINE_STATIC_CHECK
void* __ptrof(void *x) {
  return x;
}

/****** Variable argument ******/
#if defined(_MSVC)
 #define GCC_STDARG_START(last) ((unsigned long)&(last) + \
                                    (((sizeof(last) +  3) >> 2) << 2))
 #define GCC_VARARGS_START()    0
#else
 #if __GNUC__ >= 3
 #define GCC_STDARG_START(last) ({ __builtin_va_list tmp; \
                                   __builtin_stdarg_start(tmp, last);\
                                   (unsigned long)tmp; })
         /* CIL will get rid of the necessary machinery for
          * builtin_varargs_start. So, we must use the __builtin_stdarg_start
          * even in this case  */
 #define GCC_VARARGS_START()    GCC_STDARG_START(0)
 #else
 #define GCC_STDARG_START(last) (unsigned long)__builtin_next_arg(last)
 #define GCC_VARARGS_START()     GCC_STDARG_START(0)
 #endif
#endif
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
