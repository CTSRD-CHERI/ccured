/* See licence and copyright notice at the end of this file */

/* This file is included only before preprocessing a source file in 
 * preparation for CCured (and only if curing is going to take place) */

#define CCURED

/********************
 **
 ** ANNOTATIONS and some other base macros and some global declarations
 **
 *******************/
#include "ccuredannot.h"



/* Use a special allocator (synonym for malloc) to ensure that we
   have its prototype without having to guess the prototype for malloc */
extern void* wrapperAlloc(unsigned int);
#pragma cilnoremove("wrapperAlloc")
#pragma ccuredalloc("wrapperAlloc", sizein(1), nozero)

extern void wrapperFree(void *);
#pragma cilnoremove("wrapperFree")
#pragma ccuredpoly("wrapperFree")

/* Same for strdup */
extern char* wrapperStrdup(char *);
#pragma cilnoremove("wrapperStrdup")
#pragma ccuredpoly("wrapperStrdup")

  // sm: I want to call this..
unsigned __ccured_mult_u32(unsigned x, unsigned y);




//
// WRAPPER HELPER FUNCTIONS
//
//


//
//
// FUNCTIONS FOR USE ON INCOMING WRAPPER ARGUMENTS
//   to convert them to the compatible representation and to
//   perform error checking
//
//
#pragma ccuredpoly("__ptrof_nocheck")
#pragma cilnoremove("__ptrof_nocheck")
void * __SAFE  __ptrof_nocheck(void *ptr);
// Type inference:  no constraints.
// In the wrapper:  returns ptr._p
// No run-time checking!

#pragma ccuredpoly("__startof")
void * __SAFE  __startof(void *ptr); 
// Type inference:  forces ptr to have a "base" field (a SEQ or a WILD)
// In the wrapper:  returns ptr._b. (This is 0 if ptr holds a scalar)
// No run-time checking!

#pragma ccuredpoly("__endof")
void * __SAFE  __endof(void *ptr);
// Type inference:  forces ptr to have an "end" field (a SEQ, FSEQ or a WILD)
// In the wrapper:  returns ptr._e (This is 0 if ptr holds a scalar)
//                  [for WILDs: returns (ptr._b==0) ? 0 : ptr._b + length(ptr)]
// No run-time checking

// Get the length in bytes. Forces the pointer to have an "end" field
#define __LENGTH(p) ( ((unsigned int)__endof(p)) - \
                      ((unsigned int)__ptrof_nocheck(p)) )

// Get the number of elements in the sequence. Forces the pointer to have an "end" field
#define __NUM_ELEMENTS(p) ( __LENGTH(p) / sizeof(*p) )


#pragma ccuredpoly("__ptrof")
void * __SAFE  __ptrof(void *ptr);
// Type inference:  no constraints.
// In the wrapper:  returns ptr._p.
//                 Calls ccured_fail if ptr is out of bounds (for pointers with bounds)

#pragma ccuredpoly("__ptrof_size")
#pragma cilnoremove("__ptrof_size")
void * __SAFE  __ptrof_size(void *ptr, unsigned int size);
// Type inference:  ptr must have an end
// In the wrapper:  returns ptr._p.
//                 Calls ccured_fail if ptr is not-null and has less
//                 than size bytes until the end

#pragma ccuredpoly("__verify_nul")
void __verify_nul(char const *ptr);
// Type inference:  forces ptr to have an "end" field
// In the wrapper:  ensures ptr has a terminating nul character.
//                  Calls ccured_fail if ptr is null, out of bounds,
//                    or not nul-terminated.



#pragma ccuredpoly("__strlen")
int __strlen(char *ptr);      
// Type inference:  ptr must be a string type. Forces ptr to have an "end" field
// In the wrapper:  returns the length of the string, not counting the
//                    terminating nul.
//                  Calls ccured_fail if ptr is null, out of bounds,
//                    or not nul-terminated.  
//                    __strlen includes the checks in __verify_nul.


#pragma ccuredpoly("__strlen_n")
int __strlen_n(char *ptr, int n);
// purpose:         the wrapped code is going to read from 'ptr' as a
//                  nul-terminated string, but will limit itself to reading
//                  at most 'n' bytes (e.g. strncpy)
// Type inference:  forces ptr to have an "end" field
// In the wrapper:  returns the length of the string, not counting the
//                    terminating nul, or 'n', whichever is less.
//                  Calls ccured_fail if ptr is null, out of bounds, or not
//                    nul-terminated within 'n' or size(ptr) bytes, 
//                    whichever is less.
//                    __strlen_n includes the checks in __verify_nul.


#pragma ccuredpoly("__stringof")
char * __stringof(char const *ptr);
#pragma cilnoremove("__stringof")
// This is like __verify_nul(x), __ptrof(x)
// Type inference:  ptr must have an "end" field
// In the wrapper:  ensures ptr has a terminating nul character.
//                    (for FSeqN/SeqN, this is simply a null-pointer check)
//                  Calls ccured_fail if ptr is null, out of bounds,
//                    or not nul-terminated.
//                  Returns the string.

#pragma ccuredpoly("__stringof_ornull")
char * __stringof_ornull(char const *ptr);
#pragma cilnoremove("__stringof_ornull")
// This is like if (x!=0) {__verify_nul(x)}; __ptrof(x)
// Type inference:  ptr must have an "end" field
// In the wrapper:  ensures ptr is null or has a terminating nul character.
//                    (for FSeqN/SeqN, this is simply a null-pointer check)
//                  Calls ccured_fail if ptr is out of bounds
//                    or not nul-terminated.
//                  Returns the string.

#pragma ccuredpoly("__write_at_least")
void __write_at_least(void *ptr, unsigned int n);  
// Type inference:  ptr must have an "end" field
// In the wrapper:  Verifies that we can write the next n bytes of ptr. In
//                  WILDs, also clears the tags for the next n bytes.
//                  Calls ccured_fail if ptr is null, out of bounds,
//                    or not long enough.

#pragma ccuredpoly("__read_at_least")
void __read_at_least(void *ptr, unsigned int n);  
// Type inference:  ptr must have an "end" field
// In the wrapper:  Verifies that we can read the next n bytes of ptr.
//                  Calls ccured_fail if ptr is null, out of bounds,
//                    or not long enough.

#pragma ccuredpoly("__copytags")
void __copytags(void *dest, void* src, unsigned int n);  
// Type inference:  dest and src must allow forwards arithmetic.
//                  simulates a dest = src assignment to reflect the
//                  flow of data. 
// In the wrapper:  Verifies that we can read/write the next n bytes
//                    of both dest and src.  In WILDs, also copys the
//                    appropriate tags from src to dest.
//                  Calls ccured_fail if either dest or src is null,
//                    out of bounds, or not long enough.


//
//
// FUNCTION FOR USE ON WRAPPER RETURN VALUES
// These functions can construct fat pointers from regular ones
//

#pragma ccuredpoly("__mkptr")
#pragma cilnoremove("__mkptr") // wrappers.ml needs it
void * __mkptr(void * __SAFE p, void *phome);
// Purpose:  for creating wide pointers into a pre-existing home area.
  // Type inference:  phome must be castable to the return type.
  // In the wrapper:  returns a (multiword) pointer to p with phome's
  //                  memory region.

#pragma ccuredpoly("__mkptr_int")
void * __mkptr_int(unsigned long p, void *phome);
// Purpose:  for creating wide pointers into a pre-existing home area.
//           Like __mkptr but for use on scalars.
// Type inference:  phome must be castable to the return type.
// In the wrapper:  returns a (multiword) pointer to p with phome's
//                    memory region.

#pragma ccuredpoly("__mkptr_size")
#pragma cilnoremove("__mkptr_size")
void * __mkptr_size(void * __SAFE p, unsigned int len);
// Purpose:  for creating wide pointers to newly-malloc'd data.
// Type inference:  return value must not be WILD !!
// In the wrapper:  returns a (multiword) pointer to p with a home
//                    area len bytes long.
// Note: you will get a linker error on __mkptr_size_ws if you try 
//   to use the return value as WILD, which is not supported

#pragma ccuredpoly("__mkptr_string")
#pragma cilnoremove("__mkptr_string")
char * __mkptr_string(char * __SAFE p);
// Purpose:  for creating wide pointers to strings.
// Type inference:  return value must not be WILD.
// In the wrapper:  returns a (multiword) pointer to p with a home
//                  area as long as the length of the string.


#pragma ccuredpoly("__align_seq")
#pragma cilnoremove("__align_seq")
void* __align_seq(void *p, unsigned int size);
// Type inference:  pretends there is a direct cast from argument to result
// In the wrapper:  'p' should be a SEQ or FSEQ pointer; this
//                  function will truncate p's accessible region so
//                  it ends on a 'size'-byte boundary (thus it will
//                  pass the various alignment checks)


/* We add a mechanism for casting arbitrarily without penalty. This is 
 * unsound. Use only when you know what you are doing. */
#pragma ccuredpoly("__trusted_cast")
#pragma cilnoremove("__trusted_cast")
void * __trusted_cast(void * p);


/* This function is even worse than __trusted_cast, because it does not 
 * ensure compatible representations of the pointer base types.  This may
 * introduce bugs into your program if used.  (We use it only for a few very
 * specialized situations in wrapper code.) It is implemented only on SAFE
 * pointers*/
#pragma ccuredpoly("__trusted_deepcast")
#pragma cilnoremove("__trusted_deepcast")
void * __SAFE __trusted_deepcast(void * __SAFE p);


  // Here is a macro to compute ptr + idx but hide from CCured that there
  // is arithmetic going on. This one does not work properly if the
  // result is not SAFE
#define __trusted_add(ptr, idx) \
   __trusted_cast((unsigned long)(ptr) + (idx)*sizeof(* (ptr)))



#pragma ccuredpoly("ccured_hasuniontag")
int  ccured_hasuniontag(void *);

//If CCURED_HASUNIONTAG(foo.bar) is true, then it is legal to read field bar
// in tagged union foo, i.e. the most recently-written field in foo was bar
#define CCURED_HASUNIONTAG(x) ccured_hasuniontag(&(x))


int  __ccured_kind_of(void *);
#pragma ccuredpoly("__ccured_kind_of")
// Returns the kind of a pointer

  // Return values for ccured_kind_of
  // If you change these, change the implementation of Ptrnode.k2number
  #define METAPTR_KIND       256
  #define DYNAMIC_TYPE_KIND  128
  #define NULLTERM_KIND       64
  #define TABLE_KIND          32
  #define RTTI_KIND           16
  #define SCALAR_KIND    0
  #define SAFE_KIND      1
  #define SEQ_KIND       2
  #define FSEQ_KIND      3
  #define INDEX_KIND     4
  #define ROSTRING_KIND  5
  #define RWSTRING_KIND  6

  #define SEQN_KIND      (SEQ_KIND  | NULLTERM_KIND)
  #define FSEQN_KIND     (FSEQ_KIND | NULLTERM_KIND)
  #define FSEQR_KIND     (FSEQ_KIND | RTTI_KIND)
  #define SEQR_KIND      (SEQ_KIND  | RTTI_KIND)

  #define SAFEC_KIND     (SAFE_KIND  | METAPTR_KIND)
  #define SEQC_KIND      (SEQ_KIND   | METAPTR_KIND)
  #define FSEQC_KIND     (FSEQ_KIND  | METAPTR_KIND)
  #define SEQNC_KIND     (SEQN_KIND  | METAPTR_KIND)
  #define FSEQNC_KIND    (FSEQN_KIND | METAPTR_KIND)
  #define SEQRC_KIND     (SEQR_KIND  | METAPTR_KIND)
  #define FSEQRC_KIND    (FSEQR_KIND | METAPTR_KIND)
  #define RTTIC_KIND     (RTTI_KIND  | METAPTR_KIND)

  #define WILD_KIND      (0 | DYNAMIC_TYPE_KIND)

  // Get the kind of a pointer
  // Returns one of the above kinds
  #define KIND_OF(p) __ccured_kind_of(p)
  // Check that a pointer has an expected kind. We might be making everything
  // wild.
  #ifdef CCURED_CURETYPE_wild
    #define HAS_KIND(p, kind) (KIND_OF(p) == WILD_KIND)
    #define HAS_KIND_MASK(p, kind, mask) (KIND_OF(p) == WILD_KIND)
  #else 
    #define HAS_KIND(p, kind) (KIND_OF(p) == (kind))
    #define HAS_KIND_MASK(p, kind, mask) ((KIND_OF(p) & ~(mask)) == (kind))
  #endif

char* __ccured_mangling_of(unsigned int);
#pragma ccuredpoly("__ccured_mangling_of")
#pragma cilnoremove("__ccured_mangling_of")
// Returns the mangling of a pointer (a string literal)

int  __ccured_has_empty_mangling(unsigned int);
#pragma ccuredpoly("__ccured_has_empty_mangling")
#pragma cilnoremove("__ccured_has_empty_mangling")

#define CCURED_MANGLING_OF(p)  __ccured_mangling_of(sizeof(p))
#define CCURED_HAS_EMPTY_MANGLING(p)  __ccured_has_empty_mangling(sizeof(p))



/******************************************************
 *
 * DEEP COPY STUFF
 *
 *******************************************************/


#pragma cilnoremove("abort_deepcopy")
__NORETURN void abort_deepcopy(char * errmsg);

/* Use this macro to construct the prototype for the __deepcopy_to_compat 
 * function for a specific structure. Once CCured sees the prototype it will 
 * fill in the body. */
#define __DEEPCOPY_TO_COMPAT_PROTO(sname)                                   \
 void __deepcopy_ ## sname ## _to_compat(struct sname __COMPAT * compat,    \
                                         struct sname *          fat) 

/* Use this macro to construct the prototype for the __deepcopy_from_compat
   function for a specific structure. CCured will fill in the body of this one. */
#define __DEEPCOPY_FROM_COMPAT_PROTO(sname)                                 \
 void __deepcopy_ ## sname ## _from_compat(struct sname * fat,              \
                                           struct sname __COMPAT * compat) 


/* Use this macro inside _DEEPCOPY_FROM_COMPAT_PROTO only (to specify that a 
 * given field is a null-terminated string field */
#define __DEEPCOPY_FROM_COMPAT_STRING_FIELD(fname)                          \
  fat->fname = __mkptr_string(compat->fname)

/* Use this macro inside _DEEPCOPY_TO_COMPAT_PROTO only (to specify that a 
 * given field is a null-terminated string field */
#define __DEEPCOPY_TO_COMPAT_STRING_FIELD(fname)                            \
  compat->fname = __stringof(fat->fname);

/* This is the basic __DECL_COMPAT macro. You should not use this one, but 
 * use instead the ones below! Pass the source variable, the name of the 
 * struct (src must have type "struct sname *"), the name of the new 
 * variable to be declared (will have type "struct sname __COMPAT *"), and 
 * the code to make the copy */      
#define __DECL_COMPAT_BASE(x, sname, src, malloc_var_decl, copy)            \
  /* Take the __ptrof first */                                              \
  struct sname * x ## __ptrof = __ptrof_nocheck(src);                       \
  malloc_var_decl                                                           \
  struct sname __COMPAT * x =                                               \
    /* We are done if we have NULL or an already compat struct */           \
    (x ## __ptrof && (! CCURED_HAS_EMPTY_MANGLING(struct sname))) ?         \
      /* Now do the copying as specified in the argument */                 \
      (copy)                                                                \
    : /* No copying is needed. Use a trusted_cast to prevent CCured from    \
         connecting the two versions of the structure */                    \
      (struct sname __COMPAT *)__trusted_cast(x ## __ptrof)

/* This is probably the most useful macro for deep copies. It reserves space 
 * on the current stack frame for the copy. Howeve, that space is used only 
 * if a copy is really necessary. In that case a __deepcopy function is used 
 * to make the copy */
#define __DECL_COMPAT_STACK(x, sname, src)                                  \
  /* Declare the __deepcopy function that we need */                        \
  __DEEPCOPY_TO_COMPAT_PROTO(sname);                                        \
  /* Declare the place where we'll make the copy */                         \
  struct sname __COMPAT x ## __area;                                        \
  __DECL_COMPAT_BASE(x, sname, src, ,                                       \
          (__deepcopy_ ## sname ## _to_compat(& x ## __area,                \
                                             x ## __ptrof), & x ## __area))

/* Like the _STACK version but the copy is made on the heap */
#define __DECL_COMPAT_MALLOC(x, sname, src)                                 \
  /* Declare the __deepcopy function that we need */                        \
  __DEEPCOPY_TO_COMPAT_PROTO(sname);                                        \
  __DECL_COMPAT_BASE(x, sname, src,                                         \
                     struct sname __COMPAT * x ## __malloc; ,               \
          (x ## __malloc = (struct sname __COMPAT*)wrapperAlloc(sizeof(* x)),\
           __deepcopy_ ## sname ## _to_compat(x ## __malloc,x ## __ptrof),  \
           x ## __malloc))


/* Like the _STACK version but no copy is made. Instead the code aborts (but 
 * this happens only if a copy would be necessary). Use this one when you do 
 * not want to have a copy made, but instead you want to be told about it. */
#define __DECL_COMPAT_ABORTCOPY(x, sname, src)                               \
     __DECL_COMPAT_BASE(x, sname, src, ,                                     \
                        (abort_deepcopy("Abort copy of struct " ## sname),   \
                         (struct sname __COMPAT*)0))


/* Like the _STACK version but no copy is made. Use for preparing 
 * "OUT"-arguments to functions. You will do the copying after the function 
 * call */
#define __DECL_COMPAT_STACK_NOCOPY(x, sname, src)                           \
  /* Declare the place that we reserve */                                   \
  struct sname __COMPAT x ## __area;                                        \
  __DECL_COMPAT_BASE(x, sname, src, , & x ## __area)

/* Like the _STACK version but the space is reserved on the heap */
#define __DECL_COMPAT_MALLOC_NOCOPY(x, sname, src)                           \
  __DECL_COMPAT_BASE(x, sname, src,                                          \
                     (struct sname __COMPAT*)wrapperAlloc(sizeof(* x)))


/* Use this function to copy the actual results of a function from the 
 * compatible space that you reserved with one of the _NOCOPY macros, into 
 * the actual space. The copy is made only if the compatible space was 
 * actually allocated. */
#define __COPYOUT_FROM_COMPAT(compat, sname, dest)                          \
  /* Declare the __deepcopy function that we need */                        \
  { __DEEPCOPY_FROM_COMPAT_PROTO(sname);                                    \
  if(compat != (dest)) {                                                    \
    __deepcopy_ ## sname ## _from_compat((dest), compat);                   \
  }}

/* Use this function to allocate (on the heap) non-compatible space and copy 
 * into it the data from a compatible struct */
#define __DECL_NEW_FROM_COMPAT(x, sname, src)                               \
  /* Declare the __deepcopy function that we need */                        \
  __DEEPCOPY_FROM_COMPAT_PROTO(sname);                                      \
  struct sname __COMPAT * src2 = src;                                       \
  struct sname * x = 0;                                                     \
  if (src2 != 0) {                                                          \
    x = (struct sname *)wrapperAlloc(sizeof(* x));                          \
    __deepcopy_ ## sname ## _from_compat(x, src2);                          \
  }



/****************************************************************
 **
 **      VARARG
 **
 ****************************************************************/

// The structure that defines the printf arguments
#pragma cilnoremove("struct printf_arguments")
struct printf_arguments {
  int i;
  double d;  
  char * __ROSTRING s;
#ifdef _MSVC
  __int64 ll;
#else
  long long ll;
#endif
};

#ifdef __cplusplus
  #ifdef 0
    {
  #endif
  }
#endif

/*
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

