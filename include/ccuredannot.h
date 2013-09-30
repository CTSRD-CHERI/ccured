/* See licence and copyright notice at the end of this file */

/* This file defines CCured stuff that is needed both before and after 
 * processing a file and in the library as well.
 *
 * 1. Before processing a file for curing: CCURED is defined
 * 2. After preprocessing a file: CCURED and CCURED_POST are defined
 * 3. In the library: CCURED is NOT defined
 */
#ifndef CCUREDANNOT_H
#define CCUREDANNOT_H


#ifdef _MSVC
  #ifdef _GNUCC
    #error Exactly one of _MSCV and _GNUCC must be defined.
  #endif
  #define INLINE_STATIC_CHECK __inline
   /* Must restrict packing on 32-bit boundary because otherwise the
    * length and tag fields are not adjacent to the data */
  #pragma pack(4)
  #define __NORETURN __declspec(noreturn)
  #define __UNUSED
  /* On MSVC there is no __FUNCTION__. Actually VC.NET has it. */
  #ifndef __FUNCTION__
    #define __FUNCTION__ ""
  #endif
  #pragma warning(disable: 4068) // Unrecognized pragma
#else
  #ifndef _GNUCC
    #error Exactly one of _MSVC or _GNUCC must be defined.
  #endif
  #undef  _GNUCC
  #define _GNUCC 1
  #define __NORETURN __attribute__((noreturn))
  #define __UNUSED __attribute__((unused))
  #if (defined CCURED_NO_INLINE)
    #define INLINE_STATIC_CHECK
  #elif (__GNUC__  >= 3) && (defined __OPTIMIZE__)
    #define INLINE_STATIC_CHECK __inline __attribute__((always_inline)) static
  #else
    #define INLINE_STATIC_CHECK __inline static
  #endif
#endif

/* If we are in the library, then we must compile conservatively */
#if ! defined(CCURED)
 #undef CCURED_ALWAYS_STOP_ON_ERROR
 #undef CCURED_FAIL_IS_TERSE
#endif

/* When CCured is run with --alwaysStopOnError it will define 
 * CCURED_ALWAYS_STOP_ON_ERROR and will set __ccuredAlwaysStopOnError. In that 
 * case, the runtime library functions ccured_fail will not return and we 
 * want to tell gcc about that so that it can generate better code. */
#if defined(CCURED_ALWAYS_STOP_ON_ERROR)
#  ifndef __NORETURN
#    error NORETURN not defined
#  endif // ifndef __NORETURN
#  define MAYBE_NORETURN __NORETURN
#else
#  define MAYBE_NORETURN
#endif // ifdef CCURED_ALWAYS_STOP_ON_ERROR

#define CCURED_FAIL_VERBOSE_PARAMS char const *file, int line, char const *function

/* When CCured is run with --failIsTerse then it defines 
 * CCURED_FAIL_IS_TERSE and sets __ccuredFailIsTerse. In that case we pass 
 * fewer arguments to the run-time checking functions */
#if defined(CCURED_FAIL_IS_TERSE)
  #define CCURED_FAIL_EXTRA_PARAMS
  #define CCURED_FAIL_EXTRA_ARGS
  #define FILE_AND_LINE
  #define CCURED_FAIL_STR   ccured_fail_str_terse
  #define CCURED_FAIL       ccured_fail_terse
#else
  // Use this in the prototype of checkers
  #define CCURED_FAIL_EXTRA_PARAMS , CCURED_FAIL_VERBOSE_PARAMS
  // Use this to call a checker from within the body of a checker
  #define CCURED_FAIL_EXTRA_ARGS , file, line, function
  // Use this to call a checker with the current location information
  #define FILE_AND_LINE , __FILE__, __LINE__, __FUNCTION__
  // Use this to invoke failure with a custom string
  #define CCURED_FAIL_STR   ccured_fail_str
  // Use this to fail with a code (see the FAIL_ macros above)
  #define CCURED_FAIL       ccured_fail
#endif



/***********************************************************************
 **                                                                        
 **      GLOBALS DEFINED BY CCURED
 **
 ***********************************************************************/
#ifdef __cplusplus
  extern "C" {
  #ifdef 0
     }
  #endif
#endif


extern int __ccuredAlwaysStopOnError;
/* A variable that controls whether we should always stop whenever 
 * ccured_fail is called. If this variable is false then we check the values 
 * of the environment variable CCURED_CONTINUE_ON_ERROR. CCured will turn 
 * this on or off. You SHOULD not alter this variable. */

extern int __ccuredUseStrings;
/* Controls whether we should allow the +1 tricks to protect the null 
 * terminators. CCured will turn this on or off based on how it generated 
 * code. You SHOULD not alter this variable. */

extern int __ccuredLogNonPointers;
/* Controls whether we are logging scalar assignments to pointers. CCured 
 * turns this on. You SHOULD not alter this variable.  */

extern int __ccuredDisableStoreCheck;
/* Controls whether the CHECK_STORE is operational or not.  CCured 
 * turns this on. You can alter this variable. */

extern void* __ccuredStackBottom;
/* CCured initializes this variable with the addres of the stack pointer 
 * when "main" starts running. We use this to avoid STORE_PTR errors for 
 * argv and envp. */

extern void __ccuredInit(void);
#if defined(CCURED) && ! defined(CCURED_POST)
  #pragma cilnoremove("__ccuredInit")
#endif
/* CCured inserts a call to this function in your "main" */

MAYBE_NORETURN void ccured_fail_str(char const *str, 
                                    CCURED_FAIL_VERBOSE_PARAMS);
MAYBE_NORETURN void ccured_fail_str_terse(const char *str);
/* Print a given error message. Does not return if 
 * CCURED_ALWAYS_STOP_ON_ERROR or [CCURED_CONTINUE_ON_ERROR is false]. */
/* Always write:

    CCURED_FAIL_STR(mymsg FILE_AND_LINE);

*/


MAYBE_NORETURN void ccured_fail(int msgId,
                                CCURED_FAIL_VERBOSE_PARAMS);
MAYBE_NORETURN void ccured_fail_terse(int msgId);
/* fail with a given code, which maps to a message in the library */
/* Always write:

    CCURED_FAIL(mymsgcode FILE_AND_LINE);

*/


/* Use this function when you are about to dereference a non-pointer. Most 
 * often is just like ccured_fail, but if you ran CCured with 
 * --logNonPointers it might help you figure out in which cast did this 
 * scalar become a pointer. */
MAYBE_NORETURN void non_pointer_fail(unsigned long l,
                                     CCURED_FAIL_VERBOSE_PARAMS);
MAYBE_NORETURN void non_pointer_fail_terse(unsigned long l);
#if defined(CCURED_FAIL_IS_TERSE)
 #define NON_POINTER_FAIL   non_pointer_fail_terse
#else
 #define NON_POINTER_FAIL   non_pointer_fail
#endif

/* If CCured was run with --logNonPointers it will generate code to log all 
 * casts of scalars into pointers */

void __logScalar(int id, unsigned long l);

#ifdef __cplusplus
  #if 0
     {
  #endif
  }
#endif

/* See if we must turn off all CCURED_ANNOTATIONS (we do it after Ccured 
 * because gcc does not like them). Actually we need annotations only before 
 * CCured. */
#if defined(CCURED) && ! defined CCURED_POST
#define CCURED_ANNOT(x) x
#else
#define CCURED_ANNOT(x)
#endif

#define __WILD       CCURED_ANNOT(__attribute__((wild)))
#define __SAFE       CCURED_ANNOT(__attribute__((safe)))
#define __FSEQ       CCURED_ANNOT(__attribute__((fseq)))
#define __TAGGED     CCURED_ANNOT(__attribute__((tagged)))
#define __TRUSTEDUNION CCURED_ANNOT(__attribute__((trustedunion)))
#define __INDEX      CCURED_ANNOT(__attribute__((index)))
#define __SIZED      CCURED_ANNOT(__attribute__((sized)))
#define __SEQ        CCURED_ANNOT(__attribute__((seq)))
#define __SEQN       CCURED_ANNOT(__attribute__((seqn)))
#define __FSEQN      CCURED_ANNOT(__attribute__((fseqn)))
#define __SEQR       CCURED_ANNOT(__attribute__((seqr)))
#define __FSEQR      CCURED_ANNOT(__attribute__((fseqr)))
#define __ROSTRING   CCURED_ANNOT(__attribute__((rostring)))
#define __STRING     CCURED_ANNOT(__attribute__((string)))
//__RWSTRING is an old name for __STRING
#define __RWSTRING   CCURED_ANNOT(__attribute__((string)))

//Note: __NULLTERM used to mean "one of {STRING, FSeqN, SeqN, ...}"
//But now we use this term to mean __STRING instead:
// a one-word pointer to a null-terminated array.
#define __NULLTERM   CCURED_ANNOT(__attribute__((string)))
//Use __NULLTERM_BUFFER for the old meaning of __NULLTERM: 
// a (possibly multiword) pointer to a null-terminated array.
#define __NULLTERM_BUFFER   CCURED_ANNOT(__attribute__((nullterm)))

#define __SAFEUNION  CCURED_ANNOT(__attribute__((safeunion)))
#define __INDEXT     CCURED_ANNOT(__attribute__((indext)))
#define __WILDT      CCURED_ANNOT(__attribute__((wildt)))
#define __SEQT       CCURED_ANNOT(__attribute__((seqt)))
#define __SEQNT      CCURED_ANNOT(__attribute__((seqnt)))
#define __FSEQT      CCURED_ANNOT(__attribute__((fseqt)))
#define __FSEQNT     CCURED_ANNOT(__attribute__((fseqnt)))
#define __SAFEC      CCURED_ANNOT(__attribute__((safec)))
#define __WILDC      CCURED_ANNOT(__attribute__((wildc)))
#define __SEQC       CCURED_ANNOT(__attribute__((seqc)))
#define __SEQNC      CCURED_ANNOT(__attribute__((seqnc)))
#define __SEQRC      CCURED_ANNOT(__attribute__((seqrc)))
#define __FSEQC      CCURED_ANNOT(__attribute__((fseqc)))
#define __FSEQNC     CCURED_ANNOT(__attribute__((fseqnc)))
#define __FSEQRC     CCURED_ANNOT(__attribute__((fseqrc)))
#define __SPLIT      CCURED_ANNOT(__attribute__((split)))
#define __COMPAT     CCURED_ANNOT(__attribute__((compat)))
#define __RTTI       CCURED_ANNOT(__attribute__((rtti)))
#define __RTTIC      CCURED_ANNOT(__attribute__((rttic)))
#define __NODE
#ifndef DISABLE_HEAPIFY
  #define __HEAPIFY  CCURED_ANNOT(__attribute__((heapify)))
#else
  #define __HEAPIFY
#endif
#define __DUMMYDEFN   CCURED_ANNOT(__attribute__((dummydefn)))
#define __NOCUREBLOCK CCURED_ANNOT(__blockattribute__(nocure))
#define __NOCURE      CCURED_ANNOT(__attribute__((nocure)))
#define __NOUNROLL    CCURED_ANNOT(__attribute__((nounroll)))
#define __LEAN        CCURED_ANNOT(__attribute__((lean)))
#define __CCUREDVARARG(x) \
                      CCURED_ANNOT(__attribute__((ccuredvararg(sizeof(x)))))
#define __CCUREDFORMAT(x) \
         CCURED_ANNOT(__attribute__((ccuredvararg(sizeof(struct printf_arguments))))) \
         CCURED_ANNOT(__attribute__((ccuredformat(x))))
#define __MAYPOINTTOSTACK CCURED_ANNOT(__attribute__((mayPointToStack)))
#define __OVERRIDE(x) CCURED_ANNOT(__attribute__((overide(x))))
#define __MDSIZE_NULLTERM   CCURED_ANNOT(__attribute__((mdsize(nullterm))))
#define __MDSIZE_FIXED(x)   CCURED_ANNOT(__attribute__((mdsize(fixed,(x)))))
#define __MDSIZE_FIELD(x)   CCURED_ANNOT(__attribute__((mdsize(field,(x)))))
#define __MDSIZE_CONTEXT    CCURED_ANNOT(__attribute__((mdsize(context))))
#define __MDSIZE_MKCONTEXT  CCURED_ANNOT(__attribute__((mdsize(mkcontext))))

#define __SELECTEDWHEN(v) CCURED_ANNOT(__attribute__((selectedwhen(v))))
#define __SELECTOR(v)     CCURED_ANNOT(__attribute__((selector(v))))

#define __SIZE(v)         CCURED_ANNOT(__attribute__((size(v))))
#define __COUNT(v)        CCURED_ANNOT(__attribute__((count(v))))
#define __END(v)          CCURED_ANNOT(__attribute__((count((v)-__this))))

#define __NOESCAPE        CCURED_ANNOT(__attribute__((noescape)))

// each code is associated with a string that gets printed when
// we abort execution due to runtime check failure
#define FAIL_BELOW_STACK_ADDRESS 0
#define FAIL_STORE_STACK_ADDRESS 1
#define FAIL_LBOUND              2
#define FAIL_UBOUND              3
#define FAIL_FUNCTIONPOINTER     4
#define FAIL_DECR_FSEQ           5
#define FAIL_NULL                6
#define FAIL_NULL_STRING         7
#define FAIL_STRINGBOUND         8
#define FAIL_UNALIGNED           9
#define FAIL_MALLOC              10
#define FAIL_REALLOC             11
#define FAIL_FREE                12
#define FAIL_REALLOC_SHRINK      13
#define FAIL_REALLOC_GROW        14
#define FAIL_NONPOINTER          15
#define FAIL_SCALARLOG           16
#define FAIL_NULLSTRING          17
#define FAIL_VA_BADARG           18
#define FAIL_VA_NOSTART          19
#define FAIL_VA_MANY             20
#define FAIL_VA_BADTYPE          21
#define FAIL_UNRECOGNIZEDFORMAT  22
#define FAIL_OVERFLOW            23
#define FAIL_READINVALIDPTR      24
#define FAIL_RTTICAST            25
#define FAIL_NOTENOUGHROOM       26
#define FAIL_SEQUENCE_ALIGN      27
#define FAIL_UNIONTAG            28
#define FAIL_STACK_OVERFLOW      29
#define FAIL_CUSTOM              30 /* This is the error code for the custom
                                       messages given by ccured_fail_str */
#define NUM_FAIL_CODES           31   /* sm: keep this updated. If you add 
                                       * things here you must also go into 
                                       * ccuredlib.c and add the string that 
                                       * corresponds to this error.  */


#endif // CCUREDANNOT_H

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
