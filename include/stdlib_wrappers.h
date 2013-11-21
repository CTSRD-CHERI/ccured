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

#if defined(CCURED) && ! defined(STDLIB_WRAPPERS_INCLUDED)
#define STDLIB_WRAPPERS_INCLUDED

 #ifdef __cplusplus
    extern "C" {
 #endif
      

#include  "malloc_wrappers.h"     
      
#pragma ccuredwrapper("atof_wrapper", of("atof"));
__inline static
double atof_wrapper(char* str)
{
  __verify_nul(str);  //make sure str is nul-terminated
  return atof((char*)__ptrof(str));
}

#pragma ccuredwrapper("atoi_wrapper", of("atoi"));
__inline static
int atoi_wrapper(char* str)
{
  __verify_nul(str);
  return atoi((char*)__ptrof(str));
}

#pragma ccuredwrapper("atol_wrapper", of("atol"));
__inline static
long atol_wrapper(char* str)
{
  __verify_nul(str);
  return atol((char*)__ptrof(str));
}


// ***** QuickSort:

//redeclare qsort to make the __SAFEs explicit.
#ifndef __cplusplus                        
  // it turns out gcc won't parse __attribute__s on function parameters
  // unless those parameters have names
  //
  // sm: I'm getting compile errors because this declaration is seen by
  // gcc to conflict with the one in stdlib.h because of the attributes;
  // so I'm going to rename it true_qsort and make the connection in
  // ccuredlib.c
  //
  // update: I see, I was trying to compile code which was preprocessed for
  // CIL's consumption, not gcc's; reverting back to qsort..
  extern void qsort(void *, size_t, size_t,
                    int (*)(const void *__SAFE left, const void *__SAFE right));
#endif

//see ccuredlib for descriptions:
extern unsigned __ccured_mult_u32(unsigned x, unsigned y);
extern void qsort_zero_tags(void* base, size_t nelts, size_t size);
#pragma ccuredpoly("qsort_zero_tags");

#ifdef USE_POLYMORPHIC_QSORT

    //Wrappers for qsort and bsearch that don't use a base pointer (which prevents
    // polymorphism).  Do this by requring the comparison function to take
    // safe pointers.  Sendmail uses this.

    //BUG:  matth: this is unsound if you ignore warnings of "changing user
    // specified SAFE node to ..." on the arguments in the SafeCompare
    // function.  If CCured needs to change the arguments into fat pointers,
    // bad things will happen.  We need a better way to allow polymorphism...

    typedef int (*SafeCompare)(void const* __SAFE ,void const* __SAFE);

    #pragma ccuredpoly("qsort");

    #pragma ccuredwrapper("qsort_wrapper_nothunk", of("qsort"));
    static inline
    void qsort_wrapper_nothunk(void* base, size_t nmemb,
			size_t size,
			SafeCompare compare)
    {
		__read_at_least(base, __ccured_mult_u32(nmemb, size));
      qsort_zero_tags(base, nmemb, size);

      qsort(__ptrof(base), nmemb, size, __ptrof(compare));

      if (0) {  //Force the right type edges between compare and base
	compare(__ptrof(base),__ptrof(base));
      }
    }

    #pragma ccuredwrapper("bsearch_wrapper", of("bsearch"));
    static inline
    void *bsearch_wrapper(void * key, 
			  void * base, 
			  size_t nmemb,
			  size_t size,
			  SafeCompare compare)
    {
      void* result;
      __read_at_least(base, __ccured_mult_u32(nmemb, size));
      __read_at_least(key, size);
      
      result = bsearch( __ptrof(key), 
			__ptrof(base), 
			nmemb, 
			size, 
			(SafeCompare)__ptrof(compare));
      return __mkptr(result, base);		      
    }

#else //USE_POLYMORPHIC_QSORT
    // This version works for the general case of comparison functions
    // by storing a pointer to the array in global memory so that we can
    // simulate a closure.  However, this is not polymorphic, since we can only
    // assign a single type to the "base" variable.

    static void *__qsort_base __MAYPOINTTOSTACK;
      //This use of __CANPOINTTOSTACK is sound; __qsort_base might
      // point to a stack-allocated array, but it is only live during the
      // call to qsort.
    static int (*__qsort_compare)(const void*, const void*);

    static inline
    int __qsort_thunk(void * __SAFE left, void * __SAFE right)
    {
      // map the 'left' and 'right' lean pointers to the
      // fat pointers we need
      void* fatleft = __mkptr(__ptrof(left), __qsort_base);
      void* fatright = __mkptr(__ptrof(right), __qsort_base);

      // and call the user-supplied sorting function, which
      // expects fat pointers
      return __qsort_compare(fatleft, fatright);
    }

    // this function's test case is test/small2/qsort.c
    #pragma ccuredwrapper("qsort_wrapper", of("qsort"));
    static inline
    void qsort_wrapper(void* base, size_t nmemb,
		       size_t size,
		       int (*compare)(const void *left, const void *right))
    {
      if(__LENGTH(base) < __ccured_mult_u32(nmemb, size))
	CCURED_FAIL(FAIL_UBOUND FILE_AND_LINE);
      qsort_zero_tags(base, nmemb, size);

      // save the pertinent values
      __qsort_base = base;
      __qsort_compare = compare;

      qsort(__ptrof(base), nmemb, size,
            (int (*)(const void*,const void*))__ptrof((int (*)(void * __SAFE,
                                                   void * __SAFE))__qsort_thunk));

      __qsort_base = 0;
    }

	// Like qsort, this is not polymorphic:

	static void *__bsearch_base __MAYPOINTTOSTACK;  
	static void *__bsearch_key __MAYPOINTTOSTACK;  
		//This use of __CANPOINTTOSTACK is sound; __qsort_base might
		// point to a stack-allocated array, but it is only live during the
		// call to qsort.
	static int (*__bsearch_compare)(void*, void*);

	static inline
	int __bsearch_thunk(void * __SAFE key, void * __SAFE element)
	{
		// map the lean pointers to the fat pointers we need.
		// I think the key is always passed first.
		void* fatkey = __mkptr(__ptrof(key), __bsearch_key); 
		void* fatelement = __mkptr(__ptrof(element), __bsearch_base);

		// and call the user-supplied compare function, which
		// expects fat pointers
		return __bsearch_compare(fatkey, fatelement);
	}

	// this function's test case is test/small2/bsearch.c
	#pragma ccuredwrapper("bsearch_wrapper", of("bsearch"));
	static inline
	void *bsearch_wrapper(void * key, 
						void * base, 
						size_t nmemb,
						size_t size,
						int (*compare)(void *left, void *right))
	{
		void* __SAFE result;

		if(__LENGTH(base) < __ccured_mult_u32(nmemb, size))
			CCURED_FAIL(FAIL_UBOUND FILE_AND_LINE);

		// save the pertinent values
		__bsearch_key = key;
		__bsearch_base = base;
		__bsearch_compare = compare;

		result = bsearch(__ptrof(key), 
						__ptrof(base), 
						nmemb, 
						size, 
						(int (*)(const void*,const void*))__ptrof((int (*)(void * __SAFE,
														void * __SAFE))__bsearch_thunk));

		__bsearch_base = 0;
		return __mkptr(result, base);
	}
#endif // !USE_POLYMORPHIC_QSORT

// ***** end quicksort/bsearch stuff.



//Warning:  If str is stack-allocated, you must make sure that endptr is a 
// stack variable with a lower address.  (Because of how we implement 
// CHECK_STOREPTR, it's not enough to simply make endptr and str pointers to
// the same frame.)
#pragma ccuredwrapper("strtol_wrapper", of("strtol"));
__inline static
long strtol_wrapper(const char *str, char ** endptr, int base)
{
  char* __SAFE ep __SAFE;
  long result = strtol( __ptrof(str), 
			endptr == NULL ? NULL : &ep,
			base);
  if (endptr != NULL)
  {
    //matth: The pointer returned by strtol points to a character in str.
    *endptr = __mkptr(ep, str);
  }
  return result;
}

#pragma ccuredwrapper("getenv_wrapper", of("getenv"));
__inline static
char* getenv_wrapper(char* str)
{
  __verify_nul(str);  //make sure str is nul-terminated
  return __mkptr_string( getenv(__ptrof(str)) );
}

#ifdef __cplusplus
  }
#endif

#endif // CCURED

