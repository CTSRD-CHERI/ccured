// This file defines the macros for
// deepcopy_stringarrays.
#if defined(CCURED) && ! defined(__DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD)

// Turn a trusted, null-terminated array of thin pointers to nul-terminated
// strings into an array that CCured can deal with.
// This function allocates a new array, and populates it with fat pointers
// to the input strings using __mkptr_string.  Note that this won't work with
// wild pointers because of the __mkptr_string.
// A better implementation would copy both the array and the underlying
// strings into a buffer provided by the caller so that wild pointers could be
// used and malloc could be avoided.
#pragma cilnoremove("__deepcopy_stringarray_from_compat")
#pragma ccuredpoly("__deepcopy_stringarray_from_compat")
__inline static
char** __deepcopy_stringarray_from_compat(char* __SAFE * __SAFE array_in) {
  int num_strings = 0;
  int i;
  // __MAYPOINTTOSTACK is unsound, but I don't see a better way to handle
  // arrays of stack-allocated strings.
  char* __MAYPOINTTOSTACK * new_array;
  char* __SAFE * __SAFE p;
  
  if(array_in == 0){
    return 0;
  }
  
  p = array_in;
  while (*p != 0){
    // we cannot do pointer arithmetic on SAFE pointers.
    p = __trusted_add(p, 1); //p++
    num_strings++;
  }
  num_strings++; //include the ending null in the count
  
  if(CCURED_HAS_EMPTY_MANGLING(* new_array)) {
    // No need to copy the array of strings
    return __mkptr_size(__trusted_deepcast(array_in),
			num_strings * sizeof(new_array[0]));
  } else {
    //fatten each pointer in the list.
    new_array = (char**)wrapperAlloc(num_strings * sizeof(new_array[0]));
    for (i = 0; i < num_strings; i++) {
      // Don't let CCured see the array access on a SAFE ptr.
      // p = array_in + i
      p = __trusted_add(array_in, i);
      new_array[i] = __mkptr_string(*p); // = __mkptr_string(array_in[i])
    }
  }
  return new_array;
}

#pragma ccuredpoly("__deepcopy_stringarray_to_compat")
__inline static
char* __SAFE * __SAFE __deepcopy_stringarray_to_compat(char** array_in) {
  int num_strings = __NUM_ELEMENTS(array_in);
  int i;
  char* __SAFE __MAYPOINTTOSTACK /*unsound*/ * __SAFE new_array;

  if(array_in == 0)  {
    return 0;
  }

  if(CCURED_HAS_EMPTY_MANGLING(* array_in)) {
    // No need to copy the array
    return __trusted_deepcast(__ptrof(array_in));
  } else {
    //fatten each pointer in the list.
    new_array = (char**)wrapperAlloc(num_strings * sizeof(*new_array) );
    for (i = 0; i < num_strings; i++)  {
      char * __SAFE __MAYPOINTTOSTACK /*unsound*/ * __SAFE  p_new_array 
	= __trusted_add(new_array, i);
      if (array_in[i] != (void *)0) { // NULL is not always defined!
        *p_new_array = __stringof(array_in[i]);
      } else {
        *p_new_array = (char*)0;
      }
    }
  }
  
  return new_array;
}

/* Use this macro inside _DEEPCOPY_FROM_COMPAT_PROTO only (to specify that a 
 * given field is a null-terminated sequence of nul-terminated strings field */
#define __DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD(fname)                     \
  fat->fname = __deepcopy_stringarray_from_compat(compat->fname)

/* Use this macro inside _DEEPCOPY_TO_COMPAT_PROTO only (to specify that a 
 * given field is a null-terminated sequence of nul-terminated strings field */
#define __DEEPCOPY_TO_COMPAT_STRINGARRAY_FIELD(fname)                       \
  __verify_nul(fat->fname);                                                 \
  compat->fname = __deepcopy_stringarray_to_compat(fat->fname);




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
