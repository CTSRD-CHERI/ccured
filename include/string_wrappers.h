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

//wrappers for bzero, str*, and mem*

#if defined(CCURED) && ! defined(STRING_WRAPPERS_INCLUDED)
#define STRING_WRAPPERS_INCLUDED

  #ifdef __cplusplus
     extern "C" {
  #endif

  #pragma ccuredwrapper("strlen_wrapper", of("strlen"))
  __inline static
  unsigned int  strlen_wrapper(const char * s) {
    return __strlen(s);
  }

  #pragma ccuredwrapper("bzero_wrapper", of("bzero"))
  __inline static
  void bzero_wrapper (void *buff, unsigned int size) {
    if(size > 0) {
      __write_at_least(buff, size);
      bzero(__ptrof(buff), size);
    }
  }

  #pragma ccuredwrapper("strcpy_wrapper", of("strcpy"))
  __inline static
  char* strcpy_wrapper(char* dest, const char* src) 
  {
    char* result;
    int len = __strlen(src); 
    __copytags(dest, src, len);
    dest[len] = 0; // Will write the 0 as well, so make sure that's safe.
    
/*     if (len == 0) { */
/*       // sm: __ptrof(src) will fail, at least if 'src' is FSEQN; */
/*       // HACK: manually stash a nul in 'dest' */
/*       // TODO: fix this +1 business! */
/*       *dest = 0; */
/*       return dest; */
/*     } */

    result = strcpy((char*)__ptrof(dest), (char*)__ptrof(src));
    return (char*)__mkptr(result, dest);
  }

  #pragma ccuredwrapper("strncpy_wrapper", of("strncpy"))
  __inline static
  char* strncpy_wrapper(char* dest, const char* src, int n)
  {
    char* result;
    __strlen_n(src, n);

    // strncpy always writes 'n' bytes (padding with nuls if needed)
    __write_at_least(dest, n);

    // Note that result might not be null-terminated
    result = strncpy((char*)__ptrof(dest), (char*)__ptrof(src), n);
    return (char*)__mkptr(result, dest);
  }

  #pragma ccuredwrapper("strlcpy_wrapper", of("strlcpy"))
  __inline static
  size_t strlcpy_wrapper(char* dest, const char* src, int n)
  {
    int len = __strlen_n(src, n);
    if (len == n) len--; //src is not nul-terminated
    //now len points to the nul.

    __write_at_least(dest, len);
    dest[len] = 0; // Will write the 0 as well, so make sure that's safe.

    // dest will be null-terminated
    return strlcpy(__stringof(dest), __stringof(src), n);
  }


  #pragma ccuredwrapper("strcat_wrapper", of("strcat"))
  __inline static
  char* strcat_wrapper(char* dest, const char* src)
  {
    char* result;
    int len = __strlen(src);

    // the first character in dest that will be written.
    char* deststart = dest + __strlen(dest);

    __copytags(deststart, src, len);
    deststart[len] = 0; // Will write the 0 as well, so make sure that's safe.

    result = strcpy((char*)__ptrof(deststart), (char*)__ptrof(src));
    return (char*)__mkptr(result, dest);
  }

  #pragma ccuredwrapper("strncat_wrapper", of("strncat"))
  __inline static
  char* strncat_wrapper(char* dest, const char* src, int n)
  {
    char* result;
    int len = __strlen_n(src, n);

    // the first character in dest that will be written.
    char* deststart = dest + __strlen(dest);

    /*strncat writes a null at the end.  This means it writes up to n+1 
     * bytes, but the last one is a NULL, which is Ok to write at the end 
     * pointer. So we pretend that it writes only len bytes */
    __copytags(deststart, src, len); 
    deststart[len] = 0; // Will write the 0 as well, so make sure that's safe.

    result = strncat((char*)__ptrof(dest), (char*)__ptrof(src), n);
    return (char*)__mkptr(result, dest);
  }


  #pragma ccuredwrapper("strlcat_wrapper", of("strlcat"))
  __inline static
  size_t strlcat_wrapper(char* dest, const char* src, int n)
  {
    //assume we write the full buffer:
    __write_at_least(dest, n-1);
    dest[n-1] = 0; // Will write the 0 as well, so make sure that's safe.

    return strlcat((char*)__stringof(dest), (char*)__stringof(src), n);
  }


  #pragma ccuredwrapper("strchr_wrapper", of("strchr"))
  __inline static
  char* strchr_wrapper(const char* s, int chr)
  {
    char* result;
    result = strchr((char*)__stringof(s), chr);
    return (char*)__mkptr(result, s);
  }

  #pragma ccuredwrapper("strrchr_wrapper", of("strrchr"))
  char* strrchr_wrapper(const char* s, int chr)
  {
    char* result;
    result = strrchr((char*)__stringof(s), chr);
    return (char*)__mkptr(result, s);
  }


  #pragma ccuredwrapper("strdup_wrapper", of("strdup"))
  __inline static
  char *strdup_wrapper(const char *s)
  {
    int len = __strlen(s);
    char *result = (char*)malloc(len + 1);
    if (result == 0){
	return (char*)0;
    }
    strcpy((char*)__ptrof_nocheck(result), (char*)__ptrof(s));
    __copytags(result, s, len);
    return result;
    
    /* matth: we can't call the real strdup,
      because it uses a different malloc than we do.
      (we wouldn't be able to free it.)
    char* result = strdup(__ptrof(s));
    return __mkptr_size(result, len+1);
    */
  }

  #pragma ccuredwrapper("strcasecmp_wrapper", of("strcasecmp"))
  int strcasecmp_wrapper(const char* s1, const char* s2)
  {
    return strcasecmp((char*)__stringof(s1), (char*)__stringof(s2));
  }

  #pragma ccuredwrapper("strcmp_wrapper", of("strcmp"))
  __inline static
  int strcmp_wrapper(const char* s1, const char* s2)
  {
    return strcmp((char*)__stringof(s1), (char*)__stringof(s2));
  }

  #pragma ccuredwrapper("strncasecmp_wrapper", of("strncasecmp"))
  int strncasecmp_wrapper(const char* s1, const char* s2, unsigned int n)
  {
    if (__LENGTH(s1) < n){
      //if s1 is shorter than n, make sure it's nul-terminated.
      __verify_nul(s1);
    }
    if (__LENGTH(s2) < n){
      __verify_nul(s2);
    }
    return strncasecmp((char*)__ptrof(s1), (char*)__ptrof(s2), n);
  }


  #pragma ccuredwrapper("strncmp_wrapper", of("strncmp"))
  __inline static
  int strncmp_wrapper(const char* s1, const char* s2, unsigned int n)
  {
    if (__LENGTH(s1) < n){
      //if s1 is shorter than n, make sure it's nul-terminated.
      __verify_nul(s1);
    }
    if (__LENGTH(s2) < n){
      __verify_nul(s2);
    }
    return strncmp((char*)__ptrof(s1), (char*)__ptrof(s2), n);
  }

  #pragma ccuredwrapper("strpbrk_wrapper", of("strpbrk"))
  __inline static
  char* strpbrk_wrapper(const char* str, const char* accept_arg)
  {
    char* res;
    res = strpbrk((char*)__stringof(str), (char*)__stringof(accept_arg));
    return (char*)__mkptr(res, str);
  }

  #pragma ccuredwrapper("strsep_wrapper", of("strsep"))
  __inline static 
  char *strsep_wrapper(char **stringp, const char *delim)
  {
    char * res;
    if (stringp == NULL || *stringp == NULL) {
      return (char *)0;
    } else {
      //tmp stands for *stringp in the call to strsep.
      char * __SAFE tmp = __stringof(*stringp);
      res = __mkptr(strsep(&tmp, __stringof(delim)),
		    *stringp);
      *stringp = __mkptr(tmp, *stringp);
      return res;
    } 
  } 

  #pragma ccuredwrapper("strtoul_wrapper", of("strtoul"))
#include <stdlib.h>
  __inline static unsigned long 
  strtoul_wrapper(char * __restrict nptr , char ** __restrict endptr , int
      __base ) 
  {
    if (endptr != NULL) {
      char* __SAFE tmp = __ptrof(*endptr);
      //Make sure we pass a pointer to a safe pointer as the second argument.
      //tmp stands for *endptr in the call to strtoul.
      unsigned long val = strtoul(__stringof(nptr), &tmp, __base); 
      *endptr = __mkptr(tmp, *endptr);
      return val;
    } else {
      return strtoul(__stringof(nptr), 0, __base); 
    }
  } 

  // matth:  strtok is UNSOUND, because there are no guarantees that the
  // string will still be on the stack during the next call.
  static const char * saved_str __MAYPOINTTOSTACK = NULL; 

  #pragma ccuredwrapper("strtok_wrapper", of("strtok"))
  __inline static
  char* strtok_wrapper(char* str, const char* delim)
  {
    char* res;
    if (str != NULL){
      __verify_nul((void*)str);
      saved_str = str;
    }
    res = strtok((char*)__ptrof((void*)str), (char*)__stringof((void*)delim));
    return (char*)__mkptr(res, (void*)saved_str);
  }

  #pragma ccuredwrapper("strtok_r_wrapper", of("strtok_r"))
  __inline static
  char* strtok_r_wrapper(char* str, const char* delim,char ** ptrptr)
  {
      if (str != NULL) {
        __verify_nul(str);
      }

    //Create a local, SAFE copy of ptrptr. 
    char* __SAFE thin_ptrptr = __ptrof(*ptrptr);
 
    char* res = strtok_r(__ptrof(str), __stringof(delim), &thin_ptrptr);
    char* base = str == NULL ? *ptrptr : str;

    //Copy the saved pointer back to ptrptr
    *ptrptr = __mkptr(thin_ptrptr, base);

    return (char*)__mkptr(res, base);
  }

  /*
  #define IS_WILD(p) (ccured_kind_of(p) & 128)
  #pragma ccuredwrapper("strerror_wrapper", "strerror")
  char* strerror_wrapper(int errno)
  {
    char* __SAFE safe_res;
    char* null = 0;
    char* res;
    //res = __mkptr(strerror(errno), null);
    safe_res = strerror(errno);
    if(IS_WILD(res)){
      //fatten the string:
      int len = strlen(safe_res);
      char *res = (char*)malloc(len + 1);
      if (res == 0){
	  return (char*)0;
      }
      printf("wild\n");
      strcpy(__ptrof_nocheck(res), safe_res);
      __write_at_least(res, len);
    }
    else {
      res = __mkptr(safe_res, null);
    }
    //__endof(res);
    return res;
  }
  */


  #pragma ccuredwrapper("memcmp_wrapper", of("memcmp"))
  __inline static
  int memcmp_wrapper(const void* s1, const void* s2, size_t n)
  {
    if (__LENGTH((void*)s1) < n){
      CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
    }
    if (__LENGTH((void*)s2) < n){
      CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE);
    }
    return memcmp(__ptrof((void*)s1), __ptrof((void*)s2), n);
  }

  #pragma ccuredwrapper("memset_wrapper", of("memset"))
  __inline static
  void* memset_wrapper(void* buffer, int c, size_t size)
  {
    if (size) {
      __write_at_least(buffer, size);
      memset(__ptrof(buffer), c, size);
    }
    return buffer;
  }

  #pragma ccuredwrapper("memmove_wrapper", of("memmove"))
  __inline static
  void* memmove_wrapper(void* dest, const void* src, size_t size)
  {
    if (size) {
      __copytags(dest, src, size); //checks the lengths of dest, src
      memmove(__ptrof(dest), (void*)__ptrof(src), size);
    }

    return dest;
  }

  #pragma ccuredwrapper("memcpy_wrapper", of("memcpy"))
  __inline static
  void* memcpy_wrapper(void * dest, const void* src, size_t size)
  {
    if (size) {    // sm: added check b/c sftpd/provider calls with (null,null,0)
      __copytags(dest, (void*)src, size);
      memcpy(__ptrof(dest), (const void*)__ptrof((void*)src), size);
    }

    return dest;
  }
                
  // sm: testcase is small2/strerror1.c, requiring strerror_F
  #pragma ccuredwrapper("strerror_wrapper", of("strerror"))
  __inline static
  char *strerror_wrapper(int errnum)
  {
    char *ret = strerror(errnum);
    return __mkptr_string(ret);
  }

  #pragma ccuredwrapper("strstr_wrapper", of("strstr"))       
  __inline static
  char * strstr_wrapper(char const   *  __haystack,
                        char const   * __needle) {
    char* res;
    res = strstr((char*)__stringof(__haystack), (char*)__stringof(__needle));
    return (char*)__mkptr(res, __haystack);
  }
       
  #pragma ccuredwrapper("memchr_wrapper", of("memchr"))     
  __inline static
  void *memchr_wrapper (const void *s, int c, size_t n)
  {
    void* result;
    __read_at_least(s, n);
    result = memchr(__ptrof(s), c, n);
    return __mkptr(result, s);
  }

  #ifdef __cplusplus
     }
  #endif
#endif // CCURED









