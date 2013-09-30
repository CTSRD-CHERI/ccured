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

#ifndef IO_WRAPPERS_H_INCLUDED
#define IO_WRAPPERS_H_INCLUDED

//matth:  these are wrappers for fcntl.h on Linux/Cygwin, and io.h on MSVC

#ifdef CCURED

 #ifdef __cplusplus
    extern "C" {
 #endif

#include "stdarg.h" //vararg macros for open_wrapper
#include "fcntl.h" // for O_CREAT (at least on MSVC)

// sm: moved read and write wrappers to unistd_wrappers.h because
// according to my man pages they are declared in unistd.h


// dsw: This seems to be an additional system call that has no man
// page.  It is declared in /usr/include/unistd.h
#if 0
  // gn: this proto conflicts with the declaration in unistd.h
  ssize_t pwrite(int __fd, __const char *__buf, size_t __n, __off_t __offset);
  #pragma ccuredwrapper("pwrite_wrapper", of("pwrite"));
  ssize_t pwrite_wrapper(int fid, char* buff, size_t size, __off_t offset)
  {
    if (__LENGTH(buff) <  size) { CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE); }
    return pwrite(fid, __ptrof(buff), size, offset);
  }
#endif


#pragma ccuredwrapper("unlink_wrapper", of("unlink"));
__inline static
int unlink_wrapper(char* path)
{
  __verify_nul(path);
  return unlink(__ptrof(path));
}

extern int open(const char* file, int flag, ...);
#if !defined CCURED_CURETYPE_wild
#pragma ccuredwrapper("open_wrapper", of("open"));
#pragma ccuredvararg("open_wrapper", sizeof(int))
__inline static
int open_wrapper (char *file, int oflag, ...) {
  __verify_nul(file);
  //matth: from the manpage for open on Linux:
  //   mode  should  always  be  specified when O_CREAT is in the
  //   flags, and is ignored otherwise.
  if(oflag & O_CREAT){
    va_list argptr;
    int mode;
    
    va_start( argptr, oflag );
    mode = va_arg( argptr, int );
    va_end( argptr );

    return open(__ptrof(file), oflag, mode);
  } else {
    return open(__ptrof(file), oflag); // Drop the permissions. Use O_CREAT if you want perms.
  }
}

#else 
//matth: old open wrappers.  We need these for curetype=wild, since that
// doesn't support implementation of vararg functions.

//BEWARE:  when using curetype=wild, any three-argument uses of open() must
// be replaced with open_with_mode.

#pragma ccuredwrapper("open_wrapper", of("open"));
#pragma ccuredvararg("open_wrapper", sizeof(int))
int open_wrapper (char *__file, int __oflag, ...) {
  __verify_nul(__file);
  return open(__ptrof(__file), __oflag); // Drop the permissions. Use open_with_mode if you want perms.
}

#pragma ccuredwrapper("open_with_mode_wrapper", of("open_with_mode"));
extern int open_with_mode(char * __file, int __oflag, int mode);
int open_with_mode_wrapper (char *__file, int __oflag, int mode) {
  __verify_nul(__file);
  return open(__ptrof(__file), __oflag, mode); 
}
#endif //defined CCURED_CURETYPE_wild

#pragma ccuredwrapper("rename_wrapper", of("rename"))
__inline static
int rename_wrapper(char const   * __old , char const   *  __new ) {
  __verify_nul(__old);
  __verify_nul(__new);
  return rename(__ptrof(__old), __ptrof(__new));
}

// sm: moved fstat_wrapper and stat_wrapper to stat_wrappers.h


#ifdef __cplusplus
 }
#endif
#endif // CCURED

#endif // !IO_WRAPPERS_H_INCLUDED
