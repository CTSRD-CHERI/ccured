// pwd_wrappers.h
// wrappers for functions in /usr/include/pwd.h
// see copyright notice at end of file

// original author: scott

#ifndef PWD_WRAPPERS_H_INCLUDED
#define PWD_WRAPPERS_H_INCLUDED

#ifdef CCURED

#include <string.h>             // strlen, memcpy

#ifdef __CYGWIN__
# define __UID_T uid_t
#else
# define __UID_T __uid_t
#endif

// possible designs:
//   (1) allocate a new passwd object each time
//   (2) allocate one, with pointers to some large buffers
//   (3) allocate one, with pointers into one large buffer

// (1) unnecessarily leaks memory.  Client code should plan on
// results from one call being trashed by the next.  (2) wastes a bit
// by not allowing fields to share excess, and introduces a problem of
// initializing the one object.  (3) is space-efficient and requires
// no separate initialization.

//matth: here's a simple (but incomplete) solution to the problem of wrapping
//pwd functions.  Rather than copying the strings, just create fat pointers
//to the existing strings.  However, this won't work if wild strings are needed.
//In that case, replace the "__mkptr_string" references below with a function like 
//__GETPWNAM_COPY_FIELD above.


__DEEPCOPY_FROM_COMPAT_PROTO(passwd) {
  // CCured will fill in the remaining fields
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(pw_name);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(pw_passwd);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(pw_gecos);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(pw_dir);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(pw_shell);
}

// Keep here the results
static struct passwd my_passwd_result;

#pragma ccuredwrapper("getpwnam_wrapper", of("getpwnam"))
__inline static
struct passwd *getpwnam_wrapper(const char *name)
{
  struct passwd __COMPAT *libc_result;

  // call underlying function
  __verify_nul(name);
  libc_result = getpwnam(__ptrof(name));

  if (libc_result == NULL)
    return NULL;

  __COPYOUT_FROM_COMPAT(libc_result, passwd, &my_passwd_result);
  return &my_passwd_result;
}


#pragma ccuredwrapper("getpwuid_wrapper", of("getpwuid"))
__inline static
struct passwd *getpwuid_wrapper(__UID_T uid)
{
  // call underlying function
  struct passwd __COMPAT *libc_result = getpwuid(uid);
  if (libc_result == NULL)
    return NULL;

  __COPYOUT_FROM_COMPAT(libc_result, passwd, &my_passwd_result);
  return & my_passwd_result;
}

#pragma ccuredwrapper("getpwent_wrapper", of("getpwent"))
__inline static
struct passwd *getpwent_wrapper(void)
{
  struct passwd __COMPAT *libc_result = getpwent();
  if (libc_result == NULL)
    return NULL;

  __COPYOUT_FROM_COMPAT(libc_result, passwd, & my_passwd_result);
  return & my_passwd_result;
}


#endif // CCURED

#endif // PWD_WRAPPERS_H_INCLUDED

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
