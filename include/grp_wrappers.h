// arg_wrappers.h
// wrappers for functions in /usr/include/grp.h
// see copyright notice at end of file


#ifndef GRP_WRAPPERS_H_INCLUDED
#define GRP_WRAPPERS_H_INCLUDED

#ifdef CCURED

#include "functions/deepcopy_stringarray.h"

__DEEPCOPY_FROM_COMPAT_PROTO(group) {
  // CCured will fill in the remaining fields
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(gr_name);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(gr_passwd);
  // The member list is a null-terminated array of strings
  __DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD(gr_mem);
}
// Will put here the results
static struct group my_group_result;

#pragma ccuredwrapper("getgrnam_wrapper", of("getgrnam"))
__inline static
struct group *getgrnam_wrapper(const char* name)
{
  struct group __COMPAT *libc_result;

  // call underlying function
  __verify_nul(name);
  libc_result = getgrnam(__ptrof(name));
  __COPYOUT_FROM_COMPAT(libc_result, group, &my_group_result);
  if (libc_result == NULL)
    return NULL;

  return &my_group_result;
}

#ifdef __CYGWIN__
# define __GID_T gid_t
#else
# define __GID_T __gid_t
#endif

#pragma ccuredwrapper("getgrgid_wrapper", of("getgrgid"))
__inline static
struct group *getgrgid_wrapper(__GID_T gid)
{
  // call underlying function
  struct group __COMPAT *libc_result = getgrgid(gid);
  if (libc_result == NULL)
    return NULL;

  __COPYOUT_FROM_COMPAT(libc_result, group, &my_group_result);
  return &my_group_result;
}


#pragma ccuredwrapper("getgrent_wrapper", of("getgrent"))
__inline static
struct group *getgrent_wrapper(void)
{
  // call underlying function
  struct group __COMPAT *libc_result = getgrent();
  if (libc_result == NULL)
    return NULL;

  __COPYOUT_FROM_COMPAT(libc_result, group, &my_group_result);
  return &my_group_result;
}

#endif // CCURED

#endif // GRP_WRAPPERS_H_INCLUDED

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
