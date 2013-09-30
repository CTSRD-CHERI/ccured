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

#if defined(CCURED) && ! defined(NETDB_WRAPPERS_H_INCLUDED)
#define NETDB_WRAPPERS_H_INCLUDED

#include "functions/deepcopy_stringarray.h"

#ifdef _GNUCC


//matth: turn a hostent of thin pointers into a hostent of fat pointers.
// Copies data from hcompat to an existing hostent structure.
__inline static
__DEEPCOPY_FROM_COMPAT_PROTO(hostent) {
  int num_addrs;
  int i;
  char * __SAFE * __SAFE p;

  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(h_name);
  __DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD(h_aliases);

  // The ones below will be done automatically
  // hp->h_addrtype = hlean->h_addrtype;
  // hp->h_length = hlean->h_length;

  p = compat->h_addr_list;
  num_addrs = 0;
  //h_addr_list is null-terminated
  while (*p != 0){
    //we need to do pointer arithmetic on SAFE pointers.
    p = __trusted_add(p, 1); //p++
    num_addrs++;
  }
  num_addrs++; //account for the null.

  //fatten each pointer in the address list.  (Each pointer points to an
  // array 4 characters (IPv4) or 16 characters (IPv6)).
  fat->h_addr_list = (char**)wrapperAlloc(num_addrs * sizeof(fat->h_addr_list[0]));
  for (i = 0; i < num_addrs; i++)
    {
      //p = &hlean->h_addr_list[i]
      p = __trusted_add(compat->h_addr_list, i);
      fat->h_addr_list[i] = __mkptr_size(*p, 
                                         compat->h_length);
    }
  
  return;
}


#pragma ccuredwrapper("gethostbyname_wrapper", of("gethostbyname"));
__inline static
struct hostent* gethostbyname_wrapper(const char * name) {
  struct hostent __COMPAT * hcompat;
  __verify_nul(name);
  hcompat = gethostbyname(__ptrof(name));
  // return ccured_fixhostent(hcompat);
  {
    __DECL_NEW_FROM_COMPAT(hres, hostent, hcompat);
    return hres;
  }
}

#pragma ccuredwrapper("gethostbyaddr_wrapper", of("gethostbyaddr"));
__inline static
struct hostent* gethostbyaddr_wrapper (const char * addr, int len, int type) {
  struct hostent __COMPAT * hcompat;
  __read_at_least(addr, len);
  hcompat = gethostbyaddr(__ptrof(addr), len, type);
  {
    __DECL_NEW_FROM_COMPAT(hres, hostent, hcompat);
    return hres;
  }
}

// struct hostent __COMPAT * gethostent_wrapper (void);
// GN: This non-static declaration for gethostent_wrapper was leading to
// merge errors.
#pragma ccuredwrapper("gethostent_wrapper", of("gethostent"));
__inline static
struct hostent* gethostent_wrapper (void)
{
  struct hostent __COMPAT * hcompat = gethostent();
  {
    __DECL_NEW_FROM_COMPAT(hres, hostent, hcompat);
    return hres;
  }
}

#if !defined(__CYGWIN__)
//
// reentrant versions:
//
// Note:  The __buf parameter is supposed to be used by the function to
// allocate the various arrays, etc that it needs.  However, we
// ignore the __buf parameter and use malloc instead, trading efficiency
// for safety
  #pragma ccuredwrapper("gethostbyname_r_wrapper", of("gethostbyname_r"))
  __inline static
  int gethostbyname_r_wrapper (__const char * __name,
                               struct hostent * __result_buf,
                               char * __buf,
                               size_t __buflen,
                               struct hostent ** __result,
                               int * __h_errnop)
  {
    struct hostent __COMPAT hlean;
    struct hostent __COMPAT * result_lean = &hlean;
    int res;
    //matth: __buf may be stack-allocated, which would cause problems when
    //we try to store heap pointers into it in ccured_fixhostent_r.
    //(For example, the h_aliases would be stored in the buffer, so we
    // wouldn't be able to store pointers to the them in the arrays we malloc.)
    //To work around this, just create a new, heap-allocated scratch space.
    //(Note: I'm not quite sure how this interactes with the garbage collector
    // if we hold a pointer to somewhere in the middle of scratch_space but
    // not the beginning.)
    char* scratch_space = wrapperAlloc(__buflen);
    //__write_at_least(__buf, __buflen);
    __verify_nul(__name);

    res = gethostbyname_r(__ptrof(__name),
                          (&hlean),
                          __ptrof(scratch_space),
                          __buflen,
                          (&result_lean),
                          __ptrof(__h_errnop) );
    if (result_lean == NULL) {
      *__result = NULL;
    } else {
      *__result = __result_buf;
      __COPYOUT_FROM_COMPAT(&hlean, hostent, __result_buf);
    }
    return res;
  }

  // sm: replaced __socklen_t with socklen_t, since the latter is portable
  #pragma ccuredwrapper("gethostbyaddr_r_wrapper", of("gethostbyaddr_r"))
  __inline static
  int gethostbyaddr_r_wrapper (__const void * __addr,
                               socklen_t __len,
                               int __type,
                               struct hostent * __result_buf,
                               char * __buf,
                               size_t __buflen,
                               struct hostent ** __result,
                               int *__restrict __h_errnop)
  {
    struct hostent __COMPAT hlean;
    struct hostent __COMPAT * result_lean = &hlean;
    int res;
    char* scratch_space = wrapperAlloc(__buflen);
    //__write_at_least(__buf, __buflen);
    __read_at_least(__addr,__len);
  
    res = gethostbyaddr_r(__ptrof(__addr),
                          __len,
                          __type,
                          &hlean,
                          __ptrof(scratch_space),
                          __buflen,
                          &result_lean,
                          __ptrof(__h_errnop) );
    if (result_lean == NULL) {
      *__result = NULL;
    } else {
      *__result = __result_buf;
      __COPYOUT_FROM_COMPAT(&hlean, hostent, __result_buf);
    }
    return res;
  }

  #pragma ccuredwrapper("gethostent_r_wrapper", of("gethostent_r"))
  __inline static
  int gethostent_r_wrapper (struct hostent * __result_buf,
                            char * __buf,
                            size_t __buflen,
                            struct hostent ** __result,
                            int *__restrict __h_errnop)
  {
    struct hostent __COMPAT hlean;
    struct hostent __COMPAT * result_lean = &hlean;
    int res;
    char* scratch_space = wrapperAlloc(__buflen);
    //__write_at_least(__buf, __buflen);
  
    res = gethostent_r(&hlean,
                       __ptrof(scratch_space),
                       __buflen,
                       &result_lean,
                       __ptrof(__h_errnop) );
    if (result_lean == NULL) {
      *__result = NULL;
    } else {
      *__result = __result_buf;
      __COPYOUT_FROM_COMPAT(&hlean, hostent, __result_buf);
    }
    return res;
  }

#endif // !defined(__CYGWIN__)


//
// SERVENT
//
//
/* Turn the servent from compat to fat */
__inline static
__DEEPCOPY_FROM_COMPAT_PROTO(servent) {
  int num_aliases;
  int i;
  
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(s_name);
  __DEEPCOPY_FROM_COMPAT_STRING_FIELD(s_proto);
  __DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD(s_aliases);
  
  return;
}

#pragma ccuredwrapper("getservbyname_wrapper", of("getservbyname"));
__inline static
struct servent* getservbyname_wrapper(const char * name, const char *proto)
{
  struct servent __COMPAT* ssafe;
  __verify_nul(name);
  __verify_nul(proto);
  ssafe = getservbyname(__ptrof(name), __ptrof(proto));
  {
    __DECL_NEW_FROM_COMPAT(res, servent, ssafe);
    return res;
  }
}

#if !defined(__CYGWIN__)

  #pragma ccuredwrapper("getservbyname_r_wrapper", of("getservbyname_r"));
  __inline static
  int getservbyname_r_wrapper (char * __name,
                               char * __proto,
                               struct servent * __result_buf,
                               char * __buf,
                               size_t __buflen,
                               struct servent ** __result) {
    struct servent __COMPAT ssafe;
    struct servent __COMPAT * result_lean = &ssafe;
    int res;
    char* scratch_space = wrapperAlloc(__buflen);
    __verify_nul(__name);
    __verify_nul(__proto);

    res = getservbyname_r(__ptrof(__name),
			  __ptrof(__proto),
			  (&ssafe),
			  __ptrof(scratch_space),
			  __buflen,
			  (&result_lean));
    if (result_lean == NULL) {
        *__result = NULL;
    } else {
        *__result = __result_buf;
        __COPYOUT_FROM_COMPAT(&ssafe, servent, __result_buf);
    }
    return res;
  }

#endif // !defined(__CYGWIN__)


#if !defined(__CYGWIN__)
    #pragma ccuredwrapper("getnameinfo_wrapper", of("getnameinfo"));
    __inline static
    int getnameinfo_wrapper(const struct sockaddr *sa, int salen,
                            char *host, int hostlen, 
                            char *serv, int servlen,
                            int flags)
    {
      __read_at_least(sa, salen);        // sm: changed from __write_at_least because, well, it's "const"!
      if (host && hostlen) {             // sm: null ptr or 0 len means no access will happen
        __write_at_least(host, hostlen);
      }
      if (serv && servlen) {             // sm: similar to 'host'
        __write_at_least(serv, servlen);
      }
      return getnameinfo(__ptrof(sa), salen, __ptrof(host), hostlen, 
                         __ptrof(serv), servlen, flags);
    }

    
    // sm: This file (netdb_wrappers.h) is kind of messy due to all
    // the various conditional compilation; so as an experiment I'll
    // put wrappers for individual functions (or groups of
    // closely-related functions) into their own file.  Then the
    // #include line here can be subject to conditional compilation
    // (and hence indented, etc.) while the #included file will be
    // free of those complications.
    #include "functions/getaddrinfo.h"

#endif // !defined(__CYGWIN__)

// weimer: for bind!
#pragma ccuredwrapper("getservbyport_wrapper", of("getservbyport"));
static __inline
struct servent *getservbyport_wrapper(int port, const char *proto) {
  struct servent __COMPAT * lean_answer;

  lean_answer = getservbyport(port, __ptrof(proto));

  return NULL; // return ccured_fixservent(lean_answer); 
} 

#endif // _GNUCC

#endif // CCURED


