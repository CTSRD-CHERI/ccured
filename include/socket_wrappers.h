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

#if defined(CCURED) && ! defined(SOCKET_WRAPPERS_H_INCLUDED)
#define SOCKET_WRAPPERS_H_INCLUDED


#ifdef _GNUCC
  // sm: needed for 'struct iovec', below; I tried simply moving some   
  // of the definitions into uio_wrappers.h, but that doesn't work because
  // the copy functions for msghdr need to know about 'iovec'
  #include <sys/uio.h>

  // the user simply has to pass a buffer in 'optval' that is at least
  // 'optlen' bytes long
  #pragma ccuredwrapper("setsockopt_wrapper", of("setsockopt"));
  __inline static
  int setsockopt_wrapper(int s, int level, int optname, void const* optval, int optlen)
  {
    __read_at_least(optval, optlen);
    return setsockopt(s, level, optname, __ptrof(optval), optlen);
  }

  #pragma ccuredwrapper("getsockopt_wrapper", of("getsockopt"));
  __inline static
  int getsockopt_wrapper(int s, int level, int optname, void* optval, int* optlen)
  {
    __write_at_least(optval, *optlen); //CCured makes sure optlen is not null.
    return getsockopt(s, level, optname, __ptrof(optval), __ptrof(optlen));
  }

  // same deal for bind
  #pragma ccuredwrapper("bind_wrapper", of("bind"));
  __inline static
  int bind_wrapper(int sockfd, void * my_addr, int addrlen)
  {
    __read_at_least(my_addr, addrlen);
    return bind(sockfd, (void*)__ptrof(my_addr), addrlen);
  }

  // connect is just like bind
  #pragma ccuredwrapper("connect_wrapper", of("connect"));
  __inline static
  int connect_wrapper(int sockfd, void *my_addr, int addrlen)
  {
    __read_at_least(my_addr, addrlen);
    return connect(sockfd, (void*)__ptrof(my_addr), addrlen);
  }

  // similar for accept, but length is value-result
  #pragma ccuredwrapper("accept_wrapper", of("accept"));
  __inline static
  int accept_wrapper(int s, void * addr, int *addrlen)
  {
    if (addr != NULL) {
      int res;
      //make sure the buffer is as long as the caller says it is:
      if (addrlen == NULL) {
        CCURED_FAIL(FAIL_NONPOINTER  FILE_AND_LINE);
      }
      __read_at_least(addr, *addrlen);
      res = accept(s, (void*)__ptrof(addr), __ptrof(addrlen));

      //clear the tags on the actual bits written.
      __write_at_least(addr, *addrlen);
      return res;
    }
    else {
        // addr is ignored when null
        return accept(s, (void*)0, (int*)0);
    }
  }


  // same as with accept
  //int getpeername(int s, void *name, int *namelen);
  #pragma ccuredwrapper("getpeername_wrapper", of("getpeername"));
  __inline static
  int getpeername_wrapper(int s, void * name, int *namelen)
  {
    int res;
    //make sure the buffer is as long as the caller says it is:
    __read_at_least(name, *namelen);

    res = getpeername(s, (void*)__ptrof(name), __ptrof(namelen));

    //clear the tags on the actual bits written.
    __write_at_least(name, *namelen);
    return res;
  }

  // identical to getpeername
  // int getsockname(int s, void *name, int *namelen);
  #pragma ccuredwrapper("getsockname_wrapper", of("getsockname"));
  __inline static
  int getsockname_wrapper(int s, void * name, int *namelen)
  {
    int res;
    //make sure the buffer is as long as the caller says it is:
    __read_at_least(name, *namelen);

    res = getsockname(s, (void*)__ptrof(name), __ptrof(namelen));

    //clear the tags on the actual bytes written.
    __write_at_least(name, *namelen);
    return res;
  }

//matth: I'm not sure why this is needed.
#if defined __CYGWIN__ && !defined socklen_t
#define socklen_t int
#endif

  // int sendto(int s, const void *msg, size_t len, int flags,
  //            const void *to, socklen_t tolen);
  #pragma ccuredwrapper("sendto_wrapper", of("sendto"));
  __inline static
  int sendto_wrapper(int s, const void *msg, size_t len, int flags,
                     const void *to, socklen_t tolen)
  {                                
    __read_at_least(msg, len);
    __read_at_least(to, tolen);
    return sendto(s, __ptrof(msg), len, flags, __ptrof(to), tolen);
  }

  // int select(int n, fd_set *readfds, fd_set *writefds,
  //            fd_set *exceptfds, struct timeval *timeout);
  #pragma ccuredwrapper("select_wrapper", of("select"));
  __inline static
  int select_wrapper(int n, fd_set *readfds, fd_set *writefds,
                     fd_set *exceptfds, struct timeval *timeout)
  {
    if (__ptrof(timeout)) {
      __write_at_least(timeout, sizeof(struct timeval));    // writes timeout
    }
    return select(n, __ptrof(readfds), __ptrof(writefds), 
                  __ptrof(exceptfds),
                  (struct timeval *)__ptrof(timeout));
  }

  // int recvfrom(int s, void *buf, size_t len, int flags,
  //              void *from, socklen_t *fromlen);
  #pragma ccuredwrapper("recvfrom_wrapper", of("recvfrom"));
  __inline static
  int recvfrom_wrapper(int s, void *buf, size_t len, int flags,
                       void *from, socklen_t *fromlen)
  {
    __write_at_least(buf, len);
    return recvfrom(s, __ptrof(buf), len, flags, __ptrof(from), __ptrof(fromlen));
  }

  // sm: int recv(int s, void *buf, size_t len, int flags);
  #pragma ccuredwrapper("recv_wrapper", of("recv"))
  __inline static
  int recv_wrapper(int s, void *buf, size_t len, int flags)
  {
    __write_at_least(buf, len);
    return recv(s, __ptrof(buf), len, flags);
  }

  // sm: int send(int s, const void *msg, size_t len, int flags);
  #pragma ccuredwrapper("send_wrapper", of("send"))
  __inline static
  int send_wrapper(int s, const void *msg, size_t len, int flags)
  {
    __read_at_least(msg, len);
    return send(s, __ptrof(msg), len, flags);
  }

__inline static
__DEEPCOPY_TO_COMPAT_PROTO(iovec) {
  compat->iov_base = __ptrof_nocheck(fat->iov_base);
}

__inline static
__DEEPCOPY_TO_COMPAT_PROTO(msghdr) {
  // We leave the msg_name and msg_control to CCured
  
  if(CCURED_HAS_EMPTY_MANGLING(* fat->msg_iov)) {
    // We do not need to copy the msg_iov array
    compat->msg_iov = __ptrof(fat->msg_iov);
  } else {
    int len = fat->msg_iovlen;
    int v;
    compat->msg_iov = wrapperAlloc(len * sizeof(compat->msg_iov[0])); 
    for (v=0; v<len; v++) {
      struct iovec __COMPAT *iptr = __trusted_add(compat->msg_iov, v);
      __deepcopy_iovec_to_compat(iptr, & fat->msg_iov[v]);
    } 
  }
}

__inline static
__DEEPCOPY_FROM_COMPAT_PROTO(iovec) {
  fat->iov_base = __mkptr_size(compat->iov_base, compat->iov_len);
}

__inline static
__DEEPCOPY_FROM_COMPAT_PROTO(msghdr) {
  fat->msg_name = __mkptr_size(compat->msg_name, compat->msg_namelen);
  fat->msg_control = __mkptr_size(compat->msg_control, compat->msg_controllen);

  if(CCURED_HAS_EMPTY_MANGLING(* fat->msg_iov)) {
    // We do not need to copy the msg_iov array
    fat->msg_iov = __mkptr_size(compat->msg_iov,
                                compat->msg_iovlen * sizeof(fat->msg_iov[0]));
  } else {
    int len = compat->msg_iovlen;
    int v;
    fat->msg_iov = wrapperAlloc(len * sizeof(fat->msg_iov[0])); 
    for (v=0; v<len; v++) {
      struct iovec __COMPAT *iptr = __trusted_add(compat->msg_iov, v);
      __deepcopy_iovec_from_compat(& fat->msg_iov[v], iptr);
    } 
  }
}


  #pragma ccuredwrapper("sendmsg_wrapper", of("sendmsg"))
  __inline static
  int sendmsg_wrapper(int s, const struct msghdr *fat_msg, int flags) {
    __DECL_COMPAT_STACK(lean_msg, msghdr, fat_msg);
    int result = sendmsg(s, lean_msg, flags);
    // We can now free the msg_iov (if it was allocated)
    if(lean_msg->msg_iov != fat_msg->msg_iov) {
      wrapperFree(lean_msg->msg_iov);
    }
    return result;
  }

  #pragma ccuredwrapper("recvmsg_wrapper", of("recvmsg"))
  __inline static
  int recvmsg_wrapper(int s, struct msghdr *fat_msg, int flags) {
    __DECL_COMPAT_STACK(lean_msg, msghdr, fat_msg);
    int result = recvmsg(s, lean_msg, flags);
    __COPYOUT_FROM_COMPAT(lean_msg, msghdr, fat_msg);
    if(lean_msg->msg_iov != fat_msg->msg_iov) {
      wrapperFree(lean_msg->msg_iov);
    }
    return result;
  } 

#endif // _GNUCC

#endif // CCURED

