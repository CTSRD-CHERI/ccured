// getaddrinfo.h
// wrappers for getaddrinfo() and freeaddrinfo()
// see copyright notice at end of file

// NOTE: please don't wrap this whole file in any conditional
// compilation directives; instead wrap the #include line in
// netdb_wrappers.h


// sm: This is my attempt to write a wrapper for getaddrinfo ... the
// particular mangling I'm trying to hit is: getaddrinfo_ssscfss_ss,
// which means simply that the 'ai_addr' pointer in 'addrinfo' is
// FSEQ:
//    struct addrinfo {
//       int ai_flags    ;
//       int ai_family    ;
//       int ai_socktype    ;
//       int ai_protocol    ;
//       socklen_t ai_addrlen    ;
//       fseqp_s_sockaddr  __FSEQ   ai_addr    ;         <----------
//       char *    ai_canonname    ;
//       struct addrinfo *    ai_next    ;
//    };
// So my wrapper will make a duplicate (deep) copy of the list,
// including copying the memory pointed to by 'ai_addr' so that I can
// then free the original list (though I'll be leaking the one I
// make).  One complication is I need a name for the 'addrinfo' that
// libc actually uses, i.e. without CCured's modified pointers; I
// achieve that by supposing that I can call the underlying
// getaddrinfo using the name true_getaddrinfo, which I'll make
// work by a simple thunk in ccuredlib.c.
//
// Update: 9/06/02 02:21: it appears to work!  
// test/small2/getaddrinfo.c is the testcase.
                             
// the struct that libc actually uses, containing only SAFE pointers
struct libc_addrinfo {
  int ai_flags;
  int ai_family;
  int ai_socktype;
  int ai_protocol;
  socklen_t ai_addrlen;
  struct sockaddr *ai_addr;
  char *ai_canonname;
  struct libc_addrinfo *ai_next;
};

int true_getaddrinfo(
  const char *node, const char *service,
  const struct libc_addrinfo *hints, struct libc_addrinfo **res);

void true_freeaddrinfo(struct libc_addrinfo *res);

//We call memcpy on two different arrays:
#pragma ccuredpoly("memcpy");

#pragma ccuredwrapper("getaddrinfo_wrapper", of("getaddrinfo"))
int getaddrinfo_wrapper(
  const char *node,                // name or address of a remote machine
  const char *service,             // port number, or service name
  const struct addrinfo *hints,    // read-only structure with hint information
  struct addrinfo **res)           // OUT: returns a pointer to a linked-list of addrinfo's
{
  struct libc_addrinfo libc_hints;    // hints I'll pass to libc
  struct libc_addrinfo *libc_res;     // result I get from libc
  struct libc_addrinfo *source;       // for walking down source list
  struct addrinfo *dest = NULL;       // for walking down destination list
  int len;                            // various uses
  int ret;                            // return value

  // make a shallow copy, since 'hints' won't go away during this call,
  // and 'true_getaddrinfo' won't keep any pointers to what I pass
  // (in fact, I expect the pointers here to be NULL, but I copy them
  // anyway since it should be safe)
  libc_hints.ai_flags     = hints->ai_flags;
  libc_hints.ai_family    = hints->ai_family;
  libc_hints.ai_socktype  = hints->ai_socktype;
  libc_hints.ai_protocol  = hints->ai_protocol;
  libc_hints.ai_addrlen   = hints->ai_addrlen;
  libc_hints.ai_addr      = __ptrof(hints->ai_addr);
  libc_hints.ai_canonname = __ptrof(hints->ai_canonname);
  libc_hints.ai_next      = NULL;     // getaddrinfo shouldn't look at this anyway

  // I suppose I should check whether 'node' and 'service' are valid
  // pointers, but the only way I know to do that is to use e.g. __strlen,
  // but ccuredwrappers.h claims that will force them to be FSEQ, whereas
  // right now they're SAFE and I think I want them to remain so...
  ret = true_getaddrinfo(__ptrof(node), __ptrof(service),
                         &libc_hints, &libc_res);
  if (ret != 0) {
    return ret;      // error condition
  }

  // now the fun begins: make a deep copy of a list.  the source head
  // is pointed to by 'libc_res', and ultimately the destination head
  // will be pointed to by '*res'
  *res = NULL;
  for (source = libc_res; source != NULL; source = source->ai_next) {
    // allocate a node
    struct addrinfo *newNode = (struct addrinfo *)wrapperAlloc(sizeof(*dest));

    if (!dest) {
      // begin the list
      *res = newNode;
    }
    else {
      // continue the list
      dest->ai_next = newNode;
    }
    dest = newNode;

    // copy the fields of 'source' to 'dest'
    dest->ai_flags      = source->ai_flags;
    dest->ai_family     = source->ai_family;
    dest->ai_socktype   = source->ai_socktype;
    dest->ai_protocol   = source->ai_protocol;
    dest->ai_addrlen    = source->ai_addrlen;

    len = source->ai_addrlen;
    dest->ai_addr = (struct sockaddr *)wrapperAlloc(len);
    // This calls the library's memcpy directly:
    memcpy(__ptrof(dest->ai_addr), source->ai_addr, len);

    if (source->ai_canonname) {
      len = strlen(source->ai_canonname)+1;
      dest->ai_canonname = (char*)wrapperAlloc(len);
      memcpy(__ptrof(dest->ai_canonname), source->ai_canonname, len);
    }
    else {
      dest->ai_canonname = NULL;
    }

    // initialize the 'next' pointer to NULL
    dest->ai_next = NULL;
  }

  // finally, deallocate the underlying return value since we've
  // now made copies of everything it contained
  true_freeaddrinfo(libc_res);

  return ret;
}

extern void free_wrapper(void*);
#pragma ccuredwrapper("freeaddrinfo_wrapper", of("freeaddrinfo"))
void freeaddrinfo_wrapper(struct addrinfo *res)
{
  // I'll walk the list and pass things to 'free', but since
  // free() is a no-op under CCured this will have no effect
  while (res) {
    struct addrinfo *next = res->ai_next;

    free_wrapper(res->ai_addr);
    if (res->ai_canonname) {
      free_wrapper(res->ai_canonname);
    }
    free_wrapper(res);

    res = next;
  }
}

#pragma ccuredwrapper("gai_strerror_wrapper", of("gai_strerror"))
const char* gai_strerror_wrapper(int code) {
  return __mkptr_string(gai_strerror(code));
}

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
