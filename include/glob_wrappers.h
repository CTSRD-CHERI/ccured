// glob_wrappers.h
// wrapper for glob() and globfree()
// see copyright notice at end of file

// original author: Scott (smcpeak@cs)
// testcase: cil/test/small2/glob.c

#ifndef GLOB_WRAPPERS_H_INCLUDED
#define GLOB_WRAPPERS_H_INCLUDED

#ifdef CCURED                   // omit all of this when not curing

#include <stddef.h>             // NULL, size_t
#include <stdlib.h>             // malloc
#include <string.h>

#include "functions/deepcopy_stringarray.h"

// GN: this is not needed since CCured will create such a copy
//struct libc_glob_t {
//  // these fields are documented in the man page; the comments
//  // beside them came from libc's header file
//  size_t gl_pathc;         // Count of paths matched so far
//  char **gl_pathv;         // List of matched pathnames.
//  size_t gl_offs;          // Slots to reserve in `gl_pathv'.
//
//  // the following fields are undocumented; this could be a problem,
//  // since if the number of fields change we could have a situation
//  // where insufficient space is allocated for the call into libc;
//  // so, my true_* entry points below accept an additional argument
//  // so I can check this at run-time
//  int gl_flags;
//  void (*gl_closedir)(void *);
//  void* (*gl_readdir)(void *);
//  void* (*gl_opendir)(char *);
//  int (*gl_lstat)(char * __restrict, void  *__restrict);
//  int (*gl_stat)(char * __restrict, void * __restrict);
//};


// entry points that are mapped by ccuredlib.c into calls to the
// real, underlying functions; I'll pass the size of glob_t also
// to protect against the new-field problem alluded to above
//int true_glob(const char *pattern, int flags,
//              int errfunc(const char *epath, int eerrno),
//              struct libc_glob_t *pglob, int pglob_size);
//void true_globfree(struct libc_glob_t *pglob, int pglob_size);


// user-callable wrapper for glob()
#pragma ccuredwrapper("glob_wrapper", of("glob"))
__inline static
int glob_wrapper(
  const char *pattern,      // pattern to match
  int flags,                // bitwise OR of some flags
  int errfunc(const char *epath, int eerrno),   // error function
  glob_t *pglob)            // OUT: structure into which results are stored
{
  // struct libc_glob_t libc_buf;     // buffer that libc will fill
  // No allocation will be done since we do not define the DEEPCOPY_TO_COMPAT
  __DECL_COMPAT_STACK_NOCOPY(p_libc_buf, glob_s, pglob);
  
  int ret;                         // return value from this func

  // check for flags that I do not (yet?) support, primarily because they
  // involve using the 'pglob' fields on *input*, whereas I want to be
  // able to ignore pglob's initial values
  if (flags &
       (GLOB_DOOFFS |       // reserve pglob->gl_offs slots at beginning
        GLOB_APPEND |       // append these results to a previous call's
        GLOB_ALTDIRFUNC)) { // use those extra, undocumented functions
    CCURED_FAIL_STR("unsupported flags passed to glob()"  FILE_AND_LINE);
  }

  // let the underlying function have a go; I just pass the error function
  // directly, on the premise that if any weirdness creeps in we'll get
  // a link failure because I've insufficiently isolated it
  // GN: we use the actual function. CCured should do the right thing
//  ret = true_glob(__stringof(/*const_cast*/(char*)pattern), flags, errfunc,
//                  &libc_buf, sizeof(libc_buf));
  ret = glob(__stringof(/*const_cast*/(char*)pattern), flags, errfunc,
             p_libc_buf);
                  
  if (ret == GLOB_NOMATCH) {
    // the man page doesn't say what happens in this case; I'll make
    // an educated guess
    pglob->gl_pathc = 0;
    pglob->gl_pathv = NULL;
    return ret;
  }
  
  if (ret != 0) {
    // any other error return should for sure ignore pglob, so in
    // particular, the program won't be surprised if the values
    // didn't change
    return ret;
  }
  
  // now it gets interesting: we've got to copy the results from the
  // underlying call into the buffer provided by the user
  __COPYOUT_FROM_COMPAT(p_libc_buf, glob_s, pglob);

  // ok, we're done with libc's results, so give them back
  // GN: we cannot, because we are being smart about what we copy and
  // what we do not copy. So some of the stuff from what libc gave us
  // we might still use
//  if(p_libc_buf->gl_pathv != pglob->gl_pathv) {
//    // We are in a wrapper, so this should be the true globfree
//    globfree(p_libc_buf);
//  }
  return ret;
}

__DEEPCOPY_FROM_COMPAT_PROTO(glob_s) {
  __DEEPCOPY_FROM_COMPAT_STRINGARRAY_FIELD(gl_pathv);
}

//
//  // count = pglob->gl_pathc = libc_buf.gl_pathc;                             
//  int count;                       // number of matches
//  int i;                           // loop counter
//  char const *src;                 // points at source strings
//  int count = 
//  // allocate the array of pointers; we allocate one extra because the
//  // [count] entry is supposed to be NULL
//  pglob->gl_pathv = (char**)malloc(sizeof(*(pglob->gl_pathv)) * (count+1));
//  
//  // copy each of the strings
//  for (i=0; i<count; i++) {
//    {                   
//      // need to do a little arithmetic behind CCured's back, otherwise
//      // it will turn libc_buf.gl_pathv into an FSEQ pointer
//      __NOCUREBLOCK
//      src = libc_buf.gl_pathv[i];
//    }
//    
//    // This provokes the following warning:
//    //   Warning: Allocation of string. Use FSEQN instead. (tmp25)
//    // I'm not sure precisely what this means, or what should be done
//    // about it (if anything).  The code appears to work despite the
//    // warning.  If I move this into the NOCUREBLOCK that silences the
//    // warning, but I wonder if it might have other unintended effects
//    // so I'm leaving this down here.
//    pglob->gl_pathv[i] = (char*)malloc(sizeof(char) * (strlen(src)+1));
//
//    strcpy(pglob->gl_pathv[i], src);
//  }
//
//  // ok, we're done with libc's results, so give them back
//  true_globfree(&libc_buf, sizeof(libc_buf));
//  
//  // all done!
//  return ret;
//}


#pragma ccuredwrapper("globfree_wrapper", of("globfree"))
__inline static
void globfree_wrapper(glob_t *pglob)
{ 
  int i;

  // make sure I can access the array
  if (pglob == NULL) {
    CCURED_FAIL(FAIL_NONPOINTER  FILE_AND_LINE);
  }
  __read_at_least(pglob->gl_pathv,
                  __ccured_mult_u32(sizeof(pglob->gl_pathv[0]),
                                    pglob->gl_pathc+1));

  // free the strings (as always, when we're actually trying to
  // be memory safe, these calls are no-ops and we rely on the
  // garbage collector instead); don't free the last one because
  // it should always be NULL
#ifndef CCURED
  // Gn: we get a free invalid pointer if we perform this free.
  // This is almost as if glob does not use our allocator :-)
  for (i=0; i < pglob->gl_pathc; i++) {
    free(pglob->gl_pathv[i]);
  }
#endif
  
  // free the array. This is a nop with the garbage collector.
  wrapperFree(__ptrof(pglob->gl_pathv));
  
  // restore CCured's invariant about pointers not pointing to
  // invalid memory
  pglob->gl_pathv = NULL;
}


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

#endif // CCURED

#endif // GLOB_WRAPPERS_H_INCLUDED
