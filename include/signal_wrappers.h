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

#if defined(CCURED) && ! defined(SIGNAL_WRAPPERS_H_INCLUDED)
#define SIGNAL_WRAPPERS_H_INCLUDED

//a.k.a.  _sig_func_ptr (on Cygwin) or _sighandler_t (on Linux)
typedef void (* __ccured_sig_func_ptr) (int);

__inline static
__ccured_sig_func_ptr __SAFE __ptrof_signal(__ccured_sig_func_ptr fn)
{
  __ccured_sig_func_ptr __SAFE safe_fn = __ptrof_nocheck(fn);
  if( (int)safe_fn != -1 && safe_fn != 0 && (int)safe_fn != 1 ) {
    //Allow "bad" pointer values -1, 0 and 1 to be used. (signal will 
    //catch these.)  For anything else, call __ptrof to do the appropriate 
    //bounds and nonpointer checks:
    __ptrof(fn);
  }
  return safe_fn;
}

#pragma ccuredpoly("__mkfat_sighandler")
__inline static void* __mkfat_sighandler(void* in) {
  if((int)in == 1) {
    return __mkptr(in, 0);
  } else {
    return __mkptr_size(in, 1);
  }
}

#ifdef _SIGNAL_H
#pragma ccuredwrapper("signal_wrapper", of("signal"))
__inline static
__ccured_sig_func_ptr signal_wrapper(int signum, __ccured_sig_func_ptr fn)
{
  // someone wrote:  "UNSOUND (why? don't remember)"
  __ccured_sig_func_ptr null = 0;
  __ccured_sig_func_ptr __SAFE ret;
  ret = signal(signum, __ptrof_signal(fn));
  return __mkptr(ret, null);  // people don't call handlers directly (right?)
}
#endif


#ifdef _SIGNAL_H
__DEEPCOPY_FROM_COMPAT_PROTO(sigaction) {
  fat->sa_handler  = __mkfat_sighandler(compat->sa_handler);
  fat->sa_restorer = __mkfat_sighandler(compat->sa_restorer);
  // CCured will fill in the rest
}
#endif

#ifdef _SIGNAL_H
#pragma ccuredwrapper("sigaction_wrapper", of("sigaction"))
__inline static
int sigaction_wrapper(int __sig ,
                      struct sigaction  * __act , 
                      struct sigaction  * __oact ) {
  __DECL_COMPAT_STACK(p_act_compat, sigaction, __act);
  __DECL_COMPAT_STACK_NOCOPY(p_oact_compat, sigaction, __oact);
  
  int res = sigaction(__sig, p_act_compat, p_oact_compat);
  __COPYOUT_FROM_COMPAT(p_oact_compat, sigaction, __oact);
  return res;
}
#endif

#endif // CCURED && !SIGNAL_WRAPPERS_H_INCLUDED
