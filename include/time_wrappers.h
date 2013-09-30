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

#ifndef TIME_WRAPPERS_H_INCLUDED
#define TIME_WRAPPERS_H_INCLUDED

#ifdef CCURED


#if defined __CYGWIN__ || defined __time_t_defined

#pragma ccuredwrapper("time_wrapper", of("time"));
__inline static
time_t time_wrapper(time_t* timer){
  extern time_t time(time_t *t);
  if(timer != 0){
    __write_at_least(timer, sizeof(time_t));
  }
  return time(__ptrof(timer));
}

// sm: there a subtle problem with this, because time.h doesn't
// always declare ctime().  I think the right solution is to put
// this wrapper right alongside ctime's declaration, but for now
// I'm just going to live with the gcc warning..
#pragma ccuredwrapper("ctime_wrapper", of("ctime"));
__inline static
char* ctime_wrapper(const time_t* timer)
{ 
  extern char *ctime(const time_t *timep);
  time_t *thinTimer = __ptrof(/*const_cast*/(time_t*)timer);
  char *thinRet = ctime(thinTimer);
  return __mkptr_string(thinRet);
}

#endif // CCURED
#endif /* __CYGWIN__ or __time_t defined */
#endif // TIME_WRAPPERS_H_INCLUDES



// It seems that not all the time you include time.h, it defines struct tm.
// It seems that if I find _TIME_H defined then struct tm should be
// available. 
#if defined(CCURED) && ! defined(ASCTIME_WRAPPER_INCLUDED) && defined(_TIME_H)
#define ASCTIME_WRAPPER_INCLUDED 1
#pragma ccuredwrapper("asctime_wrapper", of("asctime")) 
__inline static
char *asctime_wrapper(const struct tm *timep) {
  extern char *asctime(const struct tm *timep);
  struct tm *thinTimep = __ptrof(timep);
  char *thinRet = asctime(thinTimep);
  return __mkptr_string(thinRet);
}

#pragma ccuredwrapper("localtime_wrapper", of("localtime"));
__inline static
struct tm * __SAFE localtime_wrapper(const time_t* timep){
  return __mkptr_size(localtime(__ptrof(timep)), sizeof(struct tm));
}

#endif
