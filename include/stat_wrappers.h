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

#if defined(CCURED) && ! defined(STAT_WRAPPERS_H_INCLUDED)
#define STAT_WRAPPERS_H_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif


// matth: what files should these go in?
// gn: sys/stat.h
// sm: ok, there in stat_wrappers.h now

#pragma ccuredwrapper("fstat_wrapper", of("fstat"));
__inline static
int fstat_wrapper(int fid, struct stat* buff)
{
  //__write_at_least(buff, sizeof(struct stat));
  return fstat(fid, __ptrof(buff));
}

#pragma ccuredwrapper("stat_wrapper", of("stat"));
__inline static
int stat_wrapper(char* path, struct stat* buff)
{
  //__write_at_least(buff, sizeof(struct stat));
  __verify_nul(path);
  return stat(__ptrof(path), __ptrof(buff));
}

//some newer lib versions treat stat as a wrapper around xstat, so we need
//the wrapper here. 
#pragma ccuredwrapper("__xstat_wrapper", of("__xstat"));
__inline static
int __xstat_wrapper (int __ver, __const char *__filename,
		    struct stat *__stat_buf)
{
  //__write_at_least(__stat_buf, sizeof(*__stat_buf));
  return __xstat(__ver, __stringof(__filename), __ptrof(__stat_buf));
}


#ifdef __cplusplus
}
#endif

#endif // CCURED
