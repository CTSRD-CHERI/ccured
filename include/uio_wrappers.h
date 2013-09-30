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

//Wrappers for readv and writev

#if defined(CCURED) && ! defined(UIO_WRAPPERS_INCLUDED)
#define UIO_WRAPPERS_INCLUDED

//a version of iovec that uses thin pointers:
#ifdef CCURED
# ifdef __CYGWIN__
struct iovec_SAFE {
	char* __SAFE iov_base;
	int iov_len;
};
# else
struct iovec_SAFE {
    void * __SAFE iov_base;     /* Pointer to data.  */
    size_t iov_len;     /* Length of data.  */
};
# endif
#endif


//matth: defined in ccuredlib.  (Aliases for the real readv and writev)
int true_readv(int fd, const struct iovec_SAFE* vec, int count);
int true_writev(int filedes, const struct iovec_SAFE *vector, int count);

#pragma ccuredwrapper("readv_wrapper", of("readv"))
__inline static
int readv_wrapper(int fd, const struct iovec* vec, int count)
{
    int i;
    struct iovec_SAFE* safevec = wrapperAlloc(count * sizeof(*safevec));
    for (i = 0; i < count; i++)
    {
        safevec[i].iov_base = 
            __ptrof(vec[i].iov_base);
        safevec[i].iov_len = vec[i].iov_len;
        __write_at_least(vec[i].iov_base, vec[i].iov_len);
    }
    return true_readv(fd, safevec, count);
}


#pragma ccuredwrapper("writev_wrapper", of("writev"))
__inline static
int writev_wrapper(int fd, const struct iovec* vec, int count)
{
    int i;
    struct iovec_SAFE* safevec = wrapperAlloc(count * sizeof(*safevec));
    for (i = 0; i < count; i++)
    {
        safevec[i].iov_base = 
            __ptrof(vec[i].iov_base);
        safevec[i].iov_len = vec[i].iov_len;
        __read_at_least(vec[i].iov_base, vec[i].iov_len);
    }
    return true_writev(fd, safevec, count);
}


#endif // CCURED

