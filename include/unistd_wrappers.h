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

#if defined(CCURED) && ! defined (UNISTD_WRAPPERS_INCLUDED)
#define UNISTD_WRAPPERS_INCLUDED

#include "functions/deepcopy_stringarray.h"
#include <malloc.h>


#pragma ccuredwrapper("execv_wrapper", of("execv"))
__inline static
int execv_wrapper(char *path, char **argv)
{
  int ret;
  char * __SAFE * thinArgv;
  void * e = __endof(argv);

  __verify_nul(path);
  thinArgv = __deepcopy_stringarray_to_compat(argv);

  ret = execv(__ptrof(path), __ptrof(thinArgv));

  // execv doesn't normally return, but if it does, we shouldn't
  // leak memory
  free_wrapper(thinArgv);

  return ret;
}

//execvp behaves like execv, but also searches the path.  
//So the wrapper is essentially identical.
#pragma ccuredwrapper("execvp_wrapper", of("execvp"))
__inline static
int execvp_wrapper(char *path, char **argv)
{
  int ret;
  char * __SAFE * thinArgv;
  void * e = __endof(argv); //force argv to carry a length, for __deepcopy_...

  __verify_nul(path);
  thinArgv = __deepcopy_stringarray_to_compat(argv);

  ret = execvp(__ptrof(path), __ptrof(thinArgv));

  // execvp doesn't normally return, but if it does, we shouldn't
  // leak memory
  free_wrapper(thinArgv);

  return ret;
}

#pragma ccuredwrapper("execve_wrapper", of("execve"))
__inline static
int execve_wrapper(char *path, char **argv, char **envp)
{
  int ret;
  char * __SAFE * thinArgv;
  char * __SAFE * thinEnvp;

  __verify_nul(path);
  thinArgv = __deepcopy_stringarray_to_compat(argv);
  thinEnvp = __deepcopy_stringarray_to_compat(envp);

  ret = execve(__ptrof(path), __ptrof(thinArgv), __ptrof(thinEnvp));

  free_wrapper(thinArgv);
  free_wrapper(thinEnvp);
  return ret;
}

struct __ccured_execl_arguments { char * __SAFE arg; };
#pragma ccuredvararg("execl", sizeof(struct __ccured_execl_arguments));
#pragma ccuredvararg("execlp", sizeof(struct __ccured_execl_arguments));
#pragma ccuredvararg("execle", sizeof(struct __ccured_execl_arguments));

#pragma ccuredwrapper("getlogin_wrapper", of("getlogin"))
__inline static
char *getlogin_wrapper(void)
{
  return __mkptr_string( getlogin() );
}

#pragma ccuredwrapper("ttyname_wrapper", of("ttyname"))
__inline static
char *ttyname_wrapper(int filedes)
{
  return __mkptr_string( ttyname(filedes) );
}


//matth: Sendmail defines its own getopt(), and this wrapper just confuses it.
#ifndef NO_GETOPT_WRAPPER

// wrapper for getopt(); testcase is small2/getopt.c
#pragma ccuredwrapper("getopt_wrapper", of("getopt"))
extern char* ccured_get_optarg(void);

__inline static
int getopt_wrapper(int argc, char * * argv, const char* optstring)
{
  char * __SAFE * thinArgv;
  int ret;

  // make sure argv[0..argc-1] is accessible
  __read_at_least(argv, argc * sizeof(*argv));

  // make sure 'optind' is reasonable; if it's not, the user can
  // trigger a memory safety violation, apparently due to a mistake in
  // the libc implementation (at least in glibc-2.2.3) of getopt, not
  // checking for this condition itself (since it clearly has the
  // necessary information to make the check)
  if (optind > argc) {
    CCURED_FAIL_STR("you have to reset 'optind' between sets of calls to getopt()"
                FILE_AND_LINE);
  }

  // make some thin string pointers for getopt to read; apparently
  // the implementation doesn't retain pointers directly into argv,
  // but rather maintains state in 'optind', so it's safe to create
  // new ones (and free them) for each call
  thinArgv = __deepcopy_stringarray_to_compat(argv);
  __verify_nul(optstring);
  ret = getopt(argc, thinArgv, __ptrof(optstring));
  free_wrapper(thinArgv);

  /* getopt() will have set optarg. But the program might be using another
   * optarg(_f, _q, etc.).  We copy it there.  This requires that ccuredlib.c
   * include several (mangled name) definitions of optarg. */
  optarg = __mkptr_string(ccured_get_optarg());
  return ret;
}

#endif // NO_GETOPT_WRAPPER

// sm: moved read and write wrappers from io_wrappers.h because
// according to my man pages they are declared in unistd.h; a test
// case exposing this is small2/getaddrinfo, which does not
// #include io.h but does #include unistd.h and uses read() in a
// way that requires a wrapper
#pragma ccuredwrapper("read_wrapper", of("read"));
__inline static
int read_wrapper(int fid, char* buff, unsigned int size)
{
  __write_at_least(buff, size);
  return read(fid, __ptrof(buff), size);
}

#pragma ccuredwrapper("write_wrapper", of("write"));
__inline static
int write_wrapper(int fid, const char* buff, unsigned int size)
{
  if (__LENGTH(buff) <  size) { CCURED_FAIL(FAIL_UBOUND  FILE_AND_LINE); }
  return write(fid, __ptrof(buff), size);
}


// wrapper for getusershell(), which returns lines from /etc/shells
// one at a time.  looks sound even if this returns a pointer to a
// static area (as it no doubt does) because the user won't ever get a
// pointer that can be used to write beyond whatever the true end is
#pragma ccuredwrapper("getusershell_wrapper", of("getusershell"))
__inline static
char *getusershell_wrapper()
{
  return __mkptr_string(getusershell());
}


#if 0
// matth: crypt is defined in crypt.h, not unistd.h, so I moved this to
// crypt_wrappers.h

# ifdef __CYGWIN__
//matth: Cygwin doesn't define crypt() in unistd.h
#  include <crypt.h>
# endif //__CYGWIN__

// wrapper for crypt(), which computes a cryptographic hash of its
// first two arguments
#pragma ccuredwrapper("crypt_wrapper", of("crypt"))
__inline static
char *crypt_wrapper(char const *key, char const *salt)
{
  __verify_nul(key);
  __verify_nul(salt);
  return __mkptr_string(crypt(__ptrof(key), __ptrof(salt)));
}

#endif //0


#endif // CCURED

