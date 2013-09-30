
#ifndef LIBGEN_WRAPPERS_H
#define LIBGEN_WRAPPERS_H


#pragma ccuredwrapper("dirname_wrapper", of("dirname"));
__inline static
char* dirname_wrapper(char* path)
{
  return __mkptr_string(dirname(__stringof(path)));
}

#pragma ccuredwrapper("__xpg_basename_wrapper", of("__xpg_basename"));
__inline static
char* __xpg_basename_wrapper(char* path)
{
  return __mkptr_string(__xpg_basename(__stringof(path)));
}

#endif // LIBGEN_WRAPPERS_H
