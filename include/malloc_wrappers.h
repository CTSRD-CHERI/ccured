
#ifndef MALLOC_WRAPPERS_H
#define MALLOC_WRAPPERS_H


#pragma ccuredalloc("malloc", nozero, sizein(1))
  //matth: don't use ccuredalloc on realloc. We need to zero only part of the buffer.
#pragma ccuredpoly("realloc")
#pragma ccuredwrapper("realloc_wrapper", of("realloc"))
void *realloc_wrapper(void *b, int sz) {
  // Do the actual allocation
  void *res = realloc(__ptrof(b), sz);
  // Declare the actual result. Make sure we propagate the constraint that
  // b can go to the result
  void *result = b;

  result = __mkptr_size(res, sz);
  return result;
}


#pragma ccuredwrapper("free_wrapper", of("free"))
void free_wrapper(void *x) {
  free(__ptrof(x));
}

#pragma ccuredalloc("alloca", nozero, sizein(1))
#pragma ccuredalloc("calloc", zero, sizemul(1,2))


#endif // MALLOC_WRAPPERS_H
