
#ifndef SETJMP_WRAPPERS_H
#define SETJMP_WRAPPERS_H



  // Do not remove the type jmp_buf because it is used in ccured.h
#pragma cilnoremove("type jmp_buf")

  // And keep it as it is for the same reason
#pragma ccurednounroll("jmp_buf")

#endif // SETJMP_WRAPPERS_H
