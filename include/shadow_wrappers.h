#if defined CCURED && !defined SHADOW_WRAPPERS_H
#define SHADOW_WRAPPERS_H

//redeclare these to add compatibility annotations:

extern struct spwd * __SPLIT 
  getspent (void) __COMPAT;
extern struct spwd * __SPLIT 
  getspnam (__const char * __SPLIT __name) __COMPAT;
extern struct spwd * __SPLIT 
  sgetspent (__const char * __SPLIT __string) __COMPAT;
extern struct spwd * __SPLIT 
  fgetspent (FILE * __SPLIT __stream) __COMPAT;
extern int 
  putspent (__const struct spwd * __SPLIT __p, FILE * __SPLIT __stream)
  __COMPAT;


#endif // CCURED && !SHADOW_WRAPPERS_H
