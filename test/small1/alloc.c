// run with MANUALBOX = 1

#ifndef __INDEX
#define __INDEX
#define __WILD
#endif

#pragma ccuredalloc("myalloc", nozero, sizein(1)) /* Declare this as an 
                                                * allocation function that 
                                                * does not zero the memory 
                                                * and has the size argument 
                                                * in the first argument  */


#pragma ccuredalloc("myzalloc", zero, sizemul(1, 2)) /* And this is an 
                                                   * allocation function 
                                                   * that zeroes the memory 
                                                   * and the size of the 
                                                   * product of arguments 1 
                                                   * and 2 */


extern void * myalloc(unsigned int);
extern void * myzalloc(unsigned int, unsigned int);
     
extern needsindex(int * __INDEX f);

typedef struct closed {
  struct {
    int a1[10];
  } f1;
  int a2[20];
} CLOSED;


typedef struct open {
  struct {
    int o1[10];
  } of1;
  struct {
    int a;
  } rest[0];   // The rest of the structure
} OPEN;

// A global
CLOSED globc[3];

// Now some wild stuff
typedef struct wild {
  int aw1[15];
  int *  aw2;
} THEWILD;

OPEN anopen;

int main() {
  CLOSED * p1 = (CLOSED*)myalloc(5 * sizeof(CLOSED));

  CLOSED * __INDEX p2 = (CLOSED*)myalloc(7 * sizeof(CLOSED));
  
  OPEN   *p3 = (OPEN*)myalloc(64 + sizeof(OPEN));

  THEWILD * __WILD pw = (THEWILD *)myalloc(36);
  
  p1 = (CLOSED*) myalloc(sizeof(CLOSED));
  
  // Now force a bunch of the arrays SIZED
  needsindex(& globc->a2[3]);
  needsindex(& p1[2].f1.a1[1]);
  needsindex(& p3->of1.o1[2]);

  return p3->rest[5].a;
}


int zallocations() {
  CLOSED * p1 = (CLOSED*)myzalloc(5, sizeof(CLOSED));

  CLOSED * __INDEX p2 = (CLOSED*)myzalloc(7, sizeof(CLOSED));
  
  OPEN   *p3 = (OPEN*)myzalloc(1, 64 + sizeof(OPEN));

  THEWILD * __WILD pw = (THEWILD *)myzalloc(36, 1);
  
  p1 = (CLOSED*) myzalloc(1, sizeof(CLOSED));

  return 5;
}
