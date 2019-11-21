#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Path Invariants" PLDI 07 by Beyer et al.
 */

int main() {

  int i, n, a, b;
  if ( n < 0 ) return 0;
  i = 0; a = 0; b = 0;
  while( i < n ) {
    if(unknown1()) {
      a = a+1;
      b = b+2;
    } else {
      a = a+2;
      b = b+1;
    }
    i = i+1;
  }
  sassert( a+b == 3*n );
}
