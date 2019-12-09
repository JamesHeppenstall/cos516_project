#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * from Invgen test suite
 */

int main(int argc, char* argv[]) {

  int n;
  int i, k, j;


  n = unknown1();
  if (n <= 0) return 0;

  if (k <= n) return 0;

  j = 0;
  while( j < n ) {
    j++;
    k--;
  } 
  sassert(k>=0);
  return 0;
}
