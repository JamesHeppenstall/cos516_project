#include "seahorn/seahorn.h"

/*
 * "split.c" from InvGen benchmark suite
 */


int main() {
  int k = 100;
  int b;
  int i;
  int j;
  int n;
  i = j;
  for( n = 0 ; n < 2*k ; n++ ) {
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
  sassert(i == j);
}
