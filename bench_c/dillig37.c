#include "seahorn/seahorn.h"
int unknown1();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

int main() {
  int n;
  if (n <= 0) return 0;
  int x = 0;
  int y = 0;
  while(x<n) {
     if(unknown1()) {
       y = x;
     }
     x= x+1;
  }
  sassert(0<=y && y<n);
}
