#include "seahorn/seahorn.h"
int unknown1();

/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

int main() {
  int flag;
   int j = 2; 
   int k = 0;

   while(unknown1()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   if(k!=0)
     sassert(j==2*k+2);
}
