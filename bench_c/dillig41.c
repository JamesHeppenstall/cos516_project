#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from "Automated Error Diagnosis Using Abductive Inference" by Dillig et al.
 */

int main() {
  int n; int flag;
   if (n<0) return 0;
   int k = 1;
   if(flag) {
	k = unknown1();
	if(k<0) return 0;
     
   }
   int i = 0, j = 0;
   while(i <= n) {
     i++;
     j+=i;
   }
   int z = k + i + j;
   sassert(z > 2*n);
}

