#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Simplifying Loop Invariant Generation using Splitter Predicates", Sharma et al. CAV'11
 */


int main()
{
  int n; int m;
  if (n < 0 || m < 0 || m >= n) return 0;
  int x=0; 
  int y=m;
  while(x<n) {
    x++;
    if(x>m) y++;
  }
  sassert(y==n);
}
