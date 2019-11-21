#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

int main()
{
  int x; int y; int k; int j; int i; int n;
    if ((x+y) != k) return 0;
    int m = 0;
    j = 0;
    while(j<n) {
      if(j==i)
      {
         x++;
         y--;
      }else
      {
         y++;
         x--;
      }
	if(unknown1())
  		m = j;
      j++;
    }
    if(n>0)
    {
   	sassert (0<=m);
    }

}

