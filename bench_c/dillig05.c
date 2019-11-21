#include "seahorn/seahorn.h"
int unknown1();

int main()
{

  int flag;
	int x = 0;
	int y = 0;

	int j = 0;
	int i = 0;


	while(unknown1())
	{
	  x++;
	  y++;
	  i+=x;
	  j+=y;
	  if(flag)  j+=1;
	} 
	sassert(j>=i);
  return 0;
}
