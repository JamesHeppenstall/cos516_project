#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();

/*
 *  Based on "Automatically refining abstract interpretations" fig.1
 */


int main() {
 int x = 0, y = 0;
 while(unknown1()){
   if(unknown2()){ 
      x++; 
      y+=100; 
   }
   else if (unknown3()){ 
      if (x >= 4) { 
          x++; 
          y++; 
      } 
      if (x < 0){
          y--;
      }
   }
  
 }
 sassert(x < 4 || y > 2);
}
