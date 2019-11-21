#include "horn/EquivCheck.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc != 3){
    outs() << "Two input files with CHCs should be given\n";
    return 0;
  }
  
  equivCheck(string(argv[1]), string(argv[2]));
  
  return 0;
}
