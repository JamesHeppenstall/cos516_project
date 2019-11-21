#include "horn/AnnoCheck.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc != 3){
    outs() << "Input files with CHCs and Annotations should be given\n";
    return 0;
  }

  annotationCheck(argv[1], argv[2]);

  return 0;
}
