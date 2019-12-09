#ifndef EQUIVHECK__HPP__
#define EQUIVHECK__HPP__

#include "Horn.hpp"
#include "CandChecker.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  inline void checkPrerequisites (CHCs& r)
  {
    if (r.decls.size() > 1)
    {
      outs() << "Nested loops not supported\n";
      exit(0);
    }

    if (r.chcs.size() < 2)
    {
      outs() << "Please provide a file with at least two rules (INIT and TR)\n";
      exit(0);
    }

    HornRuleExt* tr = NULL;
    HornRuleExt* fc = NULL;

    for (auto & a : r.chcs)
      if (a.isInductive) tr = &a;
      else if (a.isFact) fc = &a;

    if (tr == NULL)
    {
      outs() << "TR is missing\n";
      exit(0);
    }

    if (fc == NULL)
    {
      outs() << "INIT is missing\n";
      exit(0);
    }
  }

  inline void equivCheck(string chcfile1, string chcfile2)
  {
    ExprFactory efac;
    EZ3 z3(efac);

    CHCs ruleManager1(efac, z3);
    ruleManager1.parse(chcfile1, "v_");
    checkPrerequisites(ruleManager1);
    outs () << "Program encoding #1:\n";
    ruleManager1.print();

    CHCs ruleManager2(efac, z3);
    ruleManager2.parse(chcfile2, "w_");
    checkPrerequisites(ruleManager2);
    outs () << "Program encoding #2:\n";
    ruleManager2.print();

    // TODO: check equivalence between programs encoded in ruleManager1 and ruleManager2
  };
}

#endif
