/* BndExpl.cpp
 * COS 516: Bounded Model Checker (P1)
 * James Heppenstall (jwmh) and Josh Zhang (jiashuoz)
 */

#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;

namespace ufo {
    class BndExpl {
        private:

        ExprFactory &m_efac;
        SMTUtils u;
        CHCs& ruleManager;
        // TODO: Other fields

        public:
        // TODO: Helper methods (i.e. conversion from trace to SMT expression)

        // Explore the set of possible traces between the current bound and the
        // given bound, and return true if no trace is satisfiable
        bool exploreTraces(int cur_bnd, int bnd, bool print = false) {
            bool unsat = true;

            while (unsat && cur_bnd <= bnd) {
            // TODO: Explore traces
            // TODO: Check if any of the traces are satisfiable
            }

            if (print) {
            // TODO: some diagnostic information
            }

            return unsat;
        }

        // TODO: Unroll and check an SMT expression
        static inline void unrollAndCheck(string smt, int bnd1, int bnd2) {
            ExprFactory m_efac;
            EZ3 z3(m_efac);
            CHCs ruleManager(m_efac, z3);
            ruleManager.parse(smt);
            // TODO: Initialize the class with the CHCs
            // TODO: check that the form of the CHCs is valid
            // TODO: Explore the possible traces between the two bounds
            // TODO: Report something? (might need to change the return type)
        }
    };
}

#endif
