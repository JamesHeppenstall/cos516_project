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

        ExprFactory &e;
        SMTUtils u;
        CHCs &r;
        HornRuleExt *tr;
        HornRuleExt *fc;
        HornRuleExt *qr;
        
        // Check that the form of the CHCs encoded in private variable r is valid
        void checkPrerequisites() {
            if (r.decls.size() > 1) {
                outs() << "Nested loops not supported\n";
                exit(0);
            }

            if (r.chcs.size() != 3) {
                outs() << "Please provide a file with exactly three rules\n";
                exit(0);
            }

            for (auto &a : r.chcs) {
                if (a.isInductive) tr = &a;
                else if (a.isFact) fc = &a;
                else if (a.isQuery) qr = &a;
            }

            if (tr == NULL) {
                outs() << "TR is missing\n";
                exit(0);
            }

            if (fc == NULL) {
                outs() << "INIT is missing\n";
                exit(0);
            }

            if (qr == NULL) {
                outs() << "BAD is missing\n";
                exit(0);
            }
        }

        public:

        BndExpl(ExprFactory &efac, CHCs &ruleManager) : e(efac), u(e),
            r(ruleManager) { checkPrerequisites(); }

        // Explore the set of possible traces between the current bound and the
        // given bound, and return true if no trace is satisfiable
        bool exploreTraces(int cur_bnd, int bnd, bool print = false) {
            // Print some diagnostic information
            if (print) {
                outs() << "PROGRAM ENCODING:\n";
                r.print();
                outs() << "DIAGNOSTIC INFORMATION:\n";
            }

            bool unsat = true;

            // Explore traces and check if any of the traces are satisfiable
            while (unsat && cur_bnd <= bnd) {
                Expr body = fc->body;
                
                for (int i = 0; i < fc->dstVars.size(); i++) {
                    Expr name = mkTerm<string>("v_" + to_string(i), e);
                    Expr var = cloneVar(fc->dstVars[i], name);
                    body = replaceAll(body, fc->dstVars[i], var);
                }
                 
                Expr bmc_formula = body;

                body = tr->body;
                ExprVector srcVars = tr->srcVars;
                ExprVector dstVars = tr->dstVars;

                for (int k = 0; k < cur_bnd; k++) {
                    for (int i = 0; i < dstVars.size(); i++) {
                        int num = k * dstVars.size() + srcVars.size() + i;
                        Expr name = mkTerm<string>("v_" + to_string(num), e);
                        Expr var = cloneVar(dstVars[i], name);
                        body = replaceAll(body, dstVars[i], var);
                        dstVars[i] = var;
                    }

                    for (int i = 0; i < srcVars.size(); i++) {
                        int num = k * dstVars.size() + i;
                        Expr name = mkTerm<string>("v_" + to_string(num), e);
                        Expr var = cloneVar(srcVars[i], name);
                        body = replaceAll(body, srcVars[i], var);
                        srcVars[i] = var;
                    }

                    bmc_formula = mk<AND>(bmc_formula, body);
                }

                body = qr->body;

                for (int i = 0; i < qr->srcVars.size(); i++) {  
                    int num = (cur_bnd - 1) * tr->dstVars.size() +
                        tr->srcVars.size() + i; 
                    Expr name = mkTerm<string>("v_" + to_string(num), e);
                    Expr var = cloneVar(qr->srcVars[i], name);
                    body = replaceAll(body, qr->srcVars[i], var);
                }

                bmc_formula = mk<AND>(bmc_formula, body); 
                unsat = !u.isSat(bmc_formula);

                // Print some diagnostic information
                if (print) {
                    //outs() << "  BMC Formula (k=" << cur_bnd << "): " << (unsat ? 
                    //    "UNSAT" : "SAT") << "\n";
                    outs() << "  BMC Formula (k=" << cur_bnd << "):\n    " <<
                        *bmc_formula << " (" << (unsat ? "UNSAT" : "SAT") << ")\n";
                }
                
                cur_bnd++;
            }

            return unsat;
        }
    };
    
    // TODO: Unroll and check an SMT expression
    inline void unrollAndCheck(string smt, int bnd1, int bnd2) {
        // Initialize the class with the CHCs 
        ExprFactory efac;
        EZ3 z3(efac); 
        CHCs ruleManager(efac, z3);
        ruleManager.parse(smt);

        // Explore the possible traces between the two bounds
        BndExpl bndExpl(efac, ruleManager);
        bndExpl.exploreTraces(bnd1, bnd2, true);
        
        // TODO: Report something? (might need to change the return type)
    }
}

#endif
