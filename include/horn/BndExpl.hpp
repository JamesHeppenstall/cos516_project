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
    
        /*Expr replaceVars(HornRuleExt* hr) {
            while (i < hr->srcVars.size()) { 
                Expr name = mkTerm<string>("v_" + to_string(i), e);
                Expr var = cloneVar(hr->srcVars[i], name);
                hr->body = replaceAll(hr->body, hr->srcVars[i], var);
                i++;
            }

            int j = i;

            while (j < n + hr->srcVars.size() + hr->dstVars.size()) {
                Expr name = mkTerm<string>("v_" + to_string(j), e);
                Expr var = cloneVar(hr->dstVars[j], name);
                hr->body = replaceAll(hr->body, hr->dstVars[j], var);
                j++;
            }

            return hr->body;
        }*/

        public:

        BndExpl(ExprFactory &efac, CHCs &ruleManager) : e(efac), u(e), r(ruleManager) { checkPrerequisites(); }

        // TODO: Helper methods (i.e. conversion from trace to SMT expression)
        
        // Explore the set of possible traces between the current bound and the
        // given bound, and return true if no trace is satisfiable
        bool exploreTraces(int cur_bnd, int bnd, bool print = false) {
            bool unsat = true;

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
                    for (int j = 0; j < dstVars.size(); j++) {
                        int m = k * dstVars.size() + srcVars.size() + j;
                        Expr name = mkTerm<string>("v_" + to_string(m), e);
                        Expr var = cloneVar(dstVars[j], name);
                        body = replaceAll(body, dstVars[j], var);
                        dstVars[j] = var;
                    }

                    for (int i = 0; i < srcVars.size(); i++) {
                        int n = k * dstVars.size() + i;
                        Expr name = mkTerm<string>("v_" + to_string(n), e);
                        Expr var = cloneVar(srcVars[i], name);
                        body = replaceAll(body, srcVars[i], var);
                        srcVars[i] = var;
                    }

                    bmc_formula = mk<AND>(bmc_formula, body);
                }

                body = qr->body;

                for (int j = 0; j < qr->srcVars.size(); j++) {  
                    int m = (cur_bnd - 1) * tr->dstVars.size() + tr->srcVars.size() + j; 
                    Expr name = mkTerm<string>("v_" + to_string(m), e);
                    Expr var = cloneVar(qr->srcVars[j], name);
                    body = replaceAll(body, qr->srcVars[j], var);
                }

                outs() << "TEST: " << *body << "\n";

                bmc_formula = mk<AND>(bmc_formula, body);
                //bmc_formula = u.removeRedundantConjuncts(bmc_formula);
                outs() << "BMC Formula (k=" << cur_bnd << "): " << *bmc_formula << "\n";
                unsat = !u.isSat(bmc_formula);
                cur_bnd++;
            }

            // TODO: Explore traces
            // TODO: Check if any of the traces are satisfiable

            if (print) {
            // TODO: some diagnostic information
            }

            return unsat;
        }
    };
    
    // TODO: Unroll and check an SMT expression
    inline void unrollAndCheck(string smt, int bnd1, int bnd2) {
        ExprFactory efac;
        EZ3 z3(efac);
        
        // Initialize the class with the CHCs 
        CHCs ruleManager(efac, z3);
        ruleManager.parse(smt);
        outs() << "Program encoding:\n";
        ruleManager.print();

        // Check that the form of the CHCs is valid
        BndExpl bndExpl(efac, ruleManager);

        // TODO: Explore the possible traces between the two bounds
        bndExpl.exploreTraces(1, 5);
        
        // TODO: Report something? (might need to change the return type)
    }
}

#endif
