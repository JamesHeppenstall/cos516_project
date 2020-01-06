/* BndExpl.cpp
 * COS 516: Bounded Model Checker (P1)
 * James Heppenstall (jwmh) and Josh Zhang (jiashuoz)
 */

#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "ae/SMTUtils.hpp"
#include <chrono>

using namespace std;
using namespace boost;
using namespace std::chrono;

// This macro ensures that printed output includes BMC formula
//#define PRINT_BMC_FORMULA

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
        bool exploreTracesNormal(int cur_bnd, int bnd, bool print = false) {
            // Print some diagnostic information
            if (print) {
                outs() << "EXPLORING TRACES IN NORMAL MODE\n\n";
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

		auto start = high_resolution_clock::now();
                unsat = !u.isSat(bmc_formula);
		auto stop = high_resolution_clock::now();
		auto duration = duration_cast<microseconds>(stop - start);

                // Print some diagnostic information
                if (print) {
#ifdef PRINT_BMC_FORMULA
                    outs() << "  BMC Formula (k=" << cur_bnd << "):\n    " <<
			*bmc_formula << "\n  Result: " << (unsat ? "UNSAT" : "SAT")
                        << "\n";
#else
                    outs() << "  BMC Formula (k=" << cur_bnd << "): " << (unsat ? 
                        "UNSAT" : "SAT") << "\n";
#endif
                    cout << "  Time Taken to Check: " << duration.count() <<
                        " microseconds\n\n";        
            	}

                cur_bnd++;
            }

            return unsat;
	}

        // Explore the set of possible traces between the current bound and the
        // given bound, and return true if no trace is satisfiable
        bool exploreTracesIncremental(int cur_bnd, int bnd, bool print = false) {
            // Print some diagnostic information
            if (print) {
		outs() << "EXPLORE TRACES IN INCREMENTAL MODE\n\n";
                outs() << "PROGRAM ENCODING:\n";
                r.print();
                outs() << "DIAGNOSTIC INFORMATION:\n";
            }
            
            bool unsat = true;
	    u.reset();

	    // Add initial conditions to SMT utils expression factory
            Expr body = fc->body;
	    
            for (int i = 0; i < fc->dstVars.size(); i++) {
		Expr name = mkTerm<string>("v_" + to_string(i), e);
		Expr var = cloneVar(fc->dstVars[i], name);
		body = replaceAll(body, fc->dstVars[i], var);
	    }            
	    
            Expr prevLoopBody = body; 
            u.addExpr(body);
	    u.push();

            // Explore traces and check if any of the traces are satisfiable
            int k = 0;

	    while (unsat && k <= bnd) {
		Expr bmc_formula = prevLoopBody;

		// Expression for loop body
		if (k >= 1) {
    		    Expr loopBody = tr->body;
                    ExprVector srcVars = tr->srcVars;
                    ExprVector dstVars = tr->dstVars;
    	            for (int i = 0; i < dstVars.size(); i++) {
        	    	int num = (k-1) * dstVars.size() + srcVars.size() + i;
    			Expr name = mkTerm<string>("v_" + to_string(num), e);
                	Expr var = cloneVar(dstVars[i], name);
                  	loopBody = replaceAll(loopBody, dstVars[i], var);
                      	dstVars[i] = var;
                    }

             	    for (int i = 0; i < srcVars.size(); i++) {
               	        int num = (k-1) * srcVars.size() + i;
                   	Expr name = mkTerm<string>("v_" + to_string(num), e);
                       	Expr var = cloneVar(srcVars[i], name);
                   	loopBody = replaceAll(loopBody, srcVars[i], var);
                       	srcVars[i] = var;
                    }
                    bmc_formula = mk<AND>(bmc_formula, loopBody);
    		    prevLoopBody = bmc_formula;
		    // Add conditions for loop body and save the state
		    u.addExpr(loopBody);
		    u.push();
		}

                Expr assertBody = qr->body;
                for (int i = 0; i < qr->srcVars.size(); i++) {  
                    int num = (k - 1) * tr->srcVars.size() +
                        tr->srcVars.size() + i; 
                    Expr name = mkTerm<string>("v_" + to_string(num), e);
                    Expr var = cloneVar(qr->srcVars[i], name);
                    assertBody = replaceAll(assertBody, qr->srcVars[i], var);
                }

                bmc_formula = mk<AND>(bmc_formula, assertBody); 
		u.addExpr(assertBody);
		
                auto start = high_resolution_clock::now();
		unsat = !u.check();
		u.pop(); // Remove bad condition from SMT utils expression factory
		auto stop = high_resolution_clock::now();
		auto duration = duration_cast<microseconds>(stop - start);
                
                // Print some diagnostic information
                if (print) {
#ifdef PRINT_BMC_FORMULA
                    outs() << "  BMC Formula (k=" << k << "):\n    " <<
			*bmc_formula << "\n  Result: " << (unsat ? "UNSAT" : "SAT")
                        << "\n";
#else
                    outs() << "  BMC Formula (k=" << k << "): " << (unsat ? 
                        "UNSAT" : "SAT") << "\n";
#endif
                    cout << "  Time Taken to Check: " << duration.count() <<
                        " microseconds\n\n";        
            	}

                k++;
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
        //bndExpl.exploreTracesNormal(bnd1, bnd2, true);
	//cout << "\n";
	bndExpl.exploreTracesIncremental(bnd1, bnd2, true);

        // TODO: Report something? (might need to change the return type)
    }
}

#endif
