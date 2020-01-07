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

// This macro ensures that printed output includes the BMC formula itself
//#define PRINT_BMC_FORMULA

namespace ufo {
    class BndExpl {
        private:

        ExprFactory &e;
        SMTUtils u, v;
        CHCs &r;
        HornRuleExt *tr;
        HornRuleExt *fc;
        HornRuleExt *qr;
        ExprVector curVars;
        
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
        
        // Construct the INIT clause of the CHCs encoded in private variable r
        Expr constructInit() {
            Expr body = fc->body;
            
            for (int i = 0; i < fc->dstVars.size(); i++) {
                Expr name = mkTerm<string>("v_" + to_string(i), e);
                Expr var = cloneVar(fc->dstVars[i], name);
                body = replaceAll(body, fc->dstVars[i], var);
            }
             
            return body;
        }

        // Construct the TR clause of the CHCs encoded in private variable r
        Expr constructTransitionRelation(int k) {
            Expr body = tr->body;
            ExprVector srcVars = tr->srcVars;
            ExprVector dstVars = tr->dstVars;
            curVars.clear();

            for (int i = 0; i < dstVars.size(); i++) {
                int num = k * dstVars.size() + srcVars.size() + i;
                Expr name = mkTerm<string>("v_" + to_string(num), e);
                Expr var = cloneVar(dstVars[i], name);
                body = replaceAll(body, dstVars[i], var);
                dstVars[i] = var;
                curVars.push_back(var);
            }

            for (int i = 0; i < srcVars.size(); i++) {
                int num = k * srcVars.size() + i;
                Expr name = mkTerm<string>("v_" + to_string(num), e);
                Expr var = cloneVar(srcVars[i], name);
                body = replaceAll(body, srcVars[i], var);
                srcVars[i] = var;
            }

            return body;
        }
        
        // Unroll the TR clause of the CHCs encoded in private variable r
        Expr unrollTransitionRelation(int cur_bnd, Expr bmc_formula) {
            for (int k = 0; k < cur_bnd; k++) {
                Expr body = constructTransitionRelation(k);
                bmc_formula = mk<AND>(bmc_formula, body);
            }

            return bmc_formula;
        }

        // Construct the BAD clause of the CHCs encoded in private variable r
        Expr constructBad(int k) {
            Expr body = qr->body;
            
            for (int i = 0; i < qr->srcVars.size(); i++) {  
                int num = k * tr->dstVars.size() + tr->srcVars.size() + i; 
                Expr name = mkTerm<string>("v_" + to_string(num), e);
                Expr var = cloneVar(qr->srcVars[i], name);
                body = replaceAll(body, qr->srcVars[i], var);
            }

            return body;
        }

        Expr constructBad(int k, Expr bmc_formula) {
            Expr body = qr->body;
            
            for (int i = 0; i < qr->srcVars.size(); i++) {  
                int num = (k - 1) * tr->dstVars.size() + tr->srcVars.size() + i; 
                Expr name = mkTerm<string>("v_" + to_string(num), e);
                Expr var = cloneVar(qr->srcVars[i], name);
                body = replaceAll(body, qr->srcVars[i], var);
            }

            return mk<AND>(bmc_formula, body);
        }

        public:

        BndExpl(ExprFactory &efac, CHCs &ruleManager) : e(efac), u(e), v(e),
            r(ruleManager) { checkPrerequisites(); }

        // Explore the set of possible traces between the current bound and the
        // given bound, and return true if no trace is satisfiable (NORMAL MODE)
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
                Expr bmc_formula = constructInit();
                bmc_formula = unrollTransitionRelation(cur_bnd, bmc_formula);
                bmc_formula = constructBad(cur_bnd, bmc_formula);
		
                auto start = high_resolution_clock::now();
                unsat = !u.isSat(bmc_formula);
		auto stop = high_resolution_clock::now();
		auto duration = duration_cast<microseconds>(stop - start);

                // Print some diagnostic information
                if (print) {
#ifdef PRINT_BMC_FORMULA
                    outs() << "  BMC Formula (k=" << cur_bnd << "):\n  " <<
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
        // given bound, and return true if no trace is satisfiable (INCREMENTAL
        // MODE)
        bool exploreTracesIncremental(int cur_bnd, int bnd, bool print = false) {
            // Print some diagnostic information
            if (print) {
		outs() << "EXPLORE TRACES IN INCREMENTAL MODE\n\n";
                outs() << "PROGRAM ENCODING:\n";
                r.print();
                outs() << "DIAGNOSTIC INFORMATION:\n";
            }
            
            bool unsat = true;
            bool first_run = true;

	    // Add the initial conditions to the BMC formula
            Expr bmc_formula = constructInit();
            bmc_formula = unrollTransitionRelation(cur_bnd - 1, bmc_formula);
            Expr prev_bmc_formula = bmc_formula;
            
            auto start1 = high_resolution_clock::now();
            u.reset();
            u.addExpr(bmc_formula);
            u.push();
            auto stop1 = high_resolution_clock::now();

            // Explore traces and check if any of the traces are satisfiable
	    while (unsat && cur_bnd <= bnd) {
                bmc_formula = prev_bmc_formula;
                
                // Ensure that the scope of local variables start2 and stop2 is
                // outside the if statement below
                auto start2 = high_resolution_clock::now();
                auto stop2 = start2;

		if (cur_bnd >= 1) {
    		    Expr body = constructTransitionRelation(cur_bnd - 1);
                    bmc_formula = mk<AND>(bmc_formula, body);
		    
                    start2 = high_resolution_clock::now();
                    u.addExpr(body);
		    u.push();
                    stop2 = high_resolution_clock::now();
		}

                // Add the assertion condition to the BMC formula
                prev_bmc_formula = bmc_formula; 
                Expr body = constructBad(cur_bnd - 1);
                bmc_formula = mk<AND>(bmc_formula, body);

                auto start3 = high_resolution_clock::now();
                u.addExpr(body);
		unsat = !u.check();
		u.pop(); // Remove the BAD clause from SMT utils
		auto stop3 = high_resolution_clock::now();	
                
                auto duration = duration_cast<microseconds>(first_run ? stop1 -
                        start1 + stop2 - start2 + stop3 - start3 : stop2 - start2 +
                        stop3 - start3);
                first_run = false;
                
                // Print some diagnostic information
                if (print) {
#ifdef PRINT_BMC_FORMULA
                    outs() << "  BMC Formula (k=" << cur_bnd << "):\n  " <<
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

        bool exploreTracesInterpolant(int cur_bnd, int bnd, bool print = false) {
            // Print some diagnostic information
            if (print) {
		outs() << "EXPLORE TRACES IN INTERPOLANT MODE\n\n";
                outs() << "PROGRAM ENCODING:\n";
                r.print();
                outs() << "DIAGNOSTIC INFORMATION:\n";
            }
            
            bool unsat = true;

	    // Add the initial conditions to the BMC formula
            Expr bmc_formula = constructInit();
            bmc_formula = unrollTransitionRelation(cur_bnd - 1, bmc_formula);
            Expr prev_bmc_formula = bmc_formula;
            
            u.reset();
            u.addExpr(bmc_formula);
            u.push();

            // Explore traces and check if any of the traces are satisfiable
	    while (unsat && cur_bnd <= bnd) {
                bmc_formula = prev_bmc_formula;

		if (cur_bnd >= 1) {
    		    Expr body = constructTransitionRelation(cur_bnd - 1);
                    bmc_formula = mk<AND>(bmc_formula, body);
		    
                    u.addExpr(body);
		    u.push();
		}

                // Add the assertion condition to the BMC formula
                prev_bmc_formula = bmc_formula; 
                Expr body = constructBad(cur_bnd - 1);
                bmc_formula = mk<AND>(bmc_formula, body);

                u.addExpr(body);
		unsat = !u.check();
		u.pop(); // Remove the BAD clause from SMT utils 
                
                // Print some diagnostic information
                if (print) {
#ifdef PRINT_BMC_FORMULA
                    outs() << "  BMC Formula (k=" << cur_bnd << "):\n  " <<
			*bmc_formula << "\n  Result: " << (unsat ? "UNSAT" : "SAT")
                        << "\n";
#else
                    outs() << "  BMC Formula (k=" << cur_bnd << "): " << (unsat ? 
                        "UNSAT" : "SAT") << "\n";
#endif   
            	}
                
                // Generate an interpolant and check that it is a safe inductive
                // invariant - if so, this interpolant proves correctness for all
                // bounds k' > k
                if (unsat && cur_bnd >= 1) {
                    Expr itp = getItp(prev_bmc_formula, body);
                    Expr prev_itp = itp;
                    Expr body = constructTransitionRelation(cur_bnd - 1);
                    
                    for (int i = 0; i < curVars.size(); i++) {
                        string s = lexical_cast<string>(bind::name(curVars[i])
                            .get());
                        int num = atoi(&s.at(s.find("v_") + 2));
                        int size = curVars.size();

                        Expr name = mkTerm<string>("v_" + to_string(num - size), e);
                        Expr var = cloneVar(curVars[i], name);
                        prev_itp = replaceAll(prev_itp, curVars[i], var);
                    }

                    // Check that the interpolant is a safe inductive invariant
                    Expr inv_formula = mk<AND>(prev_itp, body);
                    inv_formula = mk<AND>(inv_formula, mk<NEG>(itp));
                    bool sat = v.isSat(inv_formula);

                    if (print) {
                        outs() << "  Interpolant: " << *itp << "\n  Safe Inductive"
                            << " Invariant: " << (sat ? "NO" : "YES") << "\n";
                    }
                }
 
                cur_bnd++;
            }
	    
            return unsat;
        }
    };
    
    // Unroll and check an SMT expression
    inline void unrollAndCheck(string smt, int bnd1, int bnd2, int inc = false) {
        // Initialize the class with the CHCs 
        ExprFactory efac;
        EZ3 z3(efac); 
        CHCs ruleManager(efac, z3);
        ruleManager.parse(smt);

        // Explore the possible traces between the two bounds
	BndExpl bndExpl(efac, ruleManager);
        if (!inc) {
            bndExpl.exploreTracesNormal(bnd1, bnd2, true);
        } else {
            bndExpl.exploreTracesIncremental(bnd1, bnd2, true);
        }

        // TODO: Report something? (might need to change the return type)
    }

    inline void getItpsAndCheck(string smt, int bnd1, int bnd2) {
        // Initialize the class with the CHCs
        ExprFactory efac;
        EZ3 z3(efac);
        CHCs ruleManager(efac, z3);
        ruleManager.parse(smt); 

        // Explore the possible traces between the two bounds
        BndExpl bndExpl(efac, ruleManager);
        bndExpl.exploreTracesInterpolant(bnd1, bnd2, true);
    }
}

#endif
