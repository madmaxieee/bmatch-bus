/****************************************************************************
  FileName     [ sat.h ]
  PackageName  [ sat ]
  Synopsis     [ Define miniSat solver interface functions ]
  Author       [ Chung-Yang (Ric) Huang, Cheng-Yin Wu ]
  Copyright    [ Copyleft(c) 2010-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef SAT_H
#define SAT_H

#include "BaseSolver.h"
#include <vector>

using namespace std;

/********** MiniSAT_Solver **********/
class MinisatSolver : public BaseSolver {
public:
  MinisatSolver() : _solver(0) {}
  ~MinisatSolver() {
    if (_solver)
      delete _solver;
  }
  // Solver initialization and reset
  void initialize();
  void reset();

  // Constructing proof model
  // Return the Var ID of the new Var
  Var newVar();
  // fa/fb = true if it is inverted
  void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb);
  // fa/fb = true if it is inverted
  void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb);

  void addCNF(const std::vector<Lit> &lits);

  void addOR(Lit f, vector<Lit> lits);

  void addXOR2(Lit f, Lit a, Lit b);
  void addAND2(Lit f, Lit a, Lit b);

  // commander encoding
  // ref:
  // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
  void addOneHot(const vector<Lit> &v);

  // ref: https://people.eng.unimelb.edu.au/pstuckey/mddenc/mddenc.pdf
  void addGte(const vector<Lit> &lits, int n, Lit implyFrom = lit_Undef);

  // adder network encoding
  void addSumConstraint(const std::vector<Lit> &lits, int sum,
                        Lit implyFrom = lit_Undef);

  // For incremental proof, use "assumeSolve()"
  void assumeRelease();
  void assumeProperty(Var prop, bool val);
  void setAssumptions(const vector<Lit> &assump);
  bool assumpSolve();

  // For one time proof, use "solve"
  void assertProperty(Var prop, bool val);
  bool solve();

  // Functions about Reporting
  // Return 1/0/-1; -1 means unknown value
  int getValue(Var v);
  void printStats() const;

private:
  Solver *_solver;  // Pointer to a Minisat solver
  Var _curVar;      // Variable currently
  vec<Lit> _assump; // Assumption List for assumption solve

  std::vector<std::vector<Lit>> HA3(Lit x, Lit y, Lit z, Lit carry, Lit sum);

  std::vector<std::vector<Lit>> HA2(Lit x, Lit y, Lit carry, Lit sum);
};

#endif // SAT_H
