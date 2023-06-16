#ifndef MY_CADICAL_SOLVER_H
#define MY_CADICAL_SOLVER_H

#include "../cadical/src/cadical.hpp"
#include "BaseSolver.h"

using namespace std;

class CadicalSolver : public BaseSolver {
public:
  CadicalSolver() : _solver(0) {}
  ~CadicalSolver() {
    if (_solver)
      delete _solver;
  }

  void initialize();
  void reset();

  inline Var newVar();

  void addCNF(const std::vector<Lit> &lits);

  void addUnit(Lit l);

  void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb);

  void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb);

  void addOR(Lit f, std::vector<Lit> lits);

  // commander encoding
  // ref:
  // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
  void addOneHot(const vector<Lit> &v);

  // ref: https://people.eng.unimelb.edu.au/pstuckey/mddenc/mddenc.pdf
  void addGte(const vector<Lit> &lits, int n, Lit implyFrom = lit_Undef);

  void addSumConstraint(const std::vector<Lit> &lits, int sum,
                        Lit implyFrom = lit_Undef);

  void assumeRelease();
  void assumeProperty(Var prop, bool val);
  void setAssumptions(const vector<Lit> &lits);

  bool assumpSolve();

  int getValue(Var v);

  // SAT -> 10, UNSAT -> 20
  bool solve();

  void printStats() const;

private:
  int _getValue(Var v) const;

  CaDiCaL::Solver *_solver;
  Var _curVar;
  std::vector<Lit> _assump;
  std::vector<int> _solution;

  std::vector<std::vector<Lit>> HA3(Lit x, Lit y, Lit z, Lit carry, Lit sum);

  std::vector<std::vector<Lit>> HA2(Lit x, Lit y, Lit carry, Lit sum);
};

#endif