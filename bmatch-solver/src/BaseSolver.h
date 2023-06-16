#ifndef BASE_SOLVER_H
#define BASE_SOLVER_H

#include "Solver.h"
#include <vector>

class BaseSolver {
public:
  virtual void initialize() = 0;
  virtual void reset() = 0;

  virtual Var newVar() = 0;

  virtual void addCNF(const std::vector<Lit> &lits) = 0;
  virtual void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) = 0;
  virtual void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) = 0;
  virtual void addOR(Lit f, std::vector<Lit> lits) = 0;
  virtual void addOneHot(const std::vector<Lit> &lits) = 0;
  virtual void addGte(const std::vector<Lit> &lits, int n,
                      Lit implyFrom = lit_Undef) = 0;
  virtual void addSumConstraint(const std::vector<Lit> &lits, int,
                                Lit implyFrom = lit_Undef) = 0;

  virtual void assumeRelease() = 0;
  virtual void assumeProperty(Var prop, bool val) = 0;
  virtual void setAssumptions(const std::vector<Lit> &lits) = 0;
  virtual bool assumpSolve() = 0;

  virtual bool solve() = 0;

  virtual int getValue(Var v) = 0;
  virtual void printStats() const = 0;
};

#endif // BASE_SOLVER_H