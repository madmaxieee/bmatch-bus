#ifndef MY_CADICAL_SOLVER_H
#define MY_CADICAL_SOLVER_H

#include "../cadical/src/cadical.hpp"
#include "BaseSolver.h"
#include <cassert>
#include <queue>

using namespace std;

class CadicalSolver : public BaseSolver {
public:
  CadicalSolver() : _solver(0) {}
  ~CadicalSolver() {}
  void initialize() { reset(); };
  void reset() {
    if (_solver)
      delete _solver;
    _solver = new CaDiCaL::Solver();
    _assump.clear();
    _solution.clear();
    _curVar = 1;
  };

  inline Var newVar() { return _curVar++; };

  void addCNF(const std::vector<Lit> &lits) {
    for (auto l : lits) {
      _solver->add(toDimacs(l));
    }
    _solver->add(0);
  }

  void addUnit(Lit l) {
    _solver->add(toDimacs(l));
    _solver->add(0);
  }

  void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    vector<Lit> lits;
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    lits.push_back(la);
    lits.push_back(~lf);
    addCNF(lits);
    lits.clear();
    lits.push_back(lb);
    lits.push_back(~lf);
    addCNF(lits);
    lits.clear();
    lits.push_back(~la);
    lits.push_back(~lb);
    lits.push_back(lf);
    addCNF(lits);
    lits.clear();
  }
  void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
    vector<Lit> lits;
    Lit lf = Lit(vf);
    Lit la = fa ? ~Lit(va) : Lit(va);
    Lit lb = fb ? ~Lit(vb) : Lit(vb);
    lits.push_back(~la);
    lits.push_back(lb);
    lits.push_back(lf);
    addCNF(lits);
    lits.clear();
    lits.push_back(la);
    lits.push_back(~lb);
    lits.push_back(lf);
    addCNF(lits);
    lits.clear();
    lits.push_back(la);
    lits.push_back(lb);
    lits.push_back(~lf);
    addCNF(lits);
    lits.clear();
    lits.push_back(~la);
    lits.push_back(~lb);
    lits.push_back(~lf);
    addCNF(lits);
    lits.clear();
  }

  void addOR(Lit f, std::vector<Lit> lits) {
    vector<Lit> outerLits;
    outerLits.push_back(~f);
    for (int i = 0; i < lits.size(); ++i) {
      outerLits.push_back(lits[i]);
      vector<Lit> innerLits;
      innerLits.push_back(f);
      innerLits.push_back(~lits[i]);
      addCNF(innerLits);
    }
    addCNF(outerLits);
  }

  // commander encoding
  // ref:
  // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
  void addOneHot(const vector<Lit> &v) {
    vector<Lit> commander_lits = vector<Lit>(v.begin(), v.end());
    vector<Lit> new_commander_lits = vector<Lit>();
    vector<Lit> clause = vector<Lit>();

    while (commander_lits.size() > 1) {
      for (int i = 0; i < commander_lits.size(); i += 3) {
        if (commander_lits.size() - i == 1) {
          new_commander_lits.push_back(commander_lits[i]);
        } else if (commander_lits.size() - i == 2) {
          Var new_commander = newVar();
          Lit new_commander_lit = Lit(new_commander);
          new_commander_lits.push_back(new_commander_lit);

          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);

          clause.clear();
          clause.push_back(~new_commander_lit);
          clause.push_back(commander_lits[i]);
          clause.push_back(commander_lits[i + 1]);
          addCNF(clause);

          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i]);
          addCNF(clause);
          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);
        } else {
          Var new_commander = newVar();
          Lit new_commander_lit = Lit(new_commander);
          new_commander_lits.push_back(new_commander_lit);

          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 1]);
          addCNF(clause);
          clause.clear();
          clause.push_back(~commander_lits[i]);
          clause.push_back(~commander_lits[i + 2]);
          addCNF(clause);
          clause.clear();
          clause.push_back(~commander_lits[i + 1]);
          clause.push_back(~commander_lits[i + 2]);
          addCNF(clause);

          clause.clear();
          clause.push_back(~new_commander_lit);
          clause.push_back(commander_lits[i]);
          clause.push_back(commander_lits[i + 1]);
          clause.push_back(commander_lits[i + 2]);
          addCNF(clause);

          clause.clear();
          clause.push_back(new_commander_lit);
          clause.push_back(~commander_lits[i]);
          addCNF(clause);
          clause[1] = ~commander_lits[i + 1];
          addCNF(clause);
          clause[1] = ~commander_lits[i + 2];
          addCNF(clause);
        }

        addCNF(clause);
      }

      // swap commander_lits and new_commander_lits
      commander_lits.clear();
      commander_lits.swap(new_commander_lits);
    }

    addUnit(commander_lits[0]);
  }

  // ref: https://people.eng.unimelb.edu.au/pstuckey/mddenc/mddenc.pdf
  void addGte(const vector<Lit> &lits, int n, Lit implyFrom = lit_Undef) {
    assert(lits.size() >= 1);

    vector<vector<Var>> BDD = vector<vector<Var>>(lits.size(), vector<Var>(n));

    Var trueNode = newVar();
    Var falseNode = newVar();

    auto inRange = [&](int i, int j) {
      return j >= std::max(i + n - int(lits.size()), 0) &&
             j < std::min(i + 1, n);
    };

    for (int i = 0; i < lits.size(); ++i) {
      for (int j = std::max(i + n - int(lits.size()), 0);
           j < std::min(i + 1, n); ++j) {
        BDD[i][j] = newVar();
      }
    }

    vector<Lit> clause;
    for (int i = 0; i < lits.size(); ++i) {
      for (int j = std::max(i + n - int(lits.size()), 0);
           j < std::min(i + 1, n); ++j) {
        Lit x = lits[i];
        Lit t = !inRange(i + 1, j + 1) ? Lit(trueNode) : Lit(BDD[i + 1][j + 1]);
        Lit f = !inRange(i + 1, j) ? Lit(falseNode) : Lit(BDD[i + 1][j]);
        Lit v = Lit(BDD[i][j]);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(~t);
        clause.push_back(~x);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(t);
        clause.push_back(~x);
        clause.push_back(~v);
        addCNF(clause);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(~f);
        clause.push_back(x);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(f);
        clause.push_back(x);
        clause.push_back(~v);
        addCNF(clause);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(~t);
        clause.push_back(~f);
        clause.push_back(v);
        addCNF(clause);

        clause.clear();
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back(t);
        clause.push_back(f);
        clause.push_back(~v);
        addCNF(clause);
      }
    }

    if (implyFrom != lit_Undef) {
      clause.clear();
      clause.push_back(~implyFrom);
      clause.push_back(Lit(trueNode));
      addCNF(clause);
      clause[1] = ~Lit(falseNode);
      addCNF(clause);
      clause[1] = Lit(BDD[0][0]);
      addCNF(clause);
    } else {
      addUnit(Lit(trueNode));
      addUnit(~Lit(falseNode));
      addUnit(Lit(BDD[0][0]));
    }
  }

  void addSumConstraint(const std::vector<Lit> &lits, int sum,
                        Lit implyFrom = lit_Undef) {
    // calculate the number of bits needed to represent the sum
    int bucketCount = 0;
    int tmp = sum;
    while (tmp > 0) {
      tmp = tmp >> 1;
      bucketCount++;
    }

    // construct bit buckets
    std::vector<std::queue<Lit>> buckets(bucketCount);
    for (int i = 0; i < lits.size(); i++) {
      buckets[0].push(lits[i]);
    }

    for (int i = 0; i < buckets.size(); i++) {
      while (buckets[i].size() >= 3) {
        Lit x = buckets[i].front();
        buckets[i].pop();
        Lit y = buckets[i].front();
        buckets[i].pop();
        Lit z = buckets[i].front();
        buckets[i].pop();
        Lit carry = Lit(newVar());
        Lit sum = Lit(newVar());
        std::vector<std::vector<Lit>> clauses = HA3(x, y, z, carry, sum);
        for (auto clause : clauses) {
          if (implyFrom != lit_Undef) {
            clause.push_back(~implyFrom);
          }
          addCNF(clause);
        }
        buckets[i].push(sum);
        // add bucket if needed
        if (i + 1 == buckets.size()) {
          buckets.push_back(std::queue<Lit>());
        }
        buckets[i + 1].push(carry);
      }

      if (buckets[i].size() == 2) {
        Lit x = buckets[i].front();
        buckets[i].pop();
        Lit y = buckets[i].front();
        buckets[i].pop();
        Lit carry = Lit(newVar());
        Lit sum = Lit(newVar());
        std::vector<std::vector<Lit>> clauses = HA2(x, y, carry, sum);
        for (auto clause : clauses) {
          if (implyFrom != lit_Undef) {
            clause.push_back(~implyFrom);
          }
          addCNF(clause);
        }
        buckets[i].push(sum);
        // add bucket if needed
        if (i + 1 == buckets.size()) {
          buckets.push_back(std::queue<Lit>());
        }
        buckets[i + 1].push(carry);
      }

      if (buckets[i].size() == 1) {
        vector<Lit> clause;
        if (implyFrom != lit_Undef) {
          clause.push_back(~implyFrom);
        }
        clause.push_back((sum & (1 << i)) ? buckets[i].front()
                                          : ~buckets[i].front());
        addCNF(clause);
      }

      if (buckets[i].size() == 0) {
        if (sum & (1 << i)) {
          addCNF({lit_Error});
        }
      }
    }
  }

  void assumeRelease() { _assump.clear(); }
  void assumeProperty(Var prop, bool val) {
    _assump.push_back(val ? Lit(prop) : ~Lit(prop));
  }
  void setAssumptions(const vector<Lit> &lits) { _assump = vector<Lit>(lits); }

  bool assumpSolve() {
    for (auto l : _assump) {
      _solver->assume(toDimacs(l));
    }
    return solve();
  }

  int getValue(Var v) {
    assert(v <= _curVar && v > 0);
    return _solution[v - 1];
  }

  // SAT -> 10, UNSAT -> 20
  bool solve() {
    _solution = std::vector<int>(_curVar, -1);
    bool res = (_solver->solve() == 10);
    if (res) {
      for (int i = 0; i < _curVar; ++i) {
        _solution[i] = _getValue(i + 1);
      }
    }
    return res;
  }

  void printStats() const { _solver->statistics(); }

private:
  int _getValue(Var v) const { return _solver->val(v) == v; }

  CaDiCaL::Solver *_solver;
  Var _curVar;
  std::vector<Lit> _assump;
  std::vector<int> _solution;
};

#endif