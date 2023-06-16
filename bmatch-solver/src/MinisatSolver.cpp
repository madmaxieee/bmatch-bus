#include "MinisatSolver.h"
#include <cassert>
#include <iostream>
#include <queue>
#include <vector>

using namespace std;

// Solver initialization and reset
void MinisatSolver::MinisatSolver::initialize() {
  reset();
  if (_curVar == 0) {
    _solver->newVar();
    ++_curVar;
  }
}

void MinisatSolver::reset() {
  if (_solver)
    delete _solver;
  _solver = new Solver();
  _assump.clear();
  _curVar = 0;
}

// Constructing proof model
// Return the Var ID of the new Var
inline Var MinisatSolver::newVar() {
  _solver->newVar();
  return _curVar++;
}
// fa/fb = true if it is inverted
void MinisatSolver::addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
  vec<Lit> lits;
  Lit lf = Lit(vf);
  Lit la = fa ? ~Lit(va) : Lit(va);
  Lit lb = fb ? ~Lit(vb) : Lit(vb);
  lits.push(la);
  lits.push(~lf);
  _solver->addClause(lits);
  lits.clear();
  lits.push(lb);
  lits.push(~lf);
  _solver->addClause(lits);
  lits.clear();
  lits.push(~la);
  lits.push(~lb);
  lits.push(lf);
  _solver->addClause(lits);
  lits.clear();
}
// fa/fb = true if it is inverted
void MinisatSolver::addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
  vec<Lit> lits;
  Lit lf = Lit(vf);
  Lit la = fa ? ~Lit(va) : Lit(va);
  Lit lb = fb ? ~Lit(vb) : Lit(vb);
  lits.push(~la);
  lits.push(lb);
  lits.push(lf);
  _solver->addClause(lits);
  lits.clear();
  lits.push(la);
  lits.push(~lb);
  lits.push(lf);
  _solver->addClause(lits);
  lits.clear();
  lits.push(la);
  lits.push(lb);
  lits.push(~lf);
  _solver->addClause(lits);
  lits.clear();
  lits.push(~la);
  lits.push(~lb);
  lits.push(~lf);
  _solver->addClause(lits);
  lits.clear();
}
void MinisatSolver::addCNF(const std::vector<Lit> &lits) {
  vec<Lit> _lits(lits.size());
  for (int i = 0; i < lits.size(); ++i) {
    _lits[i] = lits[i];
  }
  _solver->addClause(_lits);
}

void MinisatSolver::addOR(Lit f, vector<Lit> lits) { // Wish
  // f = OR(for lit in lits)
  // A <-> B + C + D + E +...+ => (¬B ∨ A) ∧ (¬C ∨ A) ∧ (¬D ∨ A) ∧ (¬E ∨ A) ∧
  // (¬A ∨ B ∨ C ∨ D ∨ E)
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
void MinisatSolver::addOneHot(const vector<Lit> &v) {
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

  _solver->addUnit(commander_lits[0]);
}

// ref: https://people.eng.unimelb.edu.au/pstuckey/mddenc/mddenc.pdf
void MinisatSolver::addGte(const vector<Lit> &lits, int n, Lit implyFrom) {
  assert(lits.size() >= n);

  vector<vector<Var>> BDD = vector<vector<Var>>(lits.size(), vector<Var>(n));

  Var trueNode = newVar();
  Var falseNode = newVar();

  auto inRange = [&](int i, int j) {
    return j >= std::max(i + n - int(lits.size()), 0) && j < std::min(i + 1, n);
  };

  for (int i = 0; i < lits.size(); ++i) {
    for (int j = std::max(i + n - int(lits.size()), 0); j < std::min(i + 1, n);
         ++j) {
      BDD[i][j] = newVar();
    }
  }

  vector<Lit> clause;
  for (int i = 0; i < lits.size(); ++i) {
    for (int j = std::max(i + n - int(lits.size()), 0); j < std::min(i + 1, n);
         ++j) {
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
    _solver->addBinary(~implyFrom, Lit(trueNode));
    _solver->addBinary(~implyFrom, ~Lit(falseNode));
    _solver->addBinary(~implyFrom, Lit(BDD[0][0]));
  } else {
    _solver->addUnit(Lit(trueNode));
    _solver->addUnit(~Lit(falseNode));
    _solver->addUnit(Lit(BDD[0][0]));
  }
}

void MinisatSolver::addSumConstraint(const std::vector<Lit> &lits, int sum,
                                     Lit implyFrom) {
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

// For incremental proof, use "assumeSolve()"
void MinisatSolver::assumeRelease() { _assump.clear(); }
void MinisatSolver::assumeProperty(Var prop, bool val) {
  _assump.push(val ? Lit(prop) : ~Lit(prop));
}
void MinisatSolver::setAssumptions(const vector<Lit> &assump) {
  _assump.clear();
  for (auto lit : assump) {
    _assump.push(lit);
  }
}
bool MinisatSolver::assumpSolve() { return _solver->solve(_assump); }

// For one time proof, use "solve"
void MinisatSolver::assertProperty(Var prop, bool val) {
  _solver->addUnit(val ? Lit(prop) : ~Lit(prop));
}
bool MinisatSolver::solve() {
  _solver->solve();
  return _solver->okay();
}

// Functions about Reporting
// Return 1/0/-1; -1 means unknown value
int MinisatSolver::getValue(Var v) {
  return (_solver->modelValue(v) == l_True
              ? 1
              : (_solver->modelValue(v) == l_False ? 0 : -1));
}
void MinisatSolver::printStats() const {
  const_cast<Solver *>(_solver)->printStats();
}

std::vector<std::vector<Lit>> MinisatSolver::HA3(Lit x, Lit y, Lit z, Lit carry,
                                                 Lit sum) {
  std::vector<std::vector<Lit>> clauses;
  clauses.push_back({z, ~carry, ~sum});
  clauses.push_back({x, y, ~carry});
  clauses.push_back({~z, carry, sum});
  clauses.push_back({~x, ~y, carry});
  clauses.push_back({x, y, z, ~sum});
  clauses.push_back({x, ~y, ~z, ~sum});
  clauses.push_back({~x, y, ~z, ~sum});
  clauses.push_back({~x, ~y, ~z, sum});
  clauses.push_back({~x, y, z, sum});
  clauses.push_back({x, ~y, z, sum});
  return clauses;
}

std::vector<std::vector<Lit>> MinisatSolver::HA2(Lit x, Lit y, Lit carry,
                                                 Lit sum) {
  std::vector<std::vector<Lit>> clauses;
  clauses.push_back({x, y, ~sum});
  clauses.push_back({~x, ~y, ~sum});
  clauses.push_back({x, ~carry});
  clauses.push_back({y, ~carry});
  clauses.push_back({~x, carry, sum});
  clauses.push_back({x, ~y, sum});
  return clauses;
}