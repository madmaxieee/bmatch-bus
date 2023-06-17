#include "CadicalSolver.h"
#include "MinisatSolver.h"
#include <fstream>
#include <iomanip>
#include <iostream>
#include <time.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;

double START;

unordered_map<int, Var> AAG2VarHashmap;
unordered_map<int, Var> outputInverted;

class Port {
public:
  Port(const string &_name, const Var &_var) {
    name = _name;
    var = _var;
  }
  ~Port() {}
  string getName() const { return name; }
  Var getVar() const { return var; }

private:
  string name;
  Var var;
};

struct mtx2Mit {
  Var matrixVar;
  Var miterVar;
};

// Global variables

// SAT Solver
CadicalSolver pureMatrixSolver, busMatrixSolver, miterSolver;

// Circuit 1
vector<Port> x;
vector<Port> f;

// Circuit 2
vector<Port> y;
vector<Port> g;
vector<Var> fStar;

// I/O Matrix
vector<vector<mtx2Mit>> a, b, c, d;

// Answer
int bestScore;
vector<vector<bool>> ans_a, ans_b, ans_c, ans_d;
vector<Var> ansHelper;

typedef unordered_map<int, vector<vector<int>>> Buses;
Buses xBus;
Buses fBus;
Buses yBus;
Buses gBus;

Var AAG2Var(int AAGVar, bool circuitOne) {
  if (!circuitOne)
    AAGVar = -AAGVar;
  if (AAG2VarHashmap.find(AAGVar) == AAG2VarHashmap.end())
    AAG2VarHashmap[AAGVar] = miterSolver.newVar();
  return AAG2VarHashmap[AAGVar];
}

int getPortIndex(const vector<Port> &ports, const string &portName) {
  for (int i = 0; i < ports.size(); ++i) {
    if (ports[i].getName() == portName) {
      return i;
    }
  }
  return -1; // return -1 if not found
}

void readPortMapping(ifstream &in) {
  // <1|2>(int) <"input"|"output">(string) <PortName>(string) <VarInCNF>(int)
  int one_two;
  string IO;
  string name;
  int litInAAG;
  while (in >> one_two >> IO >> name >> litInAAG) {
    vector<Port> &IOPorts =
        (one_two == 1 ? (IO == "input" ? x : f) : (IO == "input" ? y : g));
    Var v = AAG2Var(litInAAG / 2, (one_two == 1));
    if (litInAAG % 2 == 1) {             // inverted output
      Var invVar = miterSolver.newVar(); // invVar = ~v
      vector<Lit> lits;
      lits.push_back(Lit(invVar));
      lits.push_back(Lit(v));
      miterSolver.addCNF(lits);
      lits.clear();
      lits.push_back(~Lit(invVar));
      lits.push_back(~Lit(v));
      miterSolver.addCNF(lits);
      v = invVar;
      // output port will be the inverted var, and use AAG2VAR will get the
      // original one
    }
    IOPorts.push_back(Port(name, v));
  }
  in.close();
}
void readAAG(ifstream &in, bool circuitOne) {
  int litInAAG;
  string aag;
  int M, I, L, O, A;
  in >> aag >> M >> I >> L >> O >> A;
  for (int i = 0; i < I; ++i) {
    int temp;
    in >> temp;
  }
  for (int i = 0; i < O; ++i) {
    int outLit;
    in >> outLit;
  }
  int lf, la, lb;
  for (int i = 0; i < A; ++i) {
    in >> lf >> la >> lb;
    Var vf = AAG2Var(lf / 2, circuitOne);
    Var va = AAG2Var(la / 2, circuitOne);
    bool fa = la % 2;
    Var vb = AAG2Var(lb / 2, circuitOne);
    bool fb = lb % 2;
    miterSolver.addAigCNF(vf, va, fa, vb, fb);
  }
  in.close();
}
void outputAns(ostream &out) {
  std::cout << "----------Optimal Matching----------" << endl;
  std::cout << "Best Score: " << bestScore << endl << endl;
  std::cout << "Input matrix: " << endl;
  for (int i = 0; i < ans_a.size(); ++i) {
    for (int j = 0; j < ans_a[0].size(); ++j) {
      std::cout << ans_a[i][j] << " ";
      std::cout << ans_b[i][j] << " ";
    }
    std::cout << endl;
  }
  std::cout << endl;
  std::cout << "Output matrix: " << endl;
  for (int i = 0; i < ans_c.size(); ++i) {
    for (int j = 0; j < ans_c[0].size(); ++j) {
      std::cout << ans_c[i][j] << " ";
      std::cout << ans_d[i][j] << " ";
    }
    std::cout << endl;
  }

  // output to file as required format
  // INGROUP
  for (int j = 0; j < x.size(); ++j) {
    // all input in circuit 1 must be mapped
    out << "INGROUP" << endl;
    out << "1 + <" << x[j].getName() << ">" << endl; // include "<>" or not ????
    for (int i = 0; i < y.size(); ++i) {
      if (ans_a[i][j] != 0) {
        out << "2 + <" << y[i].getName() << ">" << endl;
      }
      if (ans_b[i][j] != 0) {
        out << "2 - <" << y[i].getName() << ">" << endl;
      }
    }
    out << "END" << endl << endl;
  }
  // OUTGROUP
  for (int j = 0; j < ans_c[0].size(); ++j) {
    bool circuit1Mapped = false;
    for (int i = 0; i < ans_c.size(); ++i) {
      if (ans_c[i][j] || ans_d[i][j]) {
        if (!circuit1Mapped) {
          circuit1Mapped = true;
          out << "OUTGROUP" << endl;
          out << "1 + <" << f[j].getName() << ">" << endl;
        }
        if (ans_c[i][j]) {
          out << "2 + <" << g[i].getName() << ">" << endl;
        } else {
          out << "2 - <" << g[i].getName() << ">" << endl;
        }
      }
    }
    if (circuit1Mapped)
      out << "END" << endl << endl;
  }
  // CONSTGROUP
  out << "CONSTGROUP" << endl;
  for (int i = 0; i < y.size(); ++i) {
    if (ans_a[i][x.size()])
      out << "+ <" << y[i].getName() << ">" << endl; // + to 0
    if (ans_b[i][x.size()])
      out << "- <" << y[i].getName() << ">" << endl; // - to 1
  }
  out << "END" << endl << endl;
}

int getScore(BaseSolver &solver) {
  int score = 0;
  for (int j = 0; j < f.size(); ++j) {
    for (int i = 0; i < fStar.size(); ++i) {
      // Not sure these assertions is correct or not
      assert(solver.getValue(c[i][j].matrixVar) != -1);
      assert(solver.getValue(d[i][j].matrixVar) != -1);
      //

      score += solver.getValue(c[i][j].matrixVar);
      score += solver.getValue(d[i][j].matrixVar);
    }
    score += solver.getValue(ansHelper[j]);
  }
  return score;
}

void genCircuitModel(ifstream &portMapping, ifstream &aag1, ifstream &aig2) {
  x.clear();
  f.clear();
  y.clear();
  g.clear();
  fStar.clear();
  // x/y, f/g

  readPortMapping(portMapping);
  readAAG(aag1, true);
  readAAG(aig2, false);

  for (int i = 0; i < g.size(); ++i) {
    fStar.push_back(miterSolver.newVar());
  }
}

void buildMatrix(BaseSolver &solver) {
  a.clear();
  a.reserve(y.size());
  b.clear();
  b.reserve(y.size());
  c.clear();
  c.reserve(g.size());
  d.clear();
  d.reserve(g.size());

  ans_a = vector<vector<bool>>(y.size(), vector<bool>(x.size() + 1));
  ans_b = vector<vector<bool>>(y.size(), vector<bool>(x.size() + 1));
  ans_c = vector<vector<bool>>(g.size(), vector<bool>(f.size()));
  ans_d = vector<vector<bool>>(g.size(), vector<bool>(f.size()));

  // Input matrix
  for (int i = 0; i < y.size(); ++i) {
    vector<mtx2Mit> aTemp(x.size() + 1);
    vector<mtx2Mit> bTemp(x.size() + 1);
    for (int j = 0; j < x.size(); ++j) {
      aTemp[j].matrixVar = solver.newVar();
      bTemp[j].matrixVar = solver.newVar();
    }
    aTemp[x.size()].matrixVar = solver.newVar();
    bTemp[x.size()].matrixVar = solver.newVar();
    a.push_back(aTemp);
    b.push_back(bTemp);
  }

  // Output matrix
  for (int i = 0; i < fStar.size(); ++i) {
    vector<mtx2Mit> cTemp(f.size());
    vector<mtx2Mit> dTemp(f.size());
    for (int j = 0; j < f.size(); ++j) {
      cTemp[j].matrixVar = solver.newVar();
      dTemp[j].matrixVar = solver.newVar();
    }
    c.push_back(cTemp);
    d.push_back(dTemp);
  }

  // Input constraints
  // sum >= 1
  vector<Lit> ls;
  ls.reserve(2 * y.size());
  for (int j = 0; j < x.size(); ++j) { // exclude the zero/one column
    ls.clear();
    for (int i = 0; i < y.size(); ++i) {
      ls.push_back(Lit(a[i][j].matrixVar));
      ls.push_back(Lit(b[i][j].matrixVar));
    }
    solver.addCNF(ls);
  }
  // sum == 1
  // one hot method
  for (int i = 0; i < y.size(); ++i) {
    vector<Lit> oneHot;
    oneHot.reserve(2 * (x.size() + 1));
    for (int j = 0; j < x.size() + 1; ++j) {
      oneHot.push_back(Lit(a[i][j].matrixVar));
      oneHot.push_back(Lit(b[i][j].matrixVar));
    }
    solver.addOneHot(oneHot);
  }

  // Output constraints
  // SUM(x_i) <= 1 === SUM(~x_i) >= 2 * f.size() - 1
  for (int i = 0; i < fStar.size(); ++i) {
    vector<Lit> lits;
    for (int j = 0; j < f.size(); ++j) {
      lits.push_back(~Lit(c[i][j].matrixVar));
      lits.push_back(~Lit(d[i][j].matrixVar));
    }
    solver.addGte(lits, 2 * f.size() - 1);
  }

  // update score helper Var
  ansHelper.reserve(f.size());
  vector<Lit> aggressiveLits;
  for (int j = 0; j < f.size(); ++j) {
    ansHelper.push_back(solver.newVar());
    // v <-> (all c in column) + (all d in column)
    // => (¬p ∨ v) ∧ (¬q ∨ v) ∧ (¬r ∨ v) ∧ (¬s ∨ v) ∧ (¬v ∨ p ∨ q ∨ r ∨ s)
    vector<Lit> lits;
    lits.push_back(~Lit(ansHelper[j]));
    for (int i = 0; i < g.size(); ++i) {
      lits.push_back(Lit(c[i][j].matrixVar));
      lits.push_back(Lit(d[i][j].matrixVar));

      vector<Lit> lits2;
      lits2.push_back(Lit(ansHelper[j]));
      lits2.push_back(~Lit(c[i][j].matrixVar)); // (~c + v)
      solver.addCNF(lits2);

      lits2[1] = ~Lit(d[i][j].matrixVar); // (~d + v)
      solver.addCNF(lits2);
    }
    solver.addCNF(lits);
    aggressiveLits.push_back(Lit(ansHelper[j]));
  }
  solver.addCNF(aggressiveLits);
}

void genMiterConstraint() {
  // p -> y == x => (~p + x + ~y)(~p + ~x + y)

  // Input constraints
  for (int i = 0; i < y.size(); ++i) {
    for (int j = 0; j < x.size(); ++j) {
      a[i][j].miterVar = miterSolver.newVar();
      vector<Lit> lits;
      lits.push_back(~Lit(a[i][j].miterVar));
      lits.push_back(Lit(x[j].getVar()));
      lits.push_back(~Lit(y[i].getVar()));
      miterSolver.addCNF(lits);

      lits.clear();
      lits.push_back(~Lit(a[i][j].miterVar));
      lits.push_back(~Lit(x[j].getVar()));
      lits.push_back(Lit(y[i].getVar()));
      miterSolver.addCNF(lits);

      b[i][j].miterVar = miterSolver.newVar();
      lits.clear();
      lits.push_back(~Lit(b[i][j].miterVar));
      lits.push_back(~Lit(x[j].getVar()));
      lits.push_back(~Lit(y[i].getVar()));
      miterSolver.addCNF(lits);

      lits.clear();
      lits.push_back(~Lit(b[i][j].miterVar));
      lits.push_back(Lit(x[j].getVar()));
      lits.push_back(Lit(y[i].getVar()));
      miterSolver.addCNF(lits);
    }
    // zero constraint a[i][x.size()] -> ~y[i]
    a[i][x.size()].miterVar = miterSolver.newVar();
    vector<Lit> lits;
    lits.push_back(~Lit(a[i][x.size()].miterVar));
    lits.push_back(~Lit(y[i].getVar()));
    miterSolver.addCNF(lits);

    // one constraint b[i][x.size()] -> y[i]
    b[i][x.size()].miterVar = miterSolver.newVar();
    lits.clear();
    lits.push_back(~Lit(b[i][x.size()].miterVar));
    lits.push_back(Lit(y[i].getVar()));
    miterSolver.addCNF(lits);
  }

  // Output constraints
  for (int i = 0; i < fStar.size(); ++i) {
    for (int j = 0; j < f.size(); ++j) {
      c[i][j].miterVar = miterSolver.newVar();
      vector<Lit> lits;
      lits.push_back(~Lit(c[i][j].miterVar));
      lits.push_back(Lit(fStar[i]));
      lits.push_back(~Lit(f[j].getVar()));
      miterSolver.addCNF(lits);

      lits.clear();
      lits.push_back(~Lit(c[i][j].miterVar));
      lits.push_back(~Lit(fStar[i]));
      lits.push_back(Lit(f[j].getVar()));
      miterSolver.addCNF(lits);

      d[i][j].miterVar = miterSolver.newVar();
      lits.clear();
      lits.push_back(~Lit(d[i][j].miterVar));
      lits.push_back(~Lit(fStar[i]));
      lits.push_back(~Lit(f[j].getVar()));
      miterSolver.addCNF(lits);

      lits.clear();
      lits.push_back(~Lit(d[i][j].miterVar));
      lits.push_back(Lit(fStar[i]));
      lits.push_back(Lit(f[j].getVar()));
      miterSolver.addCNF(lits);
    }
  }

  // x != y => (~x + ~y)(x + y)
  // p <-> (A != B) => (¬A ∨ B ∨ P) ∧ (A ∨ ¬B ∨ P) ∧ (B ∨ A ∨ ¬P) ∧ (¬A ∨ ¬B ∨
  // ¬P)
  vector<Lit> lits;
  for (int i = 0; i < fStar.size(); ++i) {
    Var p = miterSolver.newVar();
    miterSolver.addXorCNF(p, fStar[i], false, g[i].getVar(), false);

    // a <-> b+c+d+e+...+ => (¬B ∨ A) ∧ (¬C ∨ A) ∧ (¬D ∨ A) ∧ (¬E ∨ A) ∧ (¬A ∨ B
    // ∨ C ∨ D ∨ E)
    vector<Lit> lits2;
    Var care = miterSolver.newVar();
    lits2.push_back(~Lit(care));
    for (int j = 0; j < f.size(); ++j) {
      vector<Lit> lits3;
      lits3.push_back(Lit(care));
      lits3.push_back(~Lit(c[i][j].miterVar));
      miterSolver.addCNF(lits3);
      lits3[1] = ~Lit(d[i][j].miterVar);
      miterSolver.addCNF(lits3);
      lits2.push_back(Lit(c[i][j].miterVar));
      lits2.push_back(Lit(d[i][j].miterVar));
    }
    miterSolver.addCNF(lits2);

    // q <-> care & p
    Var q = miterSolver.newVar();
    miterSolver.addAigCNF(q, care, false, p, false);

    lits.push_back(Lit(q)); // q means real no match
  }
  miterSolver.addCNF(lits);
}

void setScoreLowerBound(BaseSolver &solver, int bound) {
  vector<Lit> clause;
  for (int j = 0; j < f.size(); ++j) {
    for (int i = 0; i < fStar.size(); ++i) {
      clause.push_back(Lit(c[i][j].matrixVar));
      clause.push_back(Lit(d[i][j].matrixVar));
    }
    clause.push_back(Lit(ansHelper[j]));
  }
  solver.addGte(clause, bound);
}

void addBusConstraints(const Buses &bus1, const Buses &bus2, bool isInput) {
  Buses::const_iterator it;
  for (it = bus1.begin(); it != bus1.end(); ++it) {
    if (bus2.find(it->first) == bus2.end())
      continue;
    const vector<vector<int>> &buses1 = it->second;
    const vector<vector<int>> &buses2 = bus2.find(it->first)->second;
    // cerr << "BUS with W = " << buses2[bus2Index].size() << endl;
    for (int bus2Index = 0; bus2Index < buses2.size(); ++bus2Index) {
      for (int bus1Index = 0; bus1Index < buses1.size(); ++bus1Index) {
        // p -> sum >= Width
        // p <-> OR
        Var p = busMatrixSolver.newVar();
        vector<Lit> orClause;
        vector<Lit> sumClause;
        assert(buses2[bus2Index].size() ==
               buses1[bus1Index].size()); // the same bus width

        for (int i = 0; i < buses2[bus2Index].size(); ++i) {
          for (int j = 0; j < buses1[bus1Index].size(); ++j) {
            int varIndex1 = buses1[bus1Index][j];
            int varIndex2 = buses2[bus2Index][i];
            if (isInput) {
              orClause.push_back(Lit(a[varIndex2][varIndex1].matrixVar));
              orClause.push_back(Lit(b[varIndex2][varIndex1].matrixVar));
              sumClause.push_back(Lit(a[varIndex2][varIndex1].matrixVar));
              sumClause.push_back(Lit(b[varIndex2][varIndex1].matrixVar));
            } else {
              orClause.push_back(Lit(c[varIndex2][varIndex1].matrixVar));
              orClause.push_back(Lit(d[varIndex2][varIndex1].matrixVar));
              sumClause.push_back(Lit(c[varIndex2][varIndex1].matrixVar));
              sumClause.push_back(Lit(d[varIndex2][varIndex1].matrixVar));
            }
          }
        }
        busMatrixSolver.addOR(Lit(p), orClause);
        busMatrixSolver.addSumConstraint(sumClause, buses2[bus2Index].size(),
                                         Lit(p)); // p -> (sum >= W)
      }
    }
  }
}

void readBusInfo(ifstream &in, bool isCircuit1) {
  string circuitName;
  int nof_bus;
  in >> circuitName;
  in >> nof_bus;
  for (int i = 0; i < nof_bus; ++i) {
    vector<int> bus;
    int width;
    in >> width;
    bool isInput = true;
    for (int j = 0; j < width; ++j) {
      string name;
      in >> name;
      // cerr << "name: " << name << endl;
      vector<Port> &inPorts = isCircuit1 ? x : y;
      vector<Port> &outPorts = isCircuit1 ? f : g;
      int index = getPortIndex(inPorts, name);
      if (index == -1) {
        index = getPortIndex(outPorts, name);
        isInput = false;
      }
      assert(index != -1);
      bus.push_back(index);
    }
    unordered_map<int, vector<vector<int>>> &buses =
        isCircuit1 ? (isInput ? xBus : fBus) : (isInput ? yBus : gBus);
    if (buses.find(width) == buses.end())
      buses[width] = vector<vector<int>>(1, bus);
    else
      buses[width].push_back(bus);
  }
}

unordered_set<Var> findRedundantInputs(BaseSolver &solver) {
  vector<Lit> assumptions;

  auto miter_vars = vector<vector<Port>>();
  // x[i] is stored at assumptions[i]
  // y[i] is stored at assumptions[i + x.size()]
  miter_vars.push_back(x);
  miter_vars.push_back(y);

  miter_vars.push_back(f);
  miter_vars.push_back(g);
  for (auto vars : miter_vars) {
    for (auto v : vars) {
      assumptions.push_back(solver.getValue(v.getVar()) ? Lit(v.getVar())
                                                        : ~Lit(v.getVar()));
    }
  }

  auto mat_vars = vector<vector<vector<mtx2Mit>>>();
  mat_vars.push_back(a);
  mat_vars.push_back(b);
  mat_vars.push_back(c);
  mat_vars.push_back(d);
  for (auto vars : mat_vars) {
    for (auto row : a) {
      for (auto v : row) {
        assumptions.push_back(solver.getValue(v.matrixVar) ? Lit(v.matrixVar)
                                                           : ~Lit(v.matrixVar));
      }
    }
  }

  unordered_set<Var> dontCare;

  // x[i] is stored at assumptions[i]
  // y[i] is stored at assumptions[i + x.size()]
  for (int i = 0; i < x.size(); i++) {
    assumptions[i] = ~assumptions[i];

    solver.setAssumptions(assumptions);
    bool res = solver.assumpSolve();
    if (res) {
      dontCare.insert(x[i].getVar());
    } else {
      assumptions[i] = ~assumptions[i];
    }
  }

  for (int i = 0; i < y.size(); i++) {
    assumptions[i + x.size()] = ~assumptions[i + x.size()];

    solver.setAssumptions(assumptions);
    bool res = solver.assumpSolve();
    if (res) {
      dontCare.insert(y[i].getVar());
    } else {
      assumptions[i + x.size()] = ~assumptions[i + x.size()];
    }
  }

  solver.assumeRelease();

  return dontCare;
}

void solve() {
  setScoreLowerBound(pureMatrixSolver, (f.size() + g.size()) / 2);
  setScoreLowerBound(busMatrixSolver, (f.size() + g.size()) / 2);

  bestScore = 0;
  int iterations = -1;
  int execTime = 0;
  int reportInterval = 1;

  int matrixTime = 0;
  int miterTime = 0;

  bool shouldLog = false;

  while (1) {
    iterations++;

    BaseSolver &matrixSolver =
        iterations % 2 == 0 ? busMatrixSolver : pureMatrixSolver;

    shouldLog = execTime + reportInterval <= (clock() - START) / CLOCKS_PER_SEC;

    if (shouldLog) {
      std::cout << "\r" << std::setw(6) << iterations << " iterations in"
                << std::setw(5) << execTime << " s | " << std::setw(4)
                << ((float)iterations / (execTime + reportInterval))
                << " its/s | " << std::flush;
      execTime = (clock() - START) / CLOCKS_PER_SEC;
    }

    if (bestScore == g.size() + f.size()) {
      std::cout << "\nThis must be the OPT with (#output_port(Circuit I) + "
                   "#output_port(Circuit II)) = "
                << bestScore << endl;
      return;
    }

    matrixTime = clock();
    bool matrixResult = matrixSolver.solve();
    int newMatrixTime = clock();
    if (shouldLog) {
      std::cout << "Matrix:" << std::setw(6) << newMatrixTime - matrixTime
                << " us | " << std::flush;
    }
    matrixTime = newMatrixTime;

    if (!matrixResult) {
      std::cout << "\nNo matching found!" << endl;
      return;
    }
    // Assume input mapping
    miterSolver.assumeRelease();
    for (int i = 0; i < y.size(); ++i) {
      for (int j = 0; j < x.size() + 1; ++j) {
        int matrixVarValue = matrixSolver.getValue(a[i][j].matrixVar);
        if (matrixVarValue != -1) { // -1 means unknown
          miterSolver.assumeProperty(a[i][j].miterVar, matrixVarValue);
        }
        matrixVarValue = matrixSolver.getValue(b[i][j].matrixVar);
        if (matrixVarValue != -1) { // -1 means unknown
          miterSolver.assumeProperty(b[i][j].miterVar, matrixVarValue);
        }
      }
    }

    // Assume output mapping
    for (int i = 0; i < fStar.size(); ++i) {
      for (int j = 0; j < f.size(); ++j) {
        int matrixVarValue = matrixSolver.getValue(c[i][j].matrixVar);
        if (matrixVarValue != -1) // -1 means unknown
          miterSolver.assumeProperty(c[i][j].miterVar, matrixVarValue);
        matrixVarValue = matrixSolver.getValue(d[i][j].matrixVar);
        if (matrixVarValue != -1) // -1 means unknown
          miterSolver.assumeProperty(d[i][j].miterVar, matrixVarValue);
      }
    }

    miterTime = clock();
    // Solve miter
    bool miterResult = miterSolver.assumpSolve();
    int newMiterTime = clock();
    if (shouldLog) {
      std::cout << "Miter:" << std::setw(4) << newMiterTime - miterTime << " us"
                << std::flush;
    }
    miterTime = newMiterTime;

    if (!miterResult) {
      // UNSAT => find a valid mapping
      // update answer and block this answer from matrixSolver

      // Block answer
      vector<Lit> lits;
      for (int i = 0; i < y.size(); ++i) {
        for (int j = 0; j < x.size(); ++j) {
          int value = matrixSolver.getValue(a[i][j].matrixVar);
          assert(value != -1);
          if (value != -1) {
            lits.push_back(value ? ~Lit(a[i][j].matrixVar)
                                 : Lit(a[i][j].matrixVar));
          }
          value = matrixSolver.getValue(b[i][j].matrixVar);
          assert(value != -1);
          if (value != -1) {
            lits.push_back(value ? ~Lit(b[i][j].matrixVar)
                                 : Lit(b[i][j].matrixVar));
          }
        }
      }
      for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
          int value = matrixSolver.getValue(c[i][j].matrixVar);
          assert(value != -1);
          if (value != -1) {
            lits.push_back(value ? ~Lit(c[i][j].matrixVar)
                                 : Lit(c[i][j].matrixVar));
          }
          value = matrixSolver.getValue(d[i][j].matrixVar);
          if (value != -1) {
            lits.push_back(value ? ~Lit(d[i][j].matrixVar)
                                 : Lit(d[i][j].matrixVar));
          }
          assert(value != -1);
        }
      }
      pureMatrixSolver.addCNF(lits);
      busMatrixSolver.addCNF(lits);

      std::cout << "\nFind a valid mapping!" << endl;
      int score = getScore(matrixSolver);
      if (score > bestScore) {
        setScoreLowerBound(pureMatrixSolver, score + 1);
        setScoreLowerBound(busMatrixSolver, score + 1);

        std::cout << "Better mapping!" << endl;
        bestScore = score;
        std::cout << "Input matrix:" << endl;
        for (int i = 0; i < y.size(); ++i) {
          for (int j = 0; j < x.size() + 1; ++j) {
            std::cout << matrixSolver.getValue(a[i][j].matrixVar) << " ";
            std::cout << matrixSolver.getValue(b[i][j].matrixVar) << " ";
            ans_a[i][j] = matrixSolver.getValue(a[i][j].matrixVar);
            ans_b[i][j] = matrixSolver.getValue(b[i][j].matrixVar);
          }
          std::cout << endl;
        }
        std::cout << "Output matrix:" << endl;
        for (int i = 0; i < fStar.size(); ++i) {
          for (int j = 0; j < f.size(); ++j) {
            std::cout << matrixSolver.getValue(c[i][j].matrixVar) << " ";
            std::cout << matrixSolver.getValue(d[i][j].matrixVar) << " ";
            ans_c[i][j] = matrixSolver.getValue(c[i][j].matrixVar);
            ans_d[i][j] = matrixSolver.getValue(d[i][j].matrixVar);
          }
          std::cout << endl;
        }
        std::cout << "Best Score: " << bestScore << endl;
      }
    } else {
      // SAT =>
      // AND(l_O + OR(l_I))
      // l_O = (g[i] != f[j]) ? ~c[i][j] : ~d[i][j]
      // l_I = (x[j] != y[i]) ? a[i][j] : b[i][j]

      vector<bool> tempF;
      for (int i = 0; i < f.size(); ++i) {
        tempF.push_back(miterSolver.getValue(f[i].getVar()));
      }
      vector<bool> tempG;
      for (int i = 0; i < fStar.size(); ++i) {
        tempG.push_back(miterSolver.getValue(g[i].getVar()));
      }
      vector<bool> tempX;
      for (int i = 0; i < x.size(); ++i) {
        tempX.push_back(miterSolver.getValue(x[i].getVar()));
      }
      vector<bool> tempY;
      for (int i = 0; i < y.size(); ++i) {
        tempY.push_back(miterSolver.getValue(y[i].getVar()));
      }

      unordered_set dontCare = findRedundantInputs(miterSolver);

      vector<Lit> lits;
      for (int i = 0; i < fStar.size(); ++i) {
        for (int j = 0; j < f.size(); ++j) {
          if (tempG[i] != tempF[j]) {
            lits.push_back(~Lit(c[i][j].matrixVar));
          } else {
            lits.push_back(~Lit(d[i][j].matrixVar));
          }
          for (int k = 0; k < y.size(); ++k) {
            if (dontCare.find(y[k].getVar()) != dontCare.end()) {
              continue;
            }

            for (int l = 0; l < x.size(); ++l) { // +1 or not
              if (dontCare.find(x[l].getVar()) != dontCare.end()) {
                continue;
              }

              if (tempX[l] != tempY[k]) {
                lits.push_back(Lit(a[k][l].matrixVar));
              } else {
                lits.push_back(Lit(b[k][l].matrixVar));
              }
            }
            if (tempY[k] != 0) {
              lits.push_back(Lit(a[k][x.size()].matrixVar));
            } else {
              lits.push_back(Lit(b[k][x.size()].matrixVar));
            }
          }
          pureMatrixSolver.addCNF(lits);
          busMatrixSolver.addCNF(lits);
          lits.clear();
        }
      }
    }
  }
}

int main(int argc, char **argv) {
  START = clock();
  if (argc != 6) {
    cerr << "Usage: ./bmatch-solver <PortMapping> <AAG1> <AAG2> <input> "
            "<OutputFile>"
         << endl;
    return 0;
  }
  ifstream portMapping(argv[1]);
  ifstream aag1(argv[2]);
  ifstream aag2(argv[3]);
  ifstream input(argv[4]);
  ofstream out(argv[5]);
  if (!portMapping) {
    cerr << "Error: Cannot open PortMapping " << argv[1] << endl;
    return 0;
  }
  if (!aag1) {
    cerr << "Error: Cannot open AAG " << argv[2] << endl;
    return 0;
  }
  if (!aag2) {
    cerr << "Error: Cannot open AAG " << argv[3] << endl;
    return 0;
  }
  if (!input) {
    cerr << "Error: Cannot open input " << argv[4] << endl;
    return 0;
  }
  if (!out) {
    cerr << "Error: Cannot open OutputFile " << argv[5] << endl;
    return 0;
  }

  pureMatrixSolver.initialize();
  busMatrixSolver.initialize();
  miterSolver.initialize();

  genCircuitModel(portMapping, aag1, aag2);
  readBusInfo(input, true);
  readBusInfo(input, false);

  buildMatrix(pureMatrixSolver);
  buildMatrix(busMatrixSolver);
  addBusConstraints(xBus, yBus, true);
  addBusConstraints(fBus, gBus, false);

  genMiterConstraint();

  std::cout << "Start solving..." << endl;
  solve();

  // output ans
  outputAns(out);
}