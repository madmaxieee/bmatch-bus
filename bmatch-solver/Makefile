CC_FLAGS = -std=c++2a -Wno-deprecated-declarations
OPT_FLAGS = -O3
DBG_FLAGS = -g -fsanitize=address

CADICAL_DIR = ./cadical
LIBCADICAL = $(CADICAL_DIR)/build/libcadical.a

BIN_DIR = ../bin

$(shell mkdir -p $(BIN_DIR))

all: $(BIN_DIR)/bmatch-solver

$(BIN_DIR)/bmatch-solver: src/File.o src/Proof.o src/Solver.o src/main.o $(LIBCADICAL) src/BaseSolver.h src/CadicalSolver.h
	g++ -o $@ $(CC_FLAGS) $(OPT_FLAGS) src/File.o src/Proof.o src/Solver.o src/main.o $(LIBCADICAL) -o $(BIN_DIR)/bmatch-solver

src/%.o: src/%.cpp
	g++ -c $(CC_FLAGS) $(OPT_FLAGS) $< -o $@

src/%.h:

$(LIBCADICAL): $(CADICAL_DIR)/configure $(CADICAL_DIR)/makefile
	cd $(CADICAL_DIR) && ./configure && $(MAKE) -j$((($(nproc)+1)/2))

$(CADICAL_DIR)/configure:

$(CADICAL_DIR)/makefile:

CASE_DIR_PREFIX = ./CAD_testdata/case

test_%: $(BIN_DIR)/bmatch-solver
	$(BIN_DIR)/bmatch-solver $(CASE_DIR_PREFIX)$*/name $(CASE_DIR_PREFIX)$*/circuit_1.aag $(CASE_DIR_PREFIX)$*/circuit_2.aag \
	$(CASE_DIR_PREFIX)$*/input $(CASE_DIR_PREFIX)$*/match

clean:
	rm -f *.o $(BIN_DIR)/bmatch-solver
