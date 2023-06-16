CC_FLAGS = -std=c++2a -Wno-deprecated-declarations
OPT_FLAGS = -O3
DBG_FLAGS = -g -fsanitize=address

BIN_DIR = ../bin

$(shell mkdir -p $(BIN_DIR))

all: $(BIN_DIR)/parser $(BIN_DIR)/aig_map

$(BIN_DIR)/parser: parser.cpp
	$(CXX) $(CC_FLAGS) $(OPT_FLAGS) $< -o $@

$(BIN_DIR)/aig_map: aig_map.cpp
	$(CXX) $(CC_FLAGS) $(OPT_FLAGS) $< -o $@

clean:
	rm -f *.o $(BIN_DIR)/parser $(BIN_DIR)/aig_map
	