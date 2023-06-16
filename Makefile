BIN_DIR = bin

$(shell mkdir -p $(BIN_DIR))

all: $(BIN_DIR)/bmatch-solver $(BIN_DIR)/abc $(BIN_DIR)/parser $(BIN_DIR)/aigtoaig

$(BIN_DIR)/bmatch-solver:
	$(MAKE) -C bmatch-solver

$(BIN_DIR)/abc:
	$(MAKE) -C abc -j$((($(nproc)+1)/2))
	cp abc/abc $(BIN_DIR)/abc

$(BIN_DIR)/parser:
	$(MAKE) -C parser

$(BIN_DIR)/aigtoaig:
	cd aiger && ./configure && make
	cp aiger/aigtoaig $(BIN_DIR)/aigtoaig

clean:
	$(MAKE) -C bmatch-solver clean
	$(MAKE) -C abc clean -j$((($(nproc)+1)/2))
	$(MAKE) -C parser clean
	$(MAKE) -C aiger clean
	rm -rf $(BIN_DIR)