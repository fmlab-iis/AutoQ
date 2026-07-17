BUILD_DIR=build
# Use nproc on Linux, sysctl on macOS, fallback 2
MAKE_FLAGS=-j$(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)
# TEST_FLAGS=-j 8
TEST_FLAGS=--output-on-failure

.PHONY: debug release clean test create_folder

release: create_folder
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Release .. && $(MAKE) $(MAKE_FLAGS)

create_folder:
	@mkdir -p $(BUILD_DIR)

debug: create_folder
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Debug .. && $(MAKE) $(MAKE_FLAGS)

test: create_folder
	cd $(BUILD_DIR) && ctest $(TEST_FLAGS)

clean: create_folder
	cd $(BUILD_DIR) && rm -rf *

# Argument handling for generate_circuit
ifeq ($(firstword $(MAKECMDGOALS)),generate_circuit)
  GEN_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  $(eval $(GEN_ARGS):;@:)
endif

generate_circuit:
	@NAME=$(word 1,$(GEN_ARGS)); \
	N=$(word 2,$(GEN_ARGS)); \
	if [ -z "$$NAME" ] || [ -z "$$N" ]; then \
		echo "Usage: make generate_circuit <name> <n>"; \
		exit 1; \
	fi; \
	NAME_UPPER=$$(echo $$NAME | tr '[:lower:]' '[:upper:]'); \
	DIR="benchmarks/$$NAME_UPPER/q$$N"; \
	SCRIPT="benchmarks/$$NAME_UPPER/circuit.qasm.mako.py"; \
	if [ ! -f "$$SCRIPT" ]; then \
		echo "Error: Generator script $$SCRIPT not found."; \
		exit 1; \
	fi; \
	mkdir -p $$DIR; \
	./$$SCRIPT $$N > $$DIR/circuit.qasm; \
	echo "Generated $$DIR/circuit.qasm"