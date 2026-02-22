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
