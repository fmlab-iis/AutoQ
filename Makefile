BUILD_DIR=build
# MAKE_FLAGS=-j 8
# TEST_FLAGS=-j 8
TEST_FLAGS=--output-on-failure

.PHONY: debug release clean test

debug:
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Debug .. && $(MAKE) $(MAKE_FLAGS)

release:
	cd $(BUILD_DIR) && cmake -DCMAKE_BUILD_TYPE=Release .. && $(MAKE) $(MAKE_FLAGS)

test:
	cd $(BUILD_DIR) && ctest $(TEST_FLAGS)

clean:
	cd $(BUILD_DIR) && rm -rf *
