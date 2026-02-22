cmake_minimum_required(VERSION 3.5...3.28)

project(unit_tests)

include_directories(../include)
include_directories(../include/z3)

set(TESTS
  "explicit_tree_aut_test"
  "qasm_parsing_inclusion_cli_test"
)

foreach (TEST ${TESTS})
	add_executable(${TEST} ${TEST}.cc)
	target_link_libraries(${TEST} lsta)
	target_link_libraries(${TEST} ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY})
	target_link_libraries(${TEST} ${Boost_FILESYSTEM_LIBRARY})

	if (${TEST} STREQUAL "qasm_parsing_inclusion_cli_test")
		target_compile_definitions(${TEST} PRIVATE
			AUTOQ_CLI_PATH="${CMAKE_BINARY_DIR}/cli/autoq")
	endif()

	add_test(${TEST} ${CMAKE_CURRENT_BINARY_DIR}/${TEST})
endforeach(TEST)
