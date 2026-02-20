cmake_minimum_required(VERSION 3.5...3.28)

project(unit_tests)

include_directories(../include)
include_directories(../include/z3)

set(TESTS
# 	"ondriks_mtbdd_c_test"
#   "timbuk_parser_test"
# 	"bdd_bu_tree_aut_test"
# 	"bdd_td_tree_aut_test"
  "explicit_tree_aut_test"
)

foreach (TEST ${TESTS})
	add_executable(${TEST} ${TEST}.cc)
	target_link_libraries(${TEST} lsta)
	target_link_libraries(${TEST} ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY})
	target_link_libraries(${TEST} ${Boost_FILESYSTEM_LIBRARY})
	target_link_libraries(${TEST} ${Boost_SYSTEM_LIBRARY})

	add_test(${TEST} ${CMAKE_CURRENT_BINARY_DIR}/${TEST})
endforeach(TEST)
