cmake_minimum_required(VERSION 3.0.0)

set(CMAKE_COLOR_MAKEFILE ON)
#set(CMAKE_VERBOSE_MAKEFILE ON)

# project(autoq)

# Export compile commands to be used with YouCompleteMe
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Flags for AUTOQ
set(autoq_cxx_compiler_flags
  -pedantic-errors
  -Wextra
  -Wall
  -Wfloat-equal
  -fdiagnostics-show-option
  -std=c++20
  -Wctor-dtor-privacy
  -Weffc++
  -fPIC
  -Woverloaded-virtual
  -Wold-style-cast
)

foreach(flag ${autoq_cxx_compiler_flags})
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endforeach()

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

include_directories(../include)

add_library(autoq STATIC
	# aut_base.cc
	# explicit_tree_aut_core.cc
	# explicit_tree_comp_down.cc
	# explicit_tree_incl_down.cc
	# explicit_tree_incl_up.cc
	# explicit_lts_sim.cc
	# explicit_tree_aut.cc
	# explicit_tree_candidate.cc
	# explicit_tree_union.cc
	# explicit_tree_isect.cc
	# explicit_tree_isect_bu.cc
	# explicit_tree_incl.cc
	# explicit_tree_unreach.cc
	# explicit_tree_useless.cc
	# explicit_tree_sim.cc
	# convert.cc
	# incl_param.cc
	# symbolic.cc
	timbuk_parser-nobison.cc
	timbuk_serializer.cc
	util.cc
    memory_usage.cpp
	# sym_var_asgn.cc
	# symbolic_tree_aut_base_core.cc
	util/simulation/explicit_lts_sim.cc
    util/execute.cc
	util/aut_operation.cc
    util/aut_operation_all.cc
	util/gate_operation.cc
)

# set_target_properties(autoq PROPERTIES
#   OUTPUT_NAME autoq
#   CLEAN_DIRECT_OUTPUT 1
# )

##############################################################################
#                              DEPENDENCIES - Z3
##############################################################################

# find_package(Z3 4.12.5
#   REQUIRED
#   CONFIG
#   # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
#   # This should prevent us from accidentally picking up an installed
#   # copy of Z3. This is here to benefit Z3's build system when building
#   # this project. When making your own project you probably shouldn't
#   # use this option.
#   NO_DEFAULT_PATH
# )
# target_link_libraries(autoq ${Z3_LIBRARIES})
target_link_libraries(autoq "${CMAKE_CURRENT_SOURCE_DIR}/../libz3.so.4.12")
include_directories(../include/z3)

# https://www.weiy.city/2022/06/use-cmake-to-import-shared-library-or-static-library/
# https://bayareanotes.com/cmake-adding-external-library/