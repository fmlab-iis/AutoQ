cmake_minimum_required(VERSION 3.0.0)

set(CMAKE_COLOR_MAKEFILE ON)
#set(CMAKE_VERBOSE_MAKEFILE ON)

project(autoq)

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
  -DCOMPLEX_nTuple
)

foreach(flag ${autoq_cxx_compiler_flags})
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endforeach()

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

include_directories(../include)

add_library(libautoq STATIC
	timbuk_parser-nobison.cc
	timbuk_serializer.cc
    util/string.cc
	util/util.cc
    util/memory.cpp
	simulation/explicit_lts_sim.cc
    reduce.cc
    execute.cc
    inclusion.cc
    instance.cc
	parameterized.cc
    query.cc
	gate.cc
)

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
# target_link_libraries(libautoq ${Z3_LIBRARIES})
target_link_libraries(libautoq "${CMAKE_CURRENT_SOURCE_DIR}/../libz3.so.4.12")
include_directories(../include/z3)

# https://www.weiy.city/2022/06/use-cmake-to-import-shared-library-or-static-library/
# https://bayareanotes.com/cmake-adding-external-library/
