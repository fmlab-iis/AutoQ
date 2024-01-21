cmake_minimum_required(VERSION 3.0.0)

set(CMAKE_COLOR_MAKEFILE ON)
#set(CMAKE_VERBOSE_MAKEFILE ON)

project(autoq)

set(autoq_compiler_add_flags_list
  -std=c++20
  -pedantic-errors
#  -DOPT_AC
  -DCACHE_AC
#  -DCACHE_CONGR
 # -DOPT_CONGR
  -DCACHE_OPT_CONGR
  -Wextra
  -Wall
  -Wfloat-equal
  -Wctor-dtor-privacy
  -Weffc++
  -Woverloaded-virtual
  -Wold-style-cast
  -fdiagnostics-show-option
  # -march=native
)

foreach(param ${autoq_compiler_add_flags_list})
  set(autoq_compiler_flags "${autoq_compiler_flags} ${param}")
endforeach(param)

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

include_directories(../include)

# generate the file with version names
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.cc.in
   ${CMAKE_CURRENT_BINARY_DIR}/version.cc @ONLY)

add_executable(autoq
  autoq.cc
#   parse_args.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(autoq_pldi
  autoq_pldi.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(autoq_cav24_symbolic
  autoq_cav24_symbolic.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(autoq_cav24_concrete
  autoq_cav24_concrete.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(hsl_concrete
  hsl_concrete.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(hsl_symbolic
  hsl_symbolic.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(hsl_predicate
  hsl_predicate.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(print_language
  print_language.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

add_executable(symbolic_execution
symbolic_execution.cc
  ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

if (MAKE_STATIC_AUTOQ)
  SET(CMAKE_CXX_LINK_EXECUTABLE "${CMAKE_CXX_LINK_EXECUTABLE} -static")
endif()

get_target_property(autoq_sources autoq SOURCES)

foreach(src ${autoq_sources})

  set_source_files_properties(
    ${src} PROPERTIES COMPILE_FLAGS ${autoq_compiler_flags})

endforeach()

target_link_libraries(autoq libautoq)
target_link_libraries(autoq_pldi libautoq)
target_link_libraries(autoq_cav24_symbolic libautoq)
target_link_libraries(autoq_cav24_concrete libautoq)
target_link_libraries(hsl_concrete libautoq)
target_link_libraries(hsl_symbolic libautoq)
target_link_libraries(hsl_predicate libautoq)
target_link_libraries(print_language libautoq)
target_link_libraries(symbolic_execution libautoq)