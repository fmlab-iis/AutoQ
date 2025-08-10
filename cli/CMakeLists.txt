cmake_minimum_required(VERSION 3.5...3.28)

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
  -DCOMPLEX_FiveTuple
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

# Get all files in the current directory
file(GLOB main_files "${CMAKE_CURRENT_SOURCE_DIR}/*.cc")
# Loop through each file
foreach(file ${main_files})
    get_filename_component(binary ${file} NAME_WLE)
    add_executable(${binary} ${file} ${CMAKE_CURRENT_BINARY_DIR}/version.cc)
    get_target_property(sources ${binary} SOURCES)
    foreach(src ${sources})
        set_source_files_properties(${src} PROPERTIES COMPILE_FLAGS ${autoq_compiler_flags})
    endforeach()
    target_link_libraries(${binary} lsta)
endforeach()

if (MAKE_STATIC_AUTOQ)
  SET(CMAKE_CXX_LINK_EXECUTABLE "${CMAKE_CXX_LINK_EXECUTABLE} -static")
endif()
