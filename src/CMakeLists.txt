cmake_minimum_required(VERSION 3.5...3.28)

set(CMAKE_COLOR_MAKEFILE ON)
#set(CMAKE_VERBOSE_MAKEFILE ON)

project(autoq)

# Export compile commands to be used with YouCompleteMe
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Library-only: -fPIC (common flags from parent)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

include_directories(../include)

# Automatically find all .cc files recursively in the specified directory
file(GLOB_RECURSE SOURCE_FILES "${CMAKE_CURRENT_SOURCE_DIR}/*.cc" "${CMAKE_CURRENT_SOURCE_DIR}/*.cpp")
add_library(lsta STATIC ${SOURCE_FILES})

# Suppress all warnings in the mentioned directory
file(GLOB_RECURSE Extended_Dirac_SOURCE_FILES "./ExtendedDirac/*.cpp")
set_source_files_properties(${Extended_Dirac_SOURCE_FILES} PROPERTIES COMPILE_FLAGS "-w")

##############################################################################
#                              DEPENDENCIES - Z3
##############################################################################

# USE_SYSTEM_Z3 is defined in the parent CMakeLists.txt (change OFF to ON there to use system Z3).
if (APPLE)
    target_link_libraries(lsta "${CMAKE_CURRENT_SOURCE_DIR}/../libz3.a")
elseif (UNIX)
    if (USE_SYSTEM_Z3)
        find_library(Z3_LIBRARY z3)
        if (Z3_LIBRARY)
            target_link_libraries(lsta ${Z3_LIBRARY})
            message(STATUS "Using system Z3: ${Z3_LIBRARY}")
        else ()
            message(STATUS "USE_SYSTEM_Z3=ON but Z3 not found, falling back to bundled libz3.so.4.12")
            target_link_libraries(lsta "${CMAKE_CURRENT_SOURCE_DIR}/../libz3.so.4.12")
        endif ()
    else ()
        target_link_libraries(lsta "${CMAKE_CURRENT_SOURCE_DIR}/../libz3.so.4.12")
    endif ()
endif ()
include_directories(../include/z3)

##############################################################################
#                              DEPENDENCIES - ANTLR
##############################################################################
if (APPLE)
    execute_process(
        COMMAND brew --prefix antlr4-cpp-runtime
        OUTPUT_VARIABLE ANTLR4_CPP_RUNTIME_PREFIX
    )
    string(STRIP "${ANTLR4_CPP_RUNTIME_PREFIX}" ANTLR4_CPP_RUNTIME_PREFIX)
    target_link_libraries(lsta "${ANTLR4_CPP_RUNTIME_PREFIX}/lib/libantlr4-runtime.a") # have not been built yet
elseif (UNIX)
    target_link_libraries(lsta antlr4-runtime)
#     target_link_libraries(lsta "${CMAKE_CURRENT_SOURCE_DIR}/../libantlr4-runtime.so.4.13.2")
endif ()
include_directories(../include/antlr4-runtime)
include_directories(../include/autoq/parsing/ExtendedDirac)

# https://www.weiy.city/2022/06/use-cmake-to-import-shared-library-or-static-library/
# https://bayareanotes.com/cmake-adding-external-library/
