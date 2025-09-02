cmake_minimum_required(VERSION 3.5...3.28)

project(AutoQ)

# 3rd party modules
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/Modules/")
# Enable fancy colours
set(CMAKE_COLOR_MAKEFILE ON)
# Enable verbose output for 'make'
# set(CMAKE_VERBOSE_MAKEFILE ON)


##############################################################################
#                             OUTPUT CUSTOMIZATION
##############################################################################

# Avoid dynamic linking of libraries?
OPTION(MAKE_STATIC_AUTOQ "make static library" OFF)

# The default C++ compiler
set(DEFAULT_CXX_COMPILER "g++")

# Build with Clang? -- currently does nothing, initialize with
#   $ CXX=clang++ make debug
# to enable Clang
option(USE_CLANG "build with clang" OFF)
# option(USE_CLANG "build with clang" ON)

# Building with 32-bit memory model (to work e.g. with MONA)
option(BUILD_32B_MEM_MODEL "build with 32-bit memory model" OFF)

# Building with debug information even in release (use e.g. for profiling with Callgrind)
option(DEBUG_INFO_FOR_RELEASE "build with debug info even in release builds" OFF)

##############################################################################
#                               COMPILER FUN
##############################################################################

# enable C++
enable_language(CXX)

set(REQUIRED_GCC_VERSION 4.8.0)
set(GCC_ALTERNATIVES g++ g++-4.8)

# get the git revision
include(GetGitRevisionDescription)
git_describe(GIT_DESCRIBE)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

if (NOT DEFINED CMAKE_CXX_COMPILER)
	set(CMAKE_CXX_COMPILER ${DEFAULT_CXX_COMPILER})
endif()

message("-- Default C++ compiler: ${CMAKE_CXX_COMPILER}")

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
	message("-- Assuming the GNU compiler family")
	set(COMPILER_FAMILY "gcc")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
	message("-- Assuming the Clang compiler family")
	set(COMPILER_FAMILY "clang")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang")
	message("-- Assuming the Clang compiler family")
	set(COMPILER_FAMILY "clang")
else()
	message(FATAL_ERROR "Unsupported compiler family: ${CMAKE_CXX_COMPILER_ID}")
endif()

##############################################################################
#                     TESTING FEATURES OF THE COMPILER
##############################################################################

message("-- Testing suitability of ${CMAKE_CXX_COMPILER}")

if ("${COMPILER_FAMILY}" STREQUAL "gcc")
	# check minimum GCC version
	execute_process(COMMAND ${CMAKE_CXX_COMPILER} -dumpversion
		OUTPUT_VARIABLE GCC_VERSION)

	# check whether the version is non-empty
	if ("${GCC_VERSION}" STREQUAL "")
	message(FATAL_ERROR "-- Cannot get the GCC version")
	endif()

	if (NOT(GCC_VERSION VERSION_GREATER ${REQUIRED_GCC_VERSION}
		OR GCC_VERSION VERSION_EQUAL ${REQUIRED_GCC_VERSION}))

		# in case standard (let's hope) GCC is too old
		foreach (GCC_CANDIDATE ${GCC_ALTERNATIVES})
			if (NOT FOUND_COMPILER)
				execute_process(COMMAND ${GCC_CANDIDATE} -dumpversion RESULT_VARIABLE RES
					OUTPUT_VARIABLE GCC_VERSION)
				if (NOT RES)
					# in case the process ended correctly (i.e., returns 0)
					if (GCC_VERSION VERSION_GREATER ${REQUIRED_GCC_VERSION}
						OR GCC_VERSION VERSION_EQUAL ${REQUIRED_GCC_VERSION})
						# in case the GCC version is usable
						set(CMAKE_CXX_COMPILER ${GCC_CANDIDATE})
						message("-- Using ${CMAKE_CXX_COMPILER} as the C++ compiler")
						set(FOUND_COMPILER 1)
					endif()
				endif()
			endif()
		endforeach(GCC_CANDIDATE)

		if (NOT FOUND_COMPILER)
			message(FATAL_ERROR "GCC and G++ Version >= ${REQUIRED_GCC_VERSION} required!")
		endif()
	endif()
elseif ("${COMPILER_FAMILY}" STREQUAL "clang")
	# message(FATAL_ERROR "Clang currently unsupported!")
	message("-- No fancy checks for ${CMAKE_CXX_COMPILER}, just passing through")
else()
	message(FATAL_ERROR "Unknown compiler family \"${COMPILER_FAMILY}\"")
endif()

# You can force the GCC version here
#set(CMAKE_C_COMPILER "gcc-4.8")
#set(CMAKE_CXX_COMPILER "g++-4.8")

# Support for the 32-bit memory model
if (BUILD_32B_MEM_MODEL)
	if (NOT "${COMPILER_FAMILY}" STREQUAL "gcc")
		message(FATAL_ERROR "32b memory model supported only for GCC (you can fix it yourself in /CMakeLists.txt, I'm too lazy now))")
	endif()

	set(CMAKE_C_FLAGS_RELEASE  "${CMAKE_C_FLAGS_RELEASE} -m32")
	set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -m32")
	message("-- 32b memory model enabled for ${CMAKE_CXX_COMPILER}")
endif()

# Debug information for release builds
if (DEBUG_INFO_FOR_RELEASE)
	set(CMAKE_C_FLAGS_RELEASE  "${CMAKE_C_FLAGS_RELEASE} -g")
	set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -g")
	message("-- Enabling debug information for RELEASE builds")
endif()

# for the use of "concept" and "std::same_as"
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -std=c++20")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -std=c++20")

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DCOMPLEX_FiveTuple")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DCOMPLEX_FiveTuple")

##############################################################################
#                                 PROJECT
##############################################################################

project(autoq)

# Include CTest so that sophisticated testing can be done now
include(CTest)


##############################################################################
#                                DEPENDENCIES
##############################################################################

# Boost
set(Boost_USE_MULTITHREADED OFF)
find_package(Boost 1.71.0...1.89.0 CONFIG COMPONENTS # 1.89.0 is for macOS on GitHub CI
  filesystem
#   system
  unit_test_framework
  REQUIRED)
# IMPORTANT CHANGE: https://github.com/facebook/folly/issues/2489
# Boost.System has been header-only since 1.69.
# If someone increases minimum Boost to 1.71 then can just remove the system component.
include_directories(${Boost_INCLUDE_DIRS})
include_directories(../include/z3)

# Doxygen - voluntary
find_package(Doxygen)
if (DOXYGEN_FOUND)
 configure_file(${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in
   ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile @ONLY)
 add_custom_target(doc
   ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
   WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
   COMMENT "Generating API documentation with Doxygen" VERBATIM)
endif()

##############################################################################
#                                SUB-MODULES
##############################################################################

# Process subdirectories
add_subdirectory(src)
add_subdirectory(cli)
add_subdirectory(unit_tests)
# add_subdirectory(tests)
