#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
include(CMakePushCheckState)

# Function to extract Z3 version from z3_version.h
function(get_z3_version)
    set(Z3_VERSION_HEADER "${Z3_INCLUDE_DIRS}/z3_version.h")

    if(EXISTS "${Z3_VERSION_HEADER}")
        file(READ "${Z3_VERSION_HEADER}" Z3_VERSION_CONTENT)

        string(REGEX MATCH "#define Z3_MAJOR_VERSION[ \t]+([0-9]+)" _ ${Z3_VERSION_CONTENT})
        set(Z3_VERSION_MAJOR ${CMAKE_MATCH_1})

        string(REGEX MATCH "#define Z3_MINOR_VERSION[ \t]+([0-9]+)" _ ${Z3_VERSION_CONTENT})
        set(Z3_VERSION_MINOR ${CMAKE_MATCH_1})

        string(REGEX MATCH "#define Z3_BUILD_NUMBER[ \t]+([0-9]+)" _ ${Z3_VERSION_CONTENT})
        set(Z3_VERSION_PATCH ${CMAKE_MATCH_1})

        set(Z3_VERSION "${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.${Z3_VERSION_PATCH}" PARENT_SCOPE)
    else()
        message(FATAL_ERROR "z3_version.h not found in ${Z3_INCLUDE_DIRS}")
    endif()
endfunction()

find_package(Z3)
# Set the default so that if the following is true:
# * Z3 was found
# * ENABLE_SOLVER_Z3 is not already set as a cache variable
#
# then the default is set to `ON`. Otherwise set the default to `OFF`.
# A consequence of this is if we fail to detect Z3 the first time
# subsequent calls to CMake will not change the default.
if (Z3_FOUND)
  set(ENABLE_SOLVER_Z3_DEFAULT ON)
else()
  set(ENABLE_SOLVER_Z3_DEFAULT OFF)
endif()
option(ENABLE_SOLVER_Z3 "Enable Z3 solver support" ${ENABLE_SOLVER_Z3_DEFAULT})

if (ENABLE_SOLVER_Z3)
  message(STATUS "Z3 solver support enabled")
  if (Z3_FOUND)
    message(STATUS "Found Z3")
    set(ENABLE_Z3 1) # For config.h
    list(APPEND KLEE_COMPONENT_EXTRA_INCLUDE_DIRS ${Z3_INCLUDE_DIRS})
    list(APPEND KLEE_SOLVER_LIBRARIES ${Z3_LIBRARIES})

    # Call the function to get Z3 version
    get_z3_version()

    message(STATUS "Z3 found: ${Z3_LIBRARIES}, version ${Z3_VERSION}")
    
    # Split the version into its components
    string(REPLACE "." ";" Z3_VERSION_LIST ${Z3_VERSION})
    list(GET Z3_VERSION_LIST 0 Z3_VERSION_MAJOR)
    list(GET Z3_VERSION_LIST 1 Z3_VERSION_MINOR)

    # Check if the Z3 version is greater than 4.4
    if((Z3_VERSION_MAJOR GREATER 4) OR (Z3_VERSION_MAJOR EQUAL 4 AND Z3_VERSION_MINOR GREATER 8))
        message(STATUS "Z3 version is greater than 4.8")
    else()
        message(STATUS "Z3 version is 4.8 or lower")
        klee_component_add_cxx_flag("-DUSE_OLD_Z3")
    endif()

    # Check the signature of `Z3_get_error_msg()`
    cmake_push_check_state()
    set(CMAKE_REQUIRED_INCLUDES ${CMAKE_REQUIRED_INCLUDES} ${Z3_INCLUDE_DIRS})
    set(CMAKE_REQUIRED_LIBRARIES ${CMAKE_REQUIRED_LIBRARIES} ${Z3_LIBRARIES})

    check_cxx_source_compiles("
    #include <z3.h>
    void custom_z3_error_handler(Z3_context ctx, Z3_error_code ec) {
      ::Z3_string errorMsg = Z3_get_error_msg(ctx, ec);
    }
    int main(int argc, char** argv) {
        return 0;
    }
    " HAVE_Z3_GET_ERROR_MSG_NEEDS_CONTEXT)
    cmake_pop_check_state()
    if (HAVE_Z3_GET_ERROR_MSG_NEEDS_CONTEXT)
      message(STATUS "Z3_get_error_msg requires context")
    else()
      message(STATUS "Z3_get_error_msg does not require context")
    endif()
  else()
    message(FATAL_ERROR "Z3 not found.")
  endif()
else()
  message(STATUS "Z3 solver support disabled")
  set(ENABLE_Z3 0) # For config.h
endif()
