cmake_minimum_required(VERSION 3.10)
project(ctaes C)
set(CMAKE_C_STANDARD 90)
include(GNUInstallDirs REQUIRED)

# pass basic flags to compilers depending on compiler
if ("${CMAKE_C_COMPILER_ID}" MATCHES "Clang" OR "${CMAKE_C_COMPILER_ID}" STREQUAL "GNU")
    set(CMAKE_C_FLAGS "-Wall -Wextra -Wundef -Wpointer-arith -Wconversion" CACHE STRING "C compiler flags" FORCE)
elseif ("${CMAKE_C_COMPILER_ID}" STREQUAL "MSVC")
    set(CMAKE_C_FLAGS "/Wall /sdl /MP" CACHE STRING "C compiler flags" FORCE )
endif()
message("-- C flags being used: ${CMAKE_C_FLAGS}")

# ctaes library
add_library(ctaes STATIC ctaes.c ctaes.h)

target_include_directories(ctaes
        PUBLIC
            $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
            $<INSTALL_INTERFACE:include>
)

# tests
enable_testing()
add_executable(tests test.c)
target_link_libraries(tests PRIVATE ctaes)
add_test(tests tests)  # add test to runner

# bench
add_executable(bench bench.c)
target_link_libraries(bench PRIVATE ctaes)

# installation and config file for other CMake projects to import
# defaults to /usr/local in linux and C:/Program Files(x86) in Windows
install(TARGETS ctaes EXPORT ctaesConfig
        ARCHIVE  DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY  DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME  DESTINATION ${CMAKE_INSTALL_BINDIR})
install(FILES ctaes.h DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
install(EXPORT ctaesConfig DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/ctaes)

# This makes the project importable from the build directory
export(TARGETS ctaes FILE ctaesConfig.cmake)