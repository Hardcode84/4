# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
cmake_minimum_required(VERSION 3.17)
project(ixsimpl C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

option(USE_AMALGAMATION "Build from single-file ixsimpl_amalg.c" OFF)

if(USE_AMALGAMATION)
    set(LIB_SOURCES ixsimpl_amalg.c)
else()
    set(LIB_SOURCES
        src/additive_row.c
        src/arena.c
        src/bounds.c
        src/ctx.c
        src/division_algebra.c
        src/expand.c
        src/import.c
        src/interval.c
        src/low_bits_algebra.c
        src/node.c
        src/parser.c
        src/print.c
        src/quotient_algebra.c
        src/radix_algebra.c
        src/rational.c
        src/relation_algebra.c
        src/serialize.c
        src/simplify.c
        src/walk.c
    )
endif()

# --- Python extension (driven by scikit-build-core) ---

if(SKBUILD)
    find_package(Python COMPONENTS Interpreter Development.Module REQUIRED)

    python_add_library(_ixsimpl MODULE WITH_SOABI
        bindings/python/_ixsimpl.c
        ${LIB_SOURCES}
    )
    target_include_directories(_ixsimpl PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CMAKE_CURRENT_SOURCE_DIR}/src
    )
    set_target_properties(_ixsimpl PROPERTIES C_VISIBILITY_PRESET hidden)

    install(TARGETS _ixsimpl DESTINATION ixsimpl)
    return()
endif()

# --- Standalone C library + tests + benchmarks ---

add_compile_options(-pedantic -Wall -Wextra -Werror)

option(ENABLE_ASAN "Build with AddressSanitizer" OFF)
if(ENABLE_ASAN)
    add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
    add_link_options(-fsanitize=address)
endif()

option(ENABLE_STATS "Build with rule-hit statistics (IXS_STATS)" OFF)
if(ENABLE_STATS)
    add_compile_definitions(IXS_STATS)
endif()

add_library(ixsimpl STATIC ${LIB_SOURCES})
target_include_directories(ixsimpl
    PUBLIC  ${CMAKE_CURRENT_SOURCE_DIR}/include
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# --- Tests ---

enable_testing()

# Tests that use only the public API — always built.

add_executable(test_parser test/test_parser.c)
target_link_libraries(test_parser ixsimpl)
add_test(NAME test_parser COMMAND test_parser)

add_executable(test_relational_contract test/test_relational_contract.c)
target_link_libraries(test_relational_contract ixsimpl)
add_test(NAME test_relational_contract COMMAND test_relational_contract)

# Stats-enabled build: test_simplify links this to collect rule hit counts.
add_library(ixsimpl_stats STATIC ${LIB_SOURCES})
target_include_directories(ixsimpl_stats
    PUBLIC  ${CMAKE_CURRENT_SOURCE_DIR}/include
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src
)
target_compile_definitions(ixsimpl_stats PRIVATE IXS_STATS IXS_TEST_INTERNAL)

add_executable(test_simplify test/test_simplify.c)
target_link_libraries(test_simplify ixsimpl_stats)
if(NOT USE_AMALGAMATION)
    target_include_directories(test_simplify PRIVATE src)
    target_compile_definitions(test_simplify PRIVATE IXS_TEST_INTERNAL)
endif()
add_test(NAME test_simplify COMMAND test_simplify)

add_executable(test_corpus test/test_corpus.c)
target_link_libraries(test_corpus ixsimpl)
add_test(NAME test_corpus COMMAND test_corpus
         WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})
add_test(NAME test_corpus_gemm256x192 COMMAND test_corpus
         --corpus=test/corpus_gemm256x192.txt
         --assumptions=test/corpus_gemm256x192_assumptions.txt
         --expected=test/corpus_gemm256x192_expected.txt
         WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

add_executable(test_edge_cases test/test_edge_cases.c)
target_link_libraries(test_edge_cases ixsimpl)
add_test(NAME test_edge_cases COMMAND test_edge_cases)

add_executable(test_introspect test/test_introspect.c)
target_link_libraries(test_introspect ixsimpl)
add_test(NAME test_introspect COMMAND test_introspect)

# The C++ wrapper is optional for C-only hosts, but test it whenever a C++17
# compiler is available.
include(CheckLanguage)
check_language(CXX)
if(CMAKE_CXX_COMPILER)
    enable_language(CXX)
    add_executable(test_cpp test/test_cpp.cpp)
    target_link_libraries(test_cpp ixsimpl)
    target_include_directories(test_cpp PRIVATE bindings/cpp)
    set_target_properties(test_cpp PROPERTIES
        CXX_STANDARD 17
        CXX_STANDARD_REQUIRED ON
        CXX_EXTENSIONS OFF
    )
    add_test(NAME test_cpp COMMAND test_cpp)
endif()

add_executable(test_expand test/test_expand.c)
target_link_libraries(test_expand ixsimpl)
target_include_directories(test_expand PRIVATE src)
if(USE_AMALGAMATION)
    target_compile_definitions(test_expand PRIVATE IXS_TEST_AMALGAMATION)
endif()
add_test(NAME test_expand COMMAND test_expand)

add_executable(test_import test/test_import.c)
target_link_libraries(test_import ixsimpl)
target_include_directories(test_import PRIVATE src)
if(USE_AMALGAMATION)
    target_compile_definitions(test_import PRIVATE IXS_TEST_AMALGAMATION)
endif()
add_test(NAME test_import COMMAND test_import)

add_executable(test_serialize test/test_serialize.c)
target_link_libraries(test_serialize ixsimpl)
target_include_directories(test_serialize PRIVATE src)
if(USE_AMALGAMATION)
    target_compile_definitions(test_serialize PRIVATE IXS_TEST_AMALGAMATION)
endif()
add_test(NAME test_serialize COMMAND test_serialize)

# Tests that need internal symbols — skipped in amalgamated builds.

if(NOT USE_AMALGAMATION)
    add_executable(test_rational test/test_rational.c)
    target_link_libraries(test_rational ixsimpl)
    target_include_directories(test_rational PRIVATE src)
    add_test(NAME test_rational COMMAND test_rational)

    add_executable(test_arena test/test_arena.c)
    target_link_libraries(test_arena ixsimpl)
    target_include_directories(test_arena PRIVATE src)
    add_test(NAME test_arena COMMAND test_arena)

    add_executable(test_bounds test/test_bounds.c)
    target_link_libraries(test_bounds ixsimpl_stats)
    target_include_directories(test_bounds PRIVATE src)
    target_compile_definitions(test_bounds PRIVATE IXS_TEST_INTERNAL)
    add_test(NAME test_bounds COMMAND test_bounds)

    add_executable(test_equivalence_context test/test_equivalence_context.c)
    target_link_libraries(test_equivalence_context ixsimpl_stats)
    target_include_directories(test_equivalence_context PRIVATE src)
    target_compile_definitions(test_equivalence_context PRIVATE IXS_TEST_INTERNAL)
    add_test(NAME test_equivalence_context COMMAND test_equivalence_context)

    add_executable(test_piecewise_equivalence test/test_piecewise_equivalence.c)
    target_link_libraries(test_piecewise_equivalence ixsimpl_stats)
    target_include_directories(test_piecewise_equivalence PRIVATE src)
    target_compile_definitions(test_piecewise_equivalence PRIVATE IXS_TEST_INTERNAL)
    add_test(NAME test_piecewise_equivalence COMMAND test_piecewise_equivalence)
endif()

# --- Static hot-path complexity check ---

# Skipped silently when the tree-sitter Python modules are absent; the
# pre-commit hook (which pins its own environment) is the enforcing gate.
find_package(Python3 COMPONENTS Interpreter QUIET)
if(Python3_FOUND)
  execute_process(
    COMMAND ${Python3_EXECUTABLE} -c "import tree_sitter, tree_sitter_c"
    RESULT_VARIABLE IXS_TREE_SITTER_OK
    OUTPUT_QUIET ERROR_QUIET)
  if(IXS_TREE_SITTER_OK EQUAL 0)
    add_test(NAME check_hotpaths
             COMMAND ${Python3_EXECUTABLE}
                     ${CMAKE_CURRENT_SOURCE_DIR}/scripts/check_hotpaths.py
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
  endif()
endif()

# --- Benchmark ---

add_executable(bench_corpus bench/bench_corpus.c)
target_link_libraries(bench_corpus ixsimpl)

add_executable(bench_relational_facts bench/bench_relational_facts.c)
target_link_libraries(bench_relational_facts ixsimpl)
