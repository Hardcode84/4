cmake_minimum_required(VERSION 3.10)
project(ixsimpl C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

add_compile_options(-pedantic -Wall -Wextra -Werror)

option(ENABLE_ASAN "Build with AddressSanitizer" OFF)
if(ENABLE_ASAN)
    add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
    add_link_options(-fsanitize=address)
endif()

# --- Library ---

set(LIB_SOURCES
    src/arena.c
    src/rational.c
    src/node.c
    src/simplify.c
    src/bounds.c
    src/print.c
    src/parser.c
    src/ctx.c
)

add_library(ixsimpl STATIC ${LIB_SOURCES})
target_include_directories(ixsimpl
    PUBLIC  ${CMAKE_CURRENT_SOURCE_DIR}/include
    PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# --- Tests ---

enable_testing()

add_executable(test_rational test/test_rational.c)
target_link_libraries(test_rational ixsimpl)
target_include_directories(test_rational PRIVATE src)
add_test(NAME test_rational COMMAND test_rational)

add_executable(test_parser test/test_parser.c)
target_link_libraries(test_parser ixsimpl)
target_include_directories(test_parser PRIVATE src)
add_test(NAME test_parser COMMAND test_parser)

add_executable(test_simplify test/test_simplify.c)
target_link_libraries(test_simplify ixsimpl)
target_include_directories(test_simplify PRIVATE src)
add_test(NAME test_simplify COMMAND test_simplify)

add_executable(test_corpus test/test_corpus.c)
target_link_libraries(test_corpus ixsimpl)
target_include_directories(test_corpus PRIVATE src)
add_test(NAME test_corpus COMMAND test_corpus
         WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

add_executable(test_edge_cases test/test_edge_cases.c)
target_link_libraries(test_edge_cases ixsimpl)
target_include_directories(test_edge_cases PRIVATE src)
add_test(NAME test_edge_cases COMMAND test_edge_cases)

# --- Benchmark ---

add_executable(bench_corpus bench/bench_corpus.c)
target_link_libraries(bench_corpus ixsimpl)
target_include_directories(bench_corpus PRIVATE src)
