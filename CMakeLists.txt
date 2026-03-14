cmake_minimum_required(VERSION 3.10)
project(ixsimpl C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

add_compile_options(-pedantic -Wall -Wextra -Werror)

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

# --- Benchmark ---

add_executable(bench_corpus bench/bench_corpus.c)
target_link_libraries(bench_corpus ixsimpl)
target_include_directories(bench_corpus PRIVATE src)
