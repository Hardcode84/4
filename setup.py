from setuptools import Extension, setup

sources = [
    "bindings/python/_ixsimpl.c",
    "src/arena.c",
    "src/rational.c",
    "src/node.c",
    "src/simplify.c",
    "src/bounds.c",
    "src/parser.c",
    "src/print.c",
    "src/ctx.c",
]

ixsimpl_ext = Extension(
    "ixsimpl",
    sources=sources,
    include_dirs=["include", "src"],
    extra_compile_args=["-std=c99", "-O2"],
)

setup(ext_modules=[ixsimpl_ext])
