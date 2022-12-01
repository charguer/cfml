

# Purpose

This is a prototype for compiling definitions obtained by translation from HOL.

The file `demo.ml` is processed, and produces `demo.v`.
A sample `demo_sample.ml` can be used (automatically by `make`) to generate a sample `demo.ml`.


# Installation

```
   opam install coq
   opam install pprint ocamlbuild
   cp demo_sample.ml demo.ml  # optional
   make
```

