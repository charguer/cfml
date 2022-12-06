

# Purpose

Semi-automatic translation from HOL to Coq.
Support for replacing certain definitions with custom ones,
with the generation of corresponding proof obligations.


# Installation

```
   opam install coq
   opam install pprint ocamlbuild
   cp demo_sample.ml demo.ml  # optional
   make
```

# Installation of HOL4

First one needs to install PolyML, e.g., as follows.

```
   git clone https://github.com/polyml/polyml
   cd polyml
   ./configure --prefix=/usr
   make
   make compiler
   sudo make install
   cd ..
```

Then one needs to download and build a recent HOL4:

```
   git clone https://github.com/HOL-Theorem-Prover/HOL
   cd HOL
   poly --script tools/smart-configure.sml
   bin/build
   cd ..
   export HOLDIR=`pwd`/HOL
```

One also needs a checkout of CakeML sources.

```
   git clone https://github.com/CakeML/cakeml.git
   export CAKEMLDIR=`pwd`/cakeml
```

And the contents of the current repo (if not already available).

```
   git clone git@gitlab.inria.fr:charguer/cfml2.git -b deepembedding
```


# Compilation of cakeml semantics

Exports need to be executed once per session.

```
   export HOLDIR=`pwd`/HOL
   export CAKEMLDIR=`pwd`/cakeml
   cd cfml2/cakeml/semantics
   make cakeml
```

# Compilation of unit tests

The file `demo.ml` is processed, and produces `demo.v`.
By default, `demo.ml` is generated as a symbolic link on `demo_sample.ml`.

```
   make demo
   make demo_ide
```

# Configuration of CoqIDE bindings for navigation

```
   https://github.com/coq/coq/wiki/Configuration-of-CoqIDE
```


