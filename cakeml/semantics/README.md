

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

# Installation of HOL4

First one needs to install PolyML, e.g., as follows.
```
cd
git clone https://github.com/polyml/polyml
cd polyml
./configure --prefix=/usr
make
make compiler
make install
```

Then one needs to download and build a recent HOL4:
```
cd
git clone https://github.com/HOL-Theorem-Prover/HOL
cd HOL
poly --script tools/smart-configure.sml
bin/build
```

```
cd
git clone https://github.com/CakeML/cakeml.git
export CAKEMLDIR=~/cakeml
```

Now one can build the sampleScript.sml with:
```
~/HOL/bin/Holmake -j1
```
