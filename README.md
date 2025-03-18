# CFML : a framework for interactive proofs of ML programs in Separation Logic

CFML is for carrying out proofs of correctness of OCaml programs with
respect to specifications expressed in higher-order Separation Logic.

CFML consists of two main parts:

- A front-end tool, implemented in OCaml, parses OCaml source code and
  translates it to an abstract syntax tree inside Coq.

- A Coq library provides definitions, lemmas, a characteristic formula
  generator, and a suite of tactics, which make it possible to reason in Coq
  about an OCaml program.


# Installation

CFML uses OCaml version < 5 (it has not been tested with multicore OCaml).
CFML has been tested with Coq v8.20.

To install OCaml, Coq, and the relevant packages, use the "opam" package manager.

```
   # If you have never used opam before
   opam init
```

To create a new switch to contain the relevant packages for cfml:

```
   opam switch create mycoq 4.14.1
```

or if you want to pin a specific version of Coq:
```
   opam switch create coq820 4.14.1
   opam pin add coq 8.20.0
```

Then, to install the packages:

```
   opam install coq pprint menhir 
```

To install the TLC opam package from sources:

```
   cd ~
   git clone git@github.com:charguer/tlc.git
   cd tlc/src
   make -j4 && make install
```

To obtain CFML sources and compile them:

```
  cd ~
  git clone git@github.com:charguer/cfml.git
  cd cfml
  make depend
  make -j8 all
```

To install the VsCoq IDE for Coq embedded in VScode, follow this tutorial:
https://chargueraud.org/teach/verif/install/install.html
In particular, this tutorial suggests a set of alternative key-binding.

# Starting with the tutorial

If `make all` succeeds, you can open the root folder of "cfml2"
into VScode (or another IDE), and play the files interactively.

```
  code . &
```

To begin with open the tutorial, type 'ctrl+p' then 'Tutorial_proof.v'.
If every thing goes well, you should be navigate through the file like
in any other Coq file. (Type 'ctrl+shift+p' then 'Coq' to see the shortcuts.)


# Contributing your own formalization

Copy the folder 'examples/tutorial' into 'examples/mydev'.
Rename the file, and commit the files into a git branch of your own.
Then, type "make" to compile the files located in your new folder.
Open these files in your IDE just like those from the tutorial.


# Documentation

The file `CHEATSHEET.md` provides a summary of the tactics and notation.

The file `lib/coq/WPTactics.v` contains the detailed documentation for
all the tactics.

The file `generator/README.md` contains documentation for the
characteristic formula generator.

The construction of CFML 2.0 is described in this manuscript:
https://www.chargueraud.org/research/2023/hdr/chargueraud-hdr.pdf

Besides, the core of CFML 2.0 is described in the all-in-Coq course:
[Foundations of Separation Logic](https://softwarefoundations.cis.upenn.edu/slf-current/index.html)


# Examples

The 'examples' folder contains tutorials, case studies, and unit tests.

Tutorials

- `examples/Tutorial/Tutorial.v` contains a short tutorial

Case studies

- `examples/Stack`: verification of a stack implemented as a reference on a list---a simple yet very illustrative example.
- `examples/MList`: verification of simple operations on a mutable list; includes specifications where the list "owns" its elements.
- `examples/PairingHeap`: verification of imperative pairing heaps; a heap is represented as a tree of variable arity; concretely, each tree consists of a mutable list of mutable subtrees.

Unit tests:

- `examples/UnitTests` contains unit tests covering all language constructs
- `examples/UnitTestsCredits` contains unit tests for the 'xpay' tactics,
  for reasoning about asymptotic complexity about the code.



