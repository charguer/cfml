# --- This file is a snapshot of README.md as of 2019-02-06,
#     truncated to keep only the relevant information. ---


#############################################################
# Requirements

The compilation of the files requires Coq v8.8 or v8.9.

Coq may be installed using packets:

```
   sudo apt-get install coqide
```

Or using the opam distribution manager, which is available from:
https://opam.ocaml.org/doc/Install.html
and which compiles the desired version of Coq from source 
(will take 15-30 minutes, depending on your machine).

```
   # assuming opam has already installed some recent version of Ocaml

   # install Coq at the right version (>= 8.8.0 required)
   opam pin add coq 8.8.2
   opam install coqide
```

Remark: the files depend on a third-party general-purpose Coq library,
which, for convenience, is included in the files distributed.
(This library is distributed at: https://gitlab.inria.fr/charguer/tlc)


#############################################################
# Compilation

To compile the distributed files (including TLC), from the root
of the inflated archive, just type:

```
   make
```

To play the main file interactively, use the following command,
executed from the root of the inflated archive:

```
   coqide -Q TLC TLC -Q theories Sep theories/LambdaSepCredits.v
```

There, use the shortcuts described in the Navigation menu to
navigate through the proof script.


#############################################################
# Organisation of the directory:

The folder "theories" contains the following files:

 * The file __TLCbuffer.v__
   contains scripts to be later merged into TLC.

 * The file __Fmap.v__
   defines a representation of finite maps, used to represent stores.

 * The file __Bind.v__
   defines binders and contexts.

 * The file __SepFunctor.v__
   contains a functor with derived properties for Separation Logic.

 * The file __LambdaSemantics.v__
   defines the syntax and semantics of an imperative lambda-calculus.

 * The file __LambdaSepCredits.v__
   defines and prove soundness of a Separation Logic with time credits.


