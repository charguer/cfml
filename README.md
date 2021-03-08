# CFML 2.0 : a tool for proving ML programs in Separation Logic

  http://www.chargueraud.org/softs/cfml/



#############################################################
# Description

CFML 2.0 is a tool for carrying out proofs of correctness of OCaml programs with
respect to specifications expressed in higher-order Separation Logic.
It consists of several parts:

- A characteristic formula generator implemented inside Coq, that processes
  deeply-embedded programs.

- An tool, implemented in OCaml, that provides a front-end for parsing OCaml 
  source code and directly generating the characteristic formulae---currently,
  this formulae are taken as axioms, but in the future they would be proved
  correct.

- A Coq library that provides definitions, lemmas, and tactics for carrying
  out proofs with respect to characteristic formulae.



#############################################################
# Installation

CFML 2.0 is known to work with Coq v8.8.2 and v8.9.1.
It does not work with v8.10 and v8.11 due to a bug affecting
the resolution of typeclasses in these versions.

CFML 2.0 depend on the TLC library. It may be installed using
OPAM or from sources.

To install Coq and TLC, execute:

```
   opam pin add coq 8.9.1
   opam install coq-tlc.20181116

   # optional
   opam install coqide
```

Note: if you'd rather install TLC by hand, for either Coq v8.8 or v8.9,
execute the following commands:

```
   git clone https://gitlab.inria.fr/charguer/tlc -b coq-8.9
   cd tlc/src
   make install
```

Then, the compilation of the files from CFML 2.0 can be achieved with:

```
   cd cfml/theories
   make
   make _CoqProject
```

Note: depending on your version of TLC, `make _CoqProject` might be redundant.

Note: CoqIDE generally works more smoothly with multithreading turned off.

```
   coqide -async-proofs off -async-proofs-command-error-resilience off *.v
```



#############################################################
# CFML 2.0 Coq files (/theories)


## Common infrastructure files

 * The file __LibSepTLCbuffer.v__
   contains definitions, lemmas and tactics to be later merged into TLC.

 * The file __LibSepVar.v__
   defines a representation of variables as strings.

 * The file __LibSepFmap.v__
   defines a representation of finite maps, used to represent stores.

 * The file __LibSepBind.v__
   defines binders and contexts.

 * The file __LibSepSimpl.v__
   implements the simplification tactic for heap entailment.

 * The file __SepFunctor.v__
   contains a functor with derived properties for Separation Logic.
   This functor is used by plain separation logic and also by the
   two extensions (credits and read-only) mentioned further on.


## Semantics

 * The file __Semantics.v__
   defines the syntax and semantics of an imperative lambda-calculus.


## Plain SL

 * The file __SepBase.v__
   defines a plain Separation Logic (and proves its soundness).

 * The file __WPBase.v__
   defines weakest precondition style characteristic formulae
   for plain Separation Logic.


## Lifted SL

 * The file __SepLifted.v__
   defines lifted Separation Logic.

 * The file __WPLifted.v__
   defines weakest precondition style characteristic formulae.
   for lifted Separation Logic.


## CFML tooling

 * The file __WPTactics.v__
   introduces tactics to conduct practical proofs using these lifted WP.   

 * The file __WPRecord.v__
   provides support for reasoning about records.

 * The file __WPLib.v__
   exports all the tooling


## Example proofs

 * The file __Example.v__
   common header to be included by all example files

 * The file __ExampleListNull.v__
   formalization of null-terminated lists

 * The file __ExampleList.v__
   formalization of lists as reference on a sum type

 * The file __ExampleListIndir.v__
   variant of ExampleList using the address of operator

 * The file __ExampleQueue.v__
   formalization of a mutable queue as a list segment

 * The file __ExampleStack.v__
   formalization of a stack as a reference on a pure list,
   or as a pair of a pure list and a size integer

 * The file __ExampleListOf.v__
   wrapper for lists that own their elements

 * The file __ExamplePairingHeap.v__
   formalization of a mutable pairing heaps as trees
   with node featuring mutable lists of subtrees


## Unit tests

 * The file __WPUnitTests.v__
   (work-in-progress) file with several tactic demos

 * The file __WPExamples.v__
   (work-in-progress) file with examples proofs

 * The file __WPExamplesDetails.v__
   (work-in-progress) file a few proofs containing additional details
   on the working of tactics.



#############################################################
# Course on the Foundations of Separation Logic

The implementation of CFML 2.0 is described in a full course:
  http://www.chargueraud.org/teach/verif/


#############################################################
# Model of Separation Logic with Time Credits

This file `SepCredits.v` contains a formalization of Separation Logic
extended with Time Credits, with credits represented on Z (integers).

The original "Separation Logic with time credits" represented time credits
on N (natural number). This original presentation is described in the paper:
__Verifying the correctness and amortized complexity of a union-find
implementation in separation logic with time credits__
by Arthur Charguéraud and François Pottier, published at JAR 2017.
  http://gallium.inria.fr/~fpottier/publis/chargueraud-pottier-uf-sltc.pdf

The switch from N to Z for representing credits brings numerous benefits,
as described in the paper:
__Formal proof and analysis of an incremental cycle detection algorithm__
by Armaël Guéneau, Jacques-Henri Jourdan, Arthur Charguéraud, and François Pottier,
published at ITP 2019.
  http://gallium.inria.fr/~fpottier/publis/gueneau-jourdan-chargueraud-pottier-2019.pdf



#############################################################
# Model of Separation Logic with Read-Only Permissions

The file `SepRO.v` contains a formalization of Separation Logic extended
with read-only permissions. This extension is described in the paper:
__Temporary Read-Only Permissions for Separation Logic__
by Arthur Charguéraud and François Pottier, published at ESOP 2017.
  http://www.chargueraud.org/research/2017/readonlysep/readonlysep.pdf


#############################################################
# Limitations

- Idealized integers
- No support for float values
- Limited support for functors
- Partial applications require eta-expansion: `f x` becomes `fun y => f x y`
- Over-applications require let-binding: `f x y` becomes `let g = f x in g y`
- ...

