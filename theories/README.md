#############################################################
# Additional theories

## Weakest precondition generator computing inside Coq

 * The file __WPBase.v__
   defines weakest precondition style characteristic formulae
   for plain Separation Logic. The corresponding file for
   lifted Separation Logic, namely __WPLifted.v__, is part of
   the lib/coq folder.

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

## Model of Separation Logic with Time Credits

The file `SepCredits.v` contains a formalization of Separation Logic
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

## Model of Separation Logic with Read-Only Permissions

The file `SepRO.v` contains a formalization of Separation Logic extended
with read-only permissions. This extension is described in the paper:
__Temporary Read-Only Permissions for Separation Logic__
by Arthur Charguéraud and François Pottier, published at ESOP 2017.
  http://www.chargueraud.org/research/2017/readonlysep/readonlysep.pdf
