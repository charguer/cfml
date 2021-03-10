
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