#############################################################
# Models of Separation Logics for a simple imperative lambda-calculus

This archive contains definitions and proofs of soundness for several
Separation Logics.

The plain Separation Logic and the characteristic formulae
(used for more smoothly integrating Separation Logic into interactive
proofs) is as described in Arthur Charguéraud's lecture notes, 
available from:
  http://www.chargueraud.org/teach/verif/seplogic.pdf


The Separation Logic equipped with time credits is described in:
__Verifying the correctness and amortized complexity of a union-find
implementation in separation logic with time credits__
by Arthur Charguéraud and François Pottier
(this is a submitted journal article, extending an ITP 2015 article).
  http://gallium.inria.fr/~fpottier/publis/chargueraud-pottier-uf-sltc.pdf

The Separation Logic equipped with read-only permissions is described in:
__Temporary Read-Only Permissions for Separation Logic__
by Arthur Charguéraud and François Pottier
(ESOP 2017).
  http://www.chargueraud.org/research/2017/readonlysep/readonlysep.pdf


#############################################################
# Dependencies

* The general-purpose Coq library called TLC is required.
  It is available from opam (package name "tlc"), or from sources:
  https://gitlab.inria.fr/charguer/tlc
  in which case you'll to add a file "settings.sh" with contents, e.g.
  "TLC=~/tlc/src"


#############################################################
# Organisation of the directory:


## Common files

 * The file __TLCbuffer.v__
   contains scripts to be later merged into TLC.

 * The file __Fmap.v__
   defines a representation of finite maps, used to represent stores.

 * The file __SepFunctor.v__
   contains a functor with derived properties for Separation Logic.

 * The file __LambdaSemantics.v__
   defines the syntax and semantics of an imperative lambda-calculus.

 * The file __SepGPM.v__
   contains the generic parts of the instantiation of Iris' 
   proof mode on CFML's logic.


## Plain SL

 * The file __LambdaSep.v__
   defines a plain Separation Logic (and proves its soundness).

 * The file __LambdaSepProofMode.v__
   instantiate GPM for LambdaSep.

 * The file __LambdaCF.v__
   defines characteristic formulae for plain Separation Logic.

 * The file __LambdaWP.v__
   defines weakest precondition style characteristic formulae 
   for plain Separation Logic.

 * The file __LambdaStruct.v__
   defines specifications for basic derived operations, for records 
   and for arrays, for plain Separation Logic.

 * The file __ExamplesBasicNonlifted.v__
   gives examples of basic proofs for plain Separation Logic.

 * The file __ExamplesListNonlifted.v__
   gives examples of list proofs for plain Separation Logic.

 * The file __ExamplesListProofMode.v__
   gives examples of list proofs using GPM (nonlifted version).

 * The file __ExamplesQueueNonlifted.v__
   gives examples of queue proofs for plain Separation Logic.


## Lifted SL

 * The file __LambdaCFLifted.v__
   defines characteristic formulae for lifted Separation Logic.

 * The file __LambdaStructLifted.v__
   defines specifications for basic derived operations, for records 
   and for arrays, for lifted Separation Logic.

 * The file __Example.v__
   contains common headers for examples in lifted Separation Logic.

 * The file __ExampleBasic.v__
   contains examples proofs for basic functions in lifted Separation Logic.

 * The file __ExampleList.v__
   contains examples proofs for lists in lifted Separation Logic.

 * The file __ExampleTrees.v__
   contains examples proofs for trees in lifted Separation Logic.

 * The file __ExampleHigherOrder.v__
   contains examples proofs for higher-order functions
   in lifted Separation Logic.


## Read-only SL

 * The file __LambdaSepRO.v__
   defines a Separation Logic with read-only permissions.

 * The file __LambdaSepRO.v__
   gives examples of proofs using RO logic.

 * The file __LambdaSepROProofMode.v__
   instantiate GPM for LambdaSepRO.

 * The file __ExamplesROProofMode.v__
   gives examples of proofs using RO logic with GPM.


## Time-credits SL

 * The file __LambdaSepCredits.v__
   defines a Separation Logic with time credits.

 * The file __LambdaCFCredits.v__
   defines characteristic formulae for Separation Logic with credits.


## Course files

 * The file __SL*.v__
   corresponds to the SL course.
