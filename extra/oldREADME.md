#############################################################
# Installation

Installation using opam.


```
   # create an opam switch for CFML2
   opam switch cfml_8.7.2 -A 4.05.0
   `opam config env`

   # install Coq at the right version
   opam pin add coq 8.7.2
   opam install coqide

   # install MoSel
   opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git
   opam update
   opam install coq-iris=dev.2018-07-13.0.cbf73155

   # install TLC from package
   opam repo add coq-released http://coq.inria.fr/opam/released
   opam update
   opam install coq-tlc.20180316  

   # compile CFML2
   cd ~/cfml2
   make
   # alternative: make -j4

```


Remarks:

* The general-purpose Coq library called TLC is required for all files.
  It is available from opam (package name "coq-tlc").
  
  Alternatively, one can also use TLC from sources:
     https://gitlab.inria.fr/charguer/tlc
  in which case you'll have to add a file "settings.sh" with contents, e.g.
  "TLC=~/tlc/src"


* The MoSel proof mode is required for the compilation of 
  files that depend on the proof mode. It is available via opam:
  `opam install coq-iris=branch.gen_proofmode.2018-05-29.0.9b14f90a`


#############################################################
# Execution using CoqIDE

If everything works fine, the files can be executed using CoqIDE, e.g.:

```
   coqide ExampleROMosel.v
```

Note that CoqIDE uses the file `_CoqProject` generated by the Makefile 
(by `make all`, or more specifically by `make _CoqProject`) to figure
out the paths to the libraries. For example, the contents of `_CoqProject`
might be:

```
   -R /home/charguer/.opam/4.05.0/lib/coq/user-contrib/TLC TLC -R /home/charguer/cfml2_master/theories Sep
```

If for some reason this setup fails, then CoqIDE would complain with 
an error of the form:

```
   Cannot find a physical path bound to logical path matching suffix
   <> and prefix Sep.
```

Note that it is possible to invoke CoqIDE with explicit arguments, e.g.:

```
   coqide -R /home/charguer/.opam/4.05.0/lib/coq/user-contrib/TLC TLC -R /home/charguer/cfml2_master/theories Sep ExampleROMosel.v
```

Note that CoqIDE often executes faster with multithreading turned off:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off 
```


#############################################################
# Models of Separation Logics for a simple imperative lambda-calculus

This archive contains definitions and proofs of soundness for several
Separation Logics.

The plain Separation Logic and the characteristic formulae
(used for more smoothly integrating Separation Logic into interactive
proofs) is close to that described in Arthur Charguéraud's lecture notes, 
available from:
  http://www.chargueraud.org/teach/verif/seplogic.pdf


The Separation Logic equipped with time credits is described in:
__Verifying the correctness and amortized complexity of a union-find
implementation in separation logic with time credits__
by Arthur Charguéraud and François Pottier, JAR 2017
  http://gallium.inria.fr/~fpottier/publis/chargueraud-pottier-uf-sltc.pdf

The Separation Logic equipped with read-only permissions is described in:
__Temporary Read-Only Permissions for Separation Logic__
by Arthur Charguéraud and François Pottier
(ESOP 2017).
  http://www.chargueraud.org/research/2017/readonlysep/readonlysep.pdf


#############################################################
# Organisation of the directory:


## Common files

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


## Plain SL

 * The file __LambdaSep.v__
   defines a plain Separation Logic (and proves its soundness).

 * The file __LambdaWP.v__
   defines weakest precondition style characteristic formulae 
   for plain Separation Logic.


## Lifted SL

 * The file __LambdaSepLifted.v__
   defines lifted Separation Logic.

 * The file __LambdaWPLifted.v__
   defines weakest precondition style characteristic formulae.
   for lifted Separation Logic.

 * The file __LambdaWPTactics.v__
   introduces tactics to conduct practical proofs using these lifted WP.   


## Read-only SL

 * The file __LambdaSepRO.v__
   defines a Separation Logic with read-only permissions.


## Time-credits SL

 * The file __LambdaSepCredits.v__
   defines a Separation Logic with time credits.



#############################################################
# Currently doesn't compile


## Plain SL

 * The file __LambdaCFTactics.v__
   defines notation and tactics for characteristic formulae.

 * The file __LambdaCF.v__
   defines characteristic formulae for plain Separation Logic.

 * The file __LambdaStruct.v__
   defines specifications for basic derived operations, for records 
   and for arrays, for plain Separation Logic.

 * The file __ExamplesBasicNonlifted.v__
   gives examples of basic proofs for plain Separation Logic.

 * The file __ExamplesListNonlifted.v__
   gives examples of list proofs for plain Separation Logic.

 * The file __ExamplesQueueNonlifted.v__
   gives examples of queue proofs for plain Separation Logic.


## MoSel proof mode

 * The file __SepMosel.v__
   contains the generic parts of the instantiation of Iris' 
   proof mode on CFML's logic.

 * The file __LambdaSepMosel.v__
   instantiate MoSel for LambdaSep.

 * The file __ExamplesListMosel.v__
   gives examples of list proofs using MoSel (nonlifted version).

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

 * The file __ExampleRO.v__
   gives examples of proofs using RO logic.

 * The file __LambdaSepROMosel.v__
   instantiate Mosel for LambdaSepRO.

 * The file __ExamplesROMosel.v__
   gives examples of proofs using RO logic with Mosel.


## Time-credits SL

 * The file __LambdaCFCredits.v__
   defines characteristic formulae for Separation Logic with credits.


## Course files

 * The file __SL*.v__
   corresponds to the SL course.