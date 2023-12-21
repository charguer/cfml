# --- This file is a snapshot of README.md as of 2018-05-29,
#     truncated to keep only the relevant information. ---

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
  in which case you'll to add a file "settings.sh" with contents, e.g.
  "TLC=~/tlc/src"




#############################################################
# Models of Separation Logics for a simple imperative lambda-calculus

This archive contains definitions and proofs of soundness for several
Separation Logics.

The plain Separation Logic and the characteristic formulae
(used for more smoothly integrating Separation Logic into interactive
proofs) is close to that described in Arthur Charguéraud's lecture notes, 
available from:
  http://www.chargueraud.org/teach/verif/seplogic.pdf

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

 * The file __SepFunctor.v__
   contains a functor with derived properties for Separation Logic.

 * The file __LambdaSemantics.v__
   defines the syntax and semantics of an imperative lambda-calculus.


## Plain SL

 * The file __LambdaSep.v__
   defines a plain Separation Logic (and proves its soundness).

 * The file __LambdaCFTactics.v__
   defines notation and tactics for characteristic formulae.

## Read-only SL

 * The file __LambdaSepRO.v__
   defines a Separation Logic with read-only permissions.

 * The file __ExampleRO.v__
   gives examples of proofs using RO logic.

