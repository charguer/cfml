# --- This file is a snapshot of README.md as of 2019-02-06,
#     truncated to keep only the relevant information. ---

#############################################################
# Installation

Installation using opam.


```
   # install Coq at the right version (>= 8.8.0 required)
   opam pin add coq 8.8.2
   opam install coqide

   # install TLC from package
   opam repo add coq-released http://coq.inria.fr/opam/released
   opam update
   opam install coq-tlc.20180316  

   # compile
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


#############################################################
# Organisation of the directory:


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


