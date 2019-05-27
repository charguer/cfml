#############################################################
# Version of Coq

The theories compile with Coq 8.8 and they probably also compile 
with more recent versions. (Let me know otherwise.)


#############################################################
# Setting up TLC

The theories depend on the TLC library. It may be installed using
OPAM or from sources.

```
   opam install coq-tlc.20181116
```

Or for a manual installation of TLC:

```
   git clone https://gitlab.inria.fr/charguer/tlc ~/tlc
   cd ~/tlc/src
   make install
```

Or for use of TLC without installation:

```
   git clone https://gitlab.inria.fr/charguer/tlc ~/tlc
   export TLC=~/tlc/src
```


#############################################################
# Compilation


```
   cd cfml/theories
   make
   make _CoqProject
```

Remark: depending on your version of TLC, `make _CoqProject` might be redundant.



#############################################################
# Interactive session

```
   coqide SLFIntro.v SLFHprop.v
```


Remark: the contents of `_CoqProject` should be of the following form.

```
   -R ~/.opam/4.05.0/lib/coq/user-contrib/TLC TLC -R ~/cfml2_master/theories Sep
```

Alternatively, these arguments may be passed directly to, e.g., CoqIDE.


Note that CoqIDE generally works more smoothly with multithreading turned off:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off SLFHprop.v
```


#############################################################
# SLF course files

The files whose name begins with SLF correspond to the course.
Read `SLFIntro.v` for a description of what each file contains.

The course depend on 4 auxiliary files.

 * The file __TLCbuffer.v__
   contains definitions, lemmas and tactics to be later merged into TLC.

 * The file __Var.v__
   defines a representation of variables as strings.

 * The file __Fmap.v__
   defines a representation of finite maps, used to represent stores.

 * The file __Hsimpl.v__
   implements the simplification tactic for heap entailment.


#############################################################
# CFML2.0 source files


## Common files

 * The file __Bind.v__
   defines binders and contexts.

 * The file __Semantics.v__
   defines the syntax and semantics of an imperative lambda-calculus.

 * The file __SepFunctor.v__
   contains a functor with derived properties for Separation Logic.
   This functor is used by plain separation logic and also by the
   two extensions (credits and read-only) mentioned further on.


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

 * The file __WPTactics.v__
   introduces tactics to conduct practical proofs using these lifted WP.   

 * The file __WPRecord.v__
   provides support for reasoning about records.

 * The file __WPExamples.v__
   (work-in-progress) file with examples proofs

 * The file __WPExamplesDetails.v__
   (work-in-progress) file a few proofs containing additional details 
   on the working of tactics.


## Other files: work in progress.


#############################################################
# Other models of Separation Logics

This file `SepCredits.v` and `SepRO.v` formalize variants of Separation Logic.

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


