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
# Dependencies

CFML requires a number of OCaml tooling available via opam.
Thus, make sure to install opam, and update the repository list.
https://opam.ocaml.org/doc/Install.html

CFML depends on Coq. It is likely to work with versions > 8.12,
however more recent versions are not tested on a regular basis.
The recommended way to install Coq is via opam. To install 8.12:
```
   opam pin add coq 8.12 
   opam install coq
   opam install coqide   # unless you use another IDE.
```

CFML depends on the OCaml library pprint, and the tool ocamlfind.

```
   opam install ocamlfind pprint
```

CFML depends on the Coq library TLC. To make sure to get the last
version of TLC, install it by hand as follows.

```
   git clone https://github.com/charguer/tlc
   cd tlc/src
   make install
```

Alternatively, execute "opam install coq-tlc", it should work unless
at some point CFML depends on additions to TLC that are not yet 
deployed in the opam package.


#############################################################
# Compilation and installation

Once all dependencies are installed, you can compile and install 
the "cfmlc" tool:


```
   make install
```

Then, you can try to load an example proof. The command given uses
CoqIDE, which generally works more smoothly with multithreading turned off.

```
   cd examples/Tutorial
   make
   gedit Tutorial.ml &
   coqide -async-proofs off -async-proofs-command-error-resilience off Tutorial_proof.v &
```

#############################################################
# Other theory files, in folder theories

The files may be compiled and played using:

```
   cd cfml/theories
   make
   make _CoqProject
   coqide -async-proofs off -async-proofs-command-error-resilience off ExamplePairingHeap.v &
```


#############################################################
# References

#############################################################
## Course on the Foundations of Separation Logic

The implementation of CFML 2.0 is described in a full course:
  http://www.chargueraud.org/teach/verif/


#############################################################
## Model of Separation Logic with Time Credits

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
## Model of Separation Logic with Read-Only Permissions

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

