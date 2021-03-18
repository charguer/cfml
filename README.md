# CFML 2.0 : a tool for proving ML programs in Separation Logic

# Description

CFML 2.0 is a tool that allows carrying out proofs of correctness of OCaml
programs with respect to specifications expressed in higher-order Separation
Logic. It consists of several parts:

- A characteristic formula generator, implemented inside Coq, which processes
  deeply-embedded OCaml programs (that is, OCaml programs that are represented
  inside Coq as abstract syntax trees).

- A front-end tool, implemented in OCaml, which parses OCaml source code and
  translates it to an abstract syntax tree inside Coq.

- A Coq library, which provides definitions, lemmas, and tactics to carry out
  proofs with respect to characteristic formulae.

# Installation

The standard installation procedure requires `opam`, the OCaml package
manager. If you do not have it yet, please
[install opam](https://opam.ocaml.org/doc/Install.html) first.

CFML depends on several `opam` packages, including Coq. At the time of
writing, versions 8.12 and 8.13 of Coq are supported.

To install the latest released version of CFML, type:

```
  opam install coq-cfml-stdlib
```

Then, you can try to load an example proof. The command given uses
CoqIDE, which generally works more smoothly with multithreading turned off.

```
   cd examples/Tutorial
   make
   gedit Tutorial.ml &
   coqide -async-proofs off -async-proofs-command-error-resilience off Tutorial_proof.v &
```

# Other theory files, in folder theories

The files may be compiled and played using:

```
   cd cfml/theories
   make
   make _CoqProject
   coqide -async-proofs off -async-proofs-command-error-resilience off ExamplePairingHeap.v &
```


# References

## Course on the Foundations of Separation Logic

The implementation of CFML 2.0 is described in a full course:
  http://www.chargueraud.org/teach/verif/


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



## Model of Separation Logic with Read-Only Permissions

The file `SepRO.v` contains a formalization of Separation Logic extended
with read-only permissions. This extension is described in the paper:
__Temporary Read-Only Permissions for Separation Logic__
by Arthur Charguéraud and François Pottier, published at ESOP 2017.
  http://www.chargueraud.org/research/2017/readonlysep/readonlysep.pdf


# Limitations

- Idealized integers
- No support for float values
- Limited support for functors
- Partial applications require eta-expansion: `f x` becomes `fun y => f x y`
- Over-applications require let-binding: `f x y` becomes `let g = f x in g y`
