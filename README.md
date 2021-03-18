# CFML 2.0 : a tool for proving ML programs in Separation Logic

CFML 2.0 allows carrying out proofs of correctness of OCaml programs with
respect to specifications expressed in higher-order Separation Logic. It
consists of several parts:

- A front-end tool, implemented in OCaml, parses OCaml source code and
  translates it to an abstract syntax tree inside Coq.

- A Coq library provides definitions, lemmas, a characteristic formula
  generator, and a suite of tactics, which make it possible to reason in Coq
  about an OCaml program.

# Installation

The standard installation procedure requires `opam`, the OCaml package
manager. If you do not have it yet, please
[install opam](https://opam.ocaml.org/doc/Install.html) first.

CFML depends on several `opam` packages, including Coq. At the time of
writing, versions 8.12 and 8.13 of Coq are supported.

To install the latest released version of CFML, use the following command:

```
  opam install coq-cfml-stdlib
```

To install the latest development version of CFML, use this:

```
  git clone https://gitlab.inria.fr/charguer/cfml2.git
  cd cfml2
  make pin
```

# Replaying a sample proof

Then, you can load an example proof. The following command uses CoqIDE:

```
  git clone https://gitlab.inria.fr/charguer/cfml2.git
  cd cfml2/examples/Tutorial
  make
  gedit Tutorial.ml &
  coqide -async-proofs off -async-proofs-command-error-resilience off Tutorial_proof.v &
```

# References

The implementation of CFML 2.0 is described in the course
[Foundations of Separation Logic](http://www.chargueraud.org/teach/verif/).
