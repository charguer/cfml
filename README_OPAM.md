## DEPRECATED -- Distribution as opam package

Prior releases of CFML had been distributed as opam package.
This distribution scheme might be revived in the future.
For now, it has been discontinued. 

The old makefiles have been renamed 'Makefile.pkg'.
The configuration files for the opam package have remained in place.
The previous documentation appears below.


# Installation procedure (DEPRECATED)

The standard installation procedure requires `opam`, the OCaml package
manager. If you do not have it yet, please
[install opam](https://opam.ocaml.org/doc/Install.html) first.

```
  opam install coq-cfml
```

To install the latest development version of CFML, use this:

```
  git clone https://gitlab.inria.fr/charguer/cfml2.git
  cd cfml2
  make pin
```

# Overview of the packages (DEPRECATED)

The implementation is split into three `opam` packages, named `cfml`,
`coq-cfml-basis`, and `coq-cfml-stdlib`. The last package depends on
the previous two. In addition, the meta-package `coq-cfml` contains
nothing but depends on the previous three packages, forcing them to
be installed.

- The package `cfml` contains the generator, `cfmlc`. Its source code is found
  in the directory [generator](generator). This package also installs the
  auxiliary Makefiles in [lib/make](lib/make). At runtime, the command `cmlfc
  -where` allows finding out where these Makefiles have been installed.

- The package `coq-cfml-basis` contains a Coq library. It is the
  implementation of the Coq component of CFML. This library is installed in
  the Coq hierarchy under the name `CFML`.

- The package `coq-cfml-stdlib` contains Coq specifications for some of the
  modules in the OCaml standard library. It forms a Coq library, which is
  installed in the Coq hierarchy under the name `CFML.Stdlib`. The
  `.cmj` files for the OCaml standard library, which are used by `cfmlc`,
  are installed in the directory `$(cfmlc -where)/stdlib`.

The directory `examples` contains a number of examples of use of CFML.
Provided the above packages have been installed, these examples can be
compiled by typing `make -C examples` in the root directory of the repository.

# CFML Opam Package Developer Workflow (DEPRECATED)

The root `Makefile` defines a number of commands that are useful while working
on CFML.

* `make -j` compiles the OCaml code in the directory `generator`
  and the Coq code in the directory `lib/coq`.

* `make pin` asks `opam` to install the last committed versions of the three
  packages. (Don't forget to commit your changes before using this command.)
  Use `OPAMYES=1 make pin` to automatically answer "yes" to every question
  asked by opam.

* `make reinstall` forces opam to reinstall the three packages
  (which presumably have been pinned earlier). You can also
  selectively use `opam reinstall cfml`,
  `opam reinstall coq-cfml-basis`, or
  `opam reinstall coq-cfml-stdlib` to reinstall just one package.

* `make unpin` asks `opam` to unpin the packages, so `opam` will either remove
  the packages altogether or reinstall the last publicly released versions of
  the packages.

# CFML Direct Developer Workflow (DEPRECATED)

Using `./makedev.sh`, an alias for `make -f Makefile.dev`, enables
compiling the libraries and example folders with fine-grained dependencies.
Example targets include: `

* `./makedev.sh gen` for building the characteristic formula generator

* `./makedev.sh mlv` for building `*._mlv` characteristic formulae files

* `./makedev.sh -j4 vos` for compiling files with all proofs admitted

* `./makedev.sh -j4 vok` for fast parallel compilation of all files

* `./makedev.sh -j4 target_file` for a specific target, e.g.
  `./makedev.sh -j4 examples/PairingHeap/PairingHeap_ml.vos`


