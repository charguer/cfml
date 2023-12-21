
#####################################################################
# CF Generator

This folder contains the characteristic formula (CF) generator.
It parses OCaml files and dumps CF in a Coq file.

The current implementation is based on a very old fork of files 
from the OCaml compiler. One project is to reimplement this
generator by leveraging OCaml's compiler-libs and the PR:
https://github.com/ocaml/ocaml/pull/12516
The key difficulty is to extract from the OCaml compiler a 
typed AST in the form of a System-F derivation, with every
type variable explicitly bound in the AST.


#####################################################################
# Binaries

`cfmlc`
:    for building `*_ml.v` files from `*.ml` files. The `*_ml.v` files contain the characteristic formulae.

`makecmj`
:    for building `*.cmj` files from `*.ml` and `*.mli` files, which are like `*.cmi` files, but named differently to avoid conflicts. The `*.cmj` files are required for the separate compilation performed by the `cfmlc` tool.

 
#####################################################################
# Compilation of the binaries

Execute:

```
   make
```


#####################################################################
# Options for `cfmlc` and `makecmj`


`-I` *folder*
:    Add an include directory where to look for `*.cmj` files.

`-rectypes`
:    Allow type-checking with recursive types.

`-nostdlib`
:    Use this file to compile `*.ml` files from the standard library.

`-nopervasives`
:    Use this file to compile Pervasives.ml.


#####################################################################
# Options for `main`


`-o` *FILENAME*
:    Set the output file name. By default, `*_ml.v` for `*.ml`

`-rectypes`
:    Allow type-checking with recursive types.

`-left2right`
:    Assume that side-effects are performed in the left subexpressions first, unlike OCaml's convention.

`-only_normalize`
:    Normalize the code, but do not attempt building the characteristic formula file.

`-debug`
:    Trace the various steps performed by the tool.

`-width`
:    Set the pretty-printing width for the output file.

`-credits`
:    [FUTURE USE] Generate characteristic formulae with time credits.



#####################################################################
# Organization of the code

`main.ml`
:    Drives the operations.

`renaming.ml`
:    Contains the convention for mapping names of variables, types, constructors and modules. It includes the list of builtin types and operators that are treated specially.

`normalize.ml`
:    Describes a source-to-source translation at the level of the parse tree. This translation implements a form of A-normalization: it pulls out all side-effectful sub-expressions, and all function definitions, into seperate let bindings. This translation also rejects programs using features that are not supported by CFML.

`formula.ml`
:    Describes a data type called `formula`, which serves as an intermediate representation for characteristic formulae before they get dumped as Coq syntax.

`coq.ml`
:    Describes a data type called `coq`, which serves as a structured representation for Coq terms.

`characteristic.ml`
:    Converts a typed abstract syntax tree into a structure of type `formula`.

`formula_to_coq.ml`
:    Converts a structure of type `formula` into a structured `coq` term.

`print_coq.ml`
:    Converts a structured `coq` term into a pretty-printed string.

`print_past.ml`
:    Prints an AST, obtained from the parser.

`print_tast.ml`
:    Prints a typed AST, obtained from type-checker.



#####################################################################
# Debugging 


For debugging purposes, when compiling a `*.ml` file, the `cfmlc` tool
generates three files:

   * `output/*_original.ml`
   * `output/*_normalized.ml`
   * `output/*_normalized_types.ml`

These files are not in valid syntax, and are not pretty-printed,
but they allow debugging the normalization process.


