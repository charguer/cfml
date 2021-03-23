

(** Used for typechecking the initial source code *)

val process_implementation_file :
  Format.formatter ->
  string ->
  (Parsetree.structure * (Typedtree.structure * Typedtree.module_coercion))
  option * string

(** Used for typechecking the normalized source code *)

val typecheck_implementation_file :
  Format.formatter ->
  string ->
  Parsetree.structure ->
  (Typedtree.structure * Typedtree.module_coercion) option

(** Used for compiling a "mli" interface file and produce a "cmj" file *)

val typecheck_interface_file :
  Format.formatter ->
  string ->
  string ->
  unit
