(* The directory [libdir] is where we look for the .cmj files that describe
   the OCaml standard library. *)

val libdir: string option

(* [print_libdir()] prints [libdir] and exits. *)

val print_libdir: unit -> unit
