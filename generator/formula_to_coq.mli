open Coq
open Formula

(** Convert a characteristic formula to a coq expression
    (internal function) *)

val coqtops_of_cf : cf -> coq

(** Convert a list of top-level characteristic formulae into a
    list of coqtop declarations *)

val coqtops_of_cftops : cftop list -> coqtops
