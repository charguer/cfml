
(* Width for printing
   TODO: how to change it? *)

val width : int ref

(** Print a list of coqtop declaration into a string *)

val tops : Coq.coqtops -> string
