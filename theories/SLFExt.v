


(* loops *)

(* records *)

(* arrays *)

(* constr *)

(* pattern *)

(* not a-normal *)
(** A conditional of the form [if t0 then t1 else t2] can
    be encoded as [let x = t0 in if x then t1 else t2]. 
    Thus, assuming programs to be written in A-normal form
    (i.e., with arguments of conditionals and applications 
    restricted to variables and values), one could live 
    without a reasoning rule for [if t0 then t1 else t2].
    Nevertheless, to support reasoning about programs that
    are not written in A-normal form, we present more general
    rules further in this chapter. *)
