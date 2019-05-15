


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

(** Remark: our language is set up in such a way that a non-recursive
    function is just a special case of a (potentially-recursive) function.
    The term [trm_fix z x t1] denotes a potentially-recursive function, 
    where [z] is a binder. This binder may be either a variable [f],
    in the case of a recursive function, or the special anonymous binder
    written [bind_anon] to denote a non-recursive function. *)
    
Check trm_fix : bind -> var -> trm -> trm.

Definition trm_fun' x t1 := trm_fix bind_anon x t1.

(* null pointers *)



