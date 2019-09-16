(**

Separation Logic Foundations

Chapter: "Rich".

This chapter describes extension to the Separation Logic foundations
for dealing with richer language constructs, including records, arrays,
loops, data constructors, pattern matching, null pointers, as well as
terms that are not in A-normal form, and support for linear (non-affine)
resources.

Author: Arthur Charguéraud.
License: MIT.

*)

(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Records *)

(* ******************************************************* *)
(** ** Arrays *)

(* ******************************************************* *)
(** ** While loops *)

(* ******************************************************* *)
(** ** For loops *)

(* ******************************************************* *)
(** ** Data constructors *)

(* ******************************************************* *)
(** ** Pattern matching *)

(* ******************************************************* *)
(** ** Null pointers *)

(* ******************************************************* *)
(** ** Terms not in A-normal form *)

(* ******************************************************* *)
(** ** Linear resources *)


(* ####################################################### *)
(** * Details *)



Arguments qwand_cancel [A].

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




Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 x3 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1 x2 x3, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident, x2 ident, x3 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[(fun r => \[r = v] \* H2) ===> Q] ==> WP t Q)
  (at level 39, t at level 0) : triple_scope.


Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").





