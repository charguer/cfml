(**

Separation Logic Foundations

Chapter: "Wand".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SepBase.
Notation "'\Top''" := hgc.



(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter introduces additional Separation Logic operators,
    most notably the "magic wand", written [H1  \-* H2].
    
    Magic wand does not only have a cool name, and it is not only
    a fascinating operator for logicians: it turns out that the 
    magic wand is a key ingredient to streamlining the process of
    practical program verification in Separation Logic. 
    
    In this chapter, we first introduce the new operators, then
    explain how they can be used to reformulate the frame rule
    and give a different presentation to Separation Logic triples. *)


(* ******************************************************* *)
(** ** The magic wand *)

(* ------------------------------------------------------- *)
(** *** Intuitive interpretation for [hwand] *)

(** In first approximation, [H1 \-* H2] is like [H2] but with 
    the [H1] part missing. If we were to compare with arithmetics,
    it would correspond to [ -H1 + H2 ]. 

    If you own the resource [H1 \-* H2], and you also own the
    resource [H1], then you can trade the two for [H2].
    The formal statement, shown below, is reminiscent of the arithmetic
    operation [H1 + (-H1 + H2) = H2]. *)

Parameter hwand_elim : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.

(** The magic wand satisfies a number of other properties that also
    work just like the arithmetic operations would suggest.
    For example: [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)]. 
    The formal statement, shown below, captures that if you own a
    resource asserting that you can trade it with [H1] for [H2], and own
    a resource asserting that you can trade it with [H2] for [H3], then
    you essentially own a resource asserting that you can trade it
    with [H1] for [H3] directly. *)

Parameter hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).

(** Because we are working with heap predicates, and that "negative"
    heap predicates don't quite make sense, we have to be careful.
    Essentially, our arithmetic interpretation [ -H1 + H2] should be
    intrepreted on natural numbers (N) and not on integers (Z).
    We are only allowed to reason about a subtraction [ -H1 + H2]
    if we can somehow justify that H1 is "not smaller than" H2.

    When working on natural numbers, it is not correct to replace
    a number [n] with [(n-m)+m] for some arbitrary [m]. As counter-
    example, take any value [m] greater than [n]. *)

Section TestSubtractionNat.
Open Scope nat_scope.

Lemma counterexample : exists n m, 
  n <> (n-m)+m.
Proof using. exists 0 1. intros N. simpl in N. false. Qed.

End TestSubtractionNat.

(** Likewise, it is not the case that from a heap [H2] we can
    replace it with [H1 \* (H1 \-* H2)]. As counter-example,
    consider [H2 = \[]] and [H1 = \[False]]. *)

Lemma hwand_elim_reciprocal_false : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using. 
  exists \[False] \[]. intros N. forwards K: N (fmap_empty:heap).
  applys hempty_intro. rewrite hstar_hpure in K. destruct K. auto.
Qed.

(** Intuitively, it is safe to replace a heap predicate by another
    one, if the inequalities required to justified that the first
    heap predicate makes sense (i.e. that is does not contain 
    "negative values") are sufficient to justify that the second
    heap predicate also makes sense.
    
    For example, in [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)]
    the LHS requires [H1 <= H2] and [H2 <= H3], from which we can
    deduce [H1 <= H3], as required to justify to RHS. 
  
    But the reciprocal entailment does not hold: from [H1 <= H3], 
    we could not possibly justify [H1 <= H2] not [H2 <= H3].

    Likewise, we can prove:
*)

Lemma hempty_himpl_hwand_self : forall H,
  \[] ==> (H \-* H).
Proof using. hsimpl. Qed.

(* FALSE! 
Lemma hwand_self_himpl_hempty : forall H,
  (H \-* H) ==> \[].
Proof using.
  intros. intros h M. rewrite hwand_eq_hexists_hstar_hpure in M.
  lets (H'&R): hexists_inv M.
Qed.
*)




(* ------------------------------------------------------- *)
(** *** Formal definitions for [hwand] *)



(*
    [H1 \-* H2] is a heap predicate that holds of a heap [h] if,
    when augmenting [h] with a heap [h'] that satisfies [H1],

*)