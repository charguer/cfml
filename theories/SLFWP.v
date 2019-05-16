
(**

Separation Logic Foundations

Chapter: "WP".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFRules.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.



(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter introduces the notion of weakest precondition
    for Separation Logic triples, and describes the construction
    of a function that effectively computes in Coq weakest
    preconditions. Using this function, we'll be able to carry
    out verification proofs using Separation Logic reasoning rules
    but without never needing to reason about program variables
    and substitutions. *)


(* ******************************************************* *)
(** ** Notion of weakest precondition *)

(** We next introduce a function [wp], called "weakest precondition".
    Given a term [t] and a postcondition [Q], this function computes 
    a heap predicate [wp t Q] such that [triple t H Q] holds if and
    only if [wp t Q] is weaker than the precondition [H]. Formally: *)

Parameter wp : trm -> (val->hprop) -> hprop.

Parameter wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).

(** The [wp t Q] is called "weakest precondition" for two reasons.
    First, because it is a "valid precondition" for the term [t] 
    and the postcondition [Q]: *)

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof using. intros. rewrite wp_equiv. applys himpl_refl. Qed.

(** Second, because it is the "weakest" of all valid preconditions
    for the term [t] and the postcondition [Q], in the sense that
    any other valid precondition [H] entails [wp t Q]. *)

Lemma wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.
Proof using. introv M. rewrite <- wp_equiv. applys M. Qed.

(** Note that the equivalence rule [wp_equiv] defines a unique
    function [wp]: any two functions satisfying it are equal. *)

Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
  forall t H Q, (triple t H Q) <-> (H ==> wp t Q).

Lemma wp_characterization_unique : forall wp1 wp2,
  wp_characterization wp1 ->
  wp_characterization wp2 ->
  wp1 = wp2.
Proof using. 
  asserts L: (forall t Q wp1 wp2,
    wp_characterization wp1 ->
    wp_characterization wp2 ->
    wp1 t Q ==> wp2 t Q).
  { introv M1 M2. unfolds wp_characterization.
    rewrite <- M2. rewrite M1. applys himpl_refl. }
  introv M1 M2. applys fun_ext_2. intros t Q.
  applys himpl_antisym; applys L; auto.
Qed.


(* ******************************************************* *)
(** ** Semantic definition of weakest precondition *)

(** We have seen that [wp_equiv] defines a unique function [wp].
    There remains to show that there actually exists at least
    one such function.

    In what follows, we'll give two possible definitions, a
    low-level one expressed as a function on heaps, and a high-level
    one expressed using only Separation Logic combinators.

    For both, we'll show that they satisfy [wp_equiv]. Thus, the
    two definitions must be equivalent ([wp_characterization_unique]). *)

(** We now present the low-level definition. *)

Definition wp_low (t:trm) (Q:val->hprop) : hprop :=
  fun (h:heap) => triple t (=h) Q.

Lemma wp_equiv_wp_low : wp_characterization wp_low.
  (** [forall t H Q, (triple t H Q) <-> (H ==> wp_low t Q)]. *)
Proof using.
  (** This proof is a bit technical, it is not required to follow it.
      It requires the lemma [triple_named_heap] established 
      as exercise in an earlier chapter. *)
  unfold wp_low. iff M.
  { intros h K. applys triple_conseq M.
    { intros h' ->. applys K. }
    { applys qimpl_refl. } }
  { applys triple_named_heap. intros h K.
    applys triple_conseq (=h) Q. 
    { specializes M K. applys M. }
    { intros ? ->. auto. }
    { applys qimpl_refl. } }
Qed.

(** We now present the high-level definition. *)

Definition wp_high (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(* EX3! (wp_equiv_wp_high) *)
(** Prove that this second definition of [wp] statisfies
    the characteristic property [wp_equiv]. *)

Lemma wp_equiv_wp_high : wp_characterization wp_high.
  (** [forall t H Q, (triple t H Q) <-> (H ==> wp_high t Q)]. *)
Proof using.
(* SOLUTION *)
  unfold wp_characterization, wp_high. iff M.
  { hsimpl H. apply M. }
  { applys triple_conseq Q M.
    { applys triple_hexists. intros H'.
      rewrite hstar_comm. applys triple_hpure. 
      intros N. applys N. }
    { applys qimpl_refl. } }
(* /SOLUTION *)
Qed.

(** Thereafter, we will only exploit the characterization lemma
    [wp_equiv], and never rely on the internal definition of [wp]. *)


(* ******************************************************* *)
(** ** Semantic definition of weakest precondition *)




Lemma flocal_elim : forall F H Q,
  H ==> wp t Q' \* (Q' \--* (Q \*+ \GC)) ->
  H ==> wp t Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans N. Qed.





  prove1: 
    F Q ==> mklocal F Q
    (take Q1 = Q)

  prove 2:
    (mkflocal (mkflocal F)) Q := mkflocal F
    right-to-left : instance of (1)
    left-to-right: ...

    (mkflocal (mkflocal F)) Q
  = \exists Q1, mkflocal F Q1 \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1, (\exists Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC))) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* ((Q \*+ \GC) \*+ \GC))
  ==> \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* (Q \*+ \GC \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q \*+ \GC \*+ \GC))
  = \exists Q2, F Q2 \* (Q2 \--* (Q \*+ \GC))
  = mkflocal F


  mkflocal F Q := \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)).

  \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q


  F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q



  wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q


  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ->
  H ==> wp t Q.


let H1 := wp t Q1
let H2 := (Q1 \--* (Q \*+ \GC)) 


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.


  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q


reciprocally, with 
   forall Q1,   wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q
we can simulate frame


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.

exploit fact

  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))

suffices (hchange 1 and 2)

  H1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  wp t Q1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  H2 ==> (Q1 \--* (Q \*+ \GC))

done.




-------


Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun X => F2of X Q).

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun X => F2 Q).

Definition wpgen_app (t1:trm) (t2:trm) : formula := fun Q =>  
  wp (trm_app t1 t2) Q.

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_fail
  | trm_fun x t1 => wpgen_val (val_fun x t1)
  | trm_fix f x t1 => wpgen_val (val_fix f x t1)
  | trm_if t0 t1 t2 => wpgen_if (wpgen t0) (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (subst x X t2))
  | trm_app t1 t2 => wgpen_app t1 t2
  end.


Lemma wpgen_himpl_wp : forall t Q,
  H ==> wpgen t Q ->
  triple t H Q.

  H ==> wp t Q ->
  triple t H Q.

  H ==> wpgen t Q ->
  H ==> wp t Q ->

  wpgen t Q ==> wp t Q.

(in details)

then derive

  Lemma triple_of_wpgen : forall t Q,
    H ==> wpgen t Q ->
    triple t H Q.




Lemma wpgen_himpl_wp : forall t Q,
  wpgen t Q ==> wp t Q.

Definition wpgen_sound_for t := forall Q,
  wpgen t Q ==> wp t Q.

wpgen_sound_for (trm_val v)
wpgen_sound_for (trm_fun x t).
wpgen_sound_for (trm_fix f x t).
..



--------






Definition wpgen_fail : formula := mkflocal (fun Q =>
  \[False]).

Definition wpgen_val (v:val) : formula := mkflocal (fun Q =>
  Q v).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wpgen_seq (F1 F2:formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2 Q)).

Definition wpgen_app (t1:trm) (t2:trm) : formula := mkflocal (fun Q =>  
  wp (trm_app t1 t2) Q)

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := mkflocal (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  let aux := wpgen E in
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  | trm_fun x t1 => trm_fun (isubst (Ctx.rem x E) t1)
  | trm_fix f x t1 => trm_fix (isubst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => wpgen_if (aux t0) (aux t1) (aux t2)
  | trm_let x t1 t2 => wpgen_let (aux t1) (fun X => wpgen (Ctx.add x X E) t2)
  | trm_app t1 t2 => wgpen_app (isubst E t1) (isubst E t2)
  end.







forward proof 
- with let
- lets
- subst all pb

reasoning on calls
- with = 2*x (app vs apps)
- with y st P x y

recursion
- call that does not fit coq