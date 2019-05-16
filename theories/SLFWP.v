
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

(** As prove further in this chapter, it is possible to 
    define a function [wp] satisfying [wp_equiv]. Formally: *)

Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
  forall t H Q, (triple t H Q) <-> (H ==> wp t Q).

Parameter wp_characterization_exists : exists wp0,
  wp_characterization wp0.

(** In fact, there are several ways in which [wp] can be defined.
    It turns out that all possible definitions are equivalent.
    In other words, [wp_equiv] defines a unique function.
    We next formally justify this fact. *)

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

(** Thus, it really does not matter which definition of [wp] is
    considered. Thereafter, we only exploit the characterization lemma
    [wp_equiv], and never rely on the internal definition of [wp]. *)


(* ******************************************************* *)
(** ** Syntactic construction of a weakest precondition *)

(** To carry out practical verification proofs, we introduce
    a function [wpgen] that construct a weakest precondition
    heap predicate expressed in terms of the Separation Logic
    combinators, by induction on the structure of the program. *)

Module WpgenAmbition.

Parameter wpgen : trm -> (val->hprop) -> hprop.

(** Intuitively, we'd like the "syntactic" function [wpgen]
    to be provably equal to "semantic" function [wp].

    In practice, to establish correctness of a program,
    we only care for one direction of the implication: *)

Parameter wpgen_sound : forall t Q,
  wpgen t Q ==> wp t Q.

(** If we manage to define such a function [wpgen], then we could
    use [wpgen] to establish triples. *)

Lemma triple_of_wpgen : forall H t Q,
  H ==> wpgen t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite wp_equiv. hchange M. applys wpgen_sound.
Qed.

(** The reciprocal implication from [wp] to [wpgen] would be
    interesting to have, as it would justify the completeness of [wpgen].
    Completeness would show that any Separation Logic proof can be carried 
    out using [wpgen]. Yet, it is not a priority to try to formalize this 
    result in Coq for now. *)

End WpgenAmbition.


(* ******************************************************* *)
(** ** Definition of formulae for terms *)

(* ------------------------------------------------------- *)
(** *** General structure *)

(** [wpgen t] is defined by recursion on [t], as a function
    that expects a postcondition [Q] and returns a [hprop].
    We call "formula" the result type of [wgpen t]: *)

Definition formula := (val->hprop) -> hprop.

(** The general shape of the definition of [wpgen] is a
    recursive function on [t], with recursive calls for
    the subterms. The auxiliary functions named [wpgen_val],
    [wpgen_if], etc... describe the body of [wpgen t] for
    each term construct that [t] could be.

[[
  Fixpoint wpgen (t:trm) : formula :=
    match t with
    | trm_val v => wpgen_val v
    | trm_seq t1 t2 => wpgen_seq (wpgen t1) (wpgen t2)
    | trm_if t0 t1 t2 => wpgen_if (wpgen t0) (wpgen t1) (wpgen t2)
    | ...
    end.
]]

    In what follows, we present the definition of each of
    these auxiliary functions.
*)

(* ------------------------------------------------------- *)
(** *** Case of values *)

(** First, consider a value [v]. The formula [wpgen (trm_val v)]
    should be such that [H ==> wpgen (trm_val v) Q] entails
    [triple (trm_val v) H Q]. Recall rule [triple_val]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** [H ==> Q v] is a sufficient condition for [triple (trm_val v) H Q].
    Thus, we wish [H ==> wpgen (trm_val v) Q] to imply [H ==> Q v],
    for any [H]. To achieve this implication, it suffices to define
    [wpgen (trm_val v) Q] as [Q v].

    Recall that [wpgen_val v] describes the value of [wpgen (trm_val v)].
    Thus, [wpgen_val v] is a function that takes [Q] as argument,
    and returns the heap predicate [Q v]. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

(** Just to be sure, let us check the desired property. *)

Lemma triple_of_wpgen_val : forall v H Q,
  H ==> wpgen_val v Q ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys triple_val. unfolds wpgen_val. applys M.
Qed.

(** The pattern of the above lemma will be repeated for all terms.
    To capture this pattern, let us say that a formula [F] is sound
    for a term [t] iff [H ==> F Q] entails [triple t H Q]. *)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall H Q, H ==> F Q -> triple t H Q.

(** We can reformulate the lemma above as: *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. introv M. applys triple_of_wpgen_val M. Qed.

(** Remark: ultimately, what we'd like to show for [wpgen] is:
    [forall t, formula_sound_for t (wpgen t)]. *)


(* ------------------------------------------------------- *)
(** *** Case of sequences *)

(** Second, consider a sequence [trm_seq t1 t2].
    The formula [wpgen (trm_seq t1 t2)] should be such that
    [H ==> [wpgen (trm_seq t1 t2)] Q] entails
    [triple (trm_seq t1 t2) H Q].

    Recall that [wpgen (trm_seq t1 t2)] evaluates to
    [wpgen_seq (wpgen t1) (wpgen t2)]. The definition of
    [wpgen_seq] can be derived from that of [triple_seq]. 
    Recall that rule. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** By induction hypothesis on the subterms, a [triple] for 
    [t1] or [t2] is equivalent to a [wpgen] entailment. 
    Replacing [triple t H Q] with [H ==> wp t Q] throughout
    the rule [triple_seq] gives us: 

[[
    Parameter wgpen_seq1 : forall t1 t2 H Q H1,
      H ==> wpgen t1 (fun r => H1) ->
      H1 ==> wpgen t2 Q ->
      H ==> wpgen_seq (wpgen t1) (wpgen t2) Q.
]]

    From there, let [F1] denote [wpgen t1] and [F2] denote [wpgen t2].
    Moreover, let us substitute away [H1]. We obtain:

[[
  H => F1 (fun r => F2 Q) ->
  wpgen_seq F1 F2
]]

    This leads us to the following definition of [wpgen_seq]. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun X => F2 Q).

(** Again, let us verify that we obtain the desired implication
    for [trm_seq t1 t2], assuming that we have sound formulae
    for the two subterms. *)

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_seq. applys triple_seq.
  { applys S1. applys M. }
  { applys S2. applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Case of let-bindings *)

Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (subst x X t2))
  end.


Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun X => F2of X Q).


(* ------------------------------------------------------- *)
(** *** Case of variables *)

Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_var x => wpgen_fail
  end.

Definition wpgen_fail : formula := fun Q =>
  \[False].

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.


(* ------------------------------------------------------- *)
(** *** Case of applications *)

Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_app t1 t2 => wp t
  ...
  end.

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).


(* ------------------------------------------------------- *)
(** *** Case of conditionals *)



Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Lemma wpgen_if_sound : forall F0 F1 F2 t0 t1 t2,
  formula_sound_for t0 F0 ->
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if t0 t1 t2) (wpgen_if F0 F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_seq. applys triple_seq.
  { applys S1. applys M. }
  { applys S2. applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Turning the fixpoint into a structural function *)

Definition wpgen wpgen (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_fail
  | trm_fun x t1 => wpgen_val (val_fun x t1)
  | trm_fix f x t1 => wpgen_val (val_fix f x t1)
  | trm_if t0 t1 t2 => wpgen_if (wpgen t0) (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (subst x X t2))
  | trm_app t1 t2 => wp t
  end.


(** context *)

Definition ctx : Type := list (var * val).

Check Ctx.empty : ctx.
Check Ctx.add : var -> val -> ctx -> ctx
Check Ctx.rem_var : var -> ctx -> ctx
Check Ctx.lookup : var -> ctx -> val

Check isubst : ctx -> trm -> trm.

Lemma isubst_empty : forall t,
  isubst Ctx.empty t = t.

Lemma isubst_add : forall x v E t,
  isubst (Ctx.add x v E) t = isubst E (subst x v t).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  | trm_fun x t1 => trm_fun (isubst (Ctx.rem_var x E) t1)
  | trm_fix f x t1 => trm_fix (isubst (Ctx.rem_var x (Ctx.rem_var f E)) t1))
  | trm_if t0 t1 t2 => wpgen_if (wpgen t0) (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (Ctx.add x X E) t2)
  | trm_app t1 t2 => wp (isubst E t)
  end.


Lemma wpgen_sound_trm : forall t,
  formula_sound_for (isubst E t) (wpgen E t).

Lemma triple_of_wpgen : forall t Q,
  H ==> wpgen Ctx.empty t Q ->
  triple t H Q.




(* ####################################################### *)
(** * Additional contents *)

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