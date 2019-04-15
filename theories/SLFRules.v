(** * Reasoning Rules of Separation Logic *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Require Import Semantics SepBase.


(** * Structural rules *)

(** ** Rule of consequence *)

(** ** Frame rule *)

(** ** Garbage collection rule *)

(** ** Extraction rules *)


(** * Rules for terms *)

(** ** Rule for values *)

(** ** Rule for let bindings *)

(** ** Rule for sequence *)

(** ** Rule for conditional *)



(** * Rules for functions *)

(** ** Rule for simple functions *)

(** ** Rule for let-binding of a function *)

(** ** Generalization to recursive functions *)

(** ** Generalization to nary functions *)



(** * Specification of primitive operations *)

(** ** Pure functions *)

(** ** Functions operating on the state *)






(* Note: specialized version of consequence *)
Lemma triple_htop_post_remove : forall t H Q,
  triple t H Q ->
  triple t H (Q \*+ \Top).
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M HF); hsimpl.
Qed.






Lemma Triple_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.
Proof using.

  introv M1 M2. applys* Triple_let M1. intros X.
  unfold Subst1. rewrite subst1_anon. destruct X. applys M2.
