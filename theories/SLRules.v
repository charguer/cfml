(** * Reasoning Rules of Separation Logic *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Require Import LambdaSemantics LambdaSep.


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
Lemma rule_htop_post_remove : forall t H Q,
  triple t H Q ->
  triple t H (Q \*+ \Top).
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M HF); hsimpl.
Qed.




