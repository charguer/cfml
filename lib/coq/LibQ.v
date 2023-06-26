(*
Set Implicit Arguments.
From TLC Require Import LibTactics LibRelation LibEpsilon LibInt.
Open Scope Z_scope.


Definition quotient A (R:binary A) : Type :=
  { repr : A | repr = epsilon R repr }.

Definition inject A (R:binary A) (x:A) : quotient R :=
  epsilon R x.

Lemma inject_eq_eq_rel : forall A (R:binary A) (x y:A),
  (inject x = inject y) = (R x y).
Proof using. Qed.


(* ********************************************************************** *)
(** * Parsing of integers and operations *)

(* ---------------------------------------------------------------------- *)
(** ** Notation for type and operation *)

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.

Local Open Scope Q_scope.


(* ---------------------------------------------------------------------- *)
(** ** Type definition *)

(** Equivalence of pairs *)

Definition equiv (q1 q2 : Z*Z) : Prop :=
  let '(n1,m1) := q1 in
  let '(n2,m2) := q2 in
  n1 * m2 = n2 * m1.

(** Definition of Q as the quotient *)

Definition Q : Type :=
  quotient (Z*Z)%type equiv.

Implicit Types q : Q.

(** Constructor from numerator/denominator *)

Definition make (n m : Z) : Q :=
  inject equiv (n,m).

(** Conversion from Z, registered as coercion *)

Coercion Z_to_Q (n:Z) : Q :=
  Qmake n 1.

(** Query of a numerator/denominator representation *)

Definition Q_to_ZZ (q:Q) : Z*Z :=
  repr q.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited type *)

#[global]
Instance Inhab_Q : Inhab Q.
Proof using. intros. apply (Inhab_of_val 0%Q). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Operations *)

Definition add (q1 q2 : Q) : Q :=
  let '(n1,m1) := repr q1 in
  let '(n2,m2) := repr q2 in
  make (n1*m2 + n2*m1) (m1*m2).

Definition mul (q1 q2 : Q) : Q :=
  let '(n1,m1) := repr q1 in
  let '(n2,m2) := repr q2 in
  make (n1*n2) (m1*m2).

Definition opp (q1 : Q) : Q :=
  mul minus_one q1.
  (* alternative:
  let '(n1,m1) := repr q1 in
  make (-n1) m1.
  *)

Definition sub (q1 q2 : Q) : Q :=
  add q1 (opp q2).

(* only for internal use *)
Definition inv (q1 : Q) : Q :=
  let '(n1,m1) := repr q1 in
  make m1 n1.

Definition div (q1 q2 : Q) : Q :=
  mul q1 (inv q2).


(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Definition Q_le (q1 q2 : Q) : Prop :=
  let '(n1,m1) := repr q1 in
  let '(n2,m2) := repr q2 in
  n1 * m2 <= n2 * m1.

Open Scope comp_scope.

#[global]
Instance le_int_inst : Le int := Build_Le Q_le.


(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)

Lemma plus_zero_r : forall q,
  q + 0 = q.
Proof using. math. Qed.

Lemma plus_zero_l : forall q,
  0 + q = q.
Proof using. math. Qed.

Lemma minus_zero_r : forall q,
  q - 0 = q.
Proof using. math. Qed.

Lemma minus_zero_l : forall q,
  0 - q = (- q).
Proof using. math. Qed.

Lemma mult_zero_l : forall q,
  0 * q = 0.
Proof using. math. Qed.

Lemma mult_zero_r : forall q,
  q * 0 = 0.
Proof using. math. Qed.

Lemma mult_one_l : forall q,
  1 * q = q.
Proof using. math. Qed.

Lemma mult_one_r : forall q,
  q * 1 = q.
Proof using. math. Qed.

Lemma minus_self : forall q,
  q - q = 0.
Proof using. math. Qed.

Lemma one_plus_minus_one_r : forall q,
  1 + (q - 1) = q.
Proof using. math. Qed.

Lemma plus_one_minus_one_l : forall q,
  (q + 1) - 1 = q.
Proof using. math. Qed.

Lemma one_plus_minus_one_l : forall q,
  (1 + q) - 1 = q.
Proof using. math. Qed.

(* e.g.
q1 - (q2 + q3)
*)

(* ---------------------------------------------------------------------- *)
(** ** Multiplication, division and inversions *)

Lemma mul_zero_inv : forall q1 q2,
  q1 * q2 = 0 ->
  q1 = 0 \/ q2 = 0.
Proof using. math. Qed.

Lemma mul_zero_inv_nonzero_l : forall q1 q2,
  q1 * q2 = 0 ->
  q1 <> 0 ->
  q2 = 0.
Proof using. math. Qed.

Lemma div_same : forall q,
  q / q = 1.
Proof using. math. Qed.

Lemma mul_div_r : forall q1 q2 q3,
  q1 * (q2 / q3) = (q1 * q2) / q3.
Proof using. math. Qed.

Lemma mul_inv_r : forall q,
  q * (1 / q) = 1.
Proof using. math. Qed.

Lemma div_div_r : forall q1 q2 q3,
  q1 / (q2 / q3) = (q1 * q3) / q2.
Proof using. math. Qed.

Lemma div_div_l : forall q1 q2 q3,
  (q1 / q2) / q3 = q1 / (q2 * q3).
Proof using. math. Qed.

Lemma div_mul_cancel_l : forall q1 q2,
  q1 <> 0 ->
  (q1 * q2) / q1 = q2.
Proof using. math. Qed.

Lemma mul_div_cancel_l : forall q1 q2,
  q1 <> 0 ->
  q1 * (q2 / q1) = q2.
Proof using. math. Qed.



(* ---------------------------------------------------------------------- *)
(** ** Inequalities *)

Lemma le_mul_mul : forall q1 q2 q3,
  q1 <= q2 ->
  q3 <= q4 ->
  q1 * q3 >= q2 * q4.
Proof using. math. Qed.

Lemma le_mul_same_r : forall q1 q2 q3,
  q1 <= q2 ->
  q3 >= 0 ->
  q1 * q3 <= q2 * q3.
Proof using. math. Qed.



(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_Q] performs some basic simplification on
    expressions involving rationals *)

#[global]
Hint Rewrite plus_zero_r plus_zero_l minus_zero_r minus_zero_l
  mult_zero_l mult_zero_r mult_one_l mult_one_r
  minus_self one_plus_minus_one_r plus_one_minus_one_l
  one_plus_minus_one_l : rew_Q.

Tactic Notation "rew_Q" :=
  autorewrite with rew_Q.
Tactic Notation "rew_Q" "~" :=
  rew_Q; auto_tilde.
Tactic Notation "rew_Q" "*" :=
  rew_Q; auto_star.
Tactic Notation "rew_Q" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_Q).
  (* autorewrite with rew_Q in *. *)
Tactic Notation "rew_Q" "~" "in" "*" :=
  rew_Q in *; auto_tilde.
Tactic Notation "rew_Q" "*" "in" "*" :=
  rew_Q in *; auto_star.
Tactic Notation "rew_Q" "in" hyp(H) :=
  autorewrite with rew_Q in H.
Tactic Notation "rew_Q" "~" "in" hyp(H) :=
  rew_Q in H; auto_tilde.
Tactic Notation "rew_Q" "*" "in" hyp(H) :=
  rew_Q in H; auto_star.




(* ********************************************************************** *)
(** * Conversions of operations from [int] to [Q] and back *)

(* ---------------------------------------------------------------------- *)
(** ** Lifting of comparisons *)

Lemma eq_int_of_eq_Q : forall (n1 n2:Z),
  (n1:Q) = (n2:Q) ->
  n1 = n2 :> int.
Proof using. math. Qed.

Lemma neq_int_of_neq_Q : forall (n1 n2:Z),
  (n1:Q) <> (n2:Q) ->
  n1 <> n2 :> int.
Proof using. math. Qed.

Lemma eq_Q_of_eq_Z : forall (n1 n2:Z),
  n1 = n2 :> int.
  (n1:Q) = (n2:Q) ->
Proof using. math. Qed.

Lemma neq_Q_of_neq_Z : forall (n1 n2:Z),
  n1 <> n2 :> int.
  (n1:Q) <> (n2:Q) ->
Proof using. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lifting of inequalities from [nat] to [int] *)

Lemma le_int_of_le_Q : forall (n1 n2:int),
  (n1:Q) <= (n2:Q) ->
  (n1 <= n2).
Proof using. math. Qed.

Lemma le_Q_of_le_int : forall (n1 n2:int),
  (n1 <= n2) ->
  (n1:Q) <= (n2:Q).
Proof using. math. Qed.

Lemma lt_int_of_lt_Q : forall (n1 n2:int),
  (n1:Q) < (n2:Q) ->
  (n1 < n2).
Proof using. math. Qed.

Lemma lt_Q_of_lt_int : forall (n1 n2:int),
  (n1 < n2) ->
  (n1:Q) < (n2:Q).
Proof using. math. Qed.

Lemma ge_int_of_ge_Q : forall (n1 n2:int),
  (n1:Q) >= (n2:Q) ->
  (n1 >= n2).
Proof using. math. Qed.

Lemma ge_Q_of_ge_int : forall (n1 n2:int),
  (n1 >= n2) ->
  (n1:Q) >= (n2:Q).
Proof using. math. Qed.

Lemma gt_int_of_gt_Q : forall (n1 n2:int),
  (n1:Q) > (n2:Q) ->
  (n1 > n2).
Proof using. math. Qed.

Lemma gt_Q_of_gt_int : forall (n1 n2:int),
  (n1 > n2) ->
  (n1:Q) > (n2:Q).
Proof using. math. Qed.

*)