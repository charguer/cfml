Set Implicit Arguments.
From TLC Require Import LibTactics LibRelation LibEpsilon LibLogic LibInt.
From Coq Require Import Field.
Open Scope Z_scope.
Open Scope Int_scope.


(* ********************************************************************** *)
(** * LibQuotient *)

Lemma repr_eq_repr_repr : forall A {IA:Inhab A} (R:binary A) (HR:equiv R) (x:A),
  epsilon (R x) = epsilon (R (epsilon (R x))).
Proof using.
  intros. asserts Re: (forall a, exists b, R a b). { intros a. exists a. applys* equiv_refl. }
  apply epsilon_eq. intros y. iff M1.
  { epsilon* x'. intros M2. applys* equiv_trans M1. applys* equiv_sym. }
  { epsilon* x'. intros M2. applys* equiv_trans M2. }
Qed.

Definition quotient A {IA:Inhab A} (R:binary A) : Type :=
  { repr : A | repr = epsilon (R repr) }.

#[global]
Instance Inhab_quotient : forall A {IA:Inhab A} (R:binary A) (HR:equiv R),
  Inhab (quotient R).
Proof using.
  intros. eapply Inhab_of_val. applys exist (epsilon (R (arbitrary (A:=A)))). applys* repr_eq_repr_repr.
Qed.

Definition inject A {IA:Inhab A} (R:binary A) (HR:equiv R) (x:A) : quotient R :=
  exist _ (epsilon (R x)) (repr_eq_repr_repr HR x).

Lemma inject_eq_eq_rel : forall A {IA:Inhab A} (R:binary A) (HR:equiv R) (x y:A),
  (inject HR x = inject HR y) = (R x y).
Proof using.
  intros. asserts Re: (forall a, exists b, R a b). { intros a. exists a. applys* equiv_refl. }
  extens. iff M.
  { inverts M as M'. epsilon* x'. intros Mx. epsilon* y'. intros My. rewrite M' in Mx.
    applys* equiv_trans Mx. applys* equiv_sym My. }
  { applys exist_eq_exist. applys epsilon_eq. intros z. iff M2.
    { applys* equiv_trans M2. applys* equiv_sym. }
    { applys* equiv_trans M. } }
Qed.


(* ********************************************************************** *)
(** * Q and operations *)

(* ---------------------------------------------------------------------- *)
(** ** Notation for type and operation *)

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.

Local Open Scope Q_scope.


(* ---------------------------------------------------------------------- *)
(** ** Type definition *)

(** Supports are pairs of a Z and a nonzero-Z *)

Definition support : Type :=
  { p : Z*Z | let '(n,m) := p in m <> 0 }.

#[local]
Instance Inhab_support : Inhab support.
Proof using.
  asserts E: (1 <> 0). { math. }
  intros. eapply (Inhab_of_val (exist _ (1,1) E)).
Qed.

(** Equivalence of pairs *)

Definition rel (p1 p2 : support) : Prop :=
  let '(n1,m1) := sig_val p1 in
  let '(n2,m2) := sig_val p2 in
  n1 * m2 = n2 * m1.

Require Import  Coq.ZArith.BinInt.

Lemma equiv_rel : equiv rel.
Proof using.
  constructors.
  { intros ((n,m)&H1). unfold rel; simpls. ring. }
  { intros ((n1,m1)&H1) ((n2,m2)&H2) E. unfolds rel; simpls. eauto. }
  { intros ((n1,m1)&H1) ((n2,m2)&H2) ((n3,m3)&H3) E1 E2. unfolds rel; simpls.
    applys* Z.mul_reg_l m1. rewrite Z.mul_shuffle3. rewrite Z.mul_assoc.
    rewrite E1. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm m2).
    rewrite Z.mul_assoc. rewrite E2. rewrite Z.mul_shuffle3. rewrite* Z.mul_assoc. }
Qed.

(** Definition of Q as the quotient *)

Definition Q : Type :=
  quotient rel.

Implicit Types q : Q.

(** Inhabited type *)

#[global]
Instance Inhab_Q : Inhab Q.
Proof using. intros. applys Inhab_quotient equiv_rel. Qed.


(** Constructor from numerator/denominator *)

Program Definition make (n m : Z) : Q :=
  If m = 0 then arbitrary else inject equiv_rel (n,m).


(** Conversion from Z, registered as coercion *)

Coercion Z_to_Q (n:Z) : Q :=
  make n 1.


(* ---------------------------------------------------------------------- *)
(** ** Internal operations -- don't use outside this module *)

(** Query of a numerator/denominator representation *)

Definition Q_to_ZZ (q:Q) : Z*Z :=
  sig_val (sig_val q).

(** Proving equalities -- for internal use only *)

Lemma Q_eq' : forall q1 q2,
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  (n1 = n2 /\ m1 = m2) ->
  q1 = q2.
Proof using.
  intros (((n1,m1)&Hm1)&E1) (((n2,m2)&Hm2)&E2) (EQ1&EQ2). simpls.
  applys exist_eq_exist. applys exist_eq_exist. autos*.
Qed.

From Coq Require Import Field.

Lemma make_eq : forall n1 m1 n2 m2,
  (n1 * m2 = m1 * n2)%Z ->
  m1 <> 0 ->
  m2 <> 0 ->
  make n1 m1 = make n2 m2.
Proof using.
  introv E N1 N2. unfold make.
  destruct (classicT (m1 = 0)); try math.
  destruct (classicT (m2 = 0)); try math.
  applys exist_eq_exist. applys epsilon_eq. intros ((n3&m3)&N3). simpls.
  unfold rel. simpl. iff M.
  { applys* Z.mul_reg_l m1. rewrite Z.mul_assoc. rewrite <- E.
    rewrite <- Z.mul_assoc. rewrite Z.mul_shuffle3. rewrite M.
    rewrite <- (Z.mul_comm m1). rewrite Z.mul_shuffle3.
    rewrite <- (Z.mul_comm n3). auto. }
  { applys* Z.mul_reg_l m2. rewrite Z.mul_assoc. rewrite <- (Z.mul_comm n1).
    rewrite E. rewrite <- Z.mul_assoc. rewrite M. rewrite <- (Z.mul_comm m2).
    rewrite Z.mul_shuffle3. rewrite <- (Z.mul_comm m1). auto. }
Qed.

Hint Resolve equiv_rel.

Lemma make_eq_make_inv : forall n1 m1 n2 m2,
  make n1 m1 = make n2 m2 ->
  m1 <> 0 ->
  m2 <> 0 ->
  (n1 * m2 = m1 * n2)%Z.
Proof using.
  introv E N1 N2. unfolds make.
  destruct (classicT (m1 = 0)); try math.
  destruct (classicT (m2 = 0)); try math.
  inverts E as E'.
  epsilon* s1. { esplit. applys* equiv_refl. }
  epsilon* s2. { esplit. applys* equiv_refl. }
  destruct s1 as ((a1&b1)&Nb1).
  destruct s2 as ((a2&b2)&Nb2).
  unfold rel. simpl.
  introv E1 E2. inverts E'.
  applys* Z.mul_reg_l b2. rewrite Z.mul_assoc. rewrite <- (Z.mul_comm n1). rewrite E2.
  rewrite <- Z.mul_assoc. rewrite <- (Z.mul_comm m2). rewrite Z.mul_assoc.
  rewrite <- E1. rewrite <- (Z.mul_comm b2). rewrite  (Z.mul_comm m1).
  rewrite Z.mul_assoc. auto.
Qed.

(*
Lemma make_eq : forall n m (Hm:m <> 0),
  exists H Hm, make n m = inject equiv_rel (exist _ (n,m) Hm) H.
*)

Lemma Q_inv : forall q,
  exists n m, m <> 0 /\ Q_to_ZZ q = (n,m) /\ q = make n m.
Proof using.
  intros (((n1,m1)&Hm1)&E1). exists n1 m1. splits.
  { auto. }
  { unfold Q_to_ZZ. simple*. }
  { unfold make. destruct (classicT (m1 = 0)). { false. }
    applys exist_eq_exist. auto. }
Qed.

Lemma Q_inv_Z : forall (a:Z),
  exists n m, m <> 0 /\ (Q_to_ZZ (Z_to_Q a)) = (n,m) /\ (a * m = n)%Z.
Proof using.
  intros. lets (n&m&Nm&Em&Fm): Q_inv (Z_to_Q a).
  exists n m. splits*. unfolds Z_to_Q.
  forwards E: make_eq_make_inv Fm; try math; auto.
Qed.

Lemma Q_inv_make : forall a b,
  b <> 0 ->
  exists n m, m <> 0 /\ Q_to_ZZ (make a b) = (n,m) /\ a * m = b * n.
Proof using.
  introv Hb. lets (n&m&Nm&Em&Fm): Q_inv (make a b).
  forwards*: make_eq_make_inv Fm.
Qed.




(* ---------------------------------------------------------------------- *)
(** ** Operations *)

Definition add (q1 q2 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  make (n1*m2 + n2*m1) (m1*m2).

Definition mul (q1 q2 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  make (n1*n2) (m1*m2).

Definition opp (q1 : Q) : Q :=
  mul (-1) q1.
  (* alternative:
  let '(n1,m1) := Q_to_ZZ q1 in
  make (-n1) m1.
  *)

Definition sub (q1 q2 : Q) : Q :=
  add q1 (opp q2).

(* only for internal use *)
Definition inv (q1 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  make m1 n1.

Definition div (q1 q2 : Q) : Q :=
  mul q1 (inv q2).


(** Notations *)

Infix "+" := add : Q_scope.

Infix "*" := mul : Q_scope.

Notation "- x" := (opp x) : Q_scope.

Infix "-" := sub : Q_scope.

Infix "/" := div : Q_scope.


(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Definition Q_le (q1 q2 : Q) : Prop :=
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  n1 * m2 <= n2 * m1.

Open Scope comp_scope.

#[global]
Instance le_Q_inst : Le Q := Build_Le Q_le.

Lemma le_reveal : forall A `{Le A} (R:binary A) x y,
  @le A {| le := R |} x y = R x y.
Proof using. auto. Qed.

Lemma make_le_make_inv : forall n1 m1 n2 m2,
  make n1 m1 <= make n2 m2 ->
  m1 <> 0 ->
  m2 <> 0 ->
  (n1 * m2 <= m1 * n2)%Z.
Proof using.
  introv E N1 N2. unfolds make.
  destruct (classicT (m1 = 0)); try math.
  destruct (classicT (m2 = 0)); try math.
  unfolds le_Q_inst. rewrite le_reveal in E; try typeclass.
  unfolds Q_le. unfolds inject, Q_to_ZZ. simpls.
  epsilon* s1. { esplit. applys* equiv_refl. }
  epsilon* s2. { esplit. applys* equiv_refl. }
  destruct s1 as ((a1&b1)&Nb1).
  destruct s2 as ((a2&b2)&Nb2).
  unfold rel. simpl.
  introv E1 E2. simpls. skip. (* TODO *)
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)

Open Scope Q_scope.

Lemma plus_zero_r : forall q,
  q + 0 = q.
Proof using.
  intros. lets (n1&m1&N1&E1&F1): Q_inv q.
  intros. lets (n2&m2&N2&E2&F2): Q_inv_Z 0.
  unfold add. rewrite E1, E2, F1.
  rewrite Z.mul_0_l in F2. subst. rewrite Z.mul_0_l. rew_int.
  applys* make_eq. ring. math.
Qed.

Lemma plus_zero_l : forall q,
  0 + q = q.
Proof using. skip. Qed.

Lemma minus_zero_r : forall q,
  q - 0 = q.
Proof using. skip. Qed.

Lemma minus_zero_l : forall q,
  0 - q = (- q).
Proof using. skip. Qed.

Lemma mul_zero_l : forall q,
  0 * q = 0.
Proof using. skip. Qed.

Lemma mul_zero_r : forall q,
  q * 0 = 0.
Proof using. skip. Qed.

Lemma mul_one_l : forall q,
  1 * q = q.
Proof using. skip. Qed.

Lemma mul_one_r : forall q,
  q * 1 = q.
Proof using. skip. Qed.

Lemma minus_self : forall q,
  q - q = 0.
Proof using. skip. Qed.

Lemma one_plus_minus_one_r : forall q,
  1 + (q - 1) = q.
Proof using. skip. Qed.

Lemma plus_one_minus_one_l : forall q,
  (q + 1) - 1 = q.
Proof using. skip. Qed.

Lemma one_plus_minus_one_l : forall q,
  (1 + q) - 1 = q.
Proof using. skip. Qed.

(* e.g.
q1 - (q2 + q3)
*)

(* ---------------------------------------------------------------------- *)
(** ** Multiplication, division and inversions *)

Lemma mul_zero_inv : forall q1 q2,
  q1 * q2 = 0 ->
  q1 = 0 \/ q2 = 0.
Proof using. skip. Qed.

Lemma mul_zero_inv_nonzero_l : forall q1 q2,
  q1 * q2 = 0 ->
  q1 <> 0 ->
  q2 = 0.
Proof using. skip. Qed.

Lemma div_same : forall q,
  q / q = 1.
Proof using. skip. Qed.

Lemma mul_assoc : forall q1 q2 q3,
  q1 * (q2 * q3) = (q1 * q2) * q3.
Proof using.
  intros. unfold mul.
  lets (n1&m1&N1&->&F1): Q_inv q1.
  lets (n2&m2&N2&->&F2): Q_inv q2.
  lets (n3&m3&N3&->&F3): Q_inv q3.
  forwards (n4&m4&N4&->&F4): Q_inv_make (n2 * n3)%Z (m2 * m3)%Z; try math. (* TODO: use match context *)
  forwards (n5&m5&N5&->&F5): Q_inv_make (n1 * n2)%Z (m1 * m2)%Z; try math.
  applys make_eq; try math.
  applys* Z.mul_reg_l m2.
  asserts_rewrite ((m2 * (n1 * n4 * (m5 * m3))) = (m2 * m3 * n4) * (n1 * m5))%Z; try ring.
  rewrite <- F4.
  asserts_rewrite ((n2 * n3 * m4 * (n1 * m5)) = (n1 * n2 * m5) * (n3 * m4))%Z; try ring.
  rewrite F5.
  ring.
Qed.

Lemma mul_div_r : forall q1 q2 q3,
  q1 * (q2 / q3) = (q1 * q2) / q3.
Proof using. skip. Qed.

Lemma mul_inv_r : forall q,
  q * (1 / q) = 1.
Proof using. skip. Qed.

Lemma div_div_r : forall q1 q2 q3,
  q1 / (q2 / q3) = (q1 * q3) / q2.
Proof using. skip. Qed.

Lemma div_div_l : forall q1 q2 q3,
  (q1 / q2) / q3 = q1 / (q2 * q3).
Proof using. skip. Qed.

Lemma div_mul_cancel_l : forall q1 q2,
  q1 <> 0 ->
  (q1 * q2) / q1 = q2.
Proof using. skip. Qed.

Lemma mul_div_cancel_l : forall q1 q2,
  q1 <> 0 ->
  q1 * (q2 / q1) = q2.
Proof using. skip. Qed.



(* ---------------------------------------------------------------------- *)
(** ** Inequalities *)

Lemma le_mul_mul : forall q1 q2 q3 q4,
  q1 <= q2 ->
  q3 <= q4 ->
  q1 * q3 >= q2 * q4.
Proof using. skip. Qed.

Lemma le_mul_same_r : forall q1 q2 q3,
  q1 <= q2 ->
  q3 >= 0 ->
  q1 * q3 <= q2 * q3.
Proof using. skip. Qed.



(* ---------------------------------------------------------------------- *)
(** ** Rewriting *)

Lemma add_Z_to_Q : forall n m,
  ((Z_to_Q n) + (Z_to_Q m))%Q = (Z_to_Q (n + m)%Z).
Proof. skip. (* TODO *) Qed.

Lemma sub_Z_to_Q : forall n m,
  ((Z_to_Q n) - (Z_to_Q m))%Q = (Z_to_Q (n - m)%Z).
Proof. skip. (* TODO *) Qed.

Lemma neg_Z_to_Q : forall n,
  (- (Z_to_Q n))%Q = (Z_to_Q (- n)%Z).
Proof. skip. (* TODO *) Qed.

Lemma Q_add_zero_l : forall q,
  (0 + q)%Q = q.
Proof. skip. (* TODO *) Qed.

Lemma Q_add_zero_r : forall q,
  (q + 0)%Q = q.
Proof. skip. (* TODO *) Qed.

Hint Rewrite add_Z_to_Q sub_Z_to_Q neg_Z_to_Q Q_add_zero_l Q_add_zero_r : rew_Q.



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
  n1 = n2.
Proof using. skip. Qed.

Lemma neq_int_of_neq_Q : forall (n1 n2:Z),
  (n1:Q) <> (n2:Q) ->
  n1 <> n2.
Proof using. skip. Qed.

Lemma eq_Q_of_eq_Z : forall (n1 n2:Z),
  n1 = n2 ->
  (n1:Q) = (n2:Q).
Proof using. skip. Qed.

Lemma neq_Q_of_neq_Z : forall (n1 n2:Z),
  n1 <> n2 ->
  (n1:Q) <> (n2:Q).
Proof using. skip. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lifting of inequalities from [nat] to [int] *)

Lemma le_int_of_le_Q : forall (n1 n2:Z),
  (n1:Q) <= (n2:Q) ->
  (n1 <= n2).
Proof using.
  intros a1 a2 M.
  unfolds le_Q_inst. simpls. unfolds Q_le. unfolds Z_to_Q.
  lets (n1&m1&N1&E1&F1): Q_inv_Z a1.
  lets (n2&m2&N2&E2&F2): Q_inv_Z a2.
  forwards: make_le_make_inv M; try math.
Qed.

Lemma le_Q_of_le_int : forall (n1 n2:int),
  (n1 <= n2) ->
  (n1:Q) <= (n2:Q).
Proof using. skip. Qed.

Lemma lt_int_of_lt_Q : forall (n1 n2:int),
  (n1:Q) < (n2:Q) ->
  (n1 < n2).
Proof using. skip. Qed.

Lemma lt_Q_of_lt_int : forall (n1 n2:int),
  (n1 < n2) ->
  (n1:Q) < (n2:Q).
Proof using. skip. Qed.

Lemma ge_int_of_ge_Q : forall (n1 n2:int),
  (n1:Q) >= (n2:Q) ->
  (n1 >= n2).
Proof using. skip. Qed.

Lemma ge_Q_of_ge_int : forall (n1 n2:int),
  (n1 >= n2) ->
  (n1:Q) >= (n2:Q).
Proof using. skip. Qed.

Lemma gt_int_of_gt_Q : forall (n1 n2:int),
  (n1:Q) > (n2:Q) ->
  (n1 > n2).
Proof using. skip. Qed.

Lemma gt_Q_of_gt_int : forall (n1 n2:int),
  (n1 > n2) ->
  (n1:Q) > (n2:Q).
Proof using. skip. Qed.



(* ********************************************************************** *)
(** * Ring and Field *)


Definition ring_theory_Q : ring_theory (Z_to_Q 0) (Z_to_Q 1) add mul sub opp (eq(A:=Q)).
Proof.
  constructor.
  { exact plus_zero_l. }
  { skip. (* plus_comm. *) }
  { skip. (* plus assoc *) }
  { exact mul_one_l. }
  { skip. (* mul_comm. *) }
  { skip. (* mul_assoc. *) }
  { skip. (* mul_distrib *) }
  { reflexivity. }
  { skip. (* add_opp_same *) } 
Qed. (* TODO *)

Add Ring ring_Q : ring_theory_Q.

Definition field_theory_Q :
  field_theory (Z_to_Q 0) (Z_to_Q 1)  add mul sub opp div inv (eq(A:=Q)).
Proof.
  constructor.
  { exact ring_theory_Q. }
  { applys neq_Q_of_neq_Z. math. } 
  { reflexivity. }
  { skip. } (* TODO *)
Qed.

Add Field field_Q : field_theory_Q.

(* see also https://coq.inria.fr/library/Coq.QArith.Qfield.html# for bonuses *)