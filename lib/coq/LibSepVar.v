(**

This file describes the representation of variables.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require LibListExec.
From TLC Require Export LibString LibList LibCore.
From CFML Require Import LibSepFmap LibSepTLCbuffer.
Module Fmap := LibSepFmap.
Open Scope string_scope.
Generalizable Variables A.


(* ********************************************************************** *)
(* * Variables *)

(** A variable is represented as a string.

    The boolean function [var_eq x y] compares two variables.

    The tactic [case_var] performs case analysis on expressions of the form
    [if var_eq x y then .. else ..] that appear in the goal.

*)

(* ---------------------------------------------------------------------- *)
(** Representation of variables *)

(** Variables are represented as strings *)

Definition var := string.

(** Variables can be compared via [var_eq s1 s2] *)

Definition eq_var_dec := String.string_dec.

Definition var_eq (s1:var) (s2:var) : bool :=
  if eq_var_dec s1 s2 then true else false.

Lemma var_eq_spec : forall s1 s2,
  var_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold var_eq. case_if; rew_bool_eq~.
Qed.

Global Opaque var.

(** Tactic [var_neq] for proving two concrete variables distinct.
    Also registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var =>
    solve [ let E := fresh in
            destruct (eq_var_dec x y) as [E|E];
              [ false | apply E ] ] end.

Hint Extern 1 (?x <> ?y) => var_neq.


(* ---------------------------------------------------------------------- *)
(** Tactic [case_var] *)

Tactic Notation "case_var" :=
  repeat rewrite var_eq_spec in *; repeat case_if.

Tactic Notation "case_var" "~" :=
  case_var; auto_tilde.

Tactic Notation "case_var" "*" :=
  case_var; auto_star.


(* ---------------------------------------------------------------------- *)
(** Distinct variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.

(** [var_distinct xs] asserts that [xs] consists of a list of distinct variables.
    --LATER: use [noduplicates] *)

Fixpoint var_distinct (xs:vars) : Prop :=
  match xs with
  | nil => True
  | x::xs' => var_fresh x xs' /\ var_distinct xs'
  end.

(** Computable version of [var_distinct] *)

Fixpoint var_distinct_exec (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => var_fresh x xs' && var_distinct_exec xs'
  end.

Lemma var_distinct_exec_eq : forall xs,
  var_distinct_exec xs = isTrue (var_distinct xs).
Proof using.
  intros. induction xs as [|x xs']; simpl; rew_isTrue.
  { auto. } { rewrite~ IHxs'. }
Qed.

(** Elimination lemma for [var_fresh] *)

Lemma var_fresh_mem_inv : forall y x xs,
  var_fresh x xs ->
  mem y xs ->
  x <> y.
Proof using.
  introv H M N. subst. induction xs as [|x xs'].
  { inverts M. }
  { simpls. case_var. inverts~ M. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** List of n fresh variables *)

(** [var_funs xs n] asserts that [xs] consists of [n] distinct variables,
    for [n > 0]. *)

Definition var_funs (xs:vars) (n:nat) : Prop :=
     var_distinct xs
  /\ length xs = n
  /\ xs <> nil.

(** Computable version of [var_funs] *)

Definition var_funs_exec (xs:vars) (n:nat) : bool :=
     LibNat.beq n (LibListExec.length xs)
  && LibListExec.is_not_nil xs
  && var_distinct_exec xs.

Lemma var_funs_exec_eq : forall (n:nat) xs,
  var_funs_exec xs n = isTrue (var_funs xs n).
Proof using.
  intros. unfold var_funs_exec, var_funs.
  rewrite LibNat.beq_eq.
  rewrite LibListExec.is_not_nil_eq.
  rewrite LibListExec.length_eq.
  rewrite var_distinct_exec_eq.
  extens. rew_istrue. iff*.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Generation of n variables *)

(** [nat_to_var n] converts [nat] values into distinct
    [name] values.
    Warning: the current implementation is inefficient. *)

Definition dummy_char := Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_var (n:nat) : var :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_var n')
  end.

Lemma injective_nat_to_var : injective nat_to_var.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (nat_to_var start) :: var_seq (S start) nb'
  end.

(** Properties of [var_seq] follow *)

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall (x:nat) start nb,
  (x < start)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_var.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall (x:nat) start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_var.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_distinct_var_seq : forall start nb,
  var_distinct (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { simple~. }
  { split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

Lemma var_funs_var_seq : forall start nb,
  (nb > 0%nat)%nat ->
  var_funs (var_seq start nb) nb.
Proof using.
  introv E. splits.
  { applys var_distinct_var_seq. }
  { applys length_var_seq. }
  { destruct nb. { false. math. } { simpl. auto_false. } }
Qed.

End Var_seq.


(* ********************************************************************** *)
(* * Notation for program variables *)

(** To avoid using the string notation ["x"] for refering to a
    variable called [x], one can use the notation ['x], available
    by importing the following module. *)


Module NotationForVariables.

Declare Scope var_scope.

Notation "''a'" := ("a":var) : var_scope.
Notation "''b'" := ("b":var) : var_scope.
Notation "''c'" := ("c":var) : var_scope.
Notation "''d'" := ("d":var) : var_scope.
Notation "''e'" := ("e":var) : var_scope.
Notation "''f'" := ("f":var) : var_scope.
Notation "''g'" := ("g":var) : var_scope.
Notation "''h'" := ("h":var) : var_scope.
Notation "''i'" := ("i":var) : var_scope.
Notation "''j'" := ("j":var) : var_scope.
Notation "''k'" := ("k":var) : var_scope.
Notation "''l'" := ("l":var) : var_scope.
Notation "''m'" := ("m":var) : var_scope.
Notation "''n'" := ("n":var) : var_scope.
Notation "''o'" := ("o":var) : var_scope.
Notation "''p'" := ("p":var) : var_scope.
Notation "''q'" := ("q":var) : var_scope.
Notation "''r'" := ("r":var) : var_scope.
Notation "''s'" := ("s":var) : var_scope.
Notation "''t'" := ("t":var) : var_scope.
Notation "''u'" := ("u":var) : var_scope.
Notation "''v'" := ("v":var) : var_scope.
Notation "''w'" := ("w":var) : var_scope.
Notation "''x'" := ("x":var) : var_scope.
Notation "''y'" := ("y":var) : var_scope.
Notation "''z'" := ("z":var) : var_scope.

Notation "''a1'" := ("a1":var) : var_scope.
Notation "''b1'" := ("b1":var) : var_scope.
Notation "''c1'" := ("c1":var) : var_scope.
Notation "''d1'" := ("d1":var) : var_scope.
Notation "''e1'" := ("e1":var) : var_scope.
Notation "''f1'" := ("f1":var) : var_scope.
Notation "''g1'" := ("g1":var) : var_scope.
Notation "''h1'" := ("h1":var) : var_scope.
Notation "''i1'" := ("i1":var) : var_scope.
Notation "''j1'" := ("j1":var) : var_scope.
Notation "''k1'" := ("k1":var) : var_scope.
Notation "''l1'" := ("l1":var) : var_scope.
Notation "''m1'" := ("m1":var) : var_scope.
Notation "''n1'" := ("n1":var) : var_scope.
Notation "''o1'" := ("o1":var) : var_scope.
Notation "''p1'" := ("p1":var) : var_scope.
Notation "''q1'" := ("q1":var) : var_scope.
Notation "''r1'" := ("r1":var) : var_scope.
Notation "''s1'" := ("s1":var) : var_scope.
Notation "''t1'" := ("t1":var) : var_scope.
Notation "''u1'" := ("u1":var) : var_scope.
Notation "''v1'" := ("v1":var) : var_scope.
Notation "''w1'" := ("w1":var) : var_scope.
Notation "''x1'" := ("x1":var) : var_scope.
Notation "''y1'" := ("y1":var) : var_scope.
Notation "''z1'" := ("z1":var) : var_scope.

Notation "''a2'" := ("a2":var) : var_scope.
Notation "''b2'" := ("b2":var) : var_scope.
Notation "''c2'" := ("c2":var) : var_scope.
Notation "''d2'" := ("d2":var) : var_scope.
Notation "''e2'" := ("e2":var) : var_scope.
Notation "''f2'" := ("f2":var) : var_scope.
Notation "''g2'" := ("g2":var) : var_scope.
Notation "''h2'" := ("h2":var) : var_scope.
Notation "''i2'" := ("i2":var) : var_scope.
Notation "''j2'" := ("j2":var) : var_scope.
Notation "''k2'" := ("k2":var) : var_scope.
Notation "''l2'" := ("l2":var) : var_scope.
Notation "''m2'" := ("m2":var) : var_scope.
Notation "''n2'" := ("n2":var) : var_scope.
Notation "''o2'" := ("o2":var) : var_scope.
Notation "''p2'" := ("p2":var) : var_scope.
Notation "''q2'" := ("q2":var) : var_scope.
Notation "''r2'" := ("r2":var) : var_scope.
Notation "''s2'" := ("s2":var) : var_scope.
Notation "''t2'" := ("t2":var) : var_scope.
Notation "''u2'" := ("u2":var) : var_scope.
Notation "''v2'" := ("v2":var) : var_scope.
Notation "''w2'" := ("w2":var) : var_scope.
Notation "''x2'" := ("x2":var) : var_scope.
Notation "''y2'" := ("y2":var) : var_scope.
Notation "''z2'" := ("z2":var) : var_scope.

Notation "''a3'" := ("a3":var) : var_scope.
Notation "''b3'" := ("b3":var) : var_scope.
Notation "''c3'" := ("c3":var) : var_scope.
Notation "''d3'" := ("d3":var) : var_scope.
Notation "''e3'" := ("e3":var) : var_scope.
Notation "''f3'" := ("f3":var) : var_scope.
Notation "''g3'" := ("g3":var) : var_scope.
Notation "''h3'" := ("h3":var) : var_scope.
Notation "''i3'" := ("i3":var) : var_scope.
Notation "''j3'" := ("j3":var) : var_scope.
Notation "''k3'" := ("k3":var) : var_scope.
Notation "''l3'" := ("l3":var) : var_scope.
Notation "''m3'" := ("m3":var) : var_scope.
Notation "''n3'" := ("n3":var) : var_scope.
Notation "''o3'" := ("o3":var) : var_scope.
Notation "''p3'" := ("p3":var) : var_scope.
Notation "''q3'" := ("q3":var) : var_scope.
Notation "''r3'" := ("r3":var) : var_scope.
Notation "''s3'" := ("s3":var) : var_scope.
Notation "''t3'" := ("t3":var) : var_scope.
Notation "''u3'" := ("u3":var) : var_scope.
Notation "''v3'" := ("v3":var) : var_scope.
Notation "''w3'" := ("w3":var) : var_scope.
Notation "''x3'" := ("x3":var) : var_scope.
Notation "''y3'" := ("y3":var) : var_scope.
Notation "''z3'" := ("z3":var) : var_scope.

Open Scope var_scope.

End NotationForVariables.
