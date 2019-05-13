(**

This file contains temporary definitions that will eventually
get merged into the various files from the TLC library.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibList LibReflect.
From TLC Require LibListZ.
Generalizable Variables A B.



(*----------------------*)
(* Nat *)

From TLC Require Import LibNat LibInt.


Section NatSimpl.
Open Scope nat_scope.
Implicit Types n : nat.

Lemma nat_zero_plus : forall n,
  0 + n = n.
Proof using. intros. math. Qed.

Lemma nat_plus_zero : forall n,
  n + 0 = n.
Proof using. intros. math. Qed.

Lemma nat_plus_succ : forall n1 n2,
  n1 + S n2 = S (n1 + n2).
Proof using. intros. math. Qed.

Lemma nat_minus_zero : forall n,
  n - 0 = n.
Proof using. intros. math. Qed.

Lemma nat_succ_minus_succ : forall n1 n2,
  S n1 - S n2 = n1 - n2.
Proof using. intros. math. Qed.

Lemma nat_minus_same : forall n,
  n - n = 0.
Proof using. intros. math. Qed.

Lemma nat_plus_minus_same : forall n1 n2,
  n1 + n2 - n1 = n2.
Proof using. intros. math. Qed.

End NatSimpl.

Hint Rewrite nat_zero_plus nat_plus_zero nat_plus_succ
  nat_minus_zero nat_succ_minus_succ
  nat_minus_same nat_plus_minus_same : rew_nat.


(** [nat_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint nat_seq (start:nat) (nb:nat) :=
  match nb with
  | O => nil
  | S nb' => start :: nat_seq (S start) nb'
  end.


Lemma length_nat_seq : forall start nb,
  length (nat_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.


(*----------------------*)
(*-- LATER: move to TLC LibNatExec *)

Fixpoint nat_compare (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => nat_compare x' y'
  | _, _ => false
  end.

Lemma nat_compare_eq : forall n1 n2,
  nat_compare n1 n2 = isTrue (n1 = n2).
Proof using.
  intros n1. induction n1; intros; destruct n2; simpl; rew_bool_eq; auto_false.
  rewrite IHn1. extens. rew_istrue. math.
Qed.


(*----------------------*)
(* LibLogic *)

Lemma if_classicT_eq_if_isTrue : forall A (X Y:A) (P:Prop),
  (If P then X else Y) = (if isTrue P then X else Y).
Proof using. intros. do 2 case_if~. Qed.


(*----------------------*)
(* TLCExec *)

Definition eq_exec A (cmp:A->A->bool) : Prop :=
  forall x y, cmp x y = isTrue (x = y).


(*----------------------*)
(* ListExec *)

From TLC Require Import LibLogic. (* needed? *)
From TLC Require Import LibReflect.

Lemma not_mem_inv : forall A x y (l:list A), 
  ~ mem x (y::l) ->
  x <> y /\ ~ mem x l.
Proof using.
  introv M. split.
  { intro_subst. false* M. }
  { intros N. false* M. }
Qed.

Definition is_not_nil A (l:list A) : bool :=
  match l with
  | nil => false
  | _ => true
  end.

Lemma is_not_nil_eq : forall A (l:list A),
  is_not_nil l = isTrue (l <> nil).
Proof.
  intros. destruct l; simpl; rew_bool_eq; auto_false.
Qed.

Lemma List_length_eq :
  List.length = LibList.length.
Proof using. extens ;=> A l. induction l; simpl; rew_list; auto. Qed.

Lemma List_fold_right_eq : forall A B (f:A->B->B) (l:list A) (b:B),
  List.fold_right f b l = LibList.fold_right f b l.
Proof using. intros. induction l; simpl; rew_list; fequals. Qed.

Lemma List_app_eq :
  List.app = LibList.app.
Proof using.
  extens ;=> A L1 L2. induction L1; simpl; rew_list; congruence.
Qed.

Lemma List_rev_eq : forall A, (* LATER: why fails if A is not quantified here? *)
  @List.rev A = @LibList.rev A.
Proof using.
  extens ;=> L. induction L; simpl; rew_list. { auto. }
  { rewrite List_app_eq. simpl. congruence. }
Qed.

Lemma List_map_eq :
  List.map = LibList.map.
Proof using.
  extens ;=> A B f L. induction L; simpl; rew_listx; congruence.
Qed.

Lemma List_combine_eq : forall A B (L1:list A) (L2:list B),
  length L1 = length L2 ->
  List.combine L1 L2 = LibList.combine L1 L2.
Proof using. (* LATER: redo proof using list2_ind *)
  introv E. gen L2.
  induction L1 as [|x1 L1']; intros; destruct L2 as [|x2 L2']; tryfalse.
  { auto. }
  { rew_list in E. simpl. fequals~. }
Qed.

Hint Rewrite LibList.length_map : rew_listx.

(* TODO: replace all List_foo_eq with a rew_list_exec tactic *)

Fixpoint mem_exec A (cmp:A->A->bool) (x:A) (l:list A) : bool :=
  match l with
  | nil => false
  | y::l' => cmp x y || mem_exec cmp x l'
  end.

Lemma mem_exec_eq : forall A (cmp:A->A->bool) x l,
  eq_exec cmp ->
  mem_exec cmp x l = isTrue (mem x l).
Proof using.
  introv Xcmp. induction l as [|y l']; simpl; rew_listx; rew_isTrue; fequals.
Qed.


(*----------------------*)
(* Hint for LibListZ *)

Hint Rewrite LibListZ.length_map LibListZ.index_map_eq : rew_arr.




(*----------------------*)
(* LibList *)


(** The congruence rule for [map] on lists *)

Lemma map_congr : forall A B (f1 f2 : A->B) l,
  (forall x, mem x l -> f1 x = f2 x) ->
  LibList.map f1 l = LibList.map f2 l.
Proof using. 
  introv H. induction l. { auto. } { rew_listx. fequals~. }
Qed.

Lemma map_map : forall A B C (l:list A) (f:A->B) (g:B->C), 
  map g (map f l) = map (fun x => g (f x)) l.
Proof using.
  intros. induction l as [|x l'].
  { auto. }
  { repeat rewrite map_cons. fequals. }
Qed.

Lemma mem_map' : forall A B (l : list A) (f:A->B) (x:A) (y:B),
  mem x l ->
  y = f x ->
  mem y (LibList.map f l).
Proof using. intros. subst. applys* mem_map. Qed.

(*----------------------*)
(* LibInt *)

Global Opaque Z.mul.
Global Opaque Z.add.

(*----------------------*)
(* LibEqual *)

Section FuncExtDep.
Variables (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).

Lemma fun_eta_dep_3 : forall (f : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3),
  (fun x1 x2 x3 => f x1 x2 x3) = f.
Proof using. intros. apply~ fun_ext_3. Qed.

End FuncExtDep.



(* ---------------------------------------------------------------------- *)
(* LibTactics *)

Ltac fequal_base ::=
  let go := f_equal_fixed; [ fequal_base | ] in
  match goal with
  | |- exist _ _ = exist _ _ => apply exist_eq_exist
  | |- (_,_,_) = (_,_,_) => go
  | |- (_,_,_,_) = (_,_,_,_) => go
  | |- (_,_,_,_,_) = (_,_,_,_,_) => go
  | |- (_,_,_,_,_,_) = (_,_,_,_,_,_) => go
  | |- _ => f_equal_fixed
  end.

(* [isubst] generalizes [intro_subst]
  DEPRECATED : should use [intros ? ->] *)

Ltac isbust_core tt :=
  match goal with |- forall _, _ = _ -> _ =>
    let X := fresh "TEMP" in
    let HX := fresh "E" X in
    intros X HX; subst X
  end.

Tactic Notation "isubst" :=
  isbust_core tt.

(** [get_head E] implemented recursively *)

Ltac get_head E :=
  match E with 
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

(** [has_no_evar E] succeeds if [M] contains no evars. *)

Ltac has_no_evar E :=
  first [ has_evar E; fail 1 | idtac ].


(* ---------------------------------------------------------------------- *)
(* Cases *)

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.




(* ---------------------------------------------------------------------- *)
(* Induction on pairs of lists *)

Lemma list2_ind : forall A B (P:list A->list B->Prop) l1 l2,
  length l1 = length l2 ->
  P nil nil ->
  (forall x1 xs1 x2 xs2,
     length xs1 = length xs2 -> P xs1 xs2 -> P (x1::xs1) (x2::xs2)) ->
  P l1 l2.
Proof using.
  introv E M1 M2. gen l2. induction l1 as [|x1 l1']; intros;
   destruct l2 as [|x2 l2']; try solve [false; math]; auto.
Qed.

Tactic Notation "list2_ind" constr(l1) constr(l2) :=
  pattern l2; pattern l1;
  match goal with |- (fun a => (fun b => @?P a b) _) _ =>
   (* applys list2_ind P *)
   let X := fresh "P" in set (X := P); applys list2_ind X; unfold X; try clear X
 end.

Tactic Notation "list2_ind" "~" constr(l1) constr(l2) :=
  list2_ind l1 l2; auto_tilde.

Tactic Notation "list2_ind" "*" constr(l1) constr(l2) :=
  list2_ind l1 l2; auto_star.

Tactic Notation "list2_ind" constr(E) :=
  match type of E with length ?l1 = length ?l2 =>
    list2_ind l1 l2; [ apply E | | ] end.

(** Same, but on last element *)

Lemma list2_ind_last : forall A B (P:list A->list B->Prop) l1 l2,
  length l1 = length l2 ->
  P nil nil ->
  (forall x1 xs1 x2 xs2,
     length xs1 = length xs2 -> P xs1 xs2 -> P (xs1&x1) (xs2&x2)) ->
  P l1 l2.
Proof using.
  introv E M1 M2. gen l2. induction l1 using list_ind_last;
   [| rename a into x1, l1 into l1']; intros;
   destruct (last_case l2) as [|(x2&l2'&E2)]; subst; rew_list in *;
   try solve [false; math]; auto.
Qed.

Tactic Notation "list2_ind_last" constr(l1) constr(l2) :=
  pattern l2; pattern l1;
  match goal with |- (fun a => (fun b => @?P a b) _) _ =>
   (* applys list2_ind P *)
   let X := fresh "P" in set (X := P); applys list2_ind_last X; unfold X; try clear X
 end.

Tactic Notation "list2_ind_last" "~" constr(l1) constr(l2) :=
  list2_ind_last l1 l2; auto_tilde.

Tactic Notation "list2_ind_last" "*" constr(l1) constr(l2) :=
  list2_ind_last l1 l2; auto_star.

Tactic Notation "list2_ind_last" constr(E) :=
  match type of E with length ?l1 = length ?l2 =>
    list2_ind_last l1 l2; [ apply E | | ] end.



