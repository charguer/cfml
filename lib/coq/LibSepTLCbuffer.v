(**

This file contains temporary definitions that will eventually
get merged into the various files from the TLC library.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
(*
From TLC Require Import LibTactics LibLogic LibList.
From TLC Require Import LibReflect.
From TLC Require LibListZ LibWf LibMultiset LibInt.
*)
From TLC Require Import LibTactics LibReflect.
From TLC Require Import LibInt.
Generalizable Variables A B.

Global Opaque Z.mul.
Global Opaque Z.add.


(*--------------------------------------------------------*)
(* TLC LibTactics *)

Ltac induction_wf_core_then E X cont ::=
  let clearX tt :=
    first [ clear X | fail 3 "the variable on which the induction is done appears in the hypotheses" ] in
  pattern X;
  first [ eapply (@well_founded_ind _ E)
        | eapply (@well_founded_ind _ (E _))
        | eapply (@well_founded_ind _ (E _ _))
        | eapply (@well_founded_ind _ (E _ _ _))
        | induction_wf_process_measure E
        | applys well_founded_ind E ];
  clearX tt;
  first [ induction_wf_process_wf_hyp tt
        | intros X; cont tt ].

Ltac induction_wf_core IH E X ::=
  induction_wf_core_then E X ltac:(fun _ => intros IH).

(*--------------------------------------------------------*)
(* LibList *)

From TLC Require Import LibList.

Module LibListNotation.
Notation "[ ]" := nil (format "[ ]") : liblist_scope.
Notation "[ x ]" := (cons x nil) : liblist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : liblist_scope.
End LibListNotation.


(*--------------------------------------------------------*)
(* LibListZ *)

From TLC Require Import LibListZ.

Lemma index_make_eq : forall A (n i:Z) (v:A),
  index (make n v) i = index n i.
Admitted. (* TODO *)

Lemma index_update_eq : forall A (l:list A) (i j:Z) (v:A),
  index l j ->
  (index l[j:=v] i) = (index l i).
Admitted. (* TODO *)

Hint Rewrite int_index_eq index_make_eq index_update_eq : rew_array.

Hint Extern 1 (@index _ _ _ _ _) => rew_array; math.

(* Another rewrite database for index *)

Hint Rewrite
     index_eq_index_length
     index_make_eq
     index_update_eq
     index_map_eq
     int_index_eq
  : rew_index.

Hint Rewrite
     length_cons
     length_make
     length_map
     length_app
  : rew_index.

Tactic Notation "rew_index" :=
  autorewrite with rew_index.
Tactic Notation "rew_index" "in" hyp(H) :=
  autorewrite with rew_index in H.
Tactic Notation "rew_index" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_index).
(* autorewrite with rew_index in *. *)
Tactic Notation "rew_index" "~" :=
  rew_index; auto_tilde.
Tactic Notation "rew_index" "*" :=
  rew_index; auto_star.
Tactic Notation "rew_index" "~" "in" hyp(H) :=
  rew_index in H; auto_tilde.
Tactic Notation "rew_index" "*" "in" hyp(H) :=
  rew_index in H; auto_star.
Tactic Notation "rew_index" "~" "in" "*" :=
  rew_index in *; auto_tilde.
Tactic Notation "rew_index" "*" "in" "*" :=
  rew_index in *; auto_star.

Lemma index_app_l : forall A (l l':list A) (i:int),
  index l i ->
  index (l++l') i.
Proof. intros; rew_index in *; math. Qed.

Lemma index_app_r : forall A (l l':list A) (j:int),
  index l' (j - length l) ->
  j >= length l ->
  index (l++l') j.
Proof. intros; rew_index in *; math. Qed.

Lemma index_rev_eq : forall A (l:list A) (i:int),
  index (rev l) i = index l i.
Proof.
  extens. intros.
  now rewrite index_eq_index_length, length_rev, index_eq_index_length.
Qed.

Lemma index_app_eq : forall A (l l':list A) (i:int),
  index (l++l') i = (If i < length l then index l i else index l' (i - length l)).
Proof.
  intros; extens.
  case_if; rew_index; math.
Qed.

Hint Rewrite index_rev_eq index_app_eq : rew_index.

Ltac index_prove tt := rew_index; repeat case_if; rew_list in *; math.

Module IndexHints.
Hint Extern 1 (index _ _) => index_prove tt.
End IndexHints.

(* A tactic to rewrite lists with reads *)

Hint Rewrite read_cons_case read_update_case : rew_list_cases.
Tactic Notation "rew_list_cases" :=
  autorewrite with rew_list_cases.
Tactic Notation "rew_list_cases" "*" := rew_list_cases; auto_star.

Tactic Notation "rew_list_cases" "in" "*"  :=
  (* TODO: why not? autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_list). *)
  autorewrite with rew_list_cases in *.
Tactic Notation "rew_list_cases" "*" "in" "*"  := rew_list_cases in *; auto_star.

Ltac list_cases_post tt :=
  repeat case_if; try math.

Tactic Notation "list_cases" :=
  rew_list_cases; list_cases_post tt.
Tactic Notation "list_cases" "*"  :=
  list_cases; auto_star.

Tactic Notation "list_cases" "in" "*"  :=
  rew_list_cases in *; list_cases_post tt.
Tactic Notation "list_cases" "*" "in" "*"  :=
  list_cases in *; auto_star.

(*--------------------------------------------------------*)
(* LibEqual *)

Definition rewrite_type (A B:Type) (E:A=B) (V:A) : B :=
  eq_rect A (fun T => T) V B E.

Lemma rewrite_type_self : forall A (E:A=A) (V:A),
  rewrite_type E V = V.
Proof using. intros. unfold rewrite_type. rewrite* eq_rect_refl_eq. Qed.
