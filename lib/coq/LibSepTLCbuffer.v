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
(* LibListZ *)

From TLC Require Import LibListZ.

(* Hint *)

Hint Extern 1 (@index _ _ _ _ _) => rew_array; math.

(* A tactic to rewrite lists with reads
  ---- subsumed by a more powerful version implemented in the cfml-sek package *)

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


(* TODO Move to TLC *)
Lemma list_same_length_inv_nil : forall A1 A2 (l1:list A1) (l2:list A2),
  length l1 = length l2 ->
  l1 = nil <-> l2 = nil.
Proof using. intros. destruct l1; destruct l2; auto_false*. Qed.
