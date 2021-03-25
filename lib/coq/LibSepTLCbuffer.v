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
From TLC Require Import LibTactics.
From TLC Require Import LibInt LibLogic.
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


(*--------------------------------------------------------*)
(* LibEqual *)

Definition rewrite_type (A B:Type) (E:A=B) (V:A) : B :=
  eq_rect A (fun T => T) V B E.

Lemma rewrite_type_self : forall A (E:A=A) (V:A),
  rewrite_type E V = V.
Proof using. intros. unfold rewrite_type. rewrite* eq_rect_refl_eq. Qed.

