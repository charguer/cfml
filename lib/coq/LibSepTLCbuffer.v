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

