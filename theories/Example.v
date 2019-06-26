(**

This file contains common declarations for examples in CFML 2.0.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
Generalizable Variables A B.

From TLC Require Import LibCore.
From Sep Require Export WPLib.

Export NotationForVariables NotationForTerms.
Open Scope liblist_scope.
Open Scope Z_scope.
Open Scope comp_scope.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(** Common preambule to be copied:

Set Implicit Arguments.
Generalizable Variables A B.

*)

(** Optional type declarations, e.g.:

Implicit Types p : loc.
Implicit Types n : int.

*)

(** Configuration of automation *)

Ltac auto_false_base cont ::=
  try solve [
    intros_all; try match goal with |- _ <-> _ => split end;
    solve [ cont tt
          | intros_all; false;
            solve [ try match goal with H: context [ _ <> _ ] |- _ => applys H; reflexivity end
                  | cont tt ] ] ].

Ltac auto_star ::=
  try solve [ intuition eauto
            | subst; rew_list in *; 
              solve [ math 
                    | auto_false_base ltac:(fun tt => intuition eauto) ] ].


(* LATER: move to TLC *)

Definition max (n m:int) : int := 
  If n > m then n else m.

Lemma max_nonpos : forall n,
  n <= 0 ->
  max 0 n = 0.
Proof using. introv M. unfold max. case_if; math. Qed.

Lemma max_nonneg : forall n,
  n >= 0 ->
  max 0 n = n.
Proof using. introv M. unfold max. case_if; math. Qed.
