(**

This file provides functions and their proofs for common operations
(using weakest-precondition based proofs, in lifted Separation Logic).

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export WPRecord.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* ---------------------------------------------------------------------- *)
(** Increment function *)

Definition val_incr : val :=
  VFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xappn~.
Qed.

Hint Extern 1 (Register_Spec val_incr) => Provide Triple_incr.


(* ---------------------------------------------------------------------- *)
(** Decrement function *)

Definition val_decr : val :=
  VFun 'p :=
   'p ':= ((val_get 'p) '- 1).

Lemma Triple_decr : forall (p:loc) (n:int),
  TRIPLE (val_decr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n-1))).
Proof using.
  xwp. xappn~.
Qed.

Hint Extern 1 (Register_Spec val_decr) => Provide Triple_decr.

