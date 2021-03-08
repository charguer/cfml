(**

This file provides functions and their proofs for common operations
(using weakest-precondition based proofs, in lifted Separation Logic).

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From Sep Require Export WPRecord WPArray.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* ---------------------------------------------------------------------- *)
(** Increment function *)

Definition incr : val :=
  Fun 'p :=
   'p ':= (('! 'p) '+ 1).

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xappn~. xsimpl.
Qed.

Hint Extern 1 (Register_Spec incr) => Provide Triple_incr.


(* ---------------------------------------------------------------------- *)
(** Decrement function *)

Definition decr : val :=
  Fun 'p :=
   'p ':= (('! 'p) '- 1).

Lemma Triple_decr : forall (p:loc) (n:int),
  TRIPLE (decr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n-1))).
Proof using.
  xwp. xappn~. xsimpl.
Qed.

Hint Extern 1 (Register_Spec decr) => Provide Triple_decr.


(* ---------------------------------------------------------------------- *)
(** List concatenation function *)

Definition list_concat : val :=
  Fix 'f 'l1 'l2 :=
   Match 'l1 With
   '| 'nil '=> 'l2
   '| 'x ':: 'r '=> 'x ':: ('f 'r 'l2)
   End.

Notation "t1 '++ t2" :=
  (list_concat t1 t2)
  (at level 58) : trm_scope.

Lemma Triple_list_concat : forall `{Enc A} (l1 l2:list A),
  TRIPLE (list_concat ``l1 ``l2)
    PRE \[]
    POST (fun r => \[r = l1 ++ l2]).
Proof using.
  intros. induction_wf IH: (@list_sub A) l1.
  xwp. applys xmatch_lemma_list.
  { intros ->. xvals~. }
  { intros x l1' ->. xapp~. xval (x::(l1'++l2)). xsimpl~. }
Qed.

Hint Extern 1 (Register_Spec (list_concat)) => Provide @Triple_list_concat.



