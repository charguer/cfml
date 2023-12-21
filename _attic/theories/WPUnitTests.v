(**

This file provides functions and their proofs for common operations
(using weakest-precondition based proofs, in lifted Separation Logic).

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From Sep Require Export Example.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.



(* ******************************************************* *)
(** ** Troubleshooting *)

Module Troubleshooting.

Definition incr_two : val :=
  Fun 'p 'q :=
    incr 'p ';
    incr 'q.

Lemma Triple_error_in_number_of_arguments : forall (p q:loc) (n m:int),
  TRIPLE (incr_two p) (* missing argument [q] *)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:int) => p ~~> (n+1) \* q ~~> (m+1)).
Proof using.
  intros. try xwp.
  (* [xwp] fails because the number of arguments does not match. *)
  (* [xwp_debug] would diagnose this isssue. *)
Abort.

Lemma Triple_term_among_arguments : forall (p q:loc) (n m:int) x (* with not type annotation for [x] *),
  TRIPLE (incr_two p x) (* [x] instead of [q] *)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:int) => p ~~> (n+1) \* q ~~> (m+1)).
Proof using.
  intros. try xwp.
  (* [xwp] fails because in [incr_two p x] the argument [x] has type [trm], whereas it should be a value. *)
  (* [xwp_debug] would diagnose this isssue. *)
Abort.

Lemma Triple_incorret_result_type : forall (p q:loc) (n m:int),
  TRIPLE (incr_two p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:int) => p ~~> (n+1) \* q ~~> (m+1)).
Proof using.
  xwp. xapp. try xapp.
  (* [xapp] fails because the result type of [incr q] is of type [unit]
     while the postcondition claims a result of type [int]. *)
  (* [xapp_debug] would help diagnose this isssue. *)
Abort.

Definition incr_get_error : val :=
  Fun 'p :=
    Let 'x := '! 'p in
    incr 'x '; (* ['x] instead of ['p] *)
    'x.

Lemma Triple_incorrect_argument_type : forall (p:loc) (n:int),
  TRIPLE (incr_get_error p)
    PRE (p ~~> n)
    POST (fun (r:int) => \[r = n] \* p ~~> (n+1)).
Proof using.
  intros. xwp. xapp. try xapp.
  (* [xapp] fails because the call to [incr x] has argument [x] of type [int]
     instead of an argument of type [loc] as expected by [incr]. *)
  (* [xapp_debug] would help diagnose this isssue. *)
Abort.

Definition call_incr_get_error : val :=
  Fun 'p :=
    incr_get_error 'p.

Lemma Triple_unregistered_specification : forall (p:loc) (n:int),
  TRIPLE (call_incr_get_error p)
    PRE (p ~~> n)
    POST (fun (r:int) => \[r = n] \* p ~~> (n+1)).
Proof using.
  intros. xwp. try xapp.
  (* [xapp_debug] would diagnose this isssue. *)
Abort.

End Troubleshooting.