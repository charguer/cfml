Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib.
From CFML Require Import WPRecord.
Open Scope cf_scope.
Open Scope record_scope.
(*From CFML Require Import WPDisplay WPRecord.
Open Scope cf_scope.
Open Scope record_scope.*)

From TLC Require Import LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

Require Import View_ml.


(* ******************************************************* *)
Definition vcons A (v: view_) (x: A) (L: list A) :=
	match v with
	|	Front => x :: L
	|	Back => L & x
	end.

Definition vapp A (v: view_) (L1 L2: list A) :=
	match v with
	|	Front => L1 ++ L2
	|	Back => L2 ++ L1
	end.
