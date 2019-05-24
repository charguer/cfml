(**

Separation Logic Foundations

Chapter: "Extra".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFHprop.
From Sep Require SLFDirect.

(** Implicit Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * Separation Logic Triples *)

(** The type [heap], a.k.a. [state]. By convention, the "state"
    refers to the full memory state, while the "heap" potentially
    refers to only a fraction of the memory state. *)


Definition state : Type := heap.

(* ******************************************************* *)
(** ** Structural rules *)

(* ******************************************************* *)
(** ** Rules for terms *)

(* ******************************************************* *)
(** ** Rules for primitives *)


(* ####################################################### *)
(** * Others *)

(* ******************************************************* *)
(** ** Conjunction and disjunction operators *)
