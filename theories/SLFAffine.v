(**

Separation Logic Foundations

Chapter: "Affine".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFDirect.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter introduces the notion of weakest precondition
    for Separation Logic triples. *)


(* ******************************************************* *)
(** ** Notion of weakest precondition *)


