(**

Separation Logic Foundations

Chapter: "Direct".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFHprop.
From Sep Require Var Fmap Hsimpl.

(** Implicit Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * Imports *)

(* ******************************************************* *)
(** ** Extensionality axioms *)

Module Assumptions.

(** The file [LibAxioms] from the TLC library includes the axioms of
    functional extensionality and propositional extensionality.
    These axioms are essential to proving equalities between
    heap predicates, and between postconditions. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

End Assumptions.


(* ******************************************************* *)
(** ** Variables *)

(** The file [Var.v] defines the type [var] as an alias for [string].

    It provides the boolean function [var_eq x y] to compare two variables.

    It provides the tactic [case_var] to perform case analysis on 
    expressions of the form [if var_eq x y then .. else ..] 
    that appear in the goal. *)


(* ******************************************************* *)
(** ** Finite maps *)

(** The file [Fmap.v] provides a formalization of finite maps, which
    are then used to represent heaps in the semantics.

    The implementation details need not be revealed. 
  
    Finiteness of maps is essential because to justify that allocation
    yields a fresh reference, one must be able to argue for the 
    existence of a location fresh from existing heaps. From the 
    finiteness of heaps and the infinite number of variables, we
    can conclude that fresh locations always exist. 
    
    The library [Fmap.v] provides the basic operations of finite maps,
    and in particular the definition of disjointness.

    It provides a tactic [fmap_disjoint] to automate the disjointness proofs,
    and a tactic [fmap_eq] to prove equalities between heaps modulo
    associativity and commutativity. Without these two tactics, the 
    proofs would be extremely tedious and fragile. *)



(* ####################################################### *)
(** * Source language *)

(* ******************************************************* *)
(** ** Syntax *)

(* ******************************************************* *)
(** ** Substitution *)

(* ******************************************************* *)
(** ** Semantics *)

(* ******************************************************* *)
(** ** Coercions *)

(* ******************************************************* *)
(** ** Notations *)


(* ####################################################### *)
(** * Heap predicates *)

(* ******************************************************* *)
(** ** Definitions *)

(* ******************************************************* *)
(** ** Basic properties *)

(* ******************************************************* *)
(** ** Hsimpl tactic *)


(* ####################################################### *)
(** * Reasoning rules *)

(* ******************************************************* *)
(** ** Hoare reasoning rules *)

(* ******************************************************* *)
(** ** Definition of WP and SL triple *)

(* ******************************************************* *)
(** ** WP-style structural properties *)

(* ******************************************************* *)
(** ** WP-style reasoning rules for terms *)

(* ******************************************************* *)
(** ** Specification for primitive functions *)

(* ******************************************************* *)
(** ** WP reasoning rules *)


(* ####################################################### *)
(** * WP generator *)

(* ******************************************************* *)
(** ** Definition *)

(* ******************************************************* *)
(** ** Soundness *)

(* ******************************************************* *)
(** ** Notations *)

(* ******************************************************* *)
(** ** Tactics *)

(* ******************************************************* *)
(** ** Example proof *)
