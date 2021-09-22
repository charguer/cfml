Set Implicit Arguments.
From TLC Require Import LibInt LibString.
From CFML Require Import Semantics.
Generalizable Variables A.


(********************************************************************)
(* Builtin types *)

(* If LibInt is not opened, then use:
  Require Coq.ZArith.BinInt.
  Local Notation "'int'" := (Coq.ZArith.BinInt.Z).
*)

Definition char := Ascii.ascii.

Definition array (A:Type) := loc. (* TODO: deprecate *)

Hint Transparent array : haffine.

(** Carried type for function closures *)

Definition func : Type := val.



(********************************************************************)
(* Polymorphic comparison *)

(* Axiomatization of polymorphic equality *)

Axiom polymorphic_eq_arg : forall (A:Type), A -> Prop.

(** Values that support polymorphic comparison *)

Axiom polymorphic_eq_arg_unit : forall (v:unit),
  polymorphic_eq_arg v.
Axiom polymorphic_eq_arg_int : forall (n:int),
  polymorphic_eq_arg n.
Axiom polymorphic_eq_arg_bool : forall (b:bool),
  polymorphic_eq_arg b.
Axiom polymorphic_eq_arg_char : forall (c:char),
  polymorphic_eq_arg c.
Axiom polymorphic_eq_arg_string : forall (s:string),
  polymorphic_eq_arg s.

Axiom polymorphic_eq_arg_none : forall A,
  polymorphic_eq_arg (@None A).
Axiom polymorphic_eq_arg_some : forall A (v:A),
  polymorphic_eq_arg v ->
  polymorphic_eq_arg (Some v).
Axiom polymorphic_eq_arg_nil : forall A,
  polymorphic_eq_arg (@nil A).
Axiom polymorphic_eq_arg_cons : forall A (v:A) (l:list A),
  polymorphic_eq_arg v ->
  polymorphic_eq_arg l ->
  polymorphic_eq_arg (v::l).

Axiom polymorphic_eq_arg_tuple_2 :
  forall A1 A2 (v1:A1) (v2:A2),
  polymorphic_eq_arg v1 ->
  polymorphic_eq_arg v2 ->
  polymorphic_eq_arg (v1,v2).
Axiom polymorphic_eq_arg_tuple_3 :
  forall A1 A2 A3 (v1:A1) (v2:A2) (v3:A3),
  polymorphic_eq_arg v1 ->
  polymorphic_eq_arg v2 ->
  polymorphic_eq_arg v3 ->
  polymorphic_eq_arg (v1,v2,v3).
Axiom polymorphic_eq_arg_tuple_4 :
  forall A1 A2 A3 A4 (v1:A1) (v2:A2) (v3:A3) (v4:A4),
  polymorphic_eq_arg v1 ->
  polymorphic_eq_arg v2 ->
  polymorphic_eq_arg v3 ->
  polymorphic_eq_arg v4 ->
  polymorphic_eq_arg (v1,v2,v3,v4).
Axiom polymorphic_eq_arg_tuple_5 :
  forall A1 A2 A3 A4 A5 (v1:A1) (v2:A2) (v3:A3) (v4:A4) (v5:A5),
  polymorphic_eq_arg v1 ->
  polymorphic_eq_arg v2 ->
  polymorphic_eq_arg v3 ->
  polymorphic_eq_arg v4 ->
  polymorphic_eq_arg v5 ->
  polymorphic_eq_arg (v1,v2,v3,v4,v5).

Hint Resolve
  polymorphic_eq_arg_unit
  polymorphic_eq_arg_int
  polymorphic_eq_arg_bool
  polymorphic_eq_arg_char
  polymorphic_eq_arg_string
  polymorphic_eq_arg_none
  polymorphic_eq_arg_some
  polymorphic_eq_arg_nil
  polymorphic_eq_arg_cons
  polymorphic_eq_arg_tuple_2
  polymorphic_eq_arg_tuple_3
  polymorphic_eq_arg_tuple_4
  polymorphic_eq_arg_tuple_5
  : polymorphic_eq.

(* LATER: study the link with Comparable typeclass *)


(********************************************************************)
(* FUTURE USE

Class PolyComparableType (A:Type) : Prop :=
  { polyComparableType : forall (v:A), polymorphic_eq_arg v }.

Lemma PolyComparableType_eq : forall (A:Type),
  PolyComparableType A = (forall (v:A), PolyComparable v).
Proof using.
  intros. extens. iff H.
  { intros. constructors. applys H. }
  { constructors. intros. applys H. }
Qed.

Lemma PolyComparableType_elim : forall `{PolyComparableType A} (v:A),
  PolyComparable v.
Proof using. introv. rewrite PolyComparableType_eq. typeclass. Qed.
(* DO NOT add this lemmas as instance, it makes everything slow. *)

Global Instance polymorphic_eq_arg_type_unit :
  PolyComparableType unit.
Proof using. rewrite PolyComparableType_eq. typeclass. Qed.

Global Instance polymorphic_eq_arg_type_int :
  PolyComparableType int.
Proof using. rewrite PolyComparableType_eq. typeclass. Qed.

Global Instance polymorphic_eq_arg_type_bool :
   PolyComparableType bool.
Proof using. rewrite PolyComparableType_eq. typeclass. Qed.

Global Instance polymorphic_eq_arg_type_char :
   PolyComparableType char.
Proof using. rewrite PolyComparableType_eq. typeclass. Qed.

Global Instance polymorphic_eq_arg_type_string :
   PolyComparableType string.
Proof using. rewrite PolyComparableType_eq. typeclass. Qed.

Global Instance polymorphic_eq_arg_type_option : forall `{PolyComparableType A},
  PolyComparableType (option A).
Proof using.
  introv. do 2 rewrite PolyComparableType_eq. intros.
  destruct v; typeclass.
Qed.
Global Instance polymorphic_eq_arg_type_list : forall `{PolyComparableType A},
  PolyComparableType (list A).
Proof using.
  introv. do 2 rewrite PolyComparableType_eq. intros H l.
  induction l; typeclass.
Qed.

Global Instance polymorphic_eq_arg_type_tuple_2 :
  forall `{PolyComparableType A1} `{PolyComparableType A2},
  PolyComparableType (A1 * A2)%type.
Proof using.
  intros. rewrite PolyComparableType_eq in *.
  intros (v1&v2). typeclass.
Qed.
Global Instance polymorphic_eq_arg_type_tuple_3 :
  forall `{PolyComparableType A1} `{PolyComparableType A2} `{PolyComparableType A3},
  PolyComparableType (A1 * A2 * A3)%type.
Proof using.
  intros. rewrite PolyComparableType_eq in *.
  intros [[v1 v2] v3]. typeclass.
Qed.
Global Instance polymorphic_eq_arg_type_tuple_4 :
  forall `{PolyComparableType A1} `{PolyComparableType A2} `{PolyComparableType A3}
         `{PolyComparableType A4},
  PolyComparableType (A1 * A2 * A3 * A4)%type.
Proof using.
  intros. rewrite PolyComparableType_eq in *.
  intros [[[v1 v2] v3] v4]. typeclass.
Qed.
Global Instance polymorphic_eq_arg_type_tuple_5 :
  forall `{PolyComparableType A1} `{PolyComparableType A2} `{PolyComparableType A3}
         `{PolyComparableType A4} `{PolyComparableType A5},
  PolyComparableType (A1 * A2 * A3 * A4 * A5)%type.
Proof using.
  intros. rewrite PolyComparableType_eq in *.
  intros [[[[v1 v2] v3] v4] v5]. typeclass.
Qed.

*)


(********************************************************************)
(* Direct functions to map inlined primitives from Pervasives,
   that are not already mapped to existing Coq constants.
   (see inlined_primitives_table in renaming.ml) *)

(** Pred / Succ *)

Definition pred (n:int) := (Coq.ZArith.BinInt.Z.sub n 1).

Definition succ (n:int) := (Coq.ZArith.BinInt.Z.add n 1).

(** Ignore *)

Definition ignore A (x:A) := tt.


(********************************************************************)
(* Preventing simplifications -- TODO: still needed? *)

Global Opaque
  Coq.ZArith.BinInt.Z.add
  Coq.ZArith.BinInt.Z.sub
  Coq.ZArith.BinInt.Z.mul
  Coq.ZArith.BinInt.Z.opp.

Global Transparent Coq.ZArith.BinInt.Z.sub.



