(**

Foundations of Separation Logic

Chapter: "Lift".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

(*

This chapter describes the "lifting" technique that enables smoother
specification in a Separation Logic (shallowly) embeded in the proof
assistant logic. The idea is to relate program values with corresponding
logical values, e.g. a program boolean with a logical boolean.
This relation is exploited to more concisely specify return values and
values that are stored in the heap.

*)



(* ####################################################### *)
(** * Lifting (will be later in [SLFLift] *)

Module Lift.


(* ******************************************************* *)
(** ** Motivation *)

(** Compare these two specifications for the function [ref]:

[[
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (p:loc), \[r = val_loc p] \* p ~~~> v).

  Triple (val_ref v)
    \[]
    (fun (p:loc) => p ~~> v).
]]

  Clearly, the second one is desirable. Let's see how to derive it.
*)


(* ******************************************************* *)
(** ** The encoder typeclass *)

(** [Enc A] holds if the Coq type [A] matches a data type from
    the imperative programming language embedded in Coq.

    [enc V] encodes a value [V] of type [A] to a value of type [val]. *)

Class Enc (A:Type) : Type :=
  make_Enc { enc : A -> val }.

(** Notation [``V] for [enc V] *)

Notation "`` V" := (enc V) (at level 8, format "`` V").

(** Example instances *)

Instance Enc_int : Enc int.
Proof using. constructor. applys val_int. Defined.

Instance Enc_unit : Enc unit.
Proof using. constructor. intros. applys val_unit. Defined.

Instance Enc_loc : Enc loc.
Proof using. constructor. applys val_loc. Defined.

Instance Enc_list : forall `{Enc A}, Enc (list A).
Proof using. Abort. (* details omitted *)


(* ******************************************************* *)
(** ** Lifted singleton heap predicate *)

(** Recall definition of [hsingle], written [l ~~~> v]. *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single l v).

(** Singleton: [l ~~> V] describes a singleton heap at location [l]
    whose contents is the encoding of [V]. *)

Definition Hsingle `{EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '~~>' V" := (l ~> Hsingle V)
  (at level 32, no associativity) : heap_scope.


(* ******************************************************* *)
(** ** Lifted triples and rules *)

(** [Triple t H Q] describes a triple where the postcondition [Q] has
    type [A->hprop] for some encodable type [A].

    [Triple t H Q] captures the fact that [t] evaluates to a value [v]
    which is the encoding of a value [V] for which the postcondition
    [Q] holds. *)

Definition Triple (t:trm) `{EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (fun v => \exists V, \[v = enc V] \* Q V).

(** Lifted rule for [ref] *)

Parameter Triple_ref : forall A `{EA:Enc A} (V:A),
  Triple (val_ref ``V)
    \[]
    (fun (p:loc) => p ~~> V).

(** Lifted rule for sequence: [Q1] now has type [unit->hprop] *)

Parameter Triple_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.

(** Lifted rule for let bindings: [Q1] now has type [A1->hprop]
    for some encodable type [A1] *)

Parameter Triple_let : forall z t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (subst z (enc X) t2) (Q1 X) Q) ->
  Triple (trm_let z t1 t2) H Q.


(* ******************************************************* *)
(** ** Lifted characteristic formulae *)

(** Type of a lifted formula *)

Definition Formula := forall A (EA:Enc A), (A -> hprop) -> hprop.

(** Notation [^F Q] as a shorthand for [F _ _ Q], which is same as
    [F A EA Q] where [Q] has type [A->hprop] and [EA:Enc A]. *)

Notation "^ F Q" := ((F:Formula) _ _ Q)
  (at level 45, F at level 0, Q at level 0, format "^ F  Q").

(** The [MkStruct] predicate lifts [mkstruct]. *)

Definition MkStruct (F:Formula) : Formula :=
  fun A `{EA:Enc A} Q => \exists Q', ^F Q' \* (Q' \--* Q).

(** Lifted characteristic formula generator *)

Definition Wpgen_seq (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wpgen_let (F1:Formula) (F2of:forall `{EA1:Enc A1}, A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1), ^F1 (fun (X:A1) => ^(F2of X) Q)).

(*
[[
Fixpoint Wpgen (E:ctx) (t:trm) : Formula :=
  MkStruct
  match t with
  ..
  | trm_seq t1 t2 => Wpgen_seq (Wpgen E t1) (Wpgen E t2)
  | trm_let x t1 t2 => Wpgen_let (Wpgen E t1) (fun A (EA:Enc A) (X:A) =>
                         Wpgen ((x, enc X)::E) t2)
  ...
  end
]]
*)

Parameter Wpgen : forall (E:ctx) (t:trm), Formula.

(** Soundness theorem *)

Parameter Triple_of_Wpgen : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen nil t) Q ->
  Triple t H Q.

End Lift.




*)


(* ============================
(* summary *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Lifting (will be later in [SLFLift] *)

Module Lift.


(* ########################################################### *)
(** ** Motivation *)

(** Compare these two specifications for the function [ref]:

[[
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (p:loc), \[r = val_loc p] \* p ~~> v).

  Triple (val_ref v)
    \[]
    (fun (p:loc) => p ~~> v).
]]

  Clearly, the second one is desirable. Let's see how to derive it.
*)


(* ########################################################### *)
(** ** The encoder typeclass *)

(** [Enc A] holds if the Coq type [A] matches a data type from
    the imperative programming language embedded in Coq.

    [enc V] encodes a value [V] of type [A] to a value of type [val]. *)

Class Enc (A:Type) : Type :=
  make_Enc { enc : A -> val }.

(** Notation [``V] for [enc V] *)

Notation "`` V" := (enc V) (at level 8, format "`` V").

(** Example instances *)

Instance Enc_int : Enc int.
Proof using. constructor. applys val_int. Defined.

Instance Enc_unit : Enc unit.
Proof using. constructor. intros. applys val_unit. Defined.

Instance Enc_loc : Enc loc.
Proof using. constructor. applys val_loc. Defined.

Instance Enc_list : forall `{Enc A}, Enc (list A).
Proof using. Abort. (* details omitted *)


(* ########################################################### *)
(** ** Lifted singleton heap predicate *)

(** Recall definition of [hsingle], written [l ~~> v]. *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single l v).

(** Singleton: [l ~~> V] describes a singleton heap at location [l]
    whose contents is the encoding of [V]. *)

Definition Hsingle `{EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '`~~>' V" := (l ~> Hsingle V)
  (at level 32, no associativity) : heap_scope.


(* ########################################################### *)
(** ** Lifted triples and rules *)

(** [Triple t H Q] describes a triple where the postcondition [Q] has
    type [A->hprop] for some encodable type [A].

    [Triple t H Q] captures the fact that [t] evaluates to a value [v]
    which is the encoding of a value [V] for which the postcondition
    [Q] holds. *)

Definition Triple (t:trm) `{EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (fun v => \exists V, \[v = enc V] \* Q V).

(** Lifted rule for [ref] *)

Parameter Triple_ref : forall A `{EA:Enc A} (V:A),
  Triple (val_ref ``V)
    \[]
    (fun (p:loc) => p `~~> V).

(** Lifted rule for sequence: [Q1] now has type [unit->hprop] *)

Parameter Triple_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.

(** Lifted rule for let bindings: [Q1] now has type [A1->hprop]
    for some encodable type [A1] *)

Parameter Triple_let : forall x t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (subst x (enc X) t2) (Q1 X) Q) ->
  Triple (trm_let x t1 t2) H Q.


(* ########################################################### *)
(** ** Lifted characteristic formulae *)

(** Type of a lifted formula *)

Definition Formula := forall A (EA:Enc A), (A -> hprop) -> hprop.

(** Notation [^F Q] as a shorthand for [F _ _ Q], which is same as
    [F A EA Q] where [Q] has type [A->hprop] and [EA:Enc A]. *)

Notation "^ F Q" := ((F:Formula) _ _ Q)
  (at level 45, F at level 0, Q at level 0, format "^ F  Q").

(** The [MkStruct] predicate lifts [mkstruct]. *)

Definition MkStruct (F:Formula) : Formula :=
  fun A (EA:Enc A) (Q:A->hprop) => \exists Q', ^F Q' \* (Q' \--* Q).

(** Lifted characteristic formula generator *)

Definition Wpgen_seq (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wpgen_let (F1:Formula) (F2of:forall `{EA1:Enc A1}, A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1), ^F1 (fun (X:A1) => ^(F2of X) Q)).

(*
[[
Fixpoint Wpgen (E:ctx) (t:trm) : Formula :=
  MkStruct
  match t with
  ..
  | trm_seq t1 t2 => Wpgen_seq (Wpgen E t1) (Wpgen E t2)
  | trm_let x t1 t2 => Wpgen_let (Wpgen E t1) (fun A (EA:Enc A) (X:A) =>
                         Wpgen ((x, enc X)::E) t2)
  ...
  end
]]
*)

Parameter Wpgen : forall (E:ctx) (t:trm), Formula.

(** Soundness theorem *)

Parameter Triple_of_Wpgen : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen nil t) Q ->
  Triple t H Q.

End Lift.


*)