(** * Meta-theory about Omni-small-step semantics *)

Set Implicit Arguments.


From TLC Require Import LibString LibList LibCore LibInt.

Section Simulation_diagram.

  Variable Cs: Type.            (* source configurations *)
  Variable Ct: Type.            (* target configurations *)

  Notation post_s := (Cs -> Prop). (* source postcondition *)
  Notation post_t := (Ct -> Prop). (* target postcondition *)

  Variable omnismall_s: Cs -> post_s -> Prop. (* source omni *)
  Variable omnismall_t: Ct -> post_t -> Prop. (* target omni *)

  Variable R : Cs -> Ct -> Prop.     (* Simulation relation *)

  (* Relation lifted to postconditions *)
  Definition lift_R (R : Cs -> Ct -> Prop) : post_s -> post_t -> Prop :=
    fun Ps Pt => forall t, Pt t -> exists s, Ps s /\ R s t.

  (* eventually of an omnismall judgement *)
  Inductive eventually {A : Type} (step : A -> (A -> Prop) -> Prop) : A -> (A -> Prop) -> Prop :=
  | eventually_here : forall (a : A) (P : A -> Prop),
      P a ->
      eventually step a P
  | eventually_step : forall (a : A) (P' P : A -> Prop),
      step a P' ->
      (forall (a' : A), P' a' -> eventually step a' P) ->
      eventually step a P.


  Implicit Type s : Cs.
  Implicit Type t : Ct.
  Implicit Type Ps : post_s.
  Implicit Type Pt : post_t.

  Hypothesis diagram : forall s Ps t,
      omnismall_s s Ps ->
      R s t ->
      exists Pt, eventually omnismall_t t Pt /\ lift_R R Ps Pt.

  Lemma stitch_source : forall s Ps t,
      eventually omnismall_s s Ps ->
      R s t ->
      exists Pt, eventually omnismall_t t Pt /\ lift_R R Ps Pt.
  Proof.
    introv step inv.

End Simulation_diagram.
