(** * Meta-theory about Omni-small-step semantics *)

Set Implicit Arguments.


From TLC Require Import LibString LibList LibCore LibInt.

Section Simulation_diagram.

  Variable Cs: Type.            (* source configurations *)
  Variable Ct: Type.            (* target configurations *)

  Definition post_s : Type := (Cs -> Prop). (* source postcondition *)
  Definition post_t : Type := (Ct -> Prop). (* target postcondition *)

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


  Lemma eventually_cut {A : Type} :
    forall (R : A -> (A -> Prop) -> Prop) a P' P,
      eventually R a P' ->
      (forall a', P' a' -> eventually R a' P) ->
      eventually R a P.
  Proof using.
    introv Hstep Hrest. induction Hstep.
    - applys Hrest H.
    - eapply eventually_step. apply H.
      intros. now apply H1.
  Qed.


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
  Proof using diagram.
    introv step. revert t. induction step; introv inv.
    - exists (fun (t' : Ct) => exists s', P s' /\ R s' t'). split.
      + apply eventually_here; eauto.
      + unfold lift_R. tauto.
    - set (Pt := fun t => exists Pt'', Pt'' t /\ lift_R R P Pt'').
      exists Pt. split.
      + destruct (@diagram a P' t H inv) as (Pt'&diag_step&diag_R).
        apply eventually_cut with Pt'.
        * apply diag_step.
        * intros t' Ht'. unfold lift_R in diag_R.
          destruct (diag_R t' Ht') as (s' & Hs' & Hs'R).
          destruct (H1 s' Hs' t' Hs'R) as (Pt'' & HevPt'' & HRPt'').
          unfold Pt.
          apply eventually_cut with Pt''; auto.
          intros. apply eventually_here; eauto.
      + intro t'. unfold Pt. intros (Pt''&Ht'&HR).
        destruct (HR t' Ht') as (s'&Hs'); eauto.
  Qed.

  Variable tradsmall_s: Cs -> Cs -> Prop.
  Variable tradsmall_t: Ct -> Ct -> Prop.

  Hypothesis lock_diagram : forall s t Ps,
      omnismall_s s Ps ->
      R s t ->
      exists Pt, omnismall_t t Pt /\ lift_R R Ps Pt.

  Hypothesis os_iff_prog_and_correct_s : forall s Ps,
      (omnismall_s s Ps) <->
        (exists s', tradsmall_s s s')
        /\ (forall s', tradsmall_s s s' -> Ps s').

  Hypothesis os_iff_prog_and_correct_t : forall t Pt,
      (omnismall_t t Pt) <->
        (exists t', tradsmall_t t t')
        /\ (forall t', tradsmall_t t t' -> Pt t').

  (** Assuming *)
  Lemma forward_implies_trad_backwards : forall s Ps t,
      (exists s', tradsmall_s s s') ->
      R s t ->
      (exists t', tradsmall_t t t')
      /\ (forall t', tradsmall_t t t' -> exists s', tradsmall_s s s' /\ R s' t').
  Proof using lock_diagram os_iff_prog_and_correct_s os_iff_prog_and_correct_t.
    intros s Ps t progress_s inv.
    setoid_rewrite os_iff_prog_and_correct_s in lock_diagram.
    setoid_rewrite os_iff_prog_and_correct_t in lock_diagram.
    forwards * : lock_diagram s t (fun s' => tradsmall_s s s'). firstorder.
  Qed.


End Simulation_diagram.
