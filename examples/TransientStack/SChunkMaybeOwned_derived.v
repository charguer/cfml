Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup Array_proof List_proof.

From TLC Require Import LibListZ LibMap.

Require Import EChunk_ml EChunk_proof.

Require Import Id_ml Id_proof.

Require Import SChunk_ml.
Require Export SChunk_proof.
Require Export SChunkShared_derived.

(***************************************)
(** SChunkMaybeOwned *)

Hint Rewrite Forall_cons_eq Forall_nil_eq Forall2_cons_eq Forall2_nil_eq : rew_list.

Definition SChunkUniquelyOwned A {IA:Inhab A} {EA:Enc A} (L:list A) (s:schunk_ A) : hprop :=
  s ~> SChunk true L L.

Lemma SChunkUniquelyOwned_eq : forall A {IA:Inhab A} {EA:Enc A} (L:list A) (s:schunk_ A),
  s ~> SChunkUniquelyOwned L = s ~> SChunk true L L.
Proof. xsimpl*. Qed.

Definition SChunkMaybeOwned A {IA:Inhab A} {EA:Enc A}
           (M:Memory A) (id:option Id.t_) (L:list A) (s:schunk_ A) : hprop :=
  If s.(owner') = id /\ id <> None
  then s ~> SChunkUniquelyOwned L
  else \[SChunkShared M L s].

Lemma haffine_SChunkMaybeOwned : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) L o p,
  haffine (p ~> SChunkMaybeOwned M o L).
Proof.
  intros.
  xunfold SChunkMaybeOwned; xunfold SChunkUniquelyOwned; case_if; xaffine.
Qed.

Hint Resolve haffine_SChunkMaybeOwned : haffine.

Lemma haffine_repr_SChunkMaybeOwned : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) o,
  haffine_repr (SChunkMaybeOwned M o).
Proof. intros. intros ? ?. xaffine. Qed.

Hint Resolve haffine_repr_SChunkMaybeOwned : haffine.

Ltac xunfold_SChunkMaybeOwned :=
  xunfold SChunkMaybeOwned; repeat case_if*; try math.

Tactic Notation "xunfolds_SChunkMaybeOwned" :=
  xunfold_SChunkMaybeOwned; try xsimpl.

Tactic Notation "xunfolds_SChunkMaybeOwned" "*" :=
  xunfolds_SChunkMaybeOwned; auto_star.

Lemma SChunkMaybeOwned_notOwned : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) L o p,
  owner' p <> o ->
  p ~> SChunkMaybeOwned M o L = \[SChunkShared M L p].
Proof. intros. xunfold_SChunkMaybeOwned. false*. Qed.

Lemma SChunkMaybeOwned_Owned : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) L o p,
  owner' p = o ->
  o <> None ->
  p ~> SChunkMaybeOwned M o L = p ~> SChunk true L L.
Proof. intros. xunfold_SChunkMaybeOwned. false*. Qed.

(***************************************)
(** Monotony lemmas *)

(* SChunkMaybeOwned is monotonic w.r.t the Preserve order. *)
Lemma SChunkMaybeOwned_mon : forall A (IA:Inhab A) (EA:Enc A) (M M':Memory A) L o p,
  Extend M M' ->
  p ~> SChunkMaybeOwned M o L ==> p ~> SChunkMaybeOwned M' o L.
Proof.
  intros. xunfolds_SChunkMaybeOwned.
  intros. applys* SChunkShared_mon.
Qed.

Lemma SChunkMaybeOwned_list_mon : forall A (IA:Inhab A) (EA:Enc A) (M M':Memory A) (o:option Id.t_) (pt: list (schunk_ A)) (LS:list (list A)) ,
  Extend M M' ->
  pt ~> ListOf (SChunkMaybeOwned M o) LS ==> pt ~> ListOf (SChunkMaybeOwned M' o) LS.
Proof.
  induction pt; intros.
  { now destruct LS. }
  { destruct LS; try easy.
    xunfold ListOf.
    xchange* SChunkMaybeOwned_mon.
    xchanges* IHpt. }
Qed.

(***************************************)
(** Introduction lemmas *)

(* If we already share the ownership of a SChunk, it is maybe owned. *)
Lemma MaybeOwned_of_Shared : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (vo:option Id.t_) (L:list A) (p:schunk_ A),
  (owner' p) <> vo ->
  SChunkShared M L p ->
  \[] ==> p ~> SChunkMaybeOwned M vo L.
Proof.
  intros.
  xunfolds_SChunkMaybeOwned*; firstorder.
Qed.

Lemma MaybeOwned_of_Shared_list : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (vo:option Id.t_) (pt: list (schunk_ A)) (LS:list (list A)) ,
  Forall (fun p => p.(owner') <> vo) pt ->
  Forall2 (SChunkShared M) LS pt ->
  \[] ==> pt ~> ListOf (SChunkMaybeOwned M vo) LS.
Proof.
  induction pt.
  { intros.
    now destruct LS. }
  { intros LS H1 H2.
    destruct LS; try easy.
    rew_list in H1; rew_list in H2.
    xchange* IHpt.
    xunfold (ListOf (SChunkMaybeOwned M vo)); xsimpl.
    apply* MaybeOwned_of_Shared. }
Qed.

(* If we uniquely own a SChunk, we can share its ownership. *)
Lemma Shared_of_MaybeOwned : forall A (IA:Inhab A) (EA:Enc A) M v (p:schunk_ A) (L:list A),
  Shared M \* p ~> SChunkMaybeOwned M v L ==>
  \exists M', Shared M' \* \[Extend M M' /\ SChunkShared M' L p].
Proof.
  intros. destruct M as (M,I). unfold Shared. simpl.
  xunfold_SChunkMaybeOwned.
  { xunfold SChunkUniquelyOwned.
    xopen p; intros.
    xchange* (>> Group_add_fresh (support' p) M).
    intros.
    xsimpl* (mk_m M[support' p:=L] I).
    split*.
    { eauto with extend preserve. }
    { constructor*; simpl.
      { apply* indom_update_same. }
      { rew_map. applys* SChunk_inv_share. } } }
  { xsimpl*. split*.
    eauto with extend preserve. xsimpl*. }
Qed.

(* Important lemma: we can disown a list of schunk maybe owned. *)
Lemma Shared_of_MaybeOwned_list : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (v:option Id.t_) (pt:list (schunk_ A)) (LS:list (list A)),
  Shared M \* pt ~> ListOf (SChunkMaybeOwned M v) LS ==>
  \exists M', Shared M' \* \[Extend M M' /\ Forall2 (SChunkShared M') LS pt].
Proof.
  intros. revert M LS.
  induction pt; intros M L.
  { xchange ListOf_nil_r; intros ->.
    xsimpl. split.
    { apply Extend_refl. }
    { rew_list*. } }
  { xchange ListOf_cons_r; intros L1 L2 ->.
    xchange IHpt; intros M' [].
    xchange* (>> SChunkMaybeOwned_mon M M').
    xchange* (>> Shared_of_MaybeOwned M' a); intros M'' [HM''].
    lets [] : HM''.
    xsimpl*. split*.
    { apply* Extend_trans. }
    { rew_list*. split*.
      applys* Forall2_rel_le.
      apply* SChunkShared_rel_incl_Preserve. } }
Qed.

(***************************************)
(** Specifications *)

Lemma echunk_of_schunk_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (v:option Id.t_) s L,
  SPEC (echunk_of_schunk s)
    PRE (\$(K+2))
    INV (s ~> SChunkMaybeOwned M v L \* Shared M)
    POST (fun e => e ~> EChunk L).
Proof.
  xtriple.
  xunfold SChunkMaybeOwned.
  case_if.
  { xchange SChunkUniquelyOwned_eq.
    xapp SChunk_proof.echunk_of_schunk_spec.
    xgo*. }
  { xgo*. }
Qed.
