Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup List_proof.

From TLC Require Import LibMap LibList LibListZ.

Require Import Mono.

Require Import ListMisc.
Require Import Option_aux.

Require Import EChunk_ml EChunk_proof.

Require Import Id_ml Id_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml TranstackCommon.
Require Import TranstackEphemeral_aux TranstackPersistent_aux.

(* For focus *)
Require Import Iterator_tools.

(**************************************)
(** Conversions *)

Lemma pstack_to_estack_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (p:pstack_ A),
  PStack M L p ->
  SPEC (pstack_to_estack p)
    PRE (\$(2*K+7))
    INV (Shared M)
    POST (fun e => e ~> EStack M L).
Proof.
  intros A IA EA M L (pf,pt) (LF,(LS,Hp)); simpl in *.
  destruct Hp as [Hl Hpf Hv]. rew_list in Hpf. rew_list in Hv.
  destruct Hpf as (Hp,Hf).
  unfold TripleMon. xcf*. simpl. xpay.
  destruct M as [E I]; unfold Shared; simpl.
  xapp. intros ? ?. xchange <- (>> Shared_eq (mk_m E I)).
  xapp*. intros c. xapp. intros. simpl in *.
  xopen c; intros ? ? ? ? HLF.
  xclose* c.
  xsimpl*.
  xunfolds_estack; try easy; simpl.
  { constructor*; rew_set.
    { rew_list in *. applys* Forall_pred_incl.
      intros ? ?. now left. } }
  { xchanges* (>> MaybeOwned_of_Shared_list); simpl.
    { rewrite Forall_eq_forall_mem in *. intros s Hs.
      destruct Hv as [? HV]. intros Hos.
      lets ? : (HV s Hs). rewrite Hos in *. simpl in *. false*. }
    unfold potential_pop. destruct pt; try case_if*; destruct* HLF. }
Qed.

Hint Extern 1 (RegisterSpec pstack_to_estack) => Provide pstack_to_estack_spec.

Lemma estack_to_pstack_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (e:estack_ A),
  SPEC (estack_to_pstack e)
    MONO M
    PRE (\$2 \* e ~> EStack M L)
    POST (fun M' p => \[PStack M' L p]).
Proof.
  unfold TripleMon. xcf*. xpay.
  xopen_estack e; intros f t sc v LF LS Hs.
  lets [Hst Hv] : Hs.
  xappn*; intros p Hp; simpl in *.
  xappn. xval.
  xchange Shared_of_MaybeOwned_list; intros M' HM'.
  xopen p; intros Hp'.
  xchange echunk_inv_length. intros.
  destruct M' as (E,I). unfold Shared; simpl.
  xchange (>> Group_add_fresh v I tt). 1,2:typeclass. intros.
  xchange* (>> Group_add_fresh (support' p) LF). intros Hds.
  asserts ? : (Extend (mk_m E I) (mk_m E[support' p:=LF] I[v:=tt])).
  { split*; simpl.
    { apply* Preserve_add_fresh. }
    { simpl. rewrite dom_update. apply incl_union_l. rew_maps*. } }
  xsimpl* (mk_m E[support' p:=LF] I[v:=tt]).
  { applys* Extend_trans. }
  { destruct Hs.
    exists LF LS. constructor*; rew_list.
    { split. constructor*; simpl.
      { apply* indom_update_same. }
      { rew_map. applys* SChunk_inv_share. }
      { applys* Forall2_rel_le.
        intros ? ?. applys* SChunkShared_mon. } }
    { split*.
      { destruct* Hp as (->&?). subst. simpl.
        rewrite dom_update, in_union_eq.
        now right. }
      { applys* Forall_pred_incl. intros ? [|].
        do 2 applys* valid_id_mon.
        rewrite H1. simpl. rew_maps*. typeclass. } } }
  { simpl. unfold potential_pop.
    destruct sc,t; simpl; try case_if*; math. }
Qed.

Hint Extern 1 (RegisterSpec estack_to_pstack) => Provide estack_to_pstack_spec.

(* One K for the copy, the rest for potentials functions. *)
Lemma copy_with_sharing_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (e:estack_ A),
  SPEC (copy_with_sharing e)
    MONO M
    PRE (\$(3*K + 9) \* e ~> EStack M L)
    POST (fun M' e' => e' ~> EStack M' L \* e ~> EStack M' L).
Proof.
  unfold TripleMon. xcf*.
  xpay_pre.
  xopen_estack e; intros f t sc v LF LS Hs.
  lets [? Hv] : Hs.
  xappn. intros nc.
  xchange echunk_inv_length. intros.
  destruct M as [E I]; unfold Shared; simpl in *.
  xapp. xlet.
  xchange (Group_add_fresh v). 1,2:typeclass. intros.
  xapp. intros no Hno. xchange <- (>> Shared_eq (mk_m E I[v:=tt])).
  xchange (>> Shared_of_MaybeOwned_list); intros M' (H1,HLS).
  asserts ? : (Extend (mk_m E I) (mk_m E I[v:=tt])).
  { apply Extend_from_Incl.
    repeat rewrite dom_union. repeat rewrite dom_update. apply incl_union_l.
    rew_maps*. }
  asserts ? : (EStack_inv (mk_m E I[v:=tt]) no t L LF LS).
  { constructor*; rew_set.
    applys* Forall_pred_incl; intros ? [|]; simpl in *.
    { left. applys* valid_id_mon. }
    { left. rewrite H2. simpl. rewrite dom_update. rew_maps*. } }
  unfold Shared.
  xappn. intros no' Hno'.
  asserts ? : (EStack_inv (mk_m E I[v:=tt]) no' t L LF LS).
  { constructor*; rew_set.
    applys* Forall_pred_incl; intros ? [|]; simpl in *.
    { left. applys* valid_id_mon. }
    { left. rewrite H2. simpl. rewrite dom_update. rew_maps*. } }
  xapp. intros.
  asserts Hd : (dom I[v:=tt] \c dom (ids M')).
  { destruct* H1. }
  asserts HI : (dom I \c dom I[v:=tt]).
  { rewrite dom_update. apply incl_union_l. rew_maps*. }
  xsimpl* M'.
  { applys* Extend_trans. }
  do 2 rewrite EStack_eq. xsimpl* LS LS.
  1,2:applys* EStack_inv_mon.
  xchanges* (>> MaybeOwned_of_Shared_list HLS).
  { rewrite Forall_eq_forall_mem in *. intros s Hms Hos.
    apply Hv in Hms. rewrite Hos in *.
    simpl in Hms, Hno'.
    asserts* ? : (no' \indom (ids M')).
    { apply (incl_inv Hd). destruct* Hms as [|R]; try injects R.
      { now apply (incl_inv HI). }
      { rewrite dom_update. rew_maps*. } }
    easy. }
  unfold Xsimpl. xsimpl. rewrite Pspare.
  xchanges* (>> MaybeOwned_of_Shared_list (Some no) HLS).
  { rewrite Forall_eq_forall_mem in *. intros s Hms Hos.
    apply Hv in Hms.
    rewrite Hos in *.
    asserts* ? : (no \indom I[v:=tt]).
    { destruct* Hms as [|R]; try injects R.
      { now apply (incl_inv HI). }
      { rewrite dom_update. rew_maps*. } }
    easy. }
  unfold Xsimpl. xsimpl.
  simpl. unfold potential_pop.
  destruct t; simpl; try math.
  repeat case_if*.
Qed.


Hint Extern 1 (RegisterSpec copy_with_sharing) => Provide copy_with_sharing_spec.

Lemma estack_to_pstack_preserving_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (e:estack_ A),
  SPEC (estack_to_pstack_preserving e)
    MONO M
    PRE (\$(3*K + 12) \* e ~> EStack M L)
    POST (fun M' p => \[PStack M' L p] \* e ~> EStack M' L).
Proof.
  unfold TripleMon. xcf*.
  xpay_pre. xapp. intros ? M' ?. simpl in *.
  xapp. intros ? M'' HM'' ?.
  xchange* (>> EStack_mon HM'').
  xsimpl* M''. simpl in *.
  applys* Extend_trans.
Qed.

Hint Extern 1 (RegisterSpec estack_to_pstack_preserving) => Provide estack_to_pstack_preserving_spec.
