Set Implicit Arguments.
From CFML Require Import WPLib Stdlib LibSepGroup.

From TLC Require Import LibMap.

Require Import Mono.

Require Import ListMisc.
Require Import Option_aux.

Require Import EChunk_ml EChunk_proof.

Require Import Id_ml Id_proof.

Require Import SChunk_ml SChunk_proof.
Require Import SChunkShared_derived.

Require Import Transtack_ml TranstackCommon.

(* TODO: move to TLC *)
Global Instance map_disjoint_sym : forall A B, Disjoint_sym (T:=map A B).
Proof using.
  constructor. intros x1 x2 M. rewrite disjoint_eq_disjoint_dom in *.
  applys* @disjoint_sym (set A). typeclass.
Qed.
Arguments disjoint_sym : clear implicits.
Hint Rewrite Forall2_nil_eq Forall2_cons_eq : rew_list.
Hint Rewrite Forall_nil_eq Forall_cons_eq : rew_list.


(***************************************************)
(** Definition of invariants for Persistent Stacks *)

Record PStack_inv {A} {IA:Inhab A} {EA:Enc A}
       (M:Memory A) (L:list A)
       (pf:schunk_ A) (pt:list (schunk_ A))
       (LF:list A) (LS:list (list A)) : Prop :=
  make_PStack_inv {
      pstack_stack : Stack_inv L LF LS;
      pstack_tail : Forall2 (SChunkShared M) (LF::LS) (pf::pt);
      pstack_version : Forall (fun p => valid_id M p.(owner')) (pf::pt);
    }.

(* PStack is a predicate satisfied relatively to a shared memory M *)
Definition PStack {A} {IA:Inhab A} {EA:Enc A}
  (M:Memory A) (L:list A) (p:pstack_ A) : Prop :=
  let (pfront,ptail) := p in
  exists LF LS, PStack_inv M L pfront ptail LF LS.

Definition PStackInStateDeep {A} {IA:Inhab A} {EA:Enc A}
  (st:StackState A) LFS (M:Memory A) (L:list A) (p:pstack_ A) : Prop :=
  let (ft,v,u) := st in
  let (pfront,ptail) := p in
  exists LF LS,
    LFS = LF::LS /\ ft = pfront :: ptail /\ u = None /\ v = None /\
    PStack_inv M L pfront ptail LF LS.

Definition PStackInState {A} {IA:Inhab A} {EA:Enc A}
  (st:StackState A) (M:Memory A) (L:list A) (p:pstack_ A) : Prop :=
  exists LFS, PStackInStateDeep st LFS M L p.

Lemma PStack_eqInState : forall A (IA:Inhab A) (EA:Enc A)
  (M:Memory A) (L:list A) (p:pstack_ A),
  PStack M L p = exists st, PStackInState st M L p.
Proof.
  intros. destruct p as [pf pt]. extens.
  unfold PStack, PStackInState.
  split*.
  { intros (LF,(LS,E)). exists (mk_st (pf::pt) None None) (LF::LS).
    now exists LF LS. }
  { intros ([],(?,(LF,(LS,?)))). now exists LF LS. }
Qed.

(***************************************************)
(** Monotony lemmas. *)

Lemma PStackInState_mon : forall A (IA:Inhab A) (EA:Enc A)
  (M M':Memory A) st (L:list A) (p:pstack_ A),
  Extend M M' ->
  PStackInState st M L p ->
  PStackInState st M' L p.
Proof.
  introv E P.
  destruct p, st as (ft,v,u).
  destruct P as (std,(LF,(LS,(?&?&?&?&[? Pt Pv])))).
  exists std LF LS. do 4 (split; try easy).
  rew_list in Pt. rew_list in Pv.
  constructor*; rew_list.
  { split*. constructors*.
    applys* SChunkShared_mon.
    applys* SChunkShared_mon.
    applys* Forall2_rel_le. intros ? ? ?. applys* SChunkShared_mon. }
  { split*. applys* valid_id_mon.
    applys* (>> Forall_pred_incl Pv).
    intros ? ?.
    applys* valid_id_mon. }
Qed.

Lemma PStack_mon : forall A (IA:Inhab A) (EA:Enc A)
  (M M':Memory A) (L:list A) (p:pstack_ A),
  Extend M M' ->
  PStack M L p ->
  PStack M' L p.
Proof.
  introv E.
  do 2 rewrite PStack_eqInState.
  intros (st&P).
  eapply PStackInState_mon in P; try (exact E).
  now exists st.
Qed.

(***************************************************)
(** Specifications *)

Lemma pcreate_spec_fresh_memory : forall A (IA:Inhab A) (EA:Enc A) (d:A),
  SPEC (pcreate d)
    PRE (\$(K+3))
    POST (fun ps => \exists M, Shared M \* \[PStack M (@nil A) ps]).
Proof.
  xcf. xpay.
  xapp; intros r ?.
  xopen r; intros E.
  xval.
  xchange RefGroup_empty.
  unfold Shared. simpl.
  xchange Group_singleton.
  xsimpl (@mk_m A ((support' r) \:= (@nil A)) \{}).
  { simpl. exists (@nil A) (@nil (list A)).
    constructor*; rew_list*; rew_maps*; try split*; simpl.
    { split; simpl; rew_maps*.
      applys* SChunk_inv_share. }
    { now destruct (owner' r). }
     }
Qed.

Lemma pcreate_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (d:A),
  SPEC (pcreate d)
    MONO M
    PRE (\$(K+3))
    POST (fun M' ps => \[PStack M' (@nil A) ps]).
Proof.
  unfold TripleMon. xtriple.
  xapp pcreate_spec_fresh_memory. intros ? M' ?.
  xchange Shared_disjoint. intros.
  xchange Shared_union.
  xsimpl*.
  { apply* Extend_union_r. }
  { eapply PStack_mon.
    { apply* Extend_union_l. applys* disjoint_sym. typeclass. }
    easy. }
Qed.

Hint Extern 1 (RegisterSpec pcreate) => Provide pcreate_spec.


Lemma pis_empty_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (p:pstack_ A),
  PStack M L p ->
  SPEC (pis_empty p)
    PRE (\$2)
    INV (Shared M)
    POST \[= isTrue (L=nil)].
Proof.
  intros A IA EA M L (pf,pt) (LF,(LS,Hp)); simpl.
  lets [Hs Pt] : Hp. rew_list in Pt.
  lets [] : Hs.
  xcf_go*; simpl. subst.
  now eapply Stack_inv_nil_front.
Qed.

Hint Extern 1 (RegisterSpec pis_empty) => Provide pis_empty_spec.

Lemma ppeek_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (p:pstack_ A),
  PStack M L p ->
  L <> nil ->
  SPEC (ppeek p)
    PRE (\$6)
    INV (Shared M)
    POST (fun x => \exists L', \[L = x::L']).
Proof.
  intros A IA EA M L (pf,pt) Hp HL.
  lets (LF,(LS,Hps)) : Hp.
  xcf. xpay.
  xassert_cost 2.
  { xgo*. }
  lets [Hs Hft] : Hps. rew_list in Hft.
  lets [So ? St] : Hs.
  xapp* (>> schunk_peek_spec LF).
  { subst. intros E. rewrite E in HL.
    rewrite* (St E) in HL. }
  intros. xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec ppeek) => Provide ppeek_spec.

Lemma ppop_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (p:pstack_ A),
  PStack M L p ->
  L <> nil ->
  SPEC (ppop p)
    PRE (\$7)
    INV (Shared M)
    POST (fun '(ps',x) => \exists L', \[PStack M L' ps' /\ L = x::L']).
Proof.
  intros A IA EA M L (pf,pt) (LF,(LS,Hps)) HL.
  xcf. xpay_pre; xsimpl.
  xassert_cost 2.
  { xgo*. exists LF LS. eauto. }
  lets [Hs Hft Hv] : Hps. rew_list in Hft.
  lets [So Stf Stn] : Hs.
  asserts LFnonnil : (LF <> nil).
  { intros E. eapply Stack_inv_nil_front in Hs.
    apply Hs in E. false. }
  xapp*. intros (s',x).
  xpull; intros L' (Hs'&HL'&Ho).
  simpl in *.
  lets [Ds' HIs'] : Hs'.
  xmatch. xapp*. subst.
  xif; intros HL'2.
  { xmatch; do 2 xval; xsimpl*; constructor*; destruct LS as [|L LS];
      try easy; rew_listx.
    { exists (@nil A) (@nil (list A)). constructor*.
      rew_list in *. subst. rewrite* Ho. }
    { exists L LS. rew_list in *. constructor*.
      { applys* Stack_inv_front_singl. }
      all:rew_list* in Hft. } }
  { do 2 xval.
    xsimpl. split*; rew_list in *.
    exists L' LS. constructor*.
    { constructor*. auto_false. }
    { rew_list. rewrite* Ho. } }
Qed.


Hint Extern 1 (RegisterSpec ppop) => Provide ppop_spec.

Lemma ppush_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (p:pstack_ A) (x:A),
  PStack M L p ->
  SPEC (ppush p x)
    MONO M
    PRE (\$(K+7))
    POST (fun M' p' => \[PStack M' (x::L) p']).
Proof.
  intros A IA EA M  L (pf,pt) x (LF,(LS,Hps)).
  lets [Hs Hft Hc] : Hps. rew_list in Hft. lets ([Dpf Hpf]&?) : Hft.
  unfold TripleMon. xcf; simpl. xpay.
  xapp*.
  xif; intros isFull.
  { xchange* focus_shared_same.
    xapp; intros d.
    xapp; intros r Hor.
    xapp* (SChunk_proof.schunk_push_spec).
    { apply NotFull_of_nil. }
    intros r' Hor'.
    xopen r'; intros Hr'.
    xopen pf; intros E; clear E.
    destruct M as (M,I); unfold Shared; simpl.
    xchange* (>> Group_add_fresh (support' r') M); intros HDr'.
    xval. xsimpl*; simpl in *.
    { apply Extend_from_Preserve.
      apply* Preserve_add_fresh. }
    { exists (x::nil) (LF::LS).
      constructor*; rew_list.
      { destruct Hs. constructor*; rew_listx*. auto_false. }
      { split.
        { constructor*; subst; simpl in *.
          { apply* indom_update_same. }
          { rewrite read_update_same.
            applys* SChunk_inv_share. } }
        { rew_list. split*.
          { apply* SChunkShared_mon.
            eauto with extend preserve. }
          { applys* Forall2_rel_le.
            apply* SChunkShared_rel_incl_Preserve.
            eauto with extend preserve. } } }
      { autorewrite with rew_list in *.
        split*. destruct Hor' as [E|E]; rewrite* E.
        { now rewrite Hor. }
        { now simpl. } } }
    { xsimpl*. } }
  { xapp*; intros p' M' MM' Hp' Hop'.
    xval. simpl in *. xsimpl*.
    autorewrite with rew_list in *.
    exists (x::LF) LS. constructor*.
    { destruct Hs. constructor*. auto_false. }
    { rew_list. constructor*.
      applys* Forall2_rel_le.
      apply* SChunkShared_rel_incl_Preserve. }
    { rew_list. split.
      { applys* valid_id_mon. destruct Hop' as [E|E]; try rewrite E; easy. }
      { applys* Forall_pred_incl. intros ? ?.
        applys* valid_id_mon. } } }
Qed.


Hint Extern 1 (RegisterSpec ppush) => Provide ppush_spec.

