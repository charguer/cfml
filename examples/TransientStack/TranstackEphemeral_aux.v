Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup List_proof.

From TLC Require Import LibMap.

Require Import Mono.

Require Import ListMisc.
Require Import Option_aux.

Require Import EChunk_ml EChunk_proof.

Require Id_ml. Module Id := Id_ml.
Require Import Id_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml.
Require Import TranstackCommon.

(**************************************)
(** Ephemeral Stacks *)

(* Credits stored from pushs to pay for the creation of an empty echunk. *)
Definition potential_push A (NF:int) (sc:option (echunk_ A)) : int :=
  match sc with
  | None => 1 + NF
  | Some _ => 0 end.

(* Credits stored from pop to pay for the possible copy of the support of
   a shared schunk in tail *)
Definition potential_pop A (NF:int) (tail:list (schunk_ A)) (id:Id.t_) : int :=
  match tail with
  | nil => 0
  | p::_ =>
    If p.(owner') = Some id
    then 0
    else 2 + K - NF end.

Record EStack_inv A {IA:Inhab A} {EA:Enc A}
       (M:Memory A) (id:Id.t_) (t:list (schunk_ A))
       (L LF:list A) (LS:list (list A)) : Prop :=
  make_EStack_inv {
      estack_stack : Stack_inv L LF LS;
      estack_tail_ids :
        Forall (fun p => valid_id M p.(owner') \/ p.(owner') = Some id) t;
    }.

(* A "deep" state layer, which exposes the modeled list by the tail.
   This is useful when trying to factorize proofs between estack and pstack.
   See Iterator_tools. *)
Definition EStackInStateDeep A {IA:Inhab A} {EA:Enc A}
  (st:StackState A) (std:StackStateDeep A) (M:Memory A) (L:list A) (e:estack_ A) : hprop :=
  let (ft,o,u) := st in
  \exists f t (sc:option (echunk_ A)) LF LS id,
      e ~~~> `{front' := f; tail' := t; spare' := sc; id' := id}
   \* f ~> EChunk LF
   \* t ~> ListOf (SChunkMaybeOwned M (Some id)) LS
   \* sc ~> OptionOf (EChunk (@nil A))
   \* Id id
   \* \[std = LF::LS]
   \* \[ft = schunk_make__ f (length LF) (Some id)::t]
   \* \$(potential_push (length LF) sc)
   \* \$(potential_pop  (length LF) t id)
   \* \[u = Some e /\ o = Some id]
   \* \[EStack_inv M id t L LF LS].

Lemma EStackInStateDeep_eq : forall A {IA:Inhab A} {EA:Enc A} (e:estack_ A) (M:Memory A) (st:StackState A) (std:StackStateDeep A) (L:list A),
    e ~> EStackInStateDeep st std M L =   let (ft,o,u) := st in
  \exists f t (sc:option (echunk_ A)) LF LS id,
      e ~~~> `{front' := f; tail' := t; spare' := sc; id' := id}
   \* f ~> EChunk LF
   \* t ~> ListOf (SChunkMaybeOwned M (Some id)) LS
   \* sc ~> OptionOf (EChunk (@nil A))
   \* Id id
   \* \[std = LF::LS]
   \* \[ft = schunk_make__ f (length LF) (Some id)::t]
   \* \$(potential_push (length LF) sc)
   \* \$(potential_pop  (length LF) t id)
   \* \[u = Some e /\ o = Some id]
   \* \[EStack_inv M id t L LF LS].
Proof. auto. Qed.

Tactic Notation "xopen_estackInStateDeep" constr(r) :=
  xchange (EStackInStateDeep_eq r); xpull.

(* A state layer. It allows synchronizing an estack and its iterators.
   See Iterator_proof. *)
Definition EStackInState A {IA:Inhab A} {EA:Enc A}
  (st:StackState A) (M:Memory A) (L:list A) (e:estack_ A) :=
  \exists std, e ~> EStackInStateDeep st std M L.

Lemma EStackInState_eq : forall A {IA:Inhab A} {EA:Enc A} (e:estack_ A) (M:Memory A) (st:StackState A) (L:list A),
    e ~> EStackInState st M L = \exists std, e ~> EStackInStateDeep st std M L.
Proof. auto. Qed.

Tactic Notation "xopen_estackInState" constr(r) :=
  xchange (EStackInState_eq r); xopen_estackInStateDeep r.

(* The actual definition of the EStack predicate, as a an existential
   quantification over a state. *)
Definition EStack A {IA:Inhab A} {EA:Enc A}
  (M:Memory A) (L:list A) (e:estack_ A) : hprop :=
  \exists st, e ~> EStackInState st M L.

Lemma EStack_eq : forall A {IA:Inhab A} {EA:Enc A} (e:estack_ A) (M:Memory A) (L:list A),
    e ~> EStack M L = \exists f t (sc:option (echunk_ A)) id LF LS,
      e ~~~> `{front' := f; tail' := t; spare' := sc; id' := id}
   \* f ~> EChunk LF
   \* t ~> ListOf (SChunkMaybeOwned M (Some id)) LS
   \* sc ~> OptionOf (EChunk (@nil A))
   \* Id id
   \* \$(potential_push (length LF) sc)
   \* \$(potential_pop  (length LF) t id)
   \* \[EStack_inv M id t L LF LS].
Proof.
  intros.
  apply himpl_antisym;
    xunfold EStack; xunfold EStackInState;
      xunfold EStackInStateDeep; xpull.
  { intros []. xsimpl*. }
  { intros f t ? o LF LS. intros.
    xsimpl* (mk_st (schunk_make__ f (length LF) (Some o)::t) (Some o) (Some e)). }
Qed.

Tactic Notation "xopen_estack" constr(r) :=
  xchange (EStack_eq r); xpull.

Tactic Notation "xunfolds_estack" :=
  rewrite EStack_eq; xsimpl*.

(**************************************)
(** Monotony lemmas *)

Lemma union_mon_l : forall A (x y z:set A),
  x \c y ->
  (x \u z) \c (y \u z).
Proof.
  intros.
  rew_maps. intros e E.
  rewrite in_union_eq in *.
  firstorder.
Qed.

Lemma EStack_inv_mon : forall A (IA:Inhab A) (EA:Enc A) (M M':Memory A) o t L (LF:list A) LS,
  Extend M M' ->
  EStack_inv M o t L LF LS ->
  EStack_inv M' o t L LF LS.
Proof.
  introv ? [].
  constructor*.
  { applys* Forall_pred_incl.
    intros ? [|]; try (now right). left.
    applys* valid_id_mon. }
Qed.

Lemma EStack_mon : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) L M M',
  Extend M M' ->
  e ~> EStack M L ==> e ~> EStack M' L.
Proof.
  introv ?.
  xunfolds_estack. intros.
  xchanges* SChunkMaybeOwned_list_mon.
  xunfolds_estack.
  applys* EStack_inv_mon.
Qed.

(**************************************)
(** Inversion lemmas *)

(* Inversion lemma over the length of a state. *)
Lemma estackInState_inv_schunks_length : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (st:StackState A) e,
    e ~> EStackInState st M L ==+> \[length st.(schunks) <= 1 + length L].
Proof.
  intros. destruct st as [ft ?].
  xopen_estackInState e. intros LFS f t ? LF LS ? HLFS Hft (->&->) HE.
  xchange echunk_inv_length. intros.
  xchange ListOf_inv_length. intros Hts.
  xunfold EStackInState. xunfold EStackInStateDeep.
  xsimpl* LFS. simpl.
  lets [[? ? Stn]] : HE. subst. rew_list*.
  asserts ? : (length t <= length (concat LS)).
  { rewrite Hts. applys* length_concat_nonempty.
    applys* Forall_pred_incl.
    lets ? : capacity_spec. unfold IsFull in *.
    intros [|] ? ?; rew_list* in *; try math; congruence. }
  destruct LF; rew_list*.
Qed.

(**************************************)
(** Specifications *)

Lemma ecreate_spec_fresh_memory : forall A (IA:Inhab A) (EA:Enc A) (x:A),
  SPEC (ecreate x)
    PRE (\$(K+4))
    POST (fun e => Shared (@empty A) \* e ~> EStack \{} (@nil A)).
Proof.
  xcf*.
  xchange RefGroup_empty. xpay. xapp. simpl. intros.
  xgo* Xgoto_xsimpl. xchange Shared_empty. xsimpl*.
  rewrite EStack_eq. xsimpl*.
  { constructor*. }
  { unfold Xsimpl. xchange <- ListOf_nil. xsimpl. }
Qed.

Lemma ecreate_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (x:A),
  SPEC (ecreate x)
    PRE (\$(K+4))
    POST (fun e => e ~> EStack M (@nil A)).
Proof.
  xtriple. xapp ecreate_spec_fresh_memory. intros e.
  xchange (>> EStack_mon (\{}: Memory A) M).
  { apply Extend_empty. }
  xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec ecreate) => Provide ecreate_spec.

Lemma eis_empty_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (e:estack_ A),
  SPEC (eis_empty e)
     PRE (\$2)
     INV (Shared M \* e ~> EStack M L)
     POST \[= isTrue (L=nil)].
Proof.
  intros.
  xcf*. xpay_pre; xsimpl.
  xopen_estack e; intros f t sc v LF LS Hs.
  lets [[]] : Hs.
  xchange echunk_inv_length. intros.
  xgo*; subst.
  { fequals. extens. now eapply Stack_inv_nil_front. }
  { xchanges* <- EStack_eq. }
Qed.

Hint Extern 1 (RegisterSpec eis_empty) => Provide eis_empty_spec.

Lemma epeek_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (e:estack_ A),
  L <> nil ->
  SPEC (epeek e)
    PRE (\$5)
    INV (Shared M \* e ~> EStack M L)
    POST (fun x => \exists L', \[L = x::L']).
Proof.
  introv HL.
  xcf. xpay.
  xassert_cost 2.
  { xgo*. }
  xopen_estack e. introv HLc.
  lets [[? ? St]] : HLc.
  xappn*; subst; intros.
  { apply HL. rewrite* St. }
  { xunfolds_estack. }
Qed.

Hint Extern 1 (RegisterSpec epeek) => Provide epeek_spec.

Lemma epop_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (e:estack_ A),
  L <> nil ->
  SPEC (epop e)
    PRE (\$11 \* e ~> EStack M L)
    INV (Shared M)
    POST (fun x => \exists L', \[L = x::L'] \* e ~> EStack M L').
Proof.
  introv Hl.
  xcf. xpay.
  xassert_cost 2.
  { xgo*. }
  xopen_estack e; intros f t sc v LF LS Hs.
  lets [Hst Hv] : Hs.
  lets [So Stf Stn] : Hst.
  asserts LFnonnil : (LF <> nil).
  { intros E. eapply Stack_inv_nil_front in Hst.
    rewrite* Hst in E. }
  xappn*. intros X LF' HLFF'.
  xappn; intros B HB; rewrite isTrue_eq_if in HB.
  lets ? : capacity_spec.
  xif; intros HLF'; case_if as C; clears B.
  { xapp. xcase.
    { xgo*.
      xchange ListOf_nil_r; intros ->; rew_listx.
      xchange <- ListOf_nil.
      xunfolds_estack; subst.
      { constructor*. }
      { destruct sc; simpls*. } }
    { xcase; try xdone.
      xappn.
      xchange ListOf_cons_r; intros Z ZS HLS.
      subst.
      asserts Es : (EStack_inv M v ps (concat (Z :: ZS)) Z ZS).
      { constructor*; rew_listx* in *.
        applys* Stack_inv_front_singl. }
      rew_listx in Stf; destruct Stf as (IFZ,?).
      xif; intros Ho.
      { xgo* (Z ++ concat ZS).
        xunfolds_estack.
        xunfold_SChunkMaybeOwned.
        xunfold SChunkUniquelyOwned.
        xunfolds SChunk. intros.
        destruct sc,ps;
          simpl; try rewrite IFZ; repeat (case_if*); math.
          false. apply* C1. split*. auto_false. }
      { xunfold_SChunkMaybeOwned; try (false*; fail).
        xpull; intros.
        xapp*; intros.
        xgo*.
        xunfolds_estack.
        rewrite IFZ; unfold potential_pop. rew_list. rew_int.
        destruct sc,ps; simpl; try math; try case_if*. } } }
  { xgo*.
    xunfolds_estack.
    constructor*.
    { constructor*. auto_false. }
    { unfold potential_pop. subst.
      destruct t, sc; simpl; rew_list; rew_int; try math; case_if*. } }
Qed.

Hint Extern 1 (RegisterSpec epop) => Provide epop_spec.

Lemma get_empty_spec : forall A (IA:Inhab A) (EA:Enc A) (sc:option (echunk_ A)) (d:A),
  SPEC (get_empty sc d)
    PRE (\$1 \* sc ~> OptionOf (EChunk (@nil A)))
    POST (fun e => \$(- (match sc with None =>  (1+K) | Some _ => 0 end)) \* e ~> EChunk (@nil A)).
Proof. xcf_go*; simpl; math. Qed.

Hint Extern 1 (RegisterSpec get_empty) => Provide get_empty_spec.

Lemma epush_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (e:estack_ A) (x:A),
  SPEC (epush e x)
    PRE (\$7 \* e ~> EStack M L)
    INV (Shared M)
    POSTUNIT (e ~> EStack M (x::L)).
Proof.
  xcf.
  xchanges (EStack_eq e); intros f t sc v LF LS Hs.
  lets [Hst Hvt] : Hs.
  lets [So Stf Stn] : Hst.
  xpay. xappn.
   intros B HB; rewrite isTrue_eq_if in HB.
  xif; intros isFullLF; case_if as C; clears B.
  { xappn*. intros ns (Hns,<-). xapp. xapp. xapp.
    xopen ns; intros Ins.
    xopen (support' ns). intros c' s' d' L' HL'.
    xapp. xclose* (support' ns).
    xclose* ns.
    xgo*.
    { apply NotFull_of_nil. }
    destruct (owner' ns) eqn:E; simpl in *; try easy.
    injects Hns.
    rewrite EStack_eq. xsimpl*.
    { constructor*.  constructor.
      { rew_listx. fequal*. subst. now rewrite concat_cons. }
      all:rew_listx*; simpl; try easy. }
    { unfold Xsimpl. xsimpl*.
      xunfolds ListOf.
      xchanges* <- SChunkMaybeOwned_Owned.
      { auto_false. }
      { unfold potential_pop.
        subst. rew_list; rew_int.
        destruct t,sc; simpl; try math; repeat rewrite C; repeat case_if*; false*. } } }
  { xgo*.
    xunfolds_estack.
    constructor*; subst.
    { constructor*. auto_false. }
    { destruct sc; simpl;
      rew_list; rew_int;
      unfold potential_pop;
      destruct t; simpl; try math; case_if*. } }
Qed.

Hint Extern 1 (RegisterSpec epush) => Provide epush_spec.
