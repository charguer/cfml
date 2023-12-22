Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup List_proof Array_proof.
From TLC Require Import LibListZ.

Require Import ListMisc.

Require Id_ml. Module Id := Id_ml.
Require Import Id_proof.

Require Import ListIterator_ml ListIterator_proof.

Require Import EChunk_ml EChunk_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml TranstackCommon.
Require Import TranstackEphemeral_aux TranstackPersistent_aux.

Require Import Iterator_ml.
Require Export Iterator_tools.

(**************************************)
(** Iterators *)

Record Iterator_inv A {EA:Enc A} {IA:Inhab A}
       (ft : list (schunk_ A)) (* The StackInternal *)
       (fc : schunk_ A) (vfc : int) (ta : list (schunk_ A)) (* Iterators values *)
       (k : int)
       (i : int) : Prop :=
  make_Iterator_Inv {
      it_suffix : Suffix (fc::ta) ft;
      it_tail_nil : vfc = 0 -> ta = nil;
      it_v : 0 <= vfc <= view' fc;
      it_i : i = sum_size ft - sum_size ta - vfc;
      it_tr : k = length ft - length ta - 1;
    }.

Definition Iterator_open A {EA:Enc A} {IA:Inhab A}
  (st:StackState A) (i k:int) (it:iterator_ A) : hprop :=
  \exists (fc:echunk_ A) (lfc:int) (ofc:option Id.t_) (vfc:int) r (ta:list (schunk_ A)),
      it ~~~> `{ focused' := fc; fview' := vfc; fid' := ofc;
                 traveled' := k; rest' := r; uestack' := st.(ues) }
      \* r ~> ListIterator ta
      \* \[Iterator_inv st.(schunks) (schunk_make__ fc lfc ofc) vfc ta k i].

Lemma Iterator_open_eq : forall A {EA:Enc A} {IA:Inhab A}
  (it:iterator_ A) (st:StackState A) (i k:int),
  it ~> Iterator_open st i k = \exists (fc:echunk_ A) (lfc:int) (ofc:option Id.t_) (vfc:int) r (ta:list (schunk_ A)),
      it ~~~> `{ focused' := fc; fview' := vfc; fid' := ofc;
                 traveled' := k; rest' := r; uestack' := st.(ues) }
      \* r ~> ListIterator ta
      \* \[Iterator_inv st.(schunks) (schunk_make__ fc lfc ofc) vfc ta k i].
Proof. auto. Qed.

Tactic Notation "xunfold_iterator_open" :=
  xunfold Iterator_open.

Tactic Notation "xopen_iteratorInState" constr(it) :=
  xchange (Iterator_open_eq it); xpull.

Definition Iterator A {EA:Enc A} {IA:Inhab A}
  (st:StackState A) (i:int) (it:iterator_ A) : hprop :=
  \exists tr, it ~> Iterator_open st i tr.

Tactic Notation "xunfold_iterator" :=
  xunfold Iterator; xunfold_iterator_open.

Lemma Iterator_eq : forall {A} {EA:Enc A} {IA:Inhab A} (it:iterator_ A) (st:StackState A) (i:int),
  it ~> Iterator st i =
  \exists (fc:echunk_ A) lfc (ofc:option Id.t_) (vfc:int) r ta (k:int),
      it ~~~> `{ focused' := fc; fview' := vfc; fid' := ofc;
                 traveled' := k; rest' := r; uestack' := st.(ues) }
      \* r ~> ListIterator ta
      \* \[Iterator_inv st.(schunks) (schunk_make__ fc lfc ofc) vfc ta k i].
Proof.
  intros.
  apply himpl_antisym; xunfold_iterator; xsimpl*.
Qed.

Tactic Notation "xopen_iterator" constr(it) :=
  xchange (Iterator_eq it); xpull.

Lemma iterator_inv_index : forall A (EA:Enc A) (IA: Inhab A) (M:Memory A) st LFS L it i,
  Stacked M L st LFS \* it ~> Iterator st i ==+>
  \[0 <= i <= length L].
Proof.
  intros.
  xopen_iterator it. intros ? ? ? ? ? ei ? Hi.
  xopen_stacked st. destruct st as [ft ?]. xpull. intros Hs. simpl in *.
  xchange ListOf_schunk_lengths. intros Hts.
  xunfold_iterator. xunfold Stacked. xsimpl*.
  lets (LF,(LS,(HLFS&[]))) : Hs.
  lets [Is] : Hi.
  subst i L. simpl in *.
  rewrite <- concat_cons, <- HLFS, length_concat_eq_sum, <- Hts.
  unfold sum_size.
  lets (l1,?) : (Suffix_inv_split Is).
  asserts Z : (Forall (fun x => 0 <= x) (map view' ft)).
  { rewrite Hts. rewrite Forall_map_eq.
    rewrite Forall_eq_forall_mem.
    intros. math. }
  subst ft.
  rew_listx. rew_listx in Z. simpl in *.
  asserts ? : (0 <= sum (map view' l1)).
  { apply* sum_pos. }
  asserts ? : (0 <= sum (map view' ei)).
  { apply* sum_pos. }
  math.
Qed.

(**************************************)
(** Specifications *)

Lemma of_estack_spec : forall A (EA:Enc A) (IA: Inhab A) st M L (e:estack_ A),
  SPEC (of_estack e)
    PRE (\$2)
    INV (e ~> EStackInState st M L)
    POST (fun it => it ~> Iterator st 0).
Proof.
  xcf*. xpay_pre; xsimpl. lets [ft ? ?] : st.
  xopen_estackInState e. intros LFS f t ? LF LS ? HLFS ? (?&?) Hi.
  destruct LFS; try congruence; injects HLFS.
  xopen f. introv Hf.
  xappn*. intros.
  xclose* f LF.
  xchange ListOf_inv_length. intros Heq.
  lets [[? ? Htn]] : Hi.
  xchanges ListOf_schunk_lengths; intros Htls.
  xgo*.
  xunfold EStackInState. xunfold EStackInStateDeep. xsimpl*.
  xunfold_iterator. xsimpl* f (length LF).
  destruct Hf.
  constructor*; rew_list*; simpl; subst; rew_list*.
  { eauto with suffix. }
  { intros. apply length_zero_inv.
    rewrite Heq. rewrite* Htn.
    apply* length_zero_inv. }
  { unfold sum_size. rew_listx. simpl. math. }
Qed.

Hint Extern 1 (RegisterSpec of_estack) => Provide of_estack_spec.

Lemma of_pstack_spec : forall A (EA:Enc A) (IA: Inhab A) st M (L:list A) (p:pstack_ A),
  PStackInState st M L p ->
  SPEC (of_pstack p)
    PRE (\$2)
    POST (fun it => it ~> Iterator st 0).
Proof.
  introv Hp. destruct p as (pf,pt), pf, st as [ft ? ?].
  lets (LFS,(LF,(LS,(?&?&?&?&[[? ? Stn] PSt])))) : Hp; simpl in *.
  rew_list in PSt. destruct PSt as (SLF&PSt).
  lets Htls: Forall2_inv_length PSt.
  xunfold_iterator.
  xcf_go*; simpl.
  constructor*; simpl; subst; rew_list.
  { eauto with suffix. }
  all:lets (?,[? Sl ?]) : SLF; simpl in *.
  { intros. apply length_zero_inv.
    rewrite <- Htls. rewrite* Stn.
    apply* length_zero_inv. }
  { math. }
  { unfold sum_size. rew_listx. simpl. math. }
Qed.

Hint Extern 1 (RegisterSpec of_pstack) => Provide of_pstack_spec.

Lemma finished_spec : forall A (IA:Inhab A) (EA:Enc A) M st LFS L (i:int) (it:iterator_ A),
  SPEC (finished it)
    PRE (\$1)
    INV (Stacked M L st LFS \* it ~> Iterator st i)
    POST \[= isTrue (i = (length L))].
Proof.
  xcf*.
  xopen_stacked st. destruct st as [ft]. xpull. introv HS.
  lets (LF,(LS,[])) : HS.
  xopen_iterator it. intros ? ? ? ? ? t ? Ii.
  xchange* ListOf_schunk_lengths; intros Htls. subst.
  destruct ft; rew_listx in Htls; try congruence.
  injection Htls; clear Htls; intros Htls Hf.
  xgo*.
  lets [Its It ? ?] : Ii. subst.
  split; intros E.
  { rewrite* It. rewrites* (>> Stack_inv_length). simpl.
    unfold sum_size. rew_listx. rewrite Htls, Hf, E.
    math. }
  { rew_int in *.
    asserts ? : (0 <= sum_size t).
    { apply sum_pos. rewrite Forall_map_eq.
      apply Suffix_cons2_inv in Its.
      applys* Suffix_Forall.
      rewrite <- Forall_map_eq, Htls, Forall_map_eq.
      rewrite Forall_eq_forall_mem.
      intros. math. }
    simpl in *.
    unfold sum_size in *. rew_listx in E.
    rewrites* (>> Stack_inv_length) in E.
    rewrite Htls, Hf in E. math. }
  { xunfold Stacked. xsimpl*.
    xunfold_iterator. xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec finished) => Provide finished_spec.

Lemma list_middle_eq : forall A (IA:Inhab A) (EA:Enc A) (L:list A) (i:int),
  index L i ->
  exists l1 l2,
    L = l1 ++ L[i] :: l2 /\ length l1 = i /\ length l2 = length L - i - 1.
Proof.
  intros A ? ? L i Hi.
  rew_index in *.
  exists (take i L) (drop (i+1) L).
  split; try split; rew_listp*.
  eapply eq_of_extens.
  { rew_listx; rew_listp*. }
  { intros. list_cases*; fequals*. }
Qed.

Lemma get_spec : forall A (IA:Inhab A) (EA:Enc A) M LFS st L (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (get it)
    PRE (\$3)
    INV (Shared M \* Stacked M L st LFS \* it ~> Iterator st i)
    POST \[= L[i]].
Proof.
  introv Hi.
  xcf. xpay_pre.
  xassert_cost 2.
  { xgo*. }
  xopen_stacked st. destruct st as [ft v ?]. xpull; intros HS.
  lets (LF,(LS,(?&Hst))) : HS. lets [Eio Etf ?] : Hst.
  xchange ListOf_inv_length. intros.
  xchanges ListOf_schunk_lengths; intros Htls.
  xopen_iterator it. intros fc lfc ofc vi r rs k Ii.
  remember {| support' := fc; view' := lfc; owner' := ofc |} as sfc eqn:Esfc.
  lets [Is It Iv ?] : Ii.
  asserts vn0: (vi <> 0).
  { intros ->. apply Hi. simpl in *. subst i.
    rewrite* It. unfold sum_size. rew_listx.
    rewrite Htls. rewrites* (>> Stack_inv_length). }
  lets (eis,Eeis) : Suffix_inv_split Is. simpl in *.
  asserts* ? : (length eis = k).
  xchange* (>> focus ft v k).
  intros LC.
  asserts_rewrite (ft[k] = sfc).
  { rewrite Eeis. list_cases*. }
  xopen sfc. intros Sfc.
  lets [Sl Sle ?] : Sfc.
  subst sfc. simpl in *.
  xopen fc. intros d ? ? LCP Hd.
  lets [Ef ? El Ec]: Hd.
  xappn*.
  xclose* fc LC. xclose_schunk* fc; try easy.
  xunfold_iterator. xunfold Stacked. simpl.
  unfold protect. xsimpl*.
  { rewrite* Ef. clear Ef. rewrite Eio.
    rewrite <- concat_cons.
    lets (l1,(l2,(HL&?&?))) : (>> list_middle_eq (LF::LS) k).
    { typeclass. }
    { subst. rew_list* in *. }
    rewrite HL. subst i. rewrite Eeis. rew_listx. simpl.
    asserts_rewrite (sum_size eis = length (concat l1)).
    { rewrite length_concat_eq_sum. fequal. subst.
      rewrite HL in Htls.
      do 2 rewrite map_app in Htls.
      apply app_cancel_same_length_l in Htls.
      rew_listx*. rew_listx*. }
    repeat rewrite read_app.
    repeat case_if*; subst; try (exfalso; math; fail).
    rewrite Sl.
    fequal*. rew_index* in *. }
  { simpl. constructor*. }
  { subst. xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec get) => Provide get_spec.

Lemma move_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A)
  (st:StackState A) LFS (L:list A) (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (move it)
    PRE (\$4 \* it ~> Iterator st i)
    INV (Stacked M L st LFS)
    POSTUNIT (it ~> Iterator st (i+1)).
Proof.
  introv Hi.
  xcf*. xpay_pre.
  xassert_cost 1.
  { xgo*. }
  xopen_stacked st. destruct st as [ft ? ?].
  xpull; intros (LF,(LS,(HLFS&HS))).
  xchanges ListOf_schunk_lengths; intros Htls.
  rewrite HLFS in Htls.
  destruct ft as [|f t]; rew_listx in Htls; try congruence.
  xopen_iterator it. intros fc vfc ofc vi r ts ? Ii.
  lets [Is It Iv ?] : Ii.
  xapp. xlets.
  asserts ? : (Forall (eq K) (map view' t)).
  { lets [] : HS.
    rew_listx in Htls. injection Htls. clear Htls. intros Htls Hf.
    rewrite Htls. rewrite Forall_map_eq.
    now applys* Forall_pred_incl. }
  lets ? : capacity_spec.
  xunfold_iterator. xunfold Stacked.
  xif; subst; intros E;
    rewrite isTrue_eq_if in E; case_if*; clear E.
  { xappn*. xval.
    xif; intros E.
    { xappn*. intros tsf tss Htfs. xappn.
      xsimpl* (support' tsf) (view' tsf) (owner' tsf).
      rew_list in *.
      asserts ? : (K = view' tsf).
      { applys* (>> Forall_mem_inv (map view' t)).
        apply Suffix_cons2_inv in Is.
        apply mem_map. apply* Suffix_mem. }
      constructor*; simpl; intros; try math.
      { destruct tsf. apply* Suffix_cons_inv. }
      { subst. unfold sum_size. rew_listx*. } }
    { xgo*. constructor*. } }
  { xval. xif; intros Z.
    { false. apply* Z. }
    { clear Z. xgo*.
      asserts : (vi <> 0).
      { intros ->. apply Hi. simpl.
        rewrite* It. unfold sum_size. rew_listx.
        rewrites* (>> Stack_inv_length). rew_listx in Htls. injection Htls as -> ->.
        math. }
      constructor*. } }
Qed.

Hint Extern 1 (RegisterSpec move) => Provide move_spec.

Lemma fupdate_spec : forall (A B:Type) {IB:Inhab B} (H I:hprop) (n:int) (R: A -> B -> hprop) (xs:list B) (k:int) (L:list A) (f:func) (LA:A) (RB:B -> hprop),
    haffine_repr R ->
    index xs k ->
    (SPEC (f (xs[k])) PRE (H \* \$n) INV I
          POST (fun (b:B) => RB b \* b ~> R LA)) ->
    SPEC (fupdate k f xs)
         PRE (\$(length xs) \* \$n \* H \* xs ~> ListOf R L)
         INV I
         POST (fun '(x,ys) => RB x \* \[ys = xs[k:=x]] \* ys ~> ListOf R L[k:=LA]).
Proof.
  induction xs; introv ? Hk Hf; rew_index in Hk. rew_list in Hk. try math.
  xcf*. xpay_pre.
  xchange ListOf_inv_length. intros.
  destruct L; rew_list in *; try math.
  xmatch; injects TEMP.
  { rewrite read_zero in Hf.
    xapp* Hf. intros. xval.
    do 2 rewrite update_zero.
    xunfold ListOf. xsimpl*. }
  { asserts ? : (k<>0).
    { intros ?. applys* C0. }
    rew_index in *.
    xunfold ListOf. xapp* IHxs.
    { rewrite read_cons_case in Hf. case_if*. }
    intros (?,?). xpull. intros.
    xgo*; rewrite* update_cons_pos.
    xunfold ListOf. xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec fupdate) => Provide fupdate_spec.

Lemma update_estack_spec : forall A (EA:Enc A) (IA:Inhab A) (k:int) (e:estack_ A) ft LFS v M L,
    SChunkShared M LFS[k+1] ft[k+1] ->
    0 <= k < length ft - 1 ->
    SPEC (update_estack k e)
      PRE (\$(length ft + K + 4)
           \* e ~> EStackInStateDeep (mk_st ft v (Some e)) LFS M L)
      INV (Shared M)
      POST (fun p => \exists ft', e ~> EStackInStateDeep (mk_st ft' v (Some e)) LFS M L
          \* \[ft' = ft[k+1 := schunk_make__ (support' p) (view' ft[k+1]) v]]).
Proof.
  introv Hp Hk.
  xcf*. xpay_pre.
  xopen_estackInStateDeep e. intros f t ? LF LS id HLFS Hft (?&->) HS.
  destruct ft; try congruence; injects Hft.
  rew_list in Hk.
  xchange ListOf_inv_length. intros Hl.
  xchange ListOf_schunk_lengths. intros Htls.
  xapp. xlet. xapp.
  lets [] : HS.
  xapp* (>> fupdate_spec \[SChunkShared M LS[k] t[k]] (Shared M) (K+4) (SChunkMaybeOwned M (Some id)) LS (fun (x:schunk_ A) => \[owner' x = (Some id) /\ view' x = view' t[k]])).
  { apply haffine_repr_SChunkMaybeOwned. }
  { xtriple. xpull. intros.
    xapp* Spec_upd. xpay_pre. subst.
    xapp*. intros.
    xapp*. intros ? (?&?).
    xchange schunk_inv_length. intros.
    xsimpl*; simpl.
    { split*. apply (f_equal (fun x => x[k])) in Htls.
      do 2 rewrite read_map in Htls; auto_star. }
    xchange* <- SChunkMaybeOwned_Owned. congruence.
    xsimpl*. }
  { subst. do 2 rewrite* read_cons_pos in Hp. rew_int* in Hp. }
  intros (nsc,t'). xpull. intros (Hv&?) ?. rew_list.
  xchange echunk_inv_length. intros HLF. simpl.
  xmatch. xapp. xval.
  xsimpl* (schunk_make__ f (length LF) (Some id)::t'); simpl.
  { subst. rewrite* update_cons_pos. rewrite* read_cons_pos.
     destruct nsc. repeat fequal*. }
  xunfold EStackInStateDeep. subst. xsimpl* f.
  { rewrite* LibListZ.update_same. }
  { constructor*.
    { rewrite* LibListZ.update_same. }
    all:intros;apply* Forall_update. }
  { rew_int.
    unfold potential_pop.
    destruct t. rew_listx*.
    destruct ((s :: t)[k:=nsc]) eqn:R; rewrite* update_cons_case in R;
      repeat case_if*. }
Qed.

Hint Extern 1 (RegisterSpec update_estack) => Provide update_estack_spec.

Lemma Suffix_update : forall A (IA:Inhab A) (EA:Enc A) (xs ys:list A) x x' y' k,
  Suffix (x::xs) ys ->
  x' = y' ->
  k = length ys - length xs - 1 ->
  Suffix (x'::xs) ys[k:=y'].
Proof.
  intros ? ? ? ? ys ? ? ? k S ? ?.
  lets (n,(E&?)) : S.
  asserts ? : (n <> length ys).
  { intros ?. subst. rew_list in E. congruence. }
  symmetry in E. apply drop_eq_cons_inv in E; auto_star.
  exists n. split*.
  asserts ? :(k=n).
  { subst. rew_listx in *. autorewrite with rew_listp in *; auto_star. }
  subst n.
  lets* (l,Hys) : (>> Suffix_inv_split S).
  rewrite Hys. rewrite* update_middle. rew_list.
  rewrite* drop_app_r.
  asserts_rewrite* (length l = k).
Qed.

Definition set_cost A B (ft:list A) (M:Memory B) :=
  If M = \{}
  then 0
  else length ft + K + 3.

Hint Rewrite read_update_same update_update_same update_same : rew_listp.

Lemma ensure_uniquely_own_focused_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (ft:list (schunk_ A)) (LFS:list (list A)) (o:option Id.t_) (e:estack_ A)
  (k i:int) u (it:iterator_ A),
  SPEC (ensure_uniquely_own_focused it)
    PRE (\$(set_cost ft M + 4)
         \* e ~> EStackInStateDeep (mk_st ft o u) LFS M L
         \* it ~> Iterator_open (mk_st ft o u) i k)
    INV (Shared M)
    POSTUNIT (\exists ft' c, e ~> EStackInStateDeep (mk_st ft' o u) LFS M L
              \* it ~> Iterator_open (mk_st ft' o u) i k
              \* \[ft' = ft[k := schunk_make__ c (view' ft[k]) o]]
              \* \[If M = \{} then ft' = ft else True]
             ).
Proof.
  xcf*. xpay_pre.
  xopen_estackInStateDeep e. intros f t ? ? ? id HLFS Hft (->&->) He.
  xopen_iteratorInState it. intros fc vfc ofc vi r ts Ii; simpl in *.
  lets [Its It ? ? Ik] : Ii.
  lets Iss : Suffix_length Its. rew_list in Its.
  asserts E : (ft[k] = schunk_make__ fc vfc ofc).
  { rewrites* (>> Suffix_read Its).
    list_cases*. }
  asserts ? : (index ft k).
  { rew_index in *. rewrite Hft. rew_index*. split*. math. }
  xappn. xmatch. xappn.
  xif; intros Ho'.
  { asserts knzero : (k <> 0).
    { subst. intros Ekn. apply Ho'.
      rewrite Ekn,read_zero in E. injects* E. }
    xapp.
    xchange* estack_internals. congruence.
    rewrite <- Hft.
    xchange (>> ListOf_focus k); try easy.
    asserts Oftk : (owner' ft[k] <> (Some id)). { rewrite* E. }
    xchange SChunkMaybeOwned_notOwned; try apply Oftk.
    intros (U&SSfc).
    xchange* <- (>> SChunkMaybeOwned_notOwned M); rewrite <- Ik.
    { constructor*. easy. apply SSfc. }
    unfold protect. xsimpl.
    rewrite Hft,HLFS.
    xchange* <- (>> estack_internals (Some id)). congruence.
    xchange* <- (>>EStackInStateDeep_eq (mk_st ft (Some id) (Some e))).
    xapp*; simpl; try math_rewrite (k-1+1=k).
    { constructor*; try easy. rewrite HLFS. apply SSfc. }
    { subst. rew_list* in *. }
    intros p ft' Eft.
    xopen_estackInStateDeep e. intros f' t' ? ? ? id' HLFS' Hft' (Hs'&Hid') He'. clear Hs'.
    injects Hid'.
    xchange* estack_internals. congruence. rewrite <- Hft'.
    xchange (>> ListOf_focus k).
    { rewrite Eft. applys* index_update. }
    asserts T : (owner' ft'[k] = (Some id')).
    { rewrite Eft. rew_listp*. }
    xchange SChunkMaybeOwned_Owned. try (now rewrite T). congruence.
    xopen ft'[k]. intros Hft'k.
    do 2 xapp.
    xchange* <- (SChunk_eq ft'[k]); try (apply Hft'k).
    xchange <- (>> SChunkMaybeOwned_Owned M (Some id')); try easy.
    unfold protect. xsimpl. rewrite Hft'.
    xchange* <- estack_internals. congruence.
    xapp.
    xchange* <- (EStackInStateDeep_eq e M (mk_st ft' (Some id') (Some e))); try (now rewrite Ho'').
    { now subst. }
    xsimpl* ft' (support' ft'[k]); simpl.
    { rewrite Eft. rew_listp*. }
    { case_if as HM; try easy.
      rewrite HM in *. rewrite dom_empty in U.
      false*. }
    xunfold_iterator. xsimpl*.
    { rewrite Eft. constructor*; simpl; rew_list*.
      { rewrite E. applys* Suffix_update.
        typeclass. }
      { unfold sum_size. rewrite* map_update. simpl.
        rewrite* <- map_update. rewrite* LibListZ.update_same. } }
    { rewrite Hft. unfold set_cost. rew_listx.
      case_if as HM; jauto.
      exfalso. rewrite HM in *. (* (False) case when M=\{} *)
      rewrite dom_empty in U.
      now apply in_empty in U. } }
  { xval.
    xunfold EStackInStateDeep. xunfold_iterator_open.
    xsimpl*; simpl.
    { constructor*. }
    { rewrites* <- (>> LibListZ.update_same k).
      rewrite* update_update_same.
      rewrite* read_update_same.
      fequal. rewrite* E. }
    { case_if*. }
    { unfold set_cost. case_if*.
      lets ? : capacity_spec. math. } }
  Unshelve.
  typeclass.
Qed.

Hint Extern 1 (RegisterSpec ensure_uniquely_own_focused) => Provide ensure_uniquely_own_focused_spec.

(* A specification of set with the effective time bounds.
   As it exposes the internal state, it is useful to provide a
   greater-still-linear time bound to the end-user. *)
Lemma set_spec_low_bound : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A)
  (st:StackState A) (e:estack_ A) (i:int) (it:iterator_ A) (x:A),
  i <> length L ->
  SPEC (set it x)
    PRE (\$(set_cost st.(schunks) M + 6) \* e ~> EStackInState st M L \* it ~> Iterator st i)
    INV (Shared M)
    POSTUNIT (\exists st', e ~> EStackInState st' M (L[i:=x]) \* it ~> Iterator st' i
                        \* \[If M = \{} then st = st' else True]).
Proof.
  introv Hi.
  xcf. xpay_pre.
  xassert_cost 1; xsimpl.
  { xchange Stacked_of_estack. intros.
    xunfold EStackInState.
    xgo*. unfold protect. xsimpl. }
  xunfold Iterator; xpull; intros k.
  destruct st as [ft v u]; simpl in *.
  xchange EStackInState_eq. intros LFS.
  xapp. intros ft' fc' Hft' HM.
  xopen_iteratorInState it. intros fc vfc ofc vi r ts Ii.
  lets [Its It Itv Iti Ik] : Ii.
  lets SIs : Suffix_length Its. rew_list in SIs.
  xopen_estackInStateDeep e. intros f t ? LF LS id HLFS Hft (->&->) ES.
  lets [Est] : ES. lets [EL Etf Etn] : Est. simpl in *.
  xchange* estack_internals. congruence. rewrite <- Hft.
  xchange ListOf_schunk_lengths; intros Hts. rewrite <- HLFS in Hts.
  asserts ? : (vi <> 0).
  { intros ->. apply Hi. subst i.
    rewrite* It. unfold sum_size. rew_listx.
    rewrite Hts. rewrites* (>> Stack_inv_length). }
  asserts Iftk : (index ft' k).
  { rewrite Hft',Ik in *. rew_list in SIs. rew_index*. }
  asserts* Eftft' : (length ft' = length ft).
  asserts EftLFS : (length ft = length LFS).
  { apply (f_equal (@length _)) in Hts.
    rew_listx in Hts. subst. math. }
  asserts Eftk : (ft'[k] = {| support' := fc; view' := vfc; owner' := ofc |}).
  { rewrite Ik. rewrites* (>> Suffix_read Its).
    list_cases*. }
  xchange* (>> ListOf_focus_update k).
  xchange* SChunkMaybeOwned_Owned.
  { rewrite Hft'. rew_listp*. }
  { congruence. }
  remember ft'[k] as z eqn:Z. rewrite <- Z.
  xopen z. subst z.
  intros SI.
  rewrite Eftk. simpl.
  xopen fc. intros ? ? ? LC HLC.
  asserts vftk : (view' ft'[k] = vfc).
  { destruct ft'[k]; injects* Eftk. }
  asserts vftk' : (view' ft'[k] = length LFS[k] ).
  { apply (f_equal (fun x => x[k])) in Hts.
    do 2 rewrite read_map in Hts; try easy.
    rew_index. rewrite <- EftLFS, <- Eftft'. rew_index* in Iftk. }
  lets [Ef Et El] : HLC. rewrite <- HLFS in *.
  xappn.
  { rewrite vftk, El in *. rew_index*. }
  xclose* fc (LFS[k][length LFS[k] - vi:=x]).
  { constructor*; intros j Hj; list_cases*. }
  asserts ? : (SChunk_inv true (LFS[k][length LFS[k] - vi:=x]) (LFS[k][length LFS[k] - vi:=x]) ft'[k]).
  { destruct SI. constructor*. intros. fequal*. }
  xclose_schunk* fc. { subst. now rewrite Eftk. }
  xchange (hforall_specialize (schunk_make__ fc' (view' ft[k]) (Some id))).
  xchange (hforall_specialize (LFS[k][length LFS[k] - vi:=x])).
  xchange* <- (>> SChunkMaybeOwned_Owned M).
  { rew_listp*. auto_false. }
  rewrite Hft'. rew_listp*. rewrite <- Hft'.
  xsimpl (mk_st ft' (Some id) (Some e)).
  { case_if*. fequal*. }
  xunfold Iterator_open. xsimpl*; simpl.
  clear HM.
  asserts HL : (L[i:=x] = concat (LFS[k:=LFS[k][length LFS[k] - vi:=x]])).
  { rewrite EL. rewrite <- concat_cons, <- HLFS.
    subst i.
    lets (eis,Eeis) : Suffix_inv_split Its.
    lets* (l1,(l2,(HL&Hl1&?))) : (>> list_middle_eq LFS k).
    { typeclass. }
    rewrite HL, Eeis. list_cases*. simpl.
    asserts_rewrite (sum_size eis = length (concat l1)).
    { rewrite length_concat_eq_sum. fequal.
      rewrite HL, Eeis in Hts.
      do 2 rewrite map_app in Hts.
      apply app_cancel_same_length_l in Hts. rew_listx* in *. subst k.
      rew_listx*. rewrite Hl1, Eeis.
      rew_listx*. }
    rewrites* (>> update_app_r (length LFS[k] - vi)).
    rewrites* (>> update_app_l (length LFS[k] - vi)).
    rewrites* update_middle. rew_listx*. }
  rewrite Hft,HLFS in *.
  rewrite* update_cons_case.
  xunfold EStackInState. xunfold EStackInStateDeep.
  case_if as C.
  { rewrite C in *. rew_list. xsimpl* (LFS[0][length LFS[0] - vi:=x]::LS).
    { do 2 constructor*.
      { rewrite HL. rewrite* update_zero. }
      { intros Lfn. applys Etn.
        rewrite <- length_zero_eq_eq_nil, length_update in Lfn.
        rewrite* <- length_zero_eq_eq_nil. } }
    { xunfold ListOf. subst. xsimpl*.
      xchange* SChunkMaybeOwned_Owned. congruence.
      xunfold SChunk. xsimpl*. } }
  { asserts ? : (k>0).
    { rew_index* in *. }
    rewrite read_cons_pos in *; try easy.
    xsimpl* (LF :: LS[k - 1:=LS[k - 1][length LS[k - 1] - vi:=x]]).
    { do 2 constructor*.
      { rewrite HL. rewrite* update_cons_pos. math. }
      { applys* Forall_update.
        unfold IsFull. rew_list.
        applys* (>> Forall_mem_inv Etf).
        applys mem_read. rew_index* in *. }
      { intros.
        rewrite <- length_zero_eq_eq_nil, length_update, length_zero_eq_eq_nil.
        apply* Etn. } }
    { xunfold ListOf. xsimpl*.
      xchange* SChunkMaybeOwned_Owned. congruence.
      xunfold SChunk. xpull. intros.
      math_rewrite* (1 + length t - length ts - 1 - 1 = k-1).
      xsimpl*. } }
  { subst k. rew_list in SIs. rew_list*. }
Qed.

Lemma set_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A)
  (st:StackState A) (e:estack_ A) (i:int) (it:iterator_ A) (x:A),
  i <> length L ->
  SPEC (set it x)
    PRE (\$(If M = \{} then 6 else length L + K + 10)
           \* e ~> EStackInState st M L \* it ~> Iterator st i)
    INV (Shared M)
    POSTUNIT (\exists st', e ~> EStackInState st' M (L[i:=x]) \* it ~> Iterator st' i
                        \* \[If M = \{} then st=st' else True]).
Proof.
  xtriple.
  xchange estackInState_inv_schunks_length. intros.
  xapp* set_spec_low_bound.
  intros st'. xsimpl* st'.
  unfold set_cost. case_if*.
Qed.

Hint Extern 1 (RegisterSpec set) => Provide set_spec.
