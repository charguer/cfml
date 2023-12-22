Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup List_proof Array_proof.
From TLC Require Import LibListZ.

Require Import ListMisc.

Require Import Id_ml Id_proof.

Require Import ListIterator_ml ListIterator_proof.

Require Import EChunk_ml EChunk_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml TranstackCommon.
Require Import TranstackEphemeral_aux TranstackPersistent_aux.

Require Import Iterator_ml.

(**************************************)
(** Focus *)

(* Needed for protect as xchange seems to simplify magic wands. *)
Definition protect {A} (x:A) := x.

(* We can focus an element of ListOf. *)
Lemma ListOf_focus : forall A B (IA:Inhab A) (IB:Inhab B) (R:B -> A -> hprop) (xs:list A) (ys:list B) (k:int),
  index xs k ->
  xs ~> ListOf R ys ==>
  xs[k] ~> R ys[k] \* protect (xs[k] ~> R ys[k] \-* xs ~> ListOf R ys).
Proof.
  introv Hk. revert xs k Hk.
  induction ys; intros xs i Hk; rew_index in Hk.
  { xchange ListOf_nil_l. intro_subst.
    rew_list in Hk. math. }
  { xchange ListOf_cons_l. intros x' xs' ?. subst.
    do 2 rewrite read_cons_case.
    case_if as C; xunfold ListOf; unfold protect; xsimpl*.
    xchanges* (>> IHys xs').
    unfold protect. xsimpl. }
Qed.

Lemma ListOf_focus_update : forall A B (IA:Inhab A) (IB:Inhab B) (R:B -> A -> hprop) (xs:list A) (ys:list B) (k:int),
  index xs k ->
  xs ~> ListOf R ys ==>
  xs[k] ~> R (ys[k]) \* (\forall x' y', x' ~> R y' \-* xs[k:=x'] ~> ListOf R (ys[k:=y'])).
Proof.
  introv Hk. revert xs k Hk.
  induction ys; intros xs i Hk; rew_index in Hk.
  { xchange ListOf_nil_l. intro_subst.
    rew_list in Hk. math. }
  { xchange ListOf_cons_l. intros x' xs' ?. subst.
    do 2 rewrite read_cons_case.
    case_if as C; xsimpl*.
    { intros z' y'. subst. repeat rewrite update_zero.
      xunfold ListOf. xsimpl. }
    { xchange ListOf_inv_length. intros.
      xchanges* (IHys xs'); intros z' y'.
      xchange (hforall_specialize z').
      xchange (hforall_specialize y').
      rew_list in Hk.
      repeat rewrite* update_cons_pos. } }
Qed.

Lemma Group_focus_no_update : forall a (x:a) A (IA:Inhab A) M (R:htype A a),
  x \indom M ->
  Group R M = (x ~> R (M[x])) \* protect ((x ~> R M[x]) \-* Group R M).
Proof.
  intros. unfold protect.
  apply* Group_focus_no_update.
Qed.

Lemma SChunkMaybeOwned_focus : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) v (L:list A) p,
  Shared M \* p ~> SChunkMaybeOwned M v L ==>
  \exists LC, p ~> SChunk false LC L \* protect (p ~> SChunk false LC L \-* (Shared M \* p ~> SChunkMaybeOwned M v L)).
Proof.
  intros. unfold protect.
  xunfold SChunkMaybeOwned.
  case_if*; xpull.
  { xunfold SChunkUniquelyOwned.
    xunfold SChunk.
    xsimpl*. intros. apply* SChunk_inv_share. }
  { intros (?&Hp). destruct M as (M,I); unfold Shared; simpl in *.
    xchange* (>>Group_focus_no_update (support' p) M).
    xunfold SChunk. xsimpl*.
    { intros. constructor*. }
    { intros. unfold protect. xsimpl. } }
Qed.

Lemma focus : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A)
  (t:list (schunk_ A)) (v:option Id.t_) (LS:list (list A)) (i:int),
  index t i ->
  Shared M \* t ~> ListOf (SChunkMaybeOwned M v) LS ==>
  \exists (LC:list A), t[i] ~> (SChunk false LC LS[i]) \*
           protect (t[i] ~> (SChunk false LC LS[i]) \-* (Shared M \* t ~> ListOf (SChunkMaybeOwned M v) LS)).
Proof.
  intros.
  xchange* (>> ListOf_focus).
  xchange SChunkMaybeOwned_focus. intros LC.
  xsimpl* LC. unfold protect. xsimpl.
Qed.

(**************************************)
(** sum_size *)

Definition sum_size A (l:list (schunk_ A)) :=
  sum (map view' l).

Lemma sum_size_cons : forall A (x:schunk_ A) xs,
    sum_size (x::xs) = view' x + sum_size xs.
Proof. intros. unfold sum_size. rew_listx*. Qed.

Lemma sum_size_app : forall A (xs ys: list (schunk_ A)),
    sum_size (xs++ys) = sum_size xs + sum_size ys.
Proof. intros. unfold sum_size. rew_listx*. Qed.

Hint Rewrite sum_size_cons sum_size_app : rew_listx.

(**************************************)
(** Stacked: a predicated unifying estacks and pstacks. *)

Notation Stack_inv' L LFS :=
  (exists LF LS, LFS = LF::LS /\ Stack_inv L LF LS).

(* [Stacked] is the invariant needed for working with Iterators.
   It is entailed by both EStack and PStack *)
Definition Stacked A {EA:Enc A} {IA:Inhab A}
           (M:Memory A) (L:list A) (st:StackState A) LFS :=
  let (ft,v,u) := st in
    ft ~> ListOf (SChunkMaybeOwned M v) LFS
    \* \[Stack_inv' L LFS].

Lemma Stacked_eq : forall {A} {EA:Enc A} {IA:Inhab A}
  (st:StackState A) LFS (M:Memory A) (L:list A),
  Stacked M L st LFS =
  let (ft,v,u) := st in
    ft ~> ListOf (SChunkMaybeOwned M v) LFS
    \* \[Stack_inv' L LFS].
Proof. auto. Qed.

Lemma haffine_Stacked : forall A (IA:Inhab A) (EA:Enc A) (st:StackState A) LFS (M:Memory A) (L:list A),
  haffine (Stacked M L st LFS).
Proof.
  intros. destruct st. unfold Stacked. xaffine.
Qed.

Hint Resolve haffine_Stacked : haffine.

Tactic Notation "xopen_stacked" constr(st) :=
  xchange (Stacked_eq st); xpull.

Lemma estack_internals : forall A (IA:Inhab A) (EA:Enc A)
  (M:Memory A) f t (LF:list A) (LS:list (list A)) v,
  v <> None ->
  f ~> EChunk LF \* t ~> ListOf (SChunkMaybeOwned M v) LS =
  (schunk_make__ f (length LF) v :: t) ~> ListOf (SChunkMaybeOwned M v) (LF::LS).
Proof.
  intros. xunfold ListOf. xunfold SChunkMaybeOwned.
  xsimpl;
    repeat case_if*; try xpull; simpl in *; try math;
    xunfold SChunkUniquelyOwned;
    xunfold SChunk; xsimpl*; try (false*; fail).
  constructor*.
Qed.

Lemma Stacked_of_estack : forall A (IA:Inhab A) (EA:Enc A) M (st:StackState A) (L:list A) (e:estack_ A),
  e ~> EStackInState st M L ==>
  \exists LFS, Stacked M L st LFS \* protect (Stacked M L st LFS \-* e ~> EStackInStateDeep st LFS M L).
Proof.
  intros. destruct st as [ft ? ?]. unfold protect.
  xunfold EStackInState; xpull; intros LFS.
  xunfold EStackInStateDeep; xpull; introv HLFS Hft (->,->) He.
  destruct LFS; try congruence; injects HLFS.
  destruct ft; try congruence; injects Hft.
  lets [] : He.
  xchanges* estack_internals. { auto_false*. }
  rewrite Stacked_eq; xsimpl*. intros.
  xsimpl*.
  xchange* <- estack_internals. auto_false.
Qed.

Lemma MaybeOwned_none_of_Shared : forall A (IA:Inhab A) (EA:Enc A) M (t:list (schunk_ A)) L,
  Forall2 (SChunkShared M) L t ->
  \[] ==> t ~> ListOf (SChunkMaybeOwned M None) L.
Proof.
  induction t; destruct L; intros HL; inversion HL; subst.
  { xchange <- ListOf_nil. }
  { xunfold ListOf. xchange* IHt. xsimpl.
    xunfold SChunkMaybeOwned.
    case_if*; try (false*; fail).
    xsimpl*. }
Qed.

Lemma Stacked_of_pstack : forall A (IA:Inhab A) (EA:Enc A) M (st:StackState A) (L:list A) (p:pstack_ A),
  PStackInState st M L p ->
  \[] ==> \exists LFS, Stacked M L st LFS.
Proof.
  introv HP. destruct p as (pf,pt), st as [ft ?], HP as (LFS,(LF,(LS,(HLFS&Hei&?&?&[PS Pv])))).
  xsimpl* LFS.
  destruct LFS; try congruence; injects HLFS.
  destruct ft; try congruence; injects Hei.
  rew_listx in Pv.
  rewrite Stacked_eq; xsimpl*. subst id.
  now applys* MaybeOwned_none_of_Shared.
Qed.
