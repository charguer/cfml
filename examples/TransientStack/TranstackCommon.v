Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup Array_proof List_proof.

From TLC Require Import LibMap LibListZ.

Require Import Mono.

Require Import ListMisc.
Require Import Option_aux.

Require Import EChunk_ml EChunk_proof.

Require Import Id_ml Id_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml.

(***************************************)
(** Common for stacks *)

Record Stack_inv {A} {IA:Inhab A} {EA:Enc A}
       (L LF:list A) (LS:list (list A)) : Prop :=
  make_Stack_inv {
      stack_items : L = LF ++ concat LS;
      stack_tail_full : Forall (@IsFull A) LS;
      stack_tail_nil : LF = nil -> LS = nil;
    }.

(***************************************)
(** Inversion lemmas *)

Lemma Stack_inv_all_nil : forall A (IA:Inhab A) (EA:Enc A),
  @Stack_inv A IA EA nil nil nil.
Proof. constructor*; rew_listx*. Qed.

Hint Resolve Stack_inv_all_nil.

(* TODO BROKEN: rename to Stack_inv_front_single *)
Lemma Stack_inv_front_singl : forall A (IA:Inhab A) (EA:Enc A) (x:A) L LS,
  Stack_inv (x::L++concat LS) (x::nil) (L::LS) ->
  Stack_inv (L++concat LS) L LS.
Proof.
  introv [So Stf Stn].
  rew_listx in *; destruct Stf as (StfL,StfLS).
  constructor*.
  intros ->. apply NotFull_of_nil in StfL. false.
Qed.

Lemma Stack_inv_nil_front :
  forall A (IA:Inhab A) (EA:Enc A) (L LF:list A) (LS: list (list A)),
  Stack_inv L LF LS ->
  LF = nil <-> L = nil.
Proof.
  introv [Ho Htf Htn].
  split; intros E.
  { rewrite* Htn in Ho. }
  { destruct* LF. subst. rew_listx in E. false. }
Qed.

Lemma Stack_inv_length : forall A (IA:Inhab A) (EA:Enc A) (L:list A) LF LS,
  Stack_inv L LF LS ->
  length L = length LF + sum (map (@length _) LS).
Proof.
  introv [HL].
  rewrite HL.
  rew_list. rewrite* length_concat_eq_sum.
Qed.

(**************************************)
(** StackState *)

Record StackState (A:Type) : Type :=
  mk_st {
      schunks : list (schunk_ A);
      id : option Id.t_;
      ues : option (estack_ A)
    }.

Notation StackStateDeep A := (list (list A)).

(** Inversions on ListOf *)

Lemma ListOf_inv_length : forall (A B: Type) (R:A -> B -> hprop) (xs:list B) (ys:list A),
  xs ~> ListOf R ys ==+>
  \[length xs = length ys].
Proof.
  induction xs; intros ys.
  { destruct ys.
    { xsimpl*. }
    { xchange ListOf_nil_r. } }
  { destruct ys.
    { xchange ListOf_nil_l. }
    { xchange ListOf_cons_r. intros ? ? E.
      injects E.
      xchange IHxs. intros. xsimpl*.
      xunfolds ListOf. } }
Qed.

Lemma ListOf_schunk_lengths : forall A (IA:Inhab A) (EA:Enc A)
   (M:Memory A) (v:option Id.t_) (t:list (schunk_ A)) (LS:list (list A)),
   t ~> ListOf (SChunkMaybeOwned M v) LS ==>
   (\[(map view' t) = (map (length (A:=A)) LS)]
   \* t ~> ListOf (SChunkMaybeOwned M v) LS).
Proof.
  intros. revert t. induction LS; intros t.
  { xchange ListOf_nil_l. intros.  xsimpl*. }
  { xchange ListOf_cons_l. intros y ys ?. subst.
    rew_listx* in *.
    xchange* IHLS. intros.
    xunfold (SChunkMaybeOwned (A:=A)).
    repeat case_if*; xpull.
    { xunfold SChunkUniquelyOwned.
      xopen y. intros Z. xunfold ListOf. xunfolds* SChunk.
      { destruct* Z. fequal*. }
      { rewrites (>> repr_eq y). repeat case_if*. xsimpl*. } }
    { intros Z. lets (?&[]) : Z.
      unfold protect. xunfold ListOf. xsimpl*.
      { fequal*. }
      { rewrite repr_eq. case_if*. xsimpl*. } } }
Qed.

Lemma Forall2_SchunkShared_inv_lengths : forall A (EA:Enc A) (IA: Inhab A)
  (M:Memory A) LS pt,
  Forall2 (SChunkShared M) LS pt ->
  map (view') pt = map (length (A:=A)) LS.
Proof.
  introv HF. revert pt HF.
  induction LS; intros pt HF; rew_listx.
  { apply Forall2_nil_l_inv in HF. rew_listx*. }
  { apply Forall2_cons_l_inv in HF.
    destruct HF as (x,(xs,(?&(?&[])&?))).
    subst. rew_listx*. fequals*. }
Qed.

(**************************************)
(** The valid_id predicate *)

Definition valid_id {A} (M:Memory A) (id:option Id.t_) :=
  match id with
  | None => True
  | Some x => x \indom M.(ids) end.

Lemma valid_id_mon : forall A (IA:Inhab A) (M M':Memory A) x,
  Extend M M' ->
  valid_id M x ->
  valid_id M' x.
Proof.
  introv (?&HD) ?.
  destruct x; simpl in*; try easy.
  eapply incl_inv. apply HD. easy.
Qed.
