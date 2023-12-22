Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

Require Import ListMisc.

Require Import EChunk_proof.
Require Import SChunkShared_derived.

Require Import Transtack_ml TranstackCommon.
Require Import TranstackEphemeral_aux TranstackPersistent_aux.

Require Import Iterator_ml.
Require Import Iterator_tools.
Require Import Iterator_proof.

Set Loose Hint Behavior "Strict".

(**************************************)
(** Derived proofs of Iterators for EStack. *)

Ltac derive S M :=
  xtriple;
  xchange* S; intros;
  xapp*; unfold protect; xsimpl*; try split*;
  xunfold EStackInState; xsimpl*.

Module Ephemeral.

Lemma finished_spec_ephemeral : forall A (IA:Inhab A) (EA:Enc A) M e st L (i:int) (it:iterator_ A),
  SPEC (finished it)
    PRE (\$1)
    INV (e ~> EStackInState st M L \* it ~> Iterator st i)
    POST \[= isTrue (i = length L)].
Proof. derive Stacked_of_estack M. Qed.

Hint Extern 1 (RegisterSpec finished) => Provide finished_spec_ephemeral.

Lemma get_spec_ephemeral : forall A (IA:Inhab A) (EA:Enc A) M e st L (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (get it)
    PRE (\$3)
    INV (Shared M \* e ~> EStackInState st M L \* it ~> Iterator st i)
    POST \[= L[i]].
Proof. derive Stacked_of_estack M. Qed.

Hint Extern 1 (RegisterSpec get) => Provide get_spec_ephemeral.

Lemma move_spec_ephemeral : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (e:estack_ A) (L:list A) st
  (L:list A) (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (move it)
    PRE (\$4 \* it ~> Iterator st i)
    INV (e ~> EStackInState st M L)
    POSTUNIT (it ~> Iterator st (i+1)).
Proof. derive Stacked_of_estack M. Qed.

Hint Extern 1 (RegisterSpec move) => Provide move_spec_ephemeral.

Lemma set_spec_with_sharing : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A)
  (st:StackState A) (e:estack_ A) (i:int) (it:iterator_ A) (x:A),
  i <> length L ->
  SPEC (set it x)
    PRE (\$(length L + K + 10) \* e ~> EStackInState st M L \* it ~> Iterator st i)
    INV (Shared M)
    POSTUNIT (\exists st', e ~> EStackInState st' M (L[i:=x]) \* it ~> Iterator st' i).
Proof.
  lets ? : capacity_spec.
  xtriple. xgo*.
  case_if*.
Qed.

Lemma set_spec_without_sharing : forall A (IA:Inhab A) (EA:Enc A) (L:list A)
  (st:StackState A) (e:estack_ A) (i:int) (it:iterator_ A) (x:A),
  i <> length L ->
  SPEC (set it x)
    PRE (\$6 \* e ~> EStackInState st \{} L)
    INV (Shared (@empty A) \* it ~> Iterator st i)
    POSTUNIT (e ~> EStackInState st \{} (L[i:=x])).
Proof.
  lets ? : capacity_spec.
  xtriple. xgo*; case_if*.
Qed.

End Ephemeral.

(** Derived proofs of Iterators for PStack. *)
Module Persistent.

Lemma finished_spec_persistent : forall A (IA:Inhab A) (EA:Enc A) M p st L (i:int) (it:iterator_ A),
  PStackInState st M L p ->
  SPEC (finished it)
    PRE (\$1)
    INV (it ~> Iterator st i)
    POST \[= isTrue (i = length L)].
Proof. derive Stacked_of_pstack M. Qed.

Hint Extern 1 (RegisterSpec finished) => Provide finished_spec_persistent.

Lemma get_spec_persistent : forall A (IA:Inhab A) (EA:Enc A) M p st L (i:int) (it:iterator_ A),
  PStackInState st M L p ->
  i <> length L ->
  SPEC (get it)
    PRE (\$3)
    INV (Shared M \* it ~> Iterator st i)
    POST \[= L[i]].
Proof. derive Stacked_of_pstack M. Qed.

Hint Extern 1 (RegisterSpec get) => Provide get_spec_persistent.

Lemma move_spec_persistent : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) p st (L:list A) (i:int) (it:iterator_ A),
  PStackInState st M L p ->
  i <> length L ->
  SPEC (move it)
    PRE (\$4 \* it ~> Iterator st i)
    POSTUNIT (it ~> Iterator st (i+1)).
Proof. derive Stacked_of_pstack M. Qed.

Hint Extern 1 (RegisterSpec move) => Provide move_spec_persistent.

End Persistent.

Section PIterator.

Import Persistent.

Definition PIterator A {EA:Enc A} {IA:Inhab A}
  M (L:list A) (it:iterator_ A): hprop :=
  \exists p st L' i,
      \[PStackInState st M L' p] \* \[0 <= i <= length L'] \* \[L = drop i L']
       \* it ~> Iterator st i.

Lemma of_pstack_spec_piter : forall A (EA:Enc A) (IA: Inhab A) M (L:list A) (p:pstack_ A),
  PStack M L p ->
  SPEC (of_pstack p)
    PRE (\$2)
    POST (fun it => it ~> PIterator M L).
Proof.
  introv HP. rewrite PStack_eqInState in HP. destruct HP.
  xtriple. xunfold PIterator.
  xapp*.
  intros.
  xsimpl*.
Qed.

Lemma finished_spec_piter : forall A (IA:Inhab A) (EA:Enc A) M L (it:iterator_ A),
  SPEC (finished it)
    PRE (\$1)
    INV (it ~> PIterator M L)
    POST \[= isTrue (L = nil)].
Proof.
  xtriple. xunfold PIterator. xpull. intros ? ? L' i. intros.
  xapp*. xsimpl*.
  split; intros E; subst.
  { rew_listx*. }
  { apply (f_equal (@length _)) in E.
    autorewrite with rew_list in *; math. }
Qed.

Lemma get_spec_piter : forall A (IA:Inhab A) (EA:Enc A) M L (it:iterator_ A),
  L <> nil ->
  SPEC (get it)
    PRE (\$3)
    INV (Shared M \* it ~> PIterator M L)
    POST (fun x => \exists L', \[L = x::L']).
Proof.
  xtriple. xunfold PIterator. xpull. introv ? ? HL.
  destruct L; try easy.
  xapp*.
  { intros. subst. rewrite drop_at_length in *. auto. }
  xsimpl*; try easy. fequal*.
  symmetry in HL.
  lets* (?&?) : drop_eq_cons_inv HL.
Qed.

Lemma move_spec_piter : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L:list A) (it:iterator_ A),
  L <> nil ->
  SPEC (move it)
    PRE (\$4 \* it ~> PIterator M L)
    POSTUNIT (\exists x L', \[L = x::L'] \* it ~> PIterator M L').
Proof.
  xtriple. xunfold PIterator. xpull. intros ? ? L' i ? ? HL.
  destruct L; try easy.
  asserts ? : (i <> length L').
  { intros ->. rew_list* in *. }
  xapp*. xsimpl*.
  symmetry in HL.
  lets* (?&?) : drop_eq_cons_inv HL.
  subst. fequal*.
Qed.

End PIterator.
