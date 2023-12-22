Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import List_proof.

From TLC Require Import LibListZ LibMap.

Set Loose Hint Behavior "Strict".

Require Import Mono.

Require Import EChunk_proof.
Require Import Memory Transtack_ml.
Require Import TranstackCommon.
Require Import TranstackEphemeral_aux.

Require Import Iterator_ml Iterator_proof.
Require Import Iterator_derived.

Import Ephemeral.

(**************************************)
(** Standalone Ephemeral Stacks *)

(* Standalone EStack: the predicate hides its memory. *)
Definition SEStack A {IA:Inhab A} {EA:Enc A}
  (L:list A) (e:estack_ A) : hprop :=
  Shared (@empty A) \* e ~> EStack \{} L.

Ltac derive :=
  xtriple; xunfold SEStack;
  now xgo*.

(**************************************)
(** Specification *)

Lemma ecreate_spec : forall A (IA:Inhab A) (EA:Enc A) (d:A),
  SPEC (ecreate d)
    PRE (\$(K+4))
    POST (fun e => e ~> SEStack (@nil A)).
Proof.
  xtriple. xunfold SEStack.
  xapp ecreate_spec_fresh_memory.
  now xgo*.
Qed.

Lemma eis_empty_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) (L:list A),
  SPEC (eis_empty e)
     PRE (\$2)
     INV (e ~> SEStack L)
     POST \[= isTrue (L=nil)].
Proof. derive. Qed.

Lemma epeek_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) (L: list A),
  L <> nil ->
  SPEC (epeek e)
    PRE (\$5)
    INV (e ~> SEStack L)
    POST (fun x => \exists L', \[L = x::L']).
Proof. derive. Qed.

Lemma epop_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) (L: list A),
  L <> nil ->
  SPEC (epop e)
    PRE (\$11 \* e ~> SEStack L)
    POST (fun x => \exists L', \[L = x::L'] \* e ~> SEStack L').
Proof. derive. Qed.

Lemma epush_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) (x:A) (L: list A),
  SPEC (epush e x)
    PRE (\$7 \* e ~> SEStack L)
    POSTUNIT (e ~> SEStack (x::L)).
Proof. derive. Qed.

(* An InState predicate for standalone estacks. *)

Definition SEStackInState A {IA:Inhab A} {EA:Enc A}
  (st:StackState A) (L:list A) (e:estack_ A) : hprop :=
  Shared (@empty A) \* e ~> EStackInState st \{} L.

Lemma SEStackInState_eq : forall A (IA:Inhab A) (EA:Enc A) L (e:estack_ A),
  e ~> SEStack L = \exists st, e ~> SEStackInState st L.
Proof.
  intros. xunfold SEStackInState. xunfold SEStack. do 2 xunfold EStack.
  xsimpl*.
Qed.

Ltac derive ::=
  xtriple; xunfold SEStackInState;
  now xgo*.

Lemma finished_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) st L (i:int) (it:iterator_ A),
  SPEC (finished it)
    PRE (\$1)
    INV (e ~> SEStackInState st L \* it ~> Iterator st i)
    POST \[= isTrue (i = length L)].
Proof. derive. Qed.

Lemma get_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) st L (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (get it)
    PRE (\$3)
    INV (e ~> SEStackInState st L \* it ~> Iterator st i)
    POST \[= L[i]].
Proof. derive. Qed.

Lemma move_spec : forall A (IA:Inhab A) (EA:Enc A) (e:estack_ A) (L:list A) st
  (L:list A) (i:int) (it:iterator_ A),
  i <> length L ->
  SPEC (move it)
    PRE (\$4 \* it ~> Iterator st i)
    INV (e ~> SEStackInState st L)
    POSTUNIT (it ~> Iterator st (i+1)).
Proof. derive. Qed.

Lemma set_spec : forall A (IA:Inhab A) (EA:Enc A) (L:list A)
  (st:StackState A) (e:estack_ A) (i:int) (it:iterator_ A) (x:A),
  i <> length L ->
  SPEC (set it x)
    PRE (\$6 \* e ~> SEStackInState st L)
    INV (it ~> Iterator st i)
    POSTUNIT (e ~> SEStackInState st (L[i:=x])).
Proof.
  xtriple. xunfold SEStackInState. xpull. intros.
  xapp* set_spec_without_sharing.
  xsimpl*.
Qed.
