Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.

Require Import EChunk_ml EChunk_proof.
Require Import Memory.
Require Import TranstackCommon TranstackEphemeral_aux TranstackPersistent_aux TranstackConversions_aux.

Require Import TranstackTest_ml.

(***************************************)
(** A test proof *)

Ltac extend_auto tt :=
  first [apply Extend_union_l|apply Extend_union_r|eauto with extend];
  try easy;
  try apply* disjoint_sym.

Ltac pstack_auto tt :=
  applys* PStack_mon;
  match goal with
  | |- Extend _ _ => extend_auto tt
  | _ => idtac end.

Ltac pstack_run :=
  match goal with
  | |- PStack _ _ _ =>
    simpl in *;
    repeat pstack_auto tt
  | _ => idtac end.

Ltac auto_tilde ::=
  auto_star;
  auto_false;
  pstack_run.

Ltac xassert_go tt :=
  xassert ; [ xgo | idtac ].

Tactic Notation "xassert_go" "*" :=
  xassert_go tt; auto_star.

Ltac ppop_post :=
  intros (?,?); xpull; intros ? (?&P); injects P.

Lemma contextualize : forall A (EA:Enc A) (IA:Inhab A) e M1 M2 (L:list A),
  Extend M1 M2 ->
  e ~> EStack M1 L \* Shared M2 ==> e ~> EStack M2 L \* Shared M2.
Proof. xchange* EStack_mon. Qed.

Lemma main_spec :
  SPEC (main tt)
       PRE (\$(20*capacity + 600))
       POST (fun (_:unit) => \[]).
Proof.
  xcf. xpay.
  xapp ecreate_spec_fresh_memory.
  xappn. intros.
  xappn~.
  intros ? ? P. injects P.
  xassert_go*.
  xappn*. intros.
  xapp~; intros.
  xapp~; intros.
  xapp~. ppop_post.
  xmatch. xassert_go*.
  xapp~. intros.
  xapp~. ppop_post.
  xmatch. xassert_go*.
  xchange contextualize. { simpl in *. eauto with extend. }
  xapp. intros.
  xapp~. ppop_post.
  xmatch. xassert_go*.
  xapp~. ppop_post.
  xmatch. xassert_go*.
  xapp~. intros.
  xapp. xapp.
  xapp~. auto_false. ppop_post.
  xmatch. xassert_go*.
  xapp. intros.
  xapp~. ppop_post.
  lets ? : capacity_spec.
  xgo*.
Qed.
