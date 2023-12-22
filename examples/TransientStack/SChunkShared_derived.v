Set Implicit Arguments.
From CFML Require Import WPLib Stdlib LibSepGroup Array_proof.
From TLC Require Import LibList LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import Mono.

Require Import ListMisc.

Require Import Id_ml Id_proof.

Require Import EChunk_ml EChunk_proof.

Require Import SChunk_ml SChunk_proof.

Require Export Memory.

(***************************************************)
(** Definition of the representation predicate of shared schunks. *)

Definition SChunkShared {A} {IA:Inhab A} {EA:Enc A}
           (M:Memory A) (L:list A) (s:schunk_ A) : Prop :=
  let E := M.(echunks) in
  s.(support') \indom E
  /\ SChunk_inv false E[s.(support')] L s.

(***************************************************)
(** Monotony lemmas. *)

Lemma SChunk_inv_mon : forall A (IA:Inhab A) (EA:Enc A) b (L LC LC':list A) (s:schunk_ A),
  Suffix LC LC' ->
  SChunk_inv b LC L s ->
  SChunk_inv false LC' L s.
Proof.
  introv (n,(HLC,Hn)) Hs.
  lets [Hl ? Hv] : (SChunk_inv_share Hs).
  constructor*.
  { intros i Hi. rewrite* Hl. subst.
    list_cases*. fequals*. }
  { subst. autorewrite with rew_listp in *; auto_star. }
Qed.

Lemma SChunkShared_mon : forall A (IA:Inhab A) (EA:Enc A) (M M':Memory A) (L:list A) (s:schunk_ A),
  Extend M M' ->
  SChunkShared M L s ->
  SChunkShared M' L s.
Proof.
  introv (MM',?) (HDp,HIp).
  lets (HD'p, HI) : MM' HDp.
  split*.
  applys* SChunk_inv_mon.
Qed.

Lemma SChunkShared_rel_incl_Preserve : forall A (IA:Inhab A) (EA:Enc A) (M M':Memory A),
  Extend M M' ->
  rel_incl (SChunkShared M) (SChunkShared M').
Proof. intros. intros L x. apply* SChunkShared_mon. Qed.

(***************************************************)
(** Focus lemmas. *)

Definition upd_memory {A} {IA:Inhab A} {EA:Enc A} (M:Memory A) (e:echunk_ A) (L:list A) :=
  mk_m (M.(echunks)[e:=L]) (M.(ids)).

Lemma focus_shared : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (s:schunk_ A) (L:list A),
  SChunkShared M L s ->
  Shared M ==>
    s ~> SChunk false M.(echunks)[s.(support')] L \*
    \forall v,  s.(support') ~> EChunk v \-* Shared (upd_memory M s.(support') v).
Proof.
  introv []. unfold Shared.
  xchanges* (>> Group_focus (support' s) (echunks M)).
  xunfolds* SChunk.
  intros x. xchange (>> hforall_specialize x).
Qed.

Lemma upd_memory_same : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (x:echunk_ A),
  x \indom M.(echunks) ->
  upd_memory M x M.(echunks)[x] = M.
Proof.
  intros.
  destruct M. unfold upd_memory.
  rewrite* update_same.
Qed.

Lemma focus_shared_same : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (s:schunk_ A) (L:list A),
  SChunkShared M L s ->
  Shared M ==>
    s ~> SChunk false M.(echunks)[s.(support')] L \*
    (s.(support') ~> EChunk M.(echunks)[s.(support')] \-* Shared M).
Proof.
  introv Hs. lets [] : Hs.
  xchange* focus_shared.
  xchange* (>> hforall_specialize (M.(echunks)[s.(support')])).
  rewrite* upd_memory_same.
Qed.

(***************************************************)
(** Actual formalization. *)

Ltac derive p :=
  xtriple;
  xchange* focus_shared_same;
  xgo*;
  xopen p; xsimpl*.

Lemma echunk_of_schunk_spec : forall A (IA:Inhab A) (EA:Enc A) M L (s:schunk_ A),
  SChunkShared M L s ->
  SPEC (echunk_of_schunk s)
    PRE (\$(K+2))
    INV (Shared M)
    POST (fun c => c ~> EChunk L).
Proof. derive s. Qed.

Hint Extern 1 (RegisterSpec echunk_of_schunk) => Provide echunk_of_schunk_spec.

Lemma schunk_peek_spec : forall A (IA:Inhab A) (EA:Enc A) M L (s:schunk_ A),
  L <> nil ->
  SChunkShared M L s ->
  SPEC (schunk_peek s)
    PRE (\$3)
    INV (Shared M)
    POST (fun x => \exists L', \[L = x::L']).
Proof. derive s. Qed.

Hint Extern 1 (RegisterSpec schunk_peek) => Provide schunk_peek_spec.

Lemma schunk_is_empty_spec : forall A (IA:Inhab A) (EA:Enc A) M (s:schunk_ A) (L:list A),
  SChunkShared M L s ->
  SPEC (schunk_is_empty s)
    PRE (\$1)
    INV (Shared M)
    POST \[= isTrue (L=nil)].
Proof. derive s. Qed.

Hint Extern 1 (RegisterSpec schunk_is_empty) => Provide schunk_is_empty_spec.

Lemma schunk_is_full_spec : forall A (IA:Inhab A) (EA:Enc A) M (s:schunk_ A) (L:list A),
  SChunkShared M L s ->
  SPEC (schunk_is_full s)
    PRE (\$1)
    INV (Shared M)
    POST \[= isTrue (IsFull L)].
Proof. derive s. Qed.

Hint Extern 1 (RegisterSpec schunk_is_full) => Provide schunk_is_full_spec.

Lemma schunk_pop_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (s:schunk_ A),
  SChunkShared M L s ->
  L <> nil ->
  SPEC (schunk_pop s)
    PRE (\$3)
    INV (Shared M)
    POST (fun '(s',x) =>
            \exists L', \[SChunkShared M L' s' /\ L = x::L' /\ s'.(owner') = s.(owner')]).
Proof.
  introv HMp ?.
  xtriple; simpl.
  xchange* focus_shared_same.
  xapp*; intros ([],?).
  xpull; intros L' (?&?&?); simpl in *.
  xchange SChunk_eq; intros.
  destruct s.
  xsimpl*; simpl in *.
  { destruct HMp. split*. constructor*. }
  { subst. xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec schunk_pop) => Provide schunk_pop_spec.

Ltac hor_case :=
  rewrite hor_eq_exists_bool; xpull; intros [].

Lemma schunk_push_spec : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A) (L: list A) (s:schunk_ A) (x:A),
  SChunkShared M L s ->
  ~ IsFull L ->
  SPEC (schunk_push s x)
    MONO M
    PRE (\$(K+4))
    POST (fun M' s' => \[SChunkShared M' (x::L) s']
                     \* \[owner' s' = owner' s \/ owner' s' = None] ).
Proof.
  introv HMp HL. destruct M as (M,I).
  lets [] : HMp.
  xtriple; simpl.
  xchange* focus_shared.
  xapp*; intros s' ?.
  hor_case.
  { xopen s'; intros E Hs'.
    xchange (hforall_specialize (x::M[support' s])).
    xsimpl* (mk_m M[support' s:=x :: M[support' s]] I).
    { eauto with extend preserve suffix. }
    { constructor*; rewrite E in *; simpl; rew_maps*. }
    { rewrite E in *; xsimpl. } }
  { xopen s; intros Hs.
    xopen s'; intros Hs'.
    xchange* hforall_specialize; rewrite* upd_memory_same.
    unfold Shared.
    xchange* (>> Group_add_fresh (support' s') M). intros.
    xsimpl* (mk_m (M[support' s':=x :: L]) I).
    { eauto with extend preserve. }
    { constructor*; simpl; rew_map*.
      applys* SChunk_inv_share. } }
Qed.

Hint Extern 1 (RegisterSpec schunk_push) => Provide schunk_push_spec.
