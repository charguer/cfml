(**

This file defines the [Group] predicate, for iterated separating
conjunction over a map.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From CFML Require Import WPHeader WPBuiltin WPLibCommon SepBase SepLifted.
From TLC Require Import LibSet LibMap.

(** [Group R M] describes the ownership of all the heap predicates
    of the form [x ~> R X] where [x] is bound to [X] in the finite
    map [M]. *)

Definition Group a A (G:htype A a) (M:map a A) : hprop :=
  (fold sep_monoid (fun x X => x ~> G X) M)
    \* \[LibMap.finite M].

Lemma haffine_Group : forall a A (IA:Inhab A) (G:htype A a) (M:map a A),
  haffine_repr G ->
  haffine (Group G M).
Proof using.
  introv IA HG. unfold Group. rewrite hstar_comm.
  applys haffine_hstar_hpure_l. intros HF.
  applys* LibMap.fold_induction.
  { apply Comm_monoid_sep. }
  all:simpl; intros; xaffine.
Qed.

Hint Resolve haffine_Group : haffine.

Section GroupOps.
Hint Resolve Monoid_sep Comm_monoid_sep.

(** Operations on groups *)

Lemma Group_create : forall a A (R : htype A a),
  \[] ==> Group R \{}.
Proof using.
  intros. unfold Group. xsimpl.
  { unfolds. applys finite_empty. }
  { rewrite* LibMap.fold_empty. }
Qed.

Lemma Group_singleton : forall a A (R: htype A a) (x:a) (X:A),
    x ~> R X ==> Group R (x \:= X).
Proof.
  intros. unfold Group. xsimpl.
  { unfolds. applys finite_single. }
  { rewrite* LibMap.fold_single. }
Qed.

Lemma Group_heapdata_single : forall a (x:a) A `{Inhab A} (M:map a A) (R:htype A a) X,
  Heapdata R ->
  Group R M \* (x ~> R X) ==+> \[x \notindom M].
Proof.
  introv IA HR. tests: (x \indom M).
  { (* Case [x \indom M] *)
    match goal with |- _ ==> ?X => generalize X as G; intros end.
    unfold Group. xpull; intros FM.
    rewrite (eq_union_restrict_remove_one C).
    rewrite~ LibMap.fold_union.
    { simpl. rewrite* LibMap.fold_single.
      xchange* (>> Heapdata_false x). }
    { unfolds. applys~ finite_remove. }
    { unfolds.  applys finite_single. }
    { rewrite LibMap.disjoint_eq_disjoint_dom. rewrite dom_single.
       rewrite dom_remove. rewrite disjoint_single_r_eq.
       unfold notin. rewrite in_remove_eq.
       rewrite notin_single_eq. rew_logic*. } }
  { xsimpl*. }
Qed.

(* Note: technically, `{Inhab A} is derivable from the fact that [x] exists,
   but it's easier to have the hypothesis to justify the read operation. *)

Lemma Group_add_fresh : forall a (x:a) A `{Inhab A} (M:map a A) (R:htype A a) X,
  Heapdata R ->
  Group R M \* (x ~> R X) ==> Group R (M[x:=X]) \* \[x \notindom M].
Proof using.
  introv IA HR.
  xchange* Group_heapdata_single. intros.
  unfold Group. xpull; intros FM.
  rewrite LibMap.update_eq_union_single.
  rewrite~ LibMap.fold_union.
  { simpl. rewrite~ LibMap.fold_single. xsimpl*.
    applys~ finite_union. applys finite_single. }
  { applys finite_single. }
  { rewrite LibMap.disjoint_eq_disjoint_dom. rewrite dom_single.
    rewrite disjoint_single_r_eq. auto. }
Qed. (* TODO: factorize proof better, improve set manipulations *)

Lemma Group_add : forall a (x:a) A `{IA:Inhab A} (M:map a A) (R:htype A a) X,
  Heapdata R ->
  Group R M \* (x ~> R X) ==> Group R (M[x:=X]).
Proof using. introv IA HR. xchange~ Group_add_fresh. Qed.

Arguments Group_add [a] x [A] {IA}.

Lemma Group_rem : forall a (x:a) A (IA:Inhab A) (M:map a A) (R:htype A a),
  x \indom M ->
  Group R M = Group R (M \- \{x}) \* (x ~> R (M[x])).
Proof using.
  introv Dx. unfold Group.
  forwards~ E: LibMap.eq_union_restrict_remove_one x M.
  asserts Fx: (LibMap.finite (x \:= M[x])).
  { applys finite_single. }
  asserts Dis: ((M \-- x) \# (x \:= M[x])).
  { rewrite LibMap.disjoint_eq_disjoint_dom. rewrite dom_single.
    rewrite dom_remove. rewrite disjoint_single_r_eq.
    unfold notin. rewrite in_remove_eq.
    rewrite notin_single_eq. rew_logic*. }
  applys himpl_antisym.
  { xpull; intros FM.
    asserts Fr: (LibMap.finite (M \-- x)).
    { applys~ finite_remove. }
    rewrite E at 1. rewrite* LibMap.fold_union.
    rewrite~ LibMap.fold_single. simpl. xsimpl*. }
  { xpull; intros FM'.
    asserts FM: (LibMap.finite M).
    { lets K: FM'. unfolds in K. rewrite dom_remove in K.
      applys finite_remove_one_inv K. }
    rewrite E at 3. rewrite~ LibMap.fold_union.
    rewrite~ LibMap.fold_single. simpl. xsimpl*. }
Qed. (* TODO: cleanup and factorize with earlier proofs *)

Arguments Group_rem [a] x [A] {IA}.

Lemma Group_rem_again : forall a (x:a) A `{IA:Inhab A} (M:map a A) (R:htype A a) X,
  Group R (M[x:=X]) ==> Group R (M \-- x) \* (x ~> R X).
Proof using.
  intros a x A IA M R X. rewrites (>> Group_rem x).
  { rewrite dom_update. apply in_union_r. applys* in_single; typeclass. }
  { rewrite read_update_same. rewrite* remove_one_update. }
Qed.

Arguments Group_rem_again [a] x [A] {IA}.

Lemma Group_add_again : forall a (x:a) A {IA:Inhab A} (M:map a A) (R:htype A a) X,
  x \indom M ->
  Group R (M \-- x) \* (x ~> R X) = Group R (M[x:=X]).
Proof using.
  introv IA Dx. rewrite~ (Group_rem x (M[x:=X])).
  rewrite LibMap.read_update_same. rewrite~ LibMap.remove_one_update.
  rewrite dom_update. set_prove.
Qed.

Arguments Group_add_again [a] x [A] {IA}.

Lemma Group_star_disjoint : forall a A `{Inhab A} (R:htype A a) (M1 M2:map a A),
  Heapdata R ->
  (Group R M1 \* Group R M2) ==+> \[ M1 \# M2 ].
Proof.
  introv IA HG.
  tests D: (M1 \# M2). { xsimpl*. }   (* TODO: lemma [xsimpl_absurd]. *)
  rewrite~ LibMap.disjoint_eq_disjoint_dom in D.
  rewrite disjoint_not_eq in D.
  destruct D as (x&D1&D2).
  xchange* (>> Group_rem x M1).
  xchange* (>> Group_rem x M2).
  xchange (heapdata x x).
Qed.
(* LATER: add lemma: ~ (M1 \# M2) -> exists x, x \indom M1 /\ x \indom M2 *)

Lemma Group_join : forall a A `{Inhab A} (R:htype A a) (M1 M2:map a A),
  Heapdata R ->
  Group R M1 \* Group R M2 ==> Group R (M1 \u M2) \* \[ M1 \# M2 ].
Proof.
  introv IA HG. xchange~ (>> Group_star_disjoint M1 M2). intros D.
  unfold Group. xpull; intros F1 F2. rewrite~ LibMap.fold_union.
  simpl. xsimpl*.
  { apply~ finite_union. }
Qed.

Lemma Group_split : forall a A {IA:Inhab A} (R : htype A a) (M1 M2 : map a A),
  dom M1 \# dom M2 ->
  Group R (M1 \u M2) ==> Group R M1 \* Group R M2.
Proof.
  intros.
  unfold Group. xpull. intros HF.
  apply finite_union_inv in HF.
  rewrite* fold_union; eauto with finite.
  xsimpl*.
Qed.

Lemma Group_gc : forall a A `{Inhab A} (R:htype A a) (M1 M2:map a A),
  haffine_repr R ->
  M1 \c M2 ->
  Group R M2 ==> Group R M1 \* \GC.
Proof.
  intros.
  rewrites (>> eq_union_restrict_remove (dom M1) M2).
  rewrite* restrict_incl.
  xchange* Group_split.
  { rewrite dom_remove. rew_set. intros x. rewrite set_in_remove_eq.
    firstorder. }
  { xsimpl*. }
Qed.

Lemma Group_focus : forall a (x:a) A (IA:Inhab A) (M:map a A) (R:htype A a),
  x \indom M ->
  Group R M = (x ~> R (M[x])) \* (\forall v, (x ~> R v) \-* Group R (M[x:=v])).
Proof.
  introv Dx. xsimpl.
  { rewrites* (>> Group_rem x). xsimpl; intros v.
    xchanges* Group_add_again. }
  { xchange (hforall_specialize M[x]).
    rewrite* update_same. }
Qed.

Lemma Group_focus_no_update : forall a (x:a) A (IA:Inhab A) (M:map a A) (R:htype A a),
  x \indom M ->
  Group R M = (x ~> R (M[x])) \* ((x ~> R (M[x])) \-* Group R M).
(* Consequence of Group_focus but not easier. *)
Proof.
  introv Dx. xsimpl.
  { rewrite hwand_eq_hexists_hstar_hpure.
    rewrites* (>> Group_rem x). xsimpl. xsimpl. }
Qed.

End GroupOps.
