(**

This file formalizes mutable list examples in plain Separation Logic,
illustrating the direct use of triples on one example, and conducting
other proofs using characteristic formulae.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import LambdaCF LambdaStruct.
Generalizable Variables A B.

Ltac auto_star ::= jauto.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types v : val.


(* ********************************************************************** *)
(* * List cells *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

(** Identification of head and tail fields *)

Definition hd : field := 0%nat.
Definition tl : field := 1%nat.

(** [Mcell v q p] describes one list cell allocated at address [p],
  with head value [v] and tail value [q]. *)

Definition MCell (v:val) (q:val) (p:loc) :=
  (p `.` hd ~~~> v) \* (p `.` tl ~~~> q).


(* ---------------------------------------------------------------------- *)
(** Tactics *)

(** Tactic hack to make [hsimpl] able to cancel out [hfield]
    and [Mcell] predicates in heap entailment.
    Later won't be needed when using [~>] notation. *)

Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  | MCell _ _ _ => hcancel_try_same tt
  end.


(* ---------------------------------------------------------------------- *)
(** Properties of list cells *)

Lemma MCell_eq : forall (v:val) (q:val) (p:loc),
  MCell v q p = (p `.` hd ~~~> v) \* (p `.` tl ~~~> q).
Proof using. auto. Qed.

Lemma MCell_inv_not_null : forall p v q,
  (MCell v q p) ==+> \[p <> null].
  (* i.e. (MCell v q p) ==> (MCell v q p) \* \[p <> null]. *)
Proof using.
  intros. unfold MCell, hd.
  hchange~ (hfield_not_null p hd). hsimpl~.
Qed.

Arguments MCell_inv_not_null : clear implicits.

Lemma MCell_null_false : forall v q,
  (MCell v q null) ==> \[False].
Proof using. intros. hchanges~ (MCell_inv_not_null null). Qed.

Arguments MCell_null_false : clear implicits.

Lemma MCell_hstar_MCell_inv : forall p1 p2 x1 x2 y1 y2,
  MCell x1 y1 p1 \* MCell x2 y2 p2 ==+> \[p1 <> p2].
Proof using.
  intros. do 2 rewrite MCell_eq. tests C: (p1 = p2).
  { hchanges (@hstar_hfield_same_loc_disjoint p2 hd). }
  { hsimpl~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Access to list cells *)

(** Read to head *)

Definition val_get_hd := val_get_field hd.

Lemma triple_get_hd : forall p v q,
  triple (val_get_hd p)
    (MCell v q p)
    (fun r => \[r = v] \* (MCell v q p)).
Proof using.
  intros. unfold MCell. xapplys triple_get_field. auto.
Qed.

Hint Extern 1 (Register_spec val_get_hd) => Provide triple_get_hd.

(** Read to tail *)

Definition val_get_tl := val_get_field tl.

Lemma triple_get_tl : forall p v q,
  triple (val_get_tl p)
    (MCell v q p)
    (fun r => \[r = q] \* (MCell v q p)).
Proof using.
  intros. unfold MCell.
  xapplys triple_get_field. auto.
Qed.

Hint Extern 1 (Register_spec val_get_tl) => Provide triple_get_tl.

(** Write to head *)

Definition val_set_hd := val_set_field hd.

Lemma triple_set_hd : forall p v' v vq,
  triple (val_set_hd p v)
    (MCell v' vq p)
    (fun r => MCell v vq p).
Proof using.
  intros. unfold MCell. xapplys (triple_set_field v').
Qed.

Hint Extern 1 (Register_spec val_set_hd) => Provide triple_set_hd.

(** Write to tail *)

Definition val_set_tl := val_set_field tl.

Lemma triple_set_tl : forall p v q vq',
  triple (val_set_tl p q)
    (MCell v vq' p)
    (fun r => MCell v q p).
Proof using.
  intros. unfold MCell. xapplys (triple_set_field vq').
Qed.

Hint Extern 1 (Register_spec val_set_tl) => Provide triple_set_tl.


(* ---------------------------------------------------------------------- *)
(** Allocation of list cells *)

Definition val_new_cell :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2 in
    val_set_hd 'p 'x;;;
    val_set_tl 'p 'y;;;
    'p.

Lemma triple_alloc_cell :
  triple (val_alloc 2)
    \[]
    (fun r => \exists (p:loc), \exists v1 v2,
              \[r = p] \* MCell v1 v2 p).
Proof using.
  xapply triple_alloc. { math. } { hsimpl. }
  { intros r. hpull ;=> l (E&N). subst.
    simpl_abs. rew_Alloc. hpull ;=> v1 v2.
    unfold MCell. rewrite hfield_eq_fun_hsingle.
    unfold hd, tl. hsimpl~ l v1 v2.
    math_rewrite (l + 1 = S l)%nat.
    math_rewrite (l+0 = l)%nat. hsimpl. }
Qed.

Lemma triple_new_cell : forall v q,
  triple (val_new_cell v q)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MCell v q p).
Proof using.
  intros. xcf. xapp triple_alloc_cell.
  intros p p' v' q'. intro_subst.
  xapps~. intros _. xapps~. intros _. xvals~.
Qed.

(* TODO: update?
Lemma triple_new_cell : forall v q,
  triple (val_new_cell v q)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MCell v q p).
Proof using.
  intros. applys triple_app_fun2. reflexivity. auto. simpl.
  applys triple_let. { applys triple_alloc_cell. }
  intros p. xpull ;=> p' v' q'. intro_subst. simpl.
  applys triple_seq. { xapplys triple_set_hd. }
  applys triple_seq. { xapplys triple_set_tl. }
  applys triple_val. hsimpl. auto.
Qed.
*)

Hint Extern 1 (Register_spec val_new_cell) => Provide triple_new_cell.

Global Opaque MCell_eq.


(* ********************************************************************** *)
(* * Mutable lists *)

(** Layout in memory:

  type 'a mlist = { mutable hd : 'a ; mutable tl : 'a mlist }
  // empty lists represented using null

*)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), (MCell x p' p) \* (MList L' p')
  end.


(* ---------------------------------------------------------------------- *)
(** Tactic *)

(** Tactic hack to make [hsimpl] able to cancel out [MList] in
   heap entailments. Later won't be needed when using [~>] notation. *)

Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  | MCell _ _ _ => hcancel_try_same tt
  | MList _ _ => hcancel_try_same tt
  end.


(* ---------------------------------------------------------------------- *)
(** Properties *)

Section MListProperties.
Implicit Types L : list val.

(** For empty lists *)

Lemma MList_nil_eq : forall p,
  MList nil p = \[p = null].
Proof using. intros. unfolds~ MList. Qed.

Lemma MList_null_eq : forall L,
  MList L null = \[L = nil].
Proof using.
  intros. destruct L.
  { xunfold MList. applys himpl_antisym; hsimpl~. }
  { xunfold MList. applys himpl_antisym.
    { hpull ;=> p'. hchanges (MCell_null_false v p'). }
    { hpull. } }
Qed.

Lemma MList_null_inv : forall L,
  MList L null ==+> \[L = nil].
Proof using. intros. rewrite MList_null_eq. hsimpl~. Qed.

Lemma MList_nil :
  \[] ==> MList nil null.
Proof using. intros. rewrite MList_nil_eq. hsimpl~. Qed.

(** For nonempty lists *)

Lemma MList_cons_eq : forall p x L',
  MList (x::L') p =
  \exists (p':loc), MCell x p' p \* MList L' p'.
Proof using. intros. unfold MList at 1. simple~. Qed.

Lemma MList_cons : forall p p' x L',
  MCell x p' p \* MList L' p' ==> MList (x::L') p.
Proof using. intros. rewrite MList_cons_eq. hsimpl. Qed.

Lemma MList_not_null_inv_not_nil : forall p L,
  p <> null ->
  MList L p ==+> \[L <> nil].
Proof using.
  introv N. destruct L.
  { rewrite (MList_nil_eq p). hsimpl. }
  { hsimpl. auto_false. }
Qed.

Lemma MList_not_null_inv_cons : forall p L,
  p <> null ->
    MList L p ==>
    \exists (p':loc), \exists x L',
       \[L = x::L'] \* MCell x p' p  \* MList L' p'.
Proof using.
  intros. hchange~ (@MList_not_null_inv_not_nil p).
  hpull. intros. destruct L; tryfalse.
  { hchanges~ (MList_cons_eq p). }
Qed.

End MListProperties.

Arguments MList_null_inv : clear implicits.
Arguments MList_cons_eq : clear implicits.
Arguments MList_cons : clear implicits.
Arguments MList_not_null_inv_cons : clear implicits.
Arguments MList_not_null_inv_not_nil : clear implicits.

Global Opaque MList.


(* ********************************************************************** *)
(* * Length of a mutable list *)

(* ---------------------------------------------------------------------- *)
(** Implementation *)

Definition val_mlist_length : val :=
  ValFix 'f 'p :=
    If_ 'p '<> null Then (
      Let 'q := val_get_tl 'p in
      Let 'n := 'f 'q in
      'n '+ 1
    ) Else (
      0
    ).


(* ---------------------------------------------------------------------- *)
(** Verification using triples. *)

(* TODO: fix the proof. it is meant to give an idea of the length.

  Lemma triple_mlist_length_1 : forall L (p:loc),
    triple (val_mlist_length p)
      (MList L p)
      (fun r => \[r = (length L : int)] \* MList L p).
  Proof using.
    intros L. induction_wf: list_sub_wf L. intros p.
    applys triple_app_fix. reflexivity. simpl.
    applys triple_if'. { xapplys triple_neq. }
    simpl. intros X. xpull. intros EX. subst X.
    case_if as C1; case_if as C2; tryfalse.
    { inverts C2. xchange MList_null_inv.
      xpull. intros EL. applys triple_val. hsimpl. subst~. }
    { xchange (MList_not_null_inv_cons p). { auto. }
      xpull. intros x p' L' EL. applys triple_let.
      { xapplys triple_get_tl. }
      { simpl. intros p''. xpull. intros E. subst p''.
        applys triple_let.
        { simpl. xapplys IH. { subst~. } }
        { simpl. intros r. xpull. intros Er. subst r.
          xchange (MList_cons p p' x L').
          xapplys triple_add_int.
          { intros. subst L. hsimpl. }
          { intros. subst. rew_length. fequals. math. } } } }
  Qed.

*)

(* ---------------------------------------------------------------------- *)
(** Verification using characteristic formulae, but no tactics. *)

(** Observe how, in the proof below, the deep embedding is never revealed. *)

Lemma triple_mlist_length_2 : forall L p,
  triple (val_mlist_length p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* MList L p).
Proof using.
  intros L. induction_wf: list_sub_wf L. intros p.
  applys triple_app_fix_of_cf_iter 20%nat. reflexivity.
  simpl. applys local_erase. esplit. split.
  { applys local_erase. xapplys triple_neq. }
  intros X. xpull. intros EX. subst X.
  applys local_erase. esplit. splits. eauto.
  { intros C. rew_bool_eq in *. xchange (MList_not_null_inv_cons p). { auto. }
    xpull. intros p' x L' EL.
    applys local_erase. esplit. split.
    { applys local_erase. xapplys triple_get_tl. }
    intros p''. xpull. intros E. subst p''.
    applys local_erase. esplit. split.
    { applys local_erase. xapplys IH. { subst~. } }
    { intros r. xpull. intros Er. xchange (MList_cons p).
      subst r L. applys local_erase. xapplys triple_add.
      { intros. subst. rew_list. fequals. math. } } }
  { intros C. rew_bool_eq in *. applys local_erase. unfolds. inverts C.
    xchange MList_null_inv. hpull. intros EL.
    hsimpl. subst~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Verification using characteristic formulae, and basic tactics. *)

Lemma triple_mlist_length_3 : forall L p,
  triple (val_mlist_length p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* MList L p).
Proof using.
  intros L. induction_wf: list_sub_wf L. intros p. xcf.
  xlet as b. { xapp. } xpull ;=> Eb. subst.
  xif ;=> C.
  { xchange (MList_not_null_inv_cons p). { auto. }
    xpull ;=> p' x L' EL.
    xlet as p''. { xapp. }
    xpull ;=> E. subst p''.
    xlet as r. { xapp IH. { subst~. } }
    xpull ;=> Er. subst r L. xchange (MList_cons p).
    xapp. { hsimpl. intros. subst. rew_list. fequals. math. } }
  { xval. inverts C. xchange MList_null_inv.
    hpull ;=> EL. hsimpl. subst~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Verification using characteristic formulae, and advanced tactics. *)

Lemma triple_mlist_length_1 : forall L p,
  triple (val_mlist_length p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* MList L p).
Proof using.
  intros L. induction_wf: list_sub_wf L. xcf.
  xapps. xif ;=> C.
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL. subst L.
    xapps. xapps~ (IH L').
    xchange (MList_cons p).
    xapps. hsimpl. isubst. rew_list. fequals. math. }
  { inverts C. xchanges MList_null_inv ;=> EL. subst. xvals~. }
Qed.


(* ********************************************************************** *)
(* * Length of a mutable list using a loop *)

(* ---------------------------------------------------------------------- *)
(** Implementation *)

Definition val_mlist_length_loop : val :=
  ValFun 'p1 :=
    Let 'r := val_ref 'p1 in
    Let 'n := val_ref 0 in
    While (Let 'p := val_get 'r in
           'p '<> null) Do
      val_incr 'n ;;;
      Let 'p := val_get 'r in
      Let 'q := val_get_tl 'p in
      val_set 'r 'q
    Done ;;;
    val_get 'n.

Lemma triple_mlist_length_loop : forall L p,
  triple (val_mlist_length_loop p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* MList L p).
Proof using.
  xcf. xapp ;=> V r E; subst V. xapp ;=> V n E; subst V.
  xlet. xwhile as R.
  { cuts K: (forall (nacc:int),
       R (r ~~~> p \* MList L p \* n ~~~> nacc)
         (fun r' => \[r' = val_unit] \* MList L p \* n ~~~> (nacc + length L))).
    { xapplys* K. }
    gen p. induction_wf: list_sub_wf L; intros. applys (rm HR).
    xlet. { xapps. xapps. } xpull ;=> ? ->. xif ;=> C.
    { xchanges~ (MList_not_null_inv_cons p) ;=> p' x L' EL. xseq.
      { xseq. xapp~. simpl ;=> _. xapps.
        xapps. xapps~. hsimpl. }
      { xapply (>> IH L'). { subst~. } { hsimpl. }
        { hpull. isubst. hchange (MList_cons p). subst. rew_list.
          math_rewrite (forall x (y:nat), (x+1)+y = x+(1+y)%nat). hsimpl~. } } }
          (* todo: cancel on ~~> *)
    { inverts C. xchanges MList_null_inv ;=> EL. subst. rew_list.
      math_rewrite (nacc+0%nat = nacc). xvals~. } }
  { xpull. intros ? ->. xapp. hsimpl ;=> ? ->. fequals. }
Qed.



(* ********************************************************************** *)
(* * Mutable lists Segments *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint MListSeg (q:loc) (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => \exists (p':loc), (MCell x p' p) \* (MListSeg q L' p')
  end.

(* ---------------------------------------------------------------------- *)
(** Hack *)

(** Tactic hack to make [hsimpl] able to cancel out [MList]
    in heap entailment. *)

Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  | MCell _ _ _ => hcancel_try_same tt
 (* TODO  | MList _ _ => hcancel_try_same tt *)
  | MListSeg _ _ _ => hcancel_try_same tt
  end.


(* ---------------------------------------------------------------------- *)
(** Properties *)

Section Properties.
Implicit Types L : list val.

Lemma MListSeg_nil_eq : forall p q,
  MListSeg q nil p = \[p = q].
Proof using. intros. unfolds~ MListSeg. Qed.

Lemma MListSeg_cons_eq : forall p q x L',
  MListSeg q (x::L') p =
  \exists (p':loc), MCell x p' p \* MListSeg q L' p'.
Proof using. intros. unfold MListSeg at 1. simple~. Qed.

Global Opaque MListSeg.

Lemma MListSeg_nil : forall p,
  \[] ==> MListSeg p nil p.
Proof using. intros. rewrite MListSeg_nil_eq. hsimpl~. Qed.

Lemma MListSeg_cons : forall p p' q x L',
  MCell x p' p \* MListSeg q L' p' ==> MListSeg q (x::L') p.
Proof using. intros. rewrite MListSeg_cons_eq. hsimpl. Qed.

Lemma MListSeg_one : forall p q x,
  MCell x q p ==> MListSeg q (x::nil) p.
Proof using.
  intros. hchange (@MListSeg_nil q). hchange MListSeg_cons. hsimpl.
Qed.

Lemma MListSeg_concat : forall p1 p2 p3 L1 L2,
  MListSeg p2 L1 p1 \* MListSeg p3 L2 p2 ==> MListSeg p3 (L1++L2) p1.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros.
  { rewrite MListSeg_nil_eq. hpull ;=> E. subst. rew_list~. }
  { rew_list. hchange (MListSeg_cons_eq p1). hpull ;=> p1'.
    hchange (IHL1' p1'). hchanges (@MListSeg_cons p1). }
Qed.

Lemma MListSeg_last : forall p1 p2 p3 x L,
  MListSeg p2 L p1 \* MCell x p3 p2 ==> MListSeg p3 (L&x) p1.
Proof using.
  intros. hchange (@MListSeg_one p2). hchanges MListSeg_concat.
Qed.

Lemma MListSeg_then_MCell_inv_neq : forall p q L v1 v2,
  MListSeg q L p \* MCell v1 v2 q ==>
  MListSeg q L p \* MCell v1 v2 q \* \[L = nil <-> p = q].
Proof using.
  intros. destruct L.
  { rewrite MListSeg_nil_eq. hsimpl*. split*. (* TODO: why not proved? *) }
  { rewrite MListSeg_cons_eq. hpull ;=> p'. tests: (p = q).
    { hchanges (@MCell_hstar_MCell_inv q). }
    { hsimpl. split; auto_false. } }
Qed.

End Properties.

Arguments MListSeg_then_MCell_inv_neq : clear implicits.
