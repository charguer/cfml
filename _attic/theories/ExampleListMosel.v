(**

This file formalizes mutable list examples in plain Separation Logic,
illustrating the direct use of triples on one example, and conducting
other proofs using characteristic formulae.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import LambdaCF LambdaStruct SepBaseMosel.
Import ProofMode.

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
  (p `. hd ~~~> v) \* (p `. tl ~~~> q).

(* ---------------------------------------------------------------------- *)
(** Properties of list cells *)

Lemma MCell_eq : forall (v:val) (q:val) (p:loc),
  MCell v q p = (p `. hd ~~~> v) \* (p `. tl ~~~> q).
Proof using. auto. Qed.

Lemma MCell_inv_not_null : forall p v q,
  (MCell v q p) ==+> \[p <> null].
  (* i.e. (MCell v q p) ==> (MCell v q p) \* \[p <> null]. *)
Proof using.
  intros. unfold MCell, hd.
  iIntros "[Hhd $]". by iApply hfield_not_null.
Qed.

Arguments MCell_inv_not_null : clear implicits.

Lemma MCell_null_false : forall v q,
  (MCell v q null) ==> \[False].
Proof using.
  iIntros (??) "H". by iDestruct (MCell_inv_not_null with "H") as "[? %]".
Qed.

Arguments MCell_null_false : clear implicits.

Lemma MCell_hstar_MCell_inv : forall p1 p2 x1 x2 y1 y2,
  MCell x1 y1 p1 \* MCell x2 y2 p2 ==+> \[p1 <> p2].
Proof using.
  intros. do 2 rewrite MCell_eq. tests C: (p1 = p2).
  { iPrepare. iIntros. iDestruct (hstar_hfield_same_loc_disjoint with "[$]") as %[]. }
  { iPrepare. auto with iFrame. }
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
  intros. unfold MCell. ram_apply triple_get_field. auto with iFrame.
Qed.

Hint Extern 1 (Register_spec val_get_hd) => Provide triple_get_hd.

(** Read to tail *)

Definition val_get_tl := val_get_field tl.

Lemma triple_get_tl : forall p v q,
  triple (val_get_tl p)
    (MCell v q p)
    (fun r => \[r = q] \* (MCell v q p)).
Proof using.
  intros. unfold MCell. ram_apply triple_get_field. auto with iFrame.
Qed.

Hint Extern 1 (Register_spec val_get_tl) => Provide triple_get_tl.

(** Write to head *)

Definition val_set_hd := val_set_field hd.

Lemma triple_set_hd : forall p v' v vq,
  triple (val_set_hd p v)
    (MCell v' vq p)
    (fun r => MCell v vq p).
Proof using.
  intros. unfold MCell. ram_apply triple_set_field.  auto with iFrame.
Qed.

Hint Extern 1 (Register_spec val_set_hd) => Provide triple_set_hd.

(** Write to tail *)

Definition val_set_tl := val_set_field tl.

Lemma triple_set_tl : forall p v q vq',
  triple (val_set_tl p q)
    (MCell v vq' p)
    (fun r => MCell v q p).
Proof using.
  intros. unfold MCell. ram_apply triple_set_field. auto with iFrame.
Qed.

Hint Extern 1 (Register_spec val_set_tl) => Provide triple_set_tl.


(* ---------------------------------------------------------------------- *)
(** Allocation of list cells *)

Definition val_new_cell :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2%Z in
    val_set_hd 'p 'x;;;
    val_set_tl 'p 'y;;;
    'p.

(* TODO: eliminate *)
Ltac simpl_abs :=
  match goal with
  | |- context [ abs 0 ] => change (abs 0) with 0%nat
  | |- context [ abs 1 ] => change (abs 1) with 1%nat
  | |- context [ abs 2 ] => change (abs 2) with 2%nat
  | |- context [ abs 3 ] => change (abs 3) with 3%nat
  end.

Lemma triple_alloc_cell :
  triple (val_alloc 2%Z)
    \[]
    (fun r => \exists (p:loc), \exists v1 v2,
              \[r = p] \* MCell v1 v2 p).
Proof using.
  ram_apply triple_alloc; [math|]. iDestruct 1 as (l [-> ?]) "H".
  simpl_abs. rew_Alloc. iDestruct "H" as "(Hv1 & Hv2 & _)".
  iDestruct "Hv1" as (v1) "Hv1". iDestruct "Hv2" as (v2) "Hv2".
  iExists _, _, _. unfold MCell. rewrite hfield_eq_fun_hsingle /hd /tl.
  math_rewrite (l + 1 = S l)%nat. math_rewrite (l+0 = l)%nat. auto with iFrame.
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

Ltac loop := idtac; loop.

(* LATER: port to MoSel
Lemma triple_new_cell' : forall v q,
  triple (val_new_cell v q)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MCell v q p).
Proof using.
  intros. eapply triple_app_fun2 =>//=; [].
  eapply triple_let; [apply triple_alloc_cell|]=>p /=. xtpull=> p' v' q' ->.
  eapply triple_seq.
  { rewrite MCell_eq. ram_apply triple_set_hd. auto with iFrame. }
  { unlock ;=> _. eapply triple_seq.
    ram_apply triple_set_tl.
  { auto with iFrame. }
  { unlock ;=> _. eapply triple_val. iPrepare. auto with iFrame. } }
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
  { xunfold MList. applys himpl_antisym; eauto. }
  { xunfold MList. applys himpl_antisym.
    { iDestruct 1 as (p') "[H ?]". iDestruct (MCell_null_false with "H") as %[]. }
    { iIntros ([=]). } }
Qed.

Lemma MList_null_inv : forall L,
  MList L null ==+> \[L = nil].
Proof using. intros. rewrite MList_null_eq. iIntros "#$". Qed.

Lemma MList_nil :
  \[] ==> MList nil null.
Proof using. intros. rewrite MList_nil_eq. auto. Qed.

(** For nonempty lists *)

Lemma MList_cons_eq : forall p x L',
  MList (x::L') p =
  \exists (p':loc), MCell x p' p \* MList L' p'.
Proof using. intros. unfold MList at 1. simple~. Qed.

Lemma MList_cons : forall p p' x L',
  MCell x p' p \* MList L' p' ==> MList (x::L') p.
Proof using. intros. rewrite MList_cons_eq. auto. Qed.

Lemma MList_not_null_inv_not_nil : forall p L,
  p <> null ->
  MList L p ==+> \[L <> nil].
Proof using.
  introv N. destruct L.
  { rewrite (MList_nil_eq p). auto. }
  { simpl. auto with iFrame. }
Qed.

Lemma MList_not_null_inv_cons : forall p L,
  p <> null ->
    MList L p ==>
    \exists (p':loc), \exists x L',
       \[L = x::L'] \* MCell x p' p  \* MList L' p'.
Proof using.
  iIntros (p L ?) "H".
  iDestruct (MList_not_null_inv_not_nil with "H") as "[H %]"; [done|].
  destruct L=>//=. iDestruct "H" as (l) "[??]". auto with iFrame.
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

Lemma triple_mlist_length : forall L (p:loc),
  triple (val_mlist_length p)
    (MList L p)
    (fun r => \[r = (length L : int)] \* MList L p).
Proof using.
  intros L. induction_wf: list_sub_wf L. intros p.
  applys triple_app=>//=. applys triple_if'.
  - ram_apply triple_neq. auto with iFrame.
  - unlock. xtpull ;=>[= Hp]. rewrite true_eq_isTrue_eq in Hp.
    xtchange (MList_not_null_inv_cons p); [by auto|]. xtpull=>p' x L' ?. subst.
    applys triple_let. { ram_apply triple_get_tl. auto with iFrame. }
    unlock=> q /=. xtpull=>->.
    applys triple_let. { ram_apply (IH L'); [done|]. auto with iFrame. }
    unlock=> n /=. xtpull=>->. ram_apply triple_add.
    iIntros "??" (?) "->". iSplitR.
    { iPureIntro. f_equal. math. } { iApply MList_cons. iFrame. }
  - unlock. eapply triple_val. iPrepare. iIntros "HL" ([= Hp]). revert Hp.
    rewrite false_eq_isTrue_eq=>/not_not_inv. intros [= ->].
    iDestruct (MList_null_inv with "HL") as "[$ ->]". auto.
  - unlock. iIntros ([] Hb) "[? %]"=>//. destruct Hb. eexists _. auto.
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
  intros L p. eapply triple_app=>//=.
  applys triple_let. { ram_apply triple_ref. auto with iFrame. }
  unlock=> ? /=. xtpull=>r ->.
  applys triple_let. { ram_apply triple_ref. auto with iFrame. }
  unlock=> ? /=. xtpull=>n ->. applys triple_seq.
  - applys triple_while=>t R.
    cuts K: (forall (nacc:int),
      triple t (n ~~~> nacc \* MList L p \* r ~~~> p)
          (λ r0 : val, \[r0 = '()] \* n ~~~> (nacc + length L)%Z \* MList L p)).
    { ram_apply K. auto with iFrame. }
    gen p. induction_wf: list_sub_wf L=>p nacc. apply R. applys triple_if'.
    + eapply triple_let. ram_apply triple_get. { auto with iFrame. }
      unlock=>pp /=. xtpull=>->. ram_apply triple_neq. eauto with iFrame.
    + unlock. xtpull. intros [=Hp]. rewrite true_eq_isTrue_eq in Hp.
      xtchange (MList_not_null_inv_cons p); [by auto|iPrepare; auto with iFrame|].
      xtpull=>p' x L' ?. subst. applys triple_seq.
      { applys triple_seq. { ram_apply triple_incr. auto with iFrame. }
        { unlock ;=> _. eapply triple_let. { ram_apply triple_get. auto with iFrame. }
        unlock. xtpull=>? -> /=. eapply triple_let.
        { ram_apply triple_get_tl. auto with iFrame. }
        unlock=>? /=. xtpull=>->. ram_apply triple_set'. auto with iFrame. } }
      { unlock ;=> _. ram_apply (IH L'); [done|]. iIntros. iFrame.
      iIntros (?) "$ Hn ?". iSplitL "Hn".
      * by math_rewrite ((nacc + 1) + length L' = nacc + S (length (L')))%Z.
      * iApply MList_cons. iFrame. }
    + unlock. iApply triple_val_htop. iPrepare. iIntros "? HL ?" ([= Hp]).
      revert Hp. rewrite false_eq_isTrue_eq. intros [= ->]%not_not_inv.
      iDestruct (MList_null_inv with "HL") as "[$ ->]". rewrite plus_zero_r. by iFrame.
    + unlock. iIntros ([] Hb) "(? & ? & ? & %)"=>//. destruct Hb. eexists _. auto.
  - unlock. xtpull ;=> u U. subst u. apply triple_htop_post.
    ram_apply triple_get. auto with iFrame.
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
(** Properties *)

Section Properties.
Implicit Types L : list val.

Lemma MListSeg_nil_eq : forall p q,
  MListSeg q nil p = \[p = q].
Proof using. intros. unfolds~ MListSeg. Qed.

Lemma MListSeg_cons_eq : forall p q x L',
  MListSeg q (x::L') p =
  \exists (p':loc), MCell x p' p \* MListSeg q L' p'.
Proof using. intros. unfold MListSeg at 1. done. Qed.

Global Opaque MListSeg.

Lemma MListSeg_nil : forall p,
  \[] ==> MListSeg p nil p.
Proof using. intros. rewrite MListSeg_nil_eq. auto. Qed.

Lemma MListSeg_cons : forall p p' q x L',
  MCell x p' p \* MListSeg q L' p' ==> MListSeg q (x::L') p.
Proof using. intros. rewrite MListSeg_cons_eq. auto. Qed.

Lemma MListSeg_one : forall p q x,
  MCell x q p ==> MListSeg q (x::nil) p.
Proof using.
  iIntros (p q x) "H". iApply MListSeg_cons. iFrame. by iApply MListSeg_nil.
Qed.

Lemma MListSeg_concat : forall p1 p2 p3 L1 L2,
  MListSeg p2 L1 p1 \* MListSeg p3 L2 p2 ==> MListSeg p3 (L1++L2) p1.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros.
  { rewrite MListSeg_nil_eq. iIntros "[-> $]". }
  { rew_list. rewrite MListSeg_cons_eq. iIntros "[H ?]".
    iDestruct "H" as (p') "[??]". iApply MListSeg_cons. iFrame.
    iApply IHL1'. iFrame. }
Qed.

Lemma MListSeg_last : forall p1 p2 p3 x L,
  MListSeg p2 L p1 \* MCell x p3 p2 ==> MListSeg p3 (L&x) p1.
Proof using.
  intros. iIntros "[??]". iApply MListSeg_concat. iFrame. by iApply MListSeg_one.
Qed.

Lemma MListSeg_then_MCell_inv_neq : forall p q L v1 v2,
  MListSeg q L p \* MCell v1 v2 q ==>
  MListSeg q L p \* MCell v1 v2 q \* \[L = nil <-> p = q].
Proof using.
  intros. destruct L.
  { rewrite MListSeg_nil_eq. iIntros "[-> $]". auto. }
  { rewrite MListSeg_cons_eq. xpull ;=> p'. iIntros "(H1 & ? & H2)".
    iDestruct (MCell_hstar_MCell_inv with "[$H1 $H2]") as "[[$ H2] %]".
    auto with iFrame. }
Qed.

End Properties.

Arguments MListSeg_then_MCell_inv_neq : clear implicits.
