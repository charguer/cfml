







(*-----------LATER using LambdaCFRO

(* ********************************************************************** *)
(* * Formalisation of records *)

(* ---------------------------------------------------------------------- *)
(** Read to a record field *)

Definition val_get_field (k:field) :=
  ValFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Lemma rule_get_field : forall l k v,
  triple ((val_get_field k) l)
    (l `.` k ~~~> v)
    (fun r => \[r = v] \* (l `.` k ~~~> v)).
Proof using.
  intros. applys rule_app_fun. reflexivity. simpl.
  applys rule_let. { xapplys rule_ptr_add_nat. }
  intros r. simpl. xpull. intro_subst.
  rewrite hfield_eq_fun_hsingle.
  xpull ;=> N. xapplys~ rule_get.
Qed.


(* ---------------------------------------------------------------------- *)
(** Write to a record field *)

Definition val_set_field (k:field) :=
  ValFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Lemma rule_set_field : forall v' l k v,
  triple ((val_set_field k) l v)
    (l `.` k ~~~> v')
    (fun r => (l `.` k ~~~> v)).
Proof using.
  intros. applys rule_app_fun2. reflexivity. auto. simpl.
  applys rule_let. { xapplys rule_ptr_add_nat. }
  intros r. simpl. xpull. intro_subst.
  rewrite hfield_eq_fun_hsingle.
  xpull ;=> N. xapplys~ rule_set.
Qed.

Arguments rule_set_field : clear implicits.



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

Lemma rule_get_hd : forall p v q,
  triple (val_get_hd p)
    (MCell v q p)
    (fun r => \[r = v] \* (MCell v q p)).
Proof using.
  intros. unfold MCell. xapplys rule_get_field. auto.
Qed.

Hint Extern 1 (Register_spec val_get_hd) => Provide rule_get_hd.

(** Read to tail *)

Definition val_get_tl := val_get_field tl.

Lemma rule_get_tl : forall p v q,
  triple (val_get_tl p)
    (MCell v q p)
    (fun r => \[r = q] \* (MCell v q p)).
Proof using.
  intros. unfold MCell.
  xapplys rule_get_field. auto.
Qed.

Hint Extern 1 (Register_spec val_get_tl) => Provide rule_get_tl.

(** Write to head *)

Definition val_set_hd := val_set_field hd.

Lemma rule_set_hd : forall p v' v vq,
  triple (val_set_hd p v)
    (MCell v' vq p)
    (fun r => MCell v vq p).
Proof using.
  intros. unfold MCell. xapplys (rule_set_field v'). auto.
Qed.

Hint Extern 1 (Register_spec val_set_hd) => Provide rule_set_hd.

(** Write to tail *)

Definition val_set_tl := val_set_field tl.

Lemma rule_set_tl : forall p v q vq',
  triple (val_set_tl p q)
    (MCell v vq' p)
    (fun r => MCell v q p).
Proof using.
  intros. unfold MCell. xapplys (rule_set_field vq'). auto.
Qed.

Hint Extern 1 (Register_spec val_set_tl) => Provide rule_set_tl.


(* ---------------------------------------------------------------------- *)
(** Allocation of list cells *)

Definition val_new_cell :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2 in
    val_set_hd 'p 'x;;;
    val_set_tl 'p 'y;;;
    'p.

Lemma rule_alloc_cell :
  triple (val_alloc 2)
    \[]
    (fun r => Hexists (p:loc), Hexists v1 v2,
              \[r = p] \* MCell v1 v2 p).
Proof using.
  xapply rule_alloc. { math. } { hsimpl. }
  { intros r. hpull ;=> l (E&N). subst.
    simpl_abs. rew_Alloc. hpull ;=> v1 v2.
    unfold MCell. rewrite hfield_eq_fun_hsingle.
    unfold hd, tl. hsimpl~ l v1 v2.
    math_rewrite (l + 1 = S l)%nat.
    math_rewrite (l+0 = l)%nat. hsimpl. }
Qed.

Lemma rule_new_cell : forall v q,
  triple (val_new_cell v q)
    \[]
    (fun r => Hexists p, \[r = val_loc p] \* MCell v q p).
Proof using.
  intros. xcf. xapp rule_alloc_cell.
  intros p p' v' q'. intro_subst.
  xapps~. xapps~. xvals~.
Qed.

(* TODO: update?
Lemma rule_new_cell : forall v q,
  triple (val_new_cell v q)
    \[]
    (fun r => Hexists p, \[r = val_loc p] \* MCell v q p).
Proof using.
  intros. applys rule_app_fun2. reflexivity. auto. simpl.
  applys rule_let. { applys rule_alloc_cell. }
  intros p. xpull ;=> p' v' q'. intro_subst. simpl.
  applys rule_seq. { xapplys rule_set_hd. }
  applys rule_seq. { xapplys rule_set_tl. }
  applys rule_val. hsimpl. auto.
Qed.
*)

Hint Extern 1 (Register_spec val_new_cell) => Provide rule_new_cell.

Global Opaque MCell_eq.


(* ********************************************************************** *)
(* * Mutable lists Segments *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint MListSeg (q:loc) (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => Hexists (p':loc), (MCell x p' p) \* (MListSeg q L' p')
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
  Hexists (p':loc), MCell x p' p \* MListSeg q L' p'.
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




(* ********************************************************************** *)
(* * Mutable queue *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Definition MQueue (L:list val) (p:loc) :=
  Hexists (pf:loc), Hexists (pb:loc), Hexists (vx:val), Hexists (vy:val),
    MCell pf pb p \* MListSeg pb L pf \* MCell vx vy pb.


(* ---------------------------------------------------------------------- *)
(** Copy *)

Parameter val_mqueue_copy : val.

Parameter rule_mqueue_copy : forall p (L:list val),
  triple (val_mqueue_copy p)
    PRE (RO (p ~> MList L))
    POST (fun r => Hexists p', \[r = val_loc p'] \* (p' ~> MList L)).

Hint Extern 1 (Register_spec val_mqueue_copy) => Provide rule_mqueue_copy.


(* ---------------------------------------------------------------------- *)
(** Transfer *)

Parameter val_transfer : val.

Parameter rule_transfer : forall L1 L2 p1 p2,
  triple (val_transfer p1 p2)
    PRE (p1 ~> MQueue L1 \* p2 ~> MQueue L2)
    POST (fun r => p1 ~> MQueue (L1 ++ L2) \* p2 ~> MQueue nil).

Hint Extern 1 (Register_spec val_transfer) => Provide rule_transfer.


(* ---------------------------------------------------------------------- *)
(** Copy-Transfer *)

Definition val_copy_transfer :=
  ValFun 'p1 'p2 :=
    Let 'p3 := val_mqueue_copy 'p2 in
    val_transfer 'p1 'p3.

Lemma rule_copy_transfer : forall L1 L2 p1 p2,
  triple (val_transfer p1 p2)
    PRE (p1 ~> MQueue L1 \* RO(p2 ~> MQueue L2))
    POST (fun r => p1 ~> MQueue (L1 ++ L2)).
Proof using.


Qed.


Hint Extern 1 (Register_spec val_copy_transfer) => Provide rule_copy_transfer.


*)

