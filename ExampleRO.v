(**

This file formalizes example in Separation Logic with read-only predicates

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import LambdaSepRO.
Generalizable Variables A B.
Open Scope trm_scope.
Ltac auto_star ::= jauto.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types v : val.



(* todo move *)

Lemma rule_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h1 h2 D H1.
  forwards~ (h1'&v&N1&N2&N3&N4): (rm M) h2 H1.
  exists h1' v. splits~. { subst. applys* red_app_funs_val. }
Qed.

Lemma var_funs_exec_elim : forall (n:nat) xs,
  var_funs_exec n xs -> (var_funs n xs).
Proof using. introv M. rewrite var_funs_exec_eq in M. rew_istrue~ in M. Qed.

Hint Resolve var_funs_exec_elim.

Lemma RO_himpl_RO_hstar_RO : forall H,
  RO H ==> (RO H \* RO H).
Proof using. intros. applys RO_duplicatable. Qed.

Lemma rule_xchange : forall (H1 H1':hprop), H1 ==> H1' ->
  forall t H H2 Q,
  H ==> H1 \* H2 ->
  triple t (H1' \* H2) Q ->
  triple t H Q.
Proof using.
  introv M1 M2 M. applys~ rule_consequence M2.
  applys* rule_consequence (H1' \* H2). hsimpl~.
Qed.

Lemma rule_frame_read_only_conseq : forall t H1 Q1 H2 H Q,
  H ==> (H1 \* H2) ->
  Normal H1 ->
  triple t (RO H1 \* H2) Q1 ->
  (Q1 \*+ H1) ===> Q ->
  triple t H Q.
Proof using.
  introv WP M N WQ. applys* rule_consequence (rm WP) (rm WQ).
  forwards~ R: rule_frame_read_only t H2 Q1 H1.
  { rewrite~ hstar_comm. } { rewrite~ hstar_comm. }
Qed.


Lemma rule_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* l ~~~> v).
Proof using.
  intros. applys rule_frame_read_only_conseq (l ~~~> v).
  { hsimpl. } { apply _. }
  { rew_heap. applys rule_get_ro. }
  { auto. }
Qed.

Lemma rule_let' : forall x t1 t2 H2 H1 H Q Q1,
  H ==> (H1 \* H2) ->
  triple t1 H1 Q1 ->
  (forall (X:val), triple (subst x X t2) (Q1 X \* H2) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. introv WP M1 M2. applys* rule_consequence WP. applys* rule_let. Qed.

Lemma rule_frame : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. applys~ rule_frame_read_only.
  applys~ rule_consequence (H1 \* \Top). hsimpl.
  applys* rule_htop_pre.
Qed.

Lemma rule_frame_conseq : forall t H1 Q1 H2 H Q,
  H ==> H2 \* H1 ->
  Normal H1 ->
  triple t H2 Q1 ->
  Q1 \*+ H1 ===> Q ->
  triple t H Q.
Proof using. intros. applys* rule_consequence. applys* rule_frame. Qed.

Hint Resolve Normal_hsingle.

(* ********************************************************************** *)
(* * Formalisation of higher-order iterator on a reference *)

Tactic Notation "xdef" :=
  rew_nary; rew_vals_to_trms;
  match goal with |- triple (trm_apps (trm_val ?f) _) _ _ =>
   applys rule_apps_funs;
   [unfold f; rew_nary; reflexivity | auto | simpl]
  end.

(* ---------------------------------------------------------------------- *)
(** Apply a function to the contents of a reference *)

Definition val_ref_apply :=
  ValFun 'f 'p :=
    Let 'x := val_get 'p in
    'f 'x.

Lemma rule_ref_apply : forall (f:val) (p:loc) (v:val) (H:hprop) (Q:val->hprop),
  (triple (f v)
    PRE (RO(p ~~~> v) \* H)
    POST Q)
  ->
  (triple (val_ref_apply f p)
    PRE (RO(p ~~~> v) \* H)
    POST Q).
Proof using.
  introv M. xdef. xchange (@RO_himpl_RO_hstar_RO (p ~~~> v)).
  rew_heap. applys rule_let (RO (p ~~~> v)).
  { applys rule_get_ro. }
  { intros x; simpl. xpull ;=> E. subst x.
    applys rule_consequence M; hsimpl. }
Qed.

(* Note: this specification allows [f] to call [val_get] on [r],
   as illustrated next

  Definition val_demo_1 :=
    ValFun 'n :=
      Let 'p := val_ref 'n in
      LetFun 'f 'x :=
        Let 'y := val_get 'p in
        val_add 'x 'y in
      val_ref_apply 'f 'p.

  Lemma rule_demo_1 : forall (n:int),
    triple (val_demo_1 n)
      PRE \[]
      POST (fun r => \[r = val_int (2*n)]).
  Proof using.

  Qed.

*)



(* ---------------------------------------------------------------------- *)
(** In-place update of a reference by applying a function *)

Definition val_ref_update :=
  ValFun 'f 'p :=
    Let 'x := val_get 'p in
    Let 'y := 'f 'x in
    val_set 'p 'y.

Lemma rule_ref_update : forall (f:val) (p:loc) (v:val) (H:hprop) (Q:val->hprop),
  Normal_post Q -> (* todo: this might not be needed if using "normally" *)
  (triple (f v)
    PRE (RO(p ~~~> v) \* H)
    POST Q)
  ->
  (triple (val_ref_update f p)
    PRE (p ~~~> v \* H)
    POST (fun r => \[r = val_unit] \* Hexists w, (p ~~~> w) \* (Q w))).
Proof using.
  introv N M. xdef.
  applys rule_let.
  { applys rule_get. }
  { intros x; simpl. xpull ;=> E. subst x.
    applys rule_let' \[]. { hsimpl. }
    applys~ rule_frame_read_only_conseq (p ~~~> v).
    { applys rule_consequence M; hsimpl. }
    { hsimpl. }
    { clear M. intros y; simpl. xpull.
      applys~ rule_frame_conseq (Q y).
      { applys rule_set. }
      { hsimpl~. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** In-place update of a reference by invoking a function, with representation predicate  *)

Hint Rewrite RO_hexists RO_pure : rew_RO.
 (* todo : rename to RO_hpure , RO_hstar. *)

Tactic Notation "rew_RO" :=
  autorewrite with rew_RO.

Lemma rule_htop_pre' : forall H2 H1 t H Q,
  H ==> H1 \* H2 ->
  triple t H1 Q ->
  triple t H Q.
Proof using.
  introv W M. applys rule_consequence; [| applys rule_htop_pre M |].
  { hchange W. hsimpl. } { auto. }
Qed.


(*---*)



Definition Box (n:int) (p:loc) :=
  Hexists (q:loc), (p ~~~> q) \* (q ~~~> n).

Lemma Box_unfold : forall p n,
  (p ~> Box n) ==> Hexists (q:loc), (p ~~~> q) \* (q ~~~> n).
Proof using. intros. xunfold Box. hsimpl. Qed.

Lemma Box_fold : forall p q n,
  (p ~~~> q) \* (q ~~~> n) ==> (p ~> Box n).
Proof using. intros. xunfold Box. hsimpl. Qed.

Lemma RO_Box_unfold : forall p n,
  RO (p ~> Box n) ==> RO (p ~> Box n) \* Hexists (q:loc), RO (p ~~~> q) \* RO (q ~~~> n).
Proof using.
  intros. hchange RO_duplicatable. xunfold Box at 1.
  rew_RO. hpull ;=> q. hchanges (RO_star (p ~~~> q) (q ~~~> n)).
Qed.

Arguments Box_fold : clear implicits.
Arguments Box_unfold : clear implicits.
Arguments RO_Box_unfold : clear implicits.


(*---*)

Definition val_box_get :=
  ValFun 'p :=
    Let 'q := val_get 'p in
    val_get 'q.

Lemma rule_box_get : forall p n,
  triple (val_box_get p)
    PRE (RO (p ~> Box n))
    POST (fun r => \[r = val_int n]).
Proof using.
  intros. xdef. xchange (RO_Box_unfold p). xpull ;=> q.
  applys rule_htop_pre' (RO (p ~> Box n)). hsimpl. (* not need, ideally *)
  rew_heap. applys rule_let' __ (RO (p ~~~> q)).
  { hsimpl. }
  { applys rule_get_ro. }
  { intros x; simpl; xpull ;=> E; subst x. applys rule_get_ro. }
Qed.

(*---*)

(* let box_twice f p =
      let q = !p in
      q := f !q + f !q
*)

Definition val_box_twice :=
  ValFun 'f 'p :=
    Let 'q := val_get 'p in
    Let 'n1 := val_get 'q in
    Let 'a1 := 'f 'n1 in
    Let 'n2 := val_get 'q in
    Let 'a2 := 'f 'n2 in
    Let 'm := 'a1 '+ 'a2 in
    val_set 'q 'm.

Lemma rule_box_twice : forall (f:val) p n (F:int->int),
  (forall (x:int) H, triple (val_box_twice f x)
      PRE (RO(p ~> Box n) \* H)
      POST (fun r => \[r = val_int (F x)] \* H)) ->
  triple (val_box_twice f p)
    PRE (p ~> Box n)
    POST (fun r => \[r = val_unit] \* p ~> Box (2 * F n)).
Proof using.
  introv M. xdef. xchange (Box_unfold p). xpull ;=> q.
  applys rule_let' __ (p ~~~> q).
  { hsimpl. }
  { rew_heap. applys rule_get. }
  { intros x; simpl; xpull ;=> E; subst x.
  applys rule_let' __ (q ~~~> n).
  { hsimpl. }
  { rew_heap. applys rule_get. }
  { intros x; simpl; xpull ;=> E; subst x.
Abort.











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
    (fun r => \[r = val_unit] \* (l `.` k ~~~> v)).
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
    (fun r => \[r = val_unit] \* MCell v vq p).
Proof using.
  intros. unfold MCell. xapplys (rule_set_field v'). auto.
Qed.

Hint Extern 1 (Register_spec val_set_hd) => Provide rule_set_hd.

(** Write to tail *)

Definition val_set_tl := val_set_field tl.

Lemma rule_set_tl : forall p v q vq',
  triple (val_set_tl p q)
    (MCell v vq' p)
    (fun r => \[r = val_unit] \* MCell v q p).
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
    POST (fun r => \[r = val_unit] \* p1 ~> MQueue (L1 ++ L2) \* p2 ~> MQueue nil).

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
    POST (fun r => \[r = val_unit] \* p1 ~> MQueue (L1 ++ L2)).
Proof using.


Qed.


Hint Extern 1 (Register_spec val_copy_transfer) => Provide rule_copy_transfer.


*)

