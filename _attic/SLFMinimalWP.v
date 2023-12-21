
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions




Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H0 \* H1) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, hwand (Q1 x) (Q2 x).


Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.




(* ################################################ *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).
Proof using.
  unfold hwand. iff M.
  { applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H1 \* H2 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite hstar_comm. rewrite~ <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. rewrite hwand_equiv. rewrite~ hstar_hempty_l. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_r. }
Qed.

Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using.
  introv HP. rewrite <- hstar_hempty_l at 1.
  forwards~ K: himpl_hempty_hpure P.
  applys himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. do 2 rewrite hwand_equiv.
  rewrite hstar_assoc. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite <- (hstar_comm (H1 \* H2)).
  rewrite (@hstar_comm H1). rewrite hstar_assoc.
  applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


(* ################################################ *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite hwand_equiv. rewrite* hstar_comm. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].



(* ########################################################### *)
(** ** Definition of [wp] and reasoning rules *)

(* ################################################ *)
(** *** Definition of the weakest-precondition judgment. *)

(** [wp] is defined on top of [hoare] triples. More precisely [wp t Q]
    is a heap predicate such that [H ==> wp t Q] if and
    only if [SL_triple t H Q], where [SL_triple t H Q]
    is defined as [forall H', hoare t (H \* H') (Q \*+ H')]. *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[forall H', hoare t (H \* H') (Q \*+ H')].


(* ################################################ *)
(** *** Structural rule for [wp]. *)

(** The ramified frame rule (with garbage collection) *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hoare_conseq M; xsimpl.
Qed.

Arguments wp_ramified : clear implicits.

(** Corollaries *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. applys himpl_trans_r (wp_ramified Q1 Q2). xsimpl. xchanges M.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.


(* ################################################ *)
(** *** Weakest-precondition style reasoning rules for terms. *)

Lemma wp_eval_like : forall t1 t2 Q,
  eval_like t1 t2 ->
  wp t1 Q ==> wp t2 Q.
Proof using.
  introv E. unfold wp. xpull. intros H M. xsimpl H.
  intros H'. applys hoare_eval_like E M.
Qed.

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_val. xsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_fun. xsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_fix. xsimpl. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hoare_app_fun. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fun. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hoare_app_fix. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fix. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hoare_seq. applys (rm M1). unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hoare_let. applys (rm M1). intros v. simpl. unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); rew_heap.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hoare_if. applys M.
Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans wp_if. case_if~. Qed.


Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  unfold wp, triple. iff M.
  { intros H'. applys hoare_conseq. 2:{ applys himpl_frame_l M. }
     { clear M. rewrite hstar_hexists. applys hoare_hexists. intros H''.
       rewrite (hstar_comm H''). rew_heap. applys hoare_hpure. intros N.
       applys N. }
     { auto. } }
  { xsimpl H. apply M. }
Qed.



Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq.
  applys triple_frame (Q1 \--* Q) M.
  { applys W. }
  { rewrite* <- qwand_equiv. }
Qed.










Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.



(* ########################################################### *)
(** ** The [xsimpl] tactic *)

(** The definitions and properties above enable us to instantiate
    the [xsimpl] tactic, which implements powerful simplifications
    for Separation Logic entailments.

    For technical reasons, we need to provide a definition for [hgc],
    a restriction of [htop] to affine heap predicates. For our purpose,
    it suffices to define [hgc] as an alias for [htop]. *)


(* ################################################ *)
(** *** Definition and properties of [haffine] and [hgc] *)

Definition haffine (H:hprop) :=
  True.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  \exists H, H.

Definition htop := hgc.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. Admitted.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. Admitted.


(* ################################################ *)
(** *** Functor instantiation to obtain [xsimpl] *)

Notation "\Top" := (htop) : hprop_scope.

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.


End SepSimplArgs.


(** We are now ready to instantiate the functor, and open the
    contents of the module [SepHsimplArgs], essentially pretending
    that we inlined here its contents. *)

Module Export HS := SepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

(** At this point, the tactic [xsimpl] is defined.
    There remains to customize the tactic so that it recognizes
    the predicate [p ~~> v] in a special way when performing
    simplifications. *)

(*  Internal hack: (the comment only makes sense in the context of [SepSimpl]).
    [xsimpl_pick_hsingle H] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]], and where [H] is of the form [p ~~> v]
    It searches for [p ~~> v'] among the [Hi]. If it finds it, it
    moves this [Hi] to the front, just before [H1]. Else, it fails. *)

Ltac xsimpl_pick_hsingle H :=
  match H with hsingle ?p ?v =>
    xsimpl_pick_st ltac:(fun H' =>
      match H' with (hsingle p ?v') =>
        constr:(true) end)
  end.

(** Internal hack:
    The following instantiation of the [xsimpl] hook enables the tactic
    to simplify [p ~~> v] against [p ~~> v'] by generating the
    side-condition [v = v']. *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle _ _ => xsimpl_pick_hsingle H; apply xsimpl_lr_cancel_eq;
                   [ xsimpl_lr_cancel_eq_repr_post tt | ]
  end.

(** At this point, the tactic [xsimpl] is available.
    See the file [SLFHimpl.v] for demos of its usage. *)

(** One last hack is to improve the [math] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
     form [val_int ?n = val_int ?m], and so that it is able to process
     the well-founded relations [dowto] and [upto] for induction on
     integers. *)

Ltac math_0 ::=
  unfolds downto, upto;
  try match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end.


    Global Opaque          hwand qwand htop hgc haffine.