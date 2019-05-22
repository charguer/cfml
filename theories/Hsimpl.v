(**

This file provides the essential tactics for manipulation of 
Separation Logic formulae.

The functor in this file assumes:
- definitions for Separation Logic operators
- a minimal set of properties of theses operators.

It provides the following tactics:
- [hsimpl] simplifies heap entailments
- [hpull] is a restricted version of [hsimpl] that only act over the LHS
- [hchange] performs transitivity steps in entailments, modulo frame
- [rew_heap] normalizes heap predicate expressions

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Export TLCbuffer Hoare.


(* ********************************************************************** *)
(** * Assumptions of the functor *)

Module Type HsimplParams.


(* ---------------------------------------------------------------------- *)
(* ** Operators *)

Parameter hprop : Type.

Parameter himpl : hprop -> hprop -> Prop.

Definition qimpl A (Q1 Q2:A->hprop) :=
  forall r, himpl (Q1 r) (Q2 r).

Parameter hempty : hprop.

Parameter hstar : hprop -> hprop -> hprop.

Parameter hpure : Prop -> hprop.

Parameter htop : hprop.

Parameter hgc : hprop.

Parameter hwand : hprop -> hprop -> hprop.

Parameter qwand : forall A, (A->hprop) -> (A->hprop) -> hprop.

Parameter hexists : forall A, (A->hprop) -> hprop.

Parameter hforall : forall A, (A->hprop) -> hprop.

Parameter haffine : hprop -> Prop.


(* ---------------------------------------------------------------------- *)
(* ** Notations *)

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : heap_scope.

Notation "\Top" := (htop) : heap_scope.

Notation "\GC" := (hgc) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Properties *)

Implicit Types P : Prop.
Implicit Types H : hprop.

(** Entailment is an order *)

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Parameter himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).

(** Commutative monoid *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** The frame property for entailment *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** Characterization of hpure *)

Parameter himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].

Parameter himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.

(** Characterization of hexists *)

Parameter himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.

Parameter himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).

(** Characterization of hforall *)

Parameter himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).

Parameter himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.

Parameter hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).

(** Characterization of wands *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).

Parameter qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.

(** Characterization of htop *)

Parameter himpl_htop_r : forall H,
  H ==> \Top.

Parameter hstar_htop_htop :
  \Top \* \Top = \Top.

(** Characterization of hgc *)

Parameter haffine_hempty :
  haffine \[].

Parameter himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.

Parameter hstar_hgc_hgc :
  \GC \* \GC = \GC.


End HsimplParams.


(* ********************************************************************** *)
(** * Body of the functor *)

Module HsimplSetup (HP : HsimplParams).
Import HP.

Implicit Types H : hprop.
Implicit Types P : Prop.

Hint Resolve himpl_refl.


(* ********************************************************************** *)
(** * Derived properties of operators *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [qimpl] *)

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. hnfs*. Qed.

Hint Resolve qimpl_refl.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using.
  intros. rewrite <- hstar_assoc.
  rewrite (@hstar_comm H1 H2). rewrite~ hstar_assoc.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1. 
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1. 
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hempty] *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l.
  applys~ hstar_comm.
  applys~ hstar_hempty_l.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hpure] *)

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. rewrite <- (hstar_hempty_l H).
  applys himpl_frame_lr W. applys~ himpl_hempty_hpure.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hexists] *)

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hforall] *)

Lemma himpl_hforall_l_exists : forall A (J:A->hprop) H,
  (exists x, J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv (x&M). applys* himpl_hforall_l. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hwand] *)

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
Proof using. intros. rewrite hstar_comm. applys~ himpl_hwand_r_inv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. applys himpl_hwand_r. rewrite~ hstar_hempty_l. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- (hstar_hempty_l (\[] \-* H)). applys hwand_cancel. }
  { apply himpl_hwand_r. rewrite~ hstar_hempty_r. }
Qed.

Hint Rewrite hwand_hempty_l : rew_heap.

Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using. 
  introv HP. rewrite <- (hstar_hempty_l (\[P] \-* H)).
  forwards~ K: himpl_hempty_hpure P.
  applys* himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_hwand_r. applys himpl_hwand_r.
  rewrite hstar_assoc. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. applys himpl_hwand_r. rewrite <- (hstar_comm (H1 \* H2)). 
  rewrite (@hstar_comm H1). rewrite hstar_assoc.
  applys himpl_trans. applys himpl_frame_r. applys hwand_cancel.
  applys hwand_cancel.
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [qwand] *)

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma himpl_qwand_r_inv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. introv M. rewrite~ <- qwand_equiv. Qed.

Lemma himpl_qwand_hstar_same_r : forall A (Q:A->hprop) H,
  H ==> Q \--* (Q \*+ H).
Proof using. intros. applys* himpl_qwand_r. Qed.

Lemma himpl_forall_trans : forall H1 H2,
  (forall H, H ==> H1 -> H ==> H2) ->
  H1 ==> H2.
Proof using. introv M. applys~ M. Qed.

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using.
  intros. applys himpl_forall_trans. intros H M.
  rewrite qwand_equiv in M. specializes M x.
  rewrite hwand_equiv. rewrite~ hstar_comm.
Qed.

Arguments qwand_specialize [ A ].


(* ---------------------------------------------------------------------- *)
(* ** Properties of [htop] *)

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { applys himpl_forall_trans. intros H M. applys himpl_trans M.
    rewrite <- (hstar_hempty_r \Top) at 1. applys himpl_frame_r.
    applys himpl_htop_r. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hgc] *)

(* -none- *)


(* ********************************************************************** *)
(** * Representation predicates *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for representation predicates *)

(** The arrow notation typically takes the form [x ~> R x],
   to indicate that [X] is the logical value that describes the
   heap structure [x], according to the representation predicate [R].
   It is just a notation for the heap predicate [R X x]. *)

Definition repr (A:Type) (S:A->hprop) (x:A) : hprop :=
  S x.

Notation "x '~>' S" := (repr S x)
  (at level 33, no associativity) : heap_scope.

Lemma repr_eq : forall (A:Type) (S:A->hprop) (x:A),
  (x ~> S) = (S x).
Proof using. auto. Qed.

(** [x ~> Id X] holds when [x] is equal to [X] in the empty heap.
   [Id] is called the identity representation predicate. *)

Definition Id {A:Type} (X:A) (x:A) :=
  \[ X = x ].

(** [xrepr_clean] simplifies instances of
   [p ~> (fun _ => _)] by unfolding the arrow,
   but only when the body does not captures
   mklocally-bound variables. This tactic should
   normally not be used directly *)

Ltac xrepr_clean_core tt :=
  repeat match goal with |- context C [?p ~> ?E] =>
   match E with (fun _ => _) =>
     let E' := eval cbv beta in (E p) in
     let G' := context C [E'] in
     let G := match goal with |- ?G => G end in
     change G with G' end end.

Tactic Notation "xrepr_clean" :=
  xrepr_clean_core tt.

Lemma repr_id : forall A (x X:A),
  (x ~> Id X) = \[X = x].
Proof using. intros. unfold Id. xrepr_clean. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** [rew_heap] tactic to normalize expressions with [hstar] *)

(** [rew_heap] removes empty heap predicates, and normalizes w.r.t.
    associativity of star. 

    [rew_heap_assoc] only normalizes w.r.t. associativity. 
    (It should only be used internally for tactic implementation. *)

Lemma star_post_empty : forall B (Q:B->hprop),
  Q \*+ \[] = Q.
Proof using. extens. intros. rewrite* hstar_hempty_r. Qed.

Hint Rewrite hstar_hempty_l hstar_hempty_r
            hstar_assoc star_post_empty : rew_heap.

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.

Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_star.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_star.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_star.

Hint Rewrite hstar_assoc : rew_heap_assoc.

Tactic Notation "rew_heap_assoc" :=
  autorewrite with rew_heap_assoc.


(* ---------------------------------------------------------------------- *)
(** Auxiliary tactics used by [hpull] and [hsimpl] *)

Ltac remove_empty_heaps_from H :=
  match H with context[ ?H1 \* \[] ] =>
    match is_evar_as_bool H1 with
    | false => rewrite (@hstar_hempty_r H1)
    | true => let X := fresh in
              set (X := H1);
              rewrite (@hstar_hempty_r X);
              subst X
    end end.

Ltac remove_empty_heaps_haffine tt :=
  repeat match goal with |- haffine ?H => remove_empty_heaps_from H end.

Ltac remove_empty_heaps_left tt :=
  repeat match goal with |- ?H1 ==> _ => remove_empty_heaps_from H1 end.

Ltac remove_empty_heaps_right tt :=
  repeat match goal with |- _ ==> ?H2 => remove_empty_heaps_from H2 end.



(* ********************************************************************** *)
(* * Tactic [hsimpl] for heap entailments *)

(* ---------------------------------------------------------------------- *)
(* [haffine] placeholder *)

Ltac haffine_core tt := (* to be generalized lated *)
  try solve [ assumption | apply haffine_hempty ].

Tactic Notation "haffine" :=
  haffine_core tt.


(* ---------------------------------------------------------------------- *)
(* Hints for tactics such as [hsimpl] *)

Inductive Hsimpl_hint : list Boxer -> Type :=
  | hsimpl_hint : forall (L:list Boxer), Hsimpl_hint L.

Ltac hsimpl_hint_put L :=
  let H := fresh "Hint" in
  generalize (hsimpl_hint L); intros H.

Ltac hsimpl_hint_next cont :=
  match goal with H: Hsimpl_hint ((boxer ?x)::?L) |- _ =>
    clear H; hsimpl_hint_put L; cont x end.

Ltac hsimpl_hint_remove tt :=
  match goal with H: Hsimpl_hint _ |- _ => clear H end.


(* ---------------------------------------------------------------------- *)
(* Lemmas [hstars_reorder_..] to flip an iterated [hstar]. *)

(** [hstars_flip tt] applies to a goal of the form [H1 \* .. \* Hn \* \[]= ?H]
    and instantiates [H] with [Hn \* ... \* H1 \* \[]].
    If [n > 9], the maximum arity supported, the tactic unifies [H] with
    the original LHS. *)

Lemma hstars_flip_0 :
  \[] = \[].
Proof using. auto. Qed.

Lemma hstars_flip_1 : forall H1,
  H1 \* \[] = H1 \* \[].
Proof using. auto. Qed.

Lemma hstars_flip_2 : forall H1 H2,
  H1 \* H2 \* \[] = H2 \* H1 \* \[].
Proof using. intros. rew_heap. rewrite (hstar_comm H2). rew_heap~. Qed.

Lemma hstars_flip_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 \* \[] = H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_2 H1). rew_heap. rewrite (hstar_comm H3). rew_heap~. Qed.

Lemma hstars_flip_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 \* \[] = H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_3 H1). rew_heap. rewrite (hstar_comm H4). rew_heap~. Qed.

Lemma hstars_flip_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 \* \[] = H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_4 H1). rew_heap. rewrite (hstar_comm H5). rew_heap~. Qed.

Lemma hstars_flip_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* \[]
  = H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_5 H1). rew_heap. rewrite (hstar_comm H6). rew_heap~. Qed.

Lemma hstars_flip_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* \[]
  = H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_6 H1). rew_heap. rewrite (hstar_comm H7). rew_heap~. Qed.

Lemma hstars_flip_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* \[]
  = H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_7 H1). rew_heap. rewrite (hstar_comm H8). rew_heap~. Qed.

Lemma hstars_flip_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* \[] 
  = H9 \* H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_8 H1). rew_heap. rewrite (hstar_comm H9). rew_heap~. Qed.

Ltac hstars_flip_lemma i :=
  match number_to_nat i with
  | 0%nat => constr:(hstars_flip_0)
  | 1%nat => constr:(hstars_flip_1)
  | 2%nat => constr:(hstars_flip_2)
  | 3%nat => constr:(hstars_flip_3)
  | 4%nat => constr:(hstars_flip_4)
  | 5%nat => constr:(hstars_flip_5)
  | 6%nat => constr:(hstars_flip_6)
  | 7%nat => constr:(hstars_flip_7)
  | 8%nat => constr:(hstars_flip_8)
  | 9%nat => constr:(hstars_flip_9)
  | _ => constr:(hstars_flip_1) (* unsupported *)
  end.

Ltac hstars_arity i Hs :=
  match Hs with
  | \[] => constr:(i)
  | ?H1 \* ?H2 => hstars_arity (S i) H2
  end.

Ltac hstars_flip_arity tt :=
  match goal with |- ?HL = ?HR => hstars_arity 0%nat HL end.

Ltac hstars_flip tt :=
  let i := hstars_flip_arity tt in
  let L := hstars_flip_lemma i in
  eapply L.



(* ---------------------------------------------------------------------- *)
(* Lemmas [hstars_pick_...] to extract hyps in depth. *)

(** [hstars_search Hs test] applies to an expression [Hs]
    of the form either [H1 \* ... \* Hn \* \[]] 
    or [H1 \* ... \* Hn]. It invokes the function [test i Hi]
    for each of the [Hi] in turn until the tactic succeeds. 
    In the particular case of invoking [test n Hn] when there
    is no trailing [\[]], the call is of the form [test (hstars_last n) Hn]
    where [hstars_last] is an identity tag. *)

Definition hstars_last (A:Type) (X:A) := X.

Ltac hstars_search Hs test :=
  let rec aux i Hs :=
    first [ match Hs with ?H \* _ => test i H end
          | match Hs with _ \* ?Hs' => aux (S i) Hs' end
          | match Hs with ?H => test (hstars_last i) H end ] in
  aux 1%nat Hs.

(** [hstars_pick_lemma i] returns one of the lemma below,
    which enables reordering in iterated stars, by extracting
    the i-th item to bring it to the front. *)

Lemma hstars_pick_1 : forall H1 H,
  H1 \* H = H1 \* H.
Proof using. auto. Qed.

Lemma hstars_pick_2 : forall H1 H2 H,
  H1 \* H2 \* H = H2 \* H1 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H1). Qed.

Lemma hstars_pick_3 : forall H1 H2 H3 H,
  H1 \* H2 \* H3 \* H = H3 \* H1 \* H2 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_4 : forall H1 H2 H3 H4 H,
  H1 \* H2 \* H3 \* H4 \* H = H4 \* H1 \* H2 \* H3 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_5 : forall H1 H2 H3 H4 H5 H,
  H1 \* H2 \* H3 \* H4 \* H5 \* H = H5 \* H1 \* H2 \* H3 \* H4 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_6 : forall H1 H2 H3 H4 H5 H6 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H 
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_7 : forall H1 H2 H3 H4 H5 H6 H7 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H 
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_8 : forall H1 H2 H3 H4 H5 H6 H7 H8 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H 
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H8). applys hstars_pick_8. Qed.

Lemma hstars_pick_last_1 : forall H1,
  H1 = H1.
Proof using. auto. Qed.

Lemma hstars_pick_last_2 : forall H1 H2,
  H1 \* H2 = H2 \* H1.
Proof using. intros. rewrite~ (hstar_comm). Qed.

Lemma hstars_pick_last_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 = H3 \* H1 \* H2.
Proof using. intros. rewrite~ (hstar_comm H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_last_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 = H4 \* H1 \* H2 \* H3.
Proof using. intros. rewrite~ (hstar_comm H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_last_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 = H5 \* H1 \* H2 \* H3 \* H4.
Proof using. intros. rewrite~ (hstar_comm H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_last_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5.
Proof using. intros. rewrite~ (hstar_comm H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_last_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6.
Proof using. intros. rewrite~ (hstar_comm H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_last_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7.
Proof using. intros. rewrite~ (hstar_comm H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_last_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8.
Proof using. intros. rewrite~ (hstar_comm H8). applys hstars_pick_8. Qed.

Ltac hstars_pick_lemma i :=
  let unsupported tt := fail 100 "hstars_pick supports only arity up to 9" in
  match i with
  | hstars_last ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_last_1)
    | 2%nat => constr:(hstars_pick_last_2)
    | 3%nat => constr:(hstars_pick_last_3)
    | 4%nat => constr:(hstars_pick_last_4)
    | 5%nat => constr:(hstars_pick_last_5)
    | 6%nat => constr:(hstars_pick_last_6)
    | 7%nat => constr:(hstars_pick_last_7)
    | 8%nat => constr:(hstars_pick_last_8)
    | 9%nat => constr:(hstars_pick_last_9)
    | _ => unsupported tt
    end
  | ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_1)
    | 2%nat => constr:(hstars_pick_2)
    | 3%nat => constr:(hstars_pick_3)
    | 4%nat => constr:(hstars_pick_4)
    | 5%nat => constr:(hstars_pick_5)
    | 6%nat => constr:(hstars_pick_6)
    | 7%nat => constr:(hstars_pick_7)
    | 8%nat => constr:(hstars_pick_8)
    | 9%nat => constr:(hstars_pick_9)
    | _ => unsupported tt
    end
  end.



(* ---------------------------------------------------------------------- *)
(* Tactic [hsimpl] *)

(** ... doc for [hsimpl] to update

   At the end, there remains a heap entailment with a simplified
   LHS and a simplified RHS, with items not cancelled out.
   At this point, if the goal is of the form [H ==> \GC] or [H ==> \Top] or
   [H ==> ?H'] for some evar [H'], then [hsimpl] solves the goal.
   Else, it leaves whatever remains.

   For the cancellation part, [hsimpl] cancels out [H] from the LHS
   with [H'] from the RHS if either [H'] is syntactically equal to [H],
   or if [H] and [H'] both have the form [x ~> ...] for the same [x].
   Note that, in case of a mismatch with [x ~> R X] on the LHS and
   [x ~> R' X'] on the RHS, [hsimpl] will produce a goal of the form
   [(x ~> R X) = (x ~> R' X')] which will likely be unsolvable.
   It is the user's responsability to perform the appropriate conversion
   steps prior to calling [hsimpl].

   Remark: the reason for the special treatment of [x ~> ...] is that
   it is very useful to be able to automatically cancel out
   [x ~> R X] from the LHS with [x ~> R ?Y], for some evar [?Y] which
   typically is introduced from an existential, e.g. [\exists Y, x ~> R Y].

   Remark: importantly, [hsimpl] does not attempt any simplification on
   a representation predicate of the form [?x ~> ...], when the [?x]
   is an uninstantiated evar. Such situation may arise for example
   with the following RHS: [\exists p, (r ~> Ref p) \* (p ~> Ref 3)].

   As a special feature, [hsimpl] may be provided optional arguments
   for instantiating the existentials (instead of introducing evars).
   These optional arguments need to be given in left-right order,
   and are used on a first-match basis: the head value is used if its
   type matches the type expected by the existential, else an evar
   is introduced for that existential. *)


(** [Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt)] is interepreted as
    the entailement [Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt] where
    - [Hla] denotes "cleaned up" items from the left hand side
    - [Hlw] denotes the [H1 \-* H2] and [Q1 \--* Q2] items from the left hand side
    - [Hlt] denotes the remaining items to process  items from the left hand side
    - [Hra] denotes "cleaned up" items from the right hand side
    - [Hrg] denotes the [\GC] and [\Top] items from the right hand side
    - [Hrt] denotes the remaining items to process from the right hand side 

    Note: we assume that all items consist of iterated hstars, and are 
    always terminated by an empty heap.
*)

Definition Hsimpl (HL HR:hprop*hprop*hprop) :=
  let '(Hla,Hlw,Hlt) := HL in
  let '(Hra,Hrg,Hrt) := HR in
  Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt.

(** [protect X] is use to prevent [hsimpl] from investigating inside [X] *)

Definition protect (A:Type) (X:A) : A := X.

(** Auxiliary lemmas to prove lemmas for [hsimpl] implementation. *)

Lemma Hsimpl_trans_l : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 HR,
  Hsimpl (Hla2,Hlw2,Hlt2) HR ->
  Hla1 \* Hlw1 \* Hlt1 ==> Hla2 \* Hlw2 \* Hlt2 ->
  Hsimpl (Hla1,Hlw1,Hlt1) HR.
Proof using.
  introv M1 E. destruct HR as [[Hra Hrg] Hrt]. unfolds Hsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Hsimpl_trans_r : forall Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2 HL,
  Hsimpl HL (Hra2,Hrg2,Hrt2) ->
  Hra2 \* Hrg2 \* Hrt2 ==> Hra1 \* Hrg1 \* Hrt1 ->
  Hsimpl HL (Hra1,Hrg1,Hrt1).
Proof using.
  introv M1 E. destruct HL as [[Hla Hlw] Hlt]. unfolds Hsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Hsimpl_trans : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2,
  Hsimpl (Hla2,Hlw2,Hlt2) (Hra2,Hrg2,Hrt2) ->
  (Hla2 \* Hlw2 \* Hlt2 ==> Hra2 \* Hrg2 \* Hrt2 ->
   Hla1 \* Hlw1 \* Hlt1 ==> Hra1 \* Hrg1 \* Hrt1) ->
  Hsimpl (Hla1,Hlw1,Hlt1) (Hra1,Hrg1,Hrt1).
Proof using. introv M1 E. unfolds Hsimpl. eauto. Qed.

(* DEPRECATED
Lemma Hsimpl_trans_l' : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 HR,
  (forall Hra Hrg Hrt,
    Hsimpl (Hla2,Hlw2,Hlt2) (Hra,Hrg,Hrt) ->
  Hla1 \* Hlw1 \* Hlt1 ==> Hla2 \* Hlw2 \* Hlt2 ->

[[Hla Hlw] Hlt]

  Hsimpl (Hla1,Hlw1,Hlt1) HR.
Proof using.
  introv M1 E. destruct HR as [[Hra Hrg] Hrt]. unfolds Hsimpl.
  applys* himpl_trans M1.
Qed.
*)

(* ---------------------------------------------------------------------- *)
(** ** Basic cancellation tactic used to establish lemmas used by [hsimpl] *)

Lemma hstars_simpl_start : forall H1 H2,
  H1 \* \[] ==> \[] \* H2 \* \[] ->
  H1 ==> H2.
Proof using. introv M. rew_heap~ in *. Qed.

Lemma hstars_simpl_keep : forall H1 Ha H Ht,
  H1 ==> (H \* Ha) \* Ht ->
  H1 ==> Ha \* H \* Ht.
Proof using. introv M. rew_heap in *. rewrite~ hstar_comm_assoc. Qed.

Lemma hstars_simpl_cancel : forall H1 Ha H Ht,
  H1 ==> Ha \* Ht ->
  H \* H1 ==> Ha \* H \* Ht.
Proof using. introv M. rewrite hstar_comm_assoc. applys~ himpl_frame_r. Qed.

Lemma hstars_simpl_pick_lemma : forall H1 H1' H2,
  H1 = H1' ->
  H1' ==> H2 ->
  H1 ==> H2.
Proof using. introv M. subst~. Qed.

Ltac hstars_simpl_pick i :=
  (* Remark: the [hstars_pick_last] lemmas should never be needed here *)
  let L := hstars_pick_lemma i in
  eapply hstars_simpl_pick_lemma; [ apply L | ].

Ltac hstars_simpl_start tt :=
  match goal with |- ?H1 ==> ?H2 => idtac end;
  applys hstars_simpl_start;
  rew_heap_assoc.

Ltac hstars_simpl_step tt :=
  match goal with |- ?Hl ==> ?Ha \* ?H \* ?H2 =>
    first [
      hstars_search Hl ltac:(fun i H' => 
        match H' with H => hstars_simpl_pick i end);
      apply hstars_simpl_cancel
    | apply hstars_simpl_keep ]
  end.

Ltac hstars_simpl_post tt :=
  rew_heap; try apply himpl_refl.

Ltac hstars_simpl_core tt :=
  hstars_simpl_start tt;
  repeat (hstars_simpl_step tt);
  hstars_simpl_post tt.

Tactic Notation "hstars_simpl" :=
  hstars_simpl_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Transition lemmas *)

(** Transition lemmas to start the process *)

Lemma hpull_protect : forall H1 H2,
  H1 ==> protect H2 ->
  H1 ==> H2.
Proof using. auto. Qed.

Lemma hsimpl_start : forall H1 H2,
  Hsimpl (\[], \[], (H1 \* \[])) (\[], \[], (H2 \* \[])) ->
  H1 ==> H2.
Proof using. introv M. unfolds Hsimpl. rew_heap~ in *. Qed.
(* Note: [repeat rewrite hstar_assoc] after applying this lemma *)

(** Transition lemmas for LHS extraction operations *)

Ltac hsimpl_l_start M :=
  introv M;
  match goal with HR: hprop*hprop*hprop |- _ =>
    destruct HR as [[Hra Hrg] Hrt]; unfolds Hsimpl end.

Ltac hsimpl_l_start' M :=
  hsimpl_l_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma hsimpl_l_hempty : forall Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, Hlt) HR ->
  Hsimpl (Hla, Hlw, (\[] \* Hlt)) HR.
Proof using. hsimpl_l_start' M. Qed.

Lemma hsimpl_l_hpure : forall P Hla Hlw Hlt HR,
  (P -> Hsimpl (Hla, Hlw, Hlt) HR) ->
  Hsimpl (Hla, Hlw, (\[P] \* Hlt)) HR.
Proof using.
  hsimpl_l_start M. rewrite hstars_pick_3. applys* himpl_hstar_hpure_l.
Qed.

Lemma hsimpl_l_hexists : forall A (J:A->hprop) Hla Hlw Hlt HR,
  (forall x, Hsimpl (Hla, Hlw, (J x \* Hlt)) HR) ->
  Hsimpl (Hla, Hlw, (hexists J \* Hlt)) HR.
Proof using. 
  hsimpl_l_start M. rewrite hstars_pick_3. rewrite hstar_hexists.
  applys* himpl_hexists_l. intros. rewrite~ <- hstars_pick_3.
Qed.

Lemma hsimpl_l_acc_wand : forall H Hla Hlw Hlt HR,
  Hsimpl (Hla, (H \* Hlw), Hlt) HR ->
  Hsimpl (Hla, Hlw, (H \* Hlt)) HR.
Proof using. hsimpl_l_start' M. Qed.

Lemma hsimpl_l_acc_other : forall H Hla Hlw Hlt HR,
  Hsimpl ((H \* Hla), Hlw, Hlt) HR ->
  Hsimpl (Hla, Hlw, (H \* Hlt)) HR.
Proof using. hsimpl_l_start' M. Qed.

(** Transition lemmas for LHS cancellation operations
    ---Hlt is meant to be empty there *)

Lemma hsimpl_l_cancel_hwand_hempty : forall H2 Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, (H2 \* Hlt)) HR ->
  Hsimpl (Hla, ((\[] \-* H2) \* Hlw), Hlt) HR.
Proof using. hsimpl_l_start' M. Qed.

(* DEPRECATED
Lemma hsimpl_l_cancel_hwand : forall H1 H2 Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, (H2 \* Hlt)) HR ->
  Hsimpl ((H1 \* Hla), ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. hsimpl_l_start' M. applys hwand_cancel. Qed.

Lemma hsimpl_l_cancel_qwand : forall A (x:A) (Q1 Q2:A->hprop) Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, (Q2 x \* Hlt)) HR ->
  Hsimpl ((Q1 x \* Hla), ((Q1 \--* Q2) \* Hlw), Hlt) HR.
Proof using.
  hsimpl_l_start' M. applys himpl_trans.
  applys himpl_frame_r. applys qwand_specialize x.
  applys hwand_cancel. 
Qed.
*)

Lemma hsimpl_l_cancel_hwand : forall H1 H2 Hla Hlw Hlt HR,
  Hsimpl (\[], Hlw, (Hla \* H2 \* Hlt)) HR ->
  Hsimpl ((H1 \* Hla), ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. hsimpl_l_start' M. applys hwand_cancel. Qed.

Lemma hsimpl_l_cancel_qwand : forall A (x:A) (Q1 Q2:A->hprop) Hla Hlw Hlt HR,
  Hsimpl (\[], Hlw, (Hla \* Q2 x \* Hlt)) HR ->
  Hsimpl ((Q1 x \* Hla), ((Q1 \--* Q2) \* Hlw), Hlt) HR.
Proof using.
  hsimpl_l_start' M. applys himpl_hstar_trans_r.
  applys qwand_specialize x. applys hwand_cancel.
Qed.

Lemma hsimpl_l_keep_wand : forall H Hla Hlw Hlt HR,
  Hsimpl ((H \* Hla), Hlw, Hlt) HR ->
  Hsimpl (Hla, (H \* Hlw), Hlt) HR.
Proof using. hsimpl_l_start' M. Qed.

Lemma hsimpl_l_hwand_reorder : forall H1 H1' H2 Hla Hlw Hlt HR,
  H1 = H1' ->
  Hsimpl (Hla, ((H1' \-* H2) \* Hlw), Hlt) HR ->
  Hsimpl (Hla, ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. intros. subst*. Qed.

Lemma hsimpl_l_cancel_hwand_hstar : forall H1 H2 H3 Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Hsimpl ((H1 \* Hla), (((H1 \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using.
  hsimpl_l_start' M. rewrite hwand_curry_eq. applys hwand_cancel.
Qed.

Lemma hsimpl_l_cancel_hwand_hstar_hempty : forall H2 H3 Hla Hlw Hlt HR,
  Hsimpl (Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Hsimpl (Hla, (((\[] \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using. hsimpl_l_start' M. Qed.

(** Transition lemmas for RHS extraction operations *)

Ltac hsimpl_r_start M :=
  introv M;
  match goal with HL: hprop*hprop*hprop |- _ =>
    destruct HL as [[Hla Hlw] Hlt]; unfolds Hsimpl end.

Ltac hsimpl_r_start' M :=
  hsimpl_r_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma hsimpl_r_hempty : forall Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (\[] \* Hrt)).
Proof using. hsimpl_r_start' M. Qed.

Lemma hsimpl_r_hwand_same : forall H Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, ((H \-* H) \* Hrt)).
Proof using. hsimpl_r_start' M. applys himpl_hempty_hwand_same. Qed.

Lemma hsimpl_r_hpure : forall P Hra Hrg Hrt HL,
  P ->
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (\[P] \* Hrt)).
Proof using.
  introv HP. hsimpl_r_start' M. applys* himpl_hempty_hpure.
Qed.

Lemma hsimpl_r_hexists : forall A (x:A) (J:A->hprop) Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, (J x \* Hrt)) ->
  Hsimpl HL (Hra, Hrg, (hexists J \* Hrt)).
Proof using. hsimpl_r_start' M. applys* himpl_hexists_r. Qed.

Lemma hsimpl_r_id : forall A (x X:A) Hra Hrg Hrt HL,
  (X = x) ->
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (x ~> Id X \* Hrt)).
Proof using.
  introv ->. hsimpl_r_start' M. rewrite repr_id.
  applys* himpl_hempty_hpure.
Qed.

Lemma hsimpl_r_id_unify : forall A (x:A) Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (x ~> Id x \* Hrt)).
Proof using. introv M. applys~ hsimpl_r_id. Qed.

Lemma hsimpl_r_keep : forall H Hra Hrg Hrt HL,
  Hsimpl HL ((H \* Hra), Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. hsimpl_r_start' M. Qed.

(** Transition lemmas for [\Top] and [\GC] cancellation *)

  (* [H] meant to be [\GC] or [\Top] *)
Lemma hsimpl_r_hgc_or_htop : forall H Hra Hrg Hrt HL, 
  Hsimpl HL (Hra, (H \* Hrg), Hrt) ->
  Hsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. hsimpl_r_start' M. Qed.

Lemma hsimpl_r_htop_replace_hgc : forall Hra Hrg Hrt HL,
  Hsimpl HL (Hra, (\Top \* Hrg), Hrt) ->
  Hsimpl HL (Hra, (\GC \* Hrg), (\Top \* Hrt)).
Proof using. hsimpl_r_start' M. applys himpl_hgc_r. haffine. Qed.

Lemma hsimpl_r_hgc_drop : forall Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (\GC \* Hrt)).
Proof using. hsimpl_r_start' M. applys himpl_hgc_r. haffine. Qed.

Lemma hsimpl_r_htop_drop : forall Hra Hrg Hrt HL,
  Hsimpl HL (Hra, Hrg, Hrt) ->
  Hsimpl HL (Hra, Hrg, (\Top \* Hrt)).
Proof using. hsimpl_r_start' M. applys himpl_htop_r. Qed.

(** Transition lemmas for LHS/RHS cancellation 
    --- meant to be applied when Hlw and Hlt are empty *)

Ltac hsimpl_lr_start M :=
  introv M; unfolds Hsimpl; rew_heap in *.

Ltac hsimpl_lr_start' M :=
  hsimpl_lr_start M; hstars_simpl;
  try (applys himpl_trans (rm M); hstars_simpl).

Lemma hsimpl_lr_cancel_same : forall H Hla Hlw Hlt Hra Hrg Hrt,
  Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Hsimpl ((H \* Hla), Hlw, Hlt) (Hra, Hrg, (H \* Hrt)).
Proof using. hsimpl_lr_start' M. Qed.

Lemma hsimpl_lr_cancel_htop : forall H Hla Hlw Hlt Hra Hrg Hrt,
  Hsimpl (Hla, Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt) ->
  Hsimpl ((H \* Hla), Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt).
Proof using.
  hsimpl_lr_start M. rewrite (hstar_comm_assoc Hra) in *.
  rewrite <- hstar_htop_htop. rew_heap. applys himpl_frame_lr M.
  applys himpl_htop_r.
Qed.

Lemma hsimpl_lr_cancel_hgc : forall Hla Hlw Hlt Hra Hrg Hrt,
  Hsimpl (Hla, Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt) ->
  Hsimpl ((\GC \* Hla), Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt).
Proof using.
  hsimpl_lr_start M. rewrite (hstar_comm_assoc Hra).
  rewrite <- hstar_hgc_hgc at 2. rew_heap.
  applys himpl_frame_r. applys himpl_trans M. hstars_simpl.
Qed.

(* NOTE NEEDED? *)
Lemma hsimpl_lr_cancel_eq : forall H1 H2 Hla Hlw Hlt Hra Hrg Hrt,
  (H1 = H2) ->
  Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Hsimpl ((H1 \* Hla), Hlw, Hlt) (Hra, Hrg, (H2 \* Hrt)).
Proof using. introv ->. apply~ hsimpl_lr_cancel_same. Qed.

Lemma hsimpl_lr_cancel_eq_repr : forall A p (E1 E2:A->hprop) Hla Hlw Hlt Hra Hrg Hrt,
  E1 = E2 ->
  Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Hsimpl (((p ~> E1) \* Hla), Hlw, Hlt) (Hra, Hrg, ((p ~> E2) \* Hrt)).
Proof using. introv M. subst. apply~ hsimpl_lr_cancel_same. Qed.

Lemma hsimpl_lr_hwand : forall H1 H2 Hla,
  Hsimpl (\[], \[], (H1 \* Hla)) (\[], \[], H2 \* \[]) ->
  Hsimpl (Hla, \[], \[]) ((H1 \-* H2) \* \[], \[], \[]).
Proof using.
  hsimpl_lr_start' M. apply himpl_hwand_r.
  applys himpl_trans (rm M). hstars_simpl.
Qed.

Lemma hsimpl_lr_hwand_hfalse : forall Hla H1,
  Hsimpl (Hla, \[], \[]) ((\[False] \-* H1) \* \[], \[], \[]).
Proof using.
  intros. generalize True. hsimpl_lr_start M. apply himpl_hwand_r. 
  rewrite hstar_comm. applys himpl_hstar_hpure_l. auto_false.
Qed.

Lemma hsimpl_lr_qwand : forall A (Q1 Q2:A->hprop) Hla,
  (forall x, Hsimpl (\[], \[], (Q1 x \* Hla)) (\[], \[], Q2 x \* \[])) ->
  Hsimpl (Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using. 
  hsimpl_lr_start M. applys himpl_qwand_r. intros x.
  specializes M x. rew_heap~ in M.
Qed.

Lemma hsimpl_lr_qwand_unit : forall (Q1 Q2:unit->hprop) Hla,
  Hsimpl (\[], \[], (Q1 tt \* Hla)) (\[], \[], (Q2 tt \* \[])) ->
  Hsimpl (Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using. introv M. applys hsimpl_lr_qwand. intros []. applys M. Qed.

Lemma hsimpl_lr_hforall : forall A (J:A->hprop) Hla,
  (forall x, Hsimpl (\[], \[], Hla) (\[], \[], J x \* \[])) ->
  Hsimpl (Hla, \[], \[]) ((hforall J) \* \[], \[], \[]).
Proof using. 
  hsimpl_lr_start M. applys himpl_hforall_r. intros x.
  specializes M x. rew_heap~ in M.
Qed.

Lemma himpl_lr_refl : forall Hla,
  Hsimpl (Hla, \[], \[]) (Hla, \[], \[]).
Proof using. intros. unfolds Hsimpl. hstars_simpl. Qed.

(* NEEDED?
Lemma himpl_lr_refl_hempty_r : forall Hla,
  Hsimpl (Hla, \[], \[]) (Hla \* \[], \[], \[]).
Proof using. intros. unfolds Hsimpl. hstars_simpl. Qed.
*)

Lemma himpl_lr_qwand_unify : forall A (Q:A->hprop) Hla,
  Hsimpl (Hla, \[], \[]) ((Q \--* (Q \*+ Hla)) \* \[], \[], \[]).
Proof using. intros. unfolds Hsimpl. hstars_simpl. applys himpl_qwand_hstar_same_r. Qed.

Lemma himpl_lr_htop : forall Hla Hrg,
  Hsimpl (\[], \[], \[]) (\[], Hrg, \[]) ->
  Hsimpl (Hla, \[], \[]) (\[], (\Top \* Hrg), \[]).
Proof using.
  hsimpl_lr_start M. rewrite <- (hstar_hempty_l Hla).
  applys himpl_hstar_trans_l M. hstars_simpl. apply himpl_htop_r.
Qed.

(* optional
Lemma himpl_lr_hgc_hempty : forall Hla Hrg,
  Hsimpl (\[], \[], \[]) (\[], Hrg), \[]) ->
  Hsimpl (\[], \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using. apply haffine_hempty. Qed.
*)

Lemma himpl_lr_hgc : forall Hla Hrg,
  haffine Hla ->
  Hsimpl (\[], \[], \[]) (\[], Hrg, \[]) ->
  Hsimpl (Hla, \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using.
  introv N. hsimpl_lr_start M. rewrite <- (hstar_hempty_l Hla).
  applys himpl_hstar_trans_l M. hstars_simpl. apply* himpl_hgc_r.
Qed.

Lemma hsimpl_lr_exit_nogc : forall Hla Hra,
  Hla ==> Hra ->
  Hsimpl (Hla, \[], \[]) (Hra, \[], \[]).
Proof using. introv M. unfolds Hsimpl. hstars_simpl. auto. Qed.

Lemma hsimpl_lr_exit : forall Hla Hra Hrg,
  Hla ==> Hra \* Hrg ->
  Hsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv M. unfolds Hsimpl. hstars_simpl. rewrite~ hstar_comm. Qed.

(** Lemmas to flip accumulators back in place *)

Lemma hsimpl_flip_acc_l : forall Hla Hra Hla' Hrg,
  Hla = Hla' ->
  Hsimpl (Hla', \[], \[]) (Hra, Hrg, \[]) ->
  Hsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Lemma hsimpl_flip_acc_r : forall Hla Hra Hra' Hrg,
  Hra = Hra' ->
  Hsimpl (Hla, \[], \[]) (Hra', Hrg, \[]) ->
  Hsimpl (Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Ltac hsimpl_flip_acc_l tt :=
  eapply hsimpl_flip_acc_l; [ hstars_flip tt | ].

Ltac hsimpl_flip_acc_r tt :=
  eapply hsimpl_flip_acc_r; [ hstars_flip tt | ].

Ltac hsimpl_flip_acc_lr tt :=
  hsimpl_flip_acc_l tt; hsimpl_flip_acc_r tt.

(* NOT NEEDED
Lemma hsimpl_lr_exit : forall Hla Hlw Hlt Hra Hrg Hrt,
  Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt ->
  Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt).
Proof using. auto. Qed.
*)

(* ---------------------------------------------------------------------- *)
(** ** Lemmas to pick the hypothesis to cancel *)

(** [hsimpl_pick i] applies to a goal of the form
    [Hsimpl ((H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Hsimpl ((Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]. *)

Lemma hsimpl_pick_lemma : forall Hla1 Hla2 Hlw Hlt HR,
  Hla1 = Hla2 ->
  Hsimpl (Hla2, Hlw, Hlt) HR ->
  Hsimpl (Hla1, Hlw, Hlt) HR.
Proof using. introv M. subst~. Qed.
 
Ltac hsimpl_pick i :=
  let L := hstars_pick_lemma i in
  eapply hsimpl_pick_lemma; [ apply L | ].

(** [hsimpl_pick_st f] applies to a goal of the form
    [Hsimpl ((H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Hsimpl ((Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]
    for the first [i] such that [f Hi] returns [true]. *)

Ltac hsimpl_pick_st f :=
  match goal with |- Hsimpl (?Hla, ?Hlw, ?Hlt) ?HR => 
    hstars_search Hla ltac:(fun i H => 
      match f H with true => hsimpl_pick i end)
  end.

(** [hsimpl_pick_syntactically H] is a variant of the above that only
    checks for syntactic equality, not unifiability. *)

Ltac hsimpl_pick_syntactically H :=
  hsimpl_pick_st ltac:(fun H' =>
    match H' with H => constr:(true) end).

(** [hsimpl_pick_unifiable H] applies to a goal of the form 
    [Hsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [H] among the [Hi]. 
    If it finds it, it moves this [Hi] to the front, just before [H1]. 
    Else, it fails. *)

Ltac hsimpl_pick_unifiable H :=
  match goal with |- Hsimpl (?Hla, ?Hlw, ?Hlt) ?HR => 
    hstars_search Hla ltac:(fun i H' => 
      unify H H'; hsimpl_pick i)
  end.

(** [hsimpl_pick_same H] is a choice for one of the above two,
    it is the default version used by [hsimpl].
    Syntactic matching is faster but less expressive. *)

Ltac hsimpl_pick_same H :=
  hsimpl_pick_unifiable H.

(** [hsimpl_pick_applied Q] applies to a goal of the form 
    [Hsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [Q ?x] among the [Hi]. 
    If it finds it, it moves this [Hi] to the front, just before [H1]. 
    Else, it fails. *)

Ltac hsimpl_pick_applied Q :=
  hsimpl_pick_st ltac:(fun H' =>
    match H' with Q _ => constr:(true) end).

(** [repr_get_predicate H] applies to a [H] of the form [p ~> R _ ... _]
    and it returns [R]. *)

Ltac repr_get_predicate H :=
  match H with ?p ~> ?E => get_head E end.

(** [hsimpl_pick_repr H] applies to a goal of the form 
    [Hsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]], and where [H] is of the form [p ~> R _]
    (same as [repr _ p]). It searches for [p ~> R _] among the [Hi]. 
    If it finds it, it moves this [Hi] to the front, just before [H1]. 
    Else, it fails. *)

Ltac hsimpl_pick_repr H :=
  match H with ?p ~> ?E => 
    let R := get_head E in
    hsimpl_pick_st ltac:(fun H' =>
      match H' with (p ~> ?E') => 
        let R' := get_head E' in
        match R' with R => constr:(true) end end)
  end.


(* ---------------------------------------------------------------------- *)
(** ** Tactic start and stop *)

Opaque Hsimpl.

Ltac hsimpl_handle_qimpl tt :=
  match goal with
  | |- @qimpl _ _ _ ?Q2 => is_evar Q2; apply qimpl_refl
  | |- @qimpl unit _ ?Q1 ?Q2 => let t := fresh "_tt" in intros t; destruct t
  | |- @qimpl _ _ _ _ => let r := fresh "r" in intros r
  | |- himpl _ ?H2 => is_evar H2; apply himpl_refl
  | |- himpl _ _ => idtac
  | |- eq _ _ => applys himpl_antisym
  | _ => fail 1 "not a goal for hsimpl/hpull"
  end.

Ltac hsimpl_intro tt :=
  applys hsimpl_start.

Ltac hpull_start tt :=
  pose ltac_mark;
  intros;
  hsimpl_handle_qimpl tt;
  applys hpull_protect;
  hsimpl_intro tt.

Ltac hsimpl_start tt :=
  pose ltac_mark;
  intros;
  hsimpl_handle_qimpl tt;
  hsimpl_intro tt.

Ltac hsimpl_post_before_generalize tt :=
  idtac.

Ltac hsimpl_post_after_generalize tt :=
  idtac.

Ltac himpl_post_processing_for_hyp H :=
  idtac.

Ltac hsimpl_handle_false_subgoals tt :=
  tryfalse.

(* DEPRECATED
Ltac hsimpl_handle_haffine_subgoals tt :=
  match goal with |- haffine _ =>   
    try solve [ haffine ] end.
*)

Ltac hsimpl_clean tt :=
  try remove_empty_heaps_right tt;
  try remove_empty_heaps_left tt;
  try hsimpl_hint_remove tt.

Ltac hsimpl_generalize tt :=
  hsimpl_post_before_generalize tt;
  hsimpl_handle_false_subgoals tt;
  gen_until_mark_with_processing ltac:(himpl_post_processing_for_hyp);
  hsimpl_post_after_generalize tt.

Ltac hsimpl_post tt :=
  hsimpl_clean tt;
  hsimpl_generalize tt.

Ltac hpull_post tt :=
  hsimpl_clean tt;
  unfold protect;
  hsimpl_generalize tt.


(* ---------------------------------------------------------------------- *)
(** ** Auxiliary functions step *)

(** [hsimpl_lr_cancel_eq_repr_post tt] is meant to simplify goals of the form [E1 = E2]
   that arises from cancelling [p ~> E1] with [p ~> E2] in the case where [E1] and [E2]
   share the same head symbol, that is, the same representation predicate [R]. *)

Ltac hsimpl_lr_cancel_eq_repr_post tt :=
  try fequal; try reflexivity.

(* DEPRECATED
  try solve
   [ reflexivity
   | fequal; fequal; first [ eassumption | symmetry; eassumption ] ];
      try match goal with |- repr ?X ?l = repr ?Y ?l => match constr:((X,Y)) with
      | (?F1 _, ?F1 _) => fequal; fequal
      | (?F1 ?F2 _, ?F1 ?F2 _) => fequal; fequal
      | (?F1 ?F2 ?F3 _, ?F1 ?F2 ?F3 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 _, ?F1 ?F2 ?F3 ?F4 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 _, ?F1 ?F2 ?F3 ?F4 ?F5 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 ?F9 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 ?F9 _) => fequal; fequal
      end end.
*)

(** [hsimpl_r_hexists_apply tt] is a tactic to apply [hsimpl_r_hexists]
    by exploiting a hint if one is available (see the hint section above)
    to specify the instantiation of the existential. *)

Ltac hsimpl_r_hexists_apply tt :=
  first [
    hsimpl_hint_next ltac:(fun x =>
      match x with
      | __ => eapply hsimpl_r_hexists
      | _ => apply (@hsimpl_r_hexists _ x)
      end)
  | eapply hsimpl_r_hexists ].

(** [hsimpl_hook H] can be customize to handle cancellation of specific 
    kind of heap predicates (e.g., [hsingle]). *)

Ltac hsimpl_hook H := fail.


(* ---------------------------------------------------------------------- *)
(** ** Tactic step *)

Ltac hsimpl_hwand_hstars_l tt :=
  match goal with |- Hsimpl (?Hla, ((?H1s \-* ?H2) \* ?Hlw), \[]) ?HR => 
    hstars_search H1s ltac:(fun i H =>
      let L := hstars_pick_lemma i in
      eapply hsimpl_l_hwand_reorder;
      [ apply L 
      | match H with
        | \[] => apply hsimpl_l_cancel_hwand_hstar_hempty
        | _ => hsimpl_pick_same H; apply hsimpl_l_cancel_hwand_hstar
        end
      ])
  end.

Ltac hsimpl_step_l tt :=
  match goal with |- Hsimpl ?HL ?HR => 
  match HL with
  | (?Hla, ?Hlw, (?H \* ?Hlt)) =>
    match H with 
    | \[] => apply hsimpl_l_hempty
    | \[?P] => apply hsimpl_l_hpure; intro
    | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
    | hexists ?J => apply hsimpl_l_hexists; intro
    | ?H1 \-* ?H2 => apply hsimpl_l_acc_wand
    | ?Q1 \--* ?Q2 => apply hsimpl_l_acc_wand
    | _ => apply hsimpl_l_acc_other
    end
  | (?Hla, ((?H1 \-* ?H2) \* ?Hlw), \[]) => 
      match H1 with
      | \[] => apply hsimpl_l_cancel_hwand_hempty
      | (_ \* _) => hsimpl_hwand_hstars_l tt
      | _ => first [ hsimpl_pick_same H1; apply hsimpl_l_cancel_hwand
                   | apply hsimpl_l_keep_wand ] 
      end
  | (?Hla, ((?Q1 \--* ?Q2) \* ?Hlw), \[]) => 
      first [ hsimpl_pick_applied Q1; eapply hsimpl_l_cancel_qwand
            | apply hsimpl_l_keep_wand ]
  end end.

(* Limitation: [((Q1 \*+ H) \--* Q2) \* H] is not automatically 
   simplified to [Q1 \--* Q2]. *)

Ltac hsimpl_hgc_or_htop_cancel cancel_item cancel_lemma :=
  (* match goal with |- Hsimpl (?Hla, \[], \[]) (?Hra, (?H \* ?Hrg), ?Hrt) => *)
  repeat (hsimpl_pick_same cancel_item; apply cancel_lemma).

Ltac hsimpl_hgc_or_htop_step tt :=
  match goal with |- Hsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) => 
    match constr:((Hrg,H)) with
    | (\[], \GC) => applys hsimpl_r_hgc_or_htop;
                    hsimpl_hgc_or_htop_cancel (\GC) hsimpl_lr_cancel_hgc
    | (\[], \Top) => applys hsimpl_r_hgc_or_htop;
                    hsimpl_hgc_or_htop_cancel (\GC) hsimpl_lr_cancel_htop;
                    hsimpl_hgc_or_htop_cancel (\Top) hsimpl_lr_cancel_htop
    | (\GC \* \[], \Top) => applys hsimpl_r_htop_replace_hgc; 
                            hsimpl_hgc_or_htop_cancel (\Top) hsimpl_lr_cancel_htop
    | (\GC \* \[], \GC) => applys hsimpl_r_hgc_drop
    | (\Top \* \[], \GC) => applys hsimpl_r_hgc_drop
    | (\Top \* \[], \Top) => applys hsimpl_r_htop_drop
    end end.

Ltac hsimpl_cancel_same H :=
  hsimpl_pick_same H; apply hsimpl_lr_cancel_same.

Ltac hsimpl_step_r tt :=
  match goal with |- Hsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) => 
  match H with
  | ?H' => hsimpl_hook H (* else continue *)
  | \[] => apply hsimpl_r_hempty
  | \[?P] => apply hsimpl_r_hpure
  | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
  | ?H \-* ?H'eqH =>
      match H with
      | \[?P] => fail 1 (* don't cancel out cause [P] might contain a contradiction *)
      | _ => 
        match H'eqH with 
        | H => apply hsimpl_r_hwand_same 
        (* | protect H => apply hsimpl_r_hwand_same  --NOTE: purposely refuse to unify this*)
        end
      end
  | hexists ?J => hsimpl_r_hexists_apply tt
  | \GC => hsimpl_hgc_or_htop_step tt
  | \Top => hsimpl_hgc_or_htop_step tt
  | protect ?H' => apply hsimpl_r_keep
  | protect ?Q' _ => apply hsimpl_r_keep
  | ?H' => is_not_evar H;  hsimpl_cancel_same H (* else continue *)
  | ?p ~> _ => hsimpl_pick_repr H; apply hsimpl_lr_cancel_eq_repr; 
               [ hsimpl_lr_cancel_eq_repr_post tt | ]  (* else continue *)
  | ?x ~> Id ?X => has_no_evar x; apply hsimpl_r_id
  (* TODO DEPRECATED? | ?x ~> ?T _ => has_no_evar x;
                  let M := fresh in assert (M: T = Id); [ reflexivity | clear M ];
                  apply hsimpl_r_id; [ try reflexivity |  ] *)
  | ?x ~> ?T_evar ?X_evar => has_no_evar x; is_evar T_evar; is_evar X_evar; 
                           apply hsimpl_r_id_unify
  | _ => apply hsimpl_r_keep
  end end.

Ltac hsimpl_step_lr tt :=
  match goal with |- Hsimpl (?Hla, \[], \[]) (?Hra, ?Hrg, \[]) => 
    match Hrg with
    | \[] =>
       match Hra with 
       | ?H1 \* \[] => 
         match H1 with
         | ?Hra_evar => is_evar Hra_evar; rew_heap; apply himpl_lr_refl (* else continue *)
       (*   | ?Hla' => (* unify Hla Hla'; *) apply himpl_lr_refl (* else continue *) TODO: needed? *)
         | ?Q1 \--* ?Q2 => is_evar Q2; eapply himpl_lr_qwand_unify
         | \[False] \-* ?H2 => apply hsimpl_lr_hwand_hfalse
         | ?H1 \-* ?H2 => hsimpl_flip_acc_l tt; apply hsimpl_lr_hwand
         | ?Q1 \--* ?Q2 => 
             hsimpl_flip_acc_l tt; 
             match H1 with
             | @qwand unit ?Q1' ?Q2' => apply hsimpl_lr_qwand_unit
             | _ => apply hsimpl_lr_qwand; intro
             end
         | hforall _ => hsimpl_flip_acc_l tt; apply hsimpl_lr_hforall; intro
                        (* TODO: optimize for iterated \forall bindings *)
         end
       | \[] => apply himpl_lr_refl
       | _ => hsimpl_flip_acc_lr tt; apply hsimpl_lr_exit_nogc
       end 
    | (\Top \* _) => apply himpl_lr_htop
    | (\GC \* _) => apply himpl_lr_hgc;
                    [ try remove_empty_heaps_haffine tt; try solve [ haffine ] | ] 
    | ?Hrg' => hsimpl_flip_acc_lr tt; apply hsimpl_lr_exit
  end end.

  (* TODO: handle [?HL (?Hra_evar, (\GC \* ..), \[])] *)


Ltac hsimpl_step tt :=
  first [ hsimpl_step_l tt
        | hsimpl_step_r tt
        | hsimpl_step_lr tt ].


(* ---------------------------------------------------------------------- *)
(** ** Tactic notation *)

Ltac hpull_core tt :=
  hpull_start tt;
  repeat (hsimpl_step tt);
  hpull_post tt.

Tactic Notation "hpull" := hpull_core tt.
Tactic Notation "hpull" "~" := hpull; auto_tilde.
Tactic Notation "hpull" "*" := hpull; auto_star.

Ltac hsimpl_core tt :=
  hsimpl_start tt;
  repeat (hsimpl_step tt);
  hsimpl_post tt.

Tactic Notation "hsimpl" := hsimpl_core tt.
Tactic Notation "hsimpl" "~" := hsimpl; auto_tilde.
Tactic Notation "hsimpl" "*" := hsimpl; auto_star.

Tactic Notation "hsimpl" constr(L) :=
  match type of L with
  | list Boxer => hsimpl_hint_put L
  | _ => hsimpl_hint_put (boxer L :: nil)
  end; hsimpl.
Tactic Notation "hsimpl" constr(X1) constr(X2) :=
  hsimpl (>> X1 X2).
Tactic Notation "hsimpl" constr(X1) constr(X2) constr(X3) :=
  hsimpl (>> X1 X2 X3).

Tactic Notation "hsimpl" "~" constr(L) :=
  hsimpl L; auto_tilde.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) :=
  hsimpl X1 X2; auto_tilde.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) constr(X3) :=
  hsimpl X1 X2 X3; auto_tilde.

Tactic Notation "hsimpl" "*" constr(L) :=
  hsimpl L; auto_star.
Tactic Notation "hsimpl" "*" constr(X1) constr(X2) :=
  hsimpl X1 X2; auto_star.
Tactic Notation "hsimpl" "*" constr(X1) constr(X2) constr(X3) :=
  hsimpl X1 X2 X3; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [hchange] *)

(** [hchange] performs rewriting on the LHS of an entailment.
  Essentially, it applies to a goal of the form [H1 \* H2 ==> H3],
  and exploits an entailment [H1 ==> H1'] to replace the goal with
  [H1' \* H2 ==> H3].

  The tactic is actually a bit more flexible in two respects:
  - it does not force the LHS to be exactly of the form [H1 \* H2]
  - it takes as argument any lemma, whose instantiation result in
    a heap entailment of the form [H1 ==> H1'].

  Concretely, the tactic is just a wrapper around an application
  of the lemma called [hchange_lemma], which appears below.

  [hchanges] combines a call to [hchange] with calls to [hsimpl]
  on the subgoals. *)

Lemma hchange_lemma : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 ==> H1 \* (H2 \-* protect H4) ->
  H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans (rm M2).
  applys himpl_hstar_trans_l (rm M1). applys hwand_cancel.
Qed.

Ltac hchange_apply L :=
  eapply hchange_lemma; [ eapply L | ].

(* Below, the modifier is either [__] or [himpl_of_eq]
   or [himpl_of_eq_sym] *)

Ltac hchange_build_entailment modifier K :=
  match modifier with
  | __ =>
     match type of K with
     | _ = _ => constr:(@himpl_of_eq _ _ _ K)
     | _ => constr:(K)
     end
  | _ => constr:(@modifier _ _ _ K)
  end.

Ltac hchange_perform L modifier cont :=
  forwards_nounfold_then L ltac:(fun K =>
    let M := hchange_build_entailment modifier K in
    hchange_apply M;
    cont tt).

Ltac hchange_core L modifier cont :=
  pose ltac_mark;
  intros;
  match goal with
  | |- _ ==> _ => idtac
  | |- _ ===> _ => let x := fresh "r" in intros x
  end;
  hchange_perform L modifier cont;
  gen_until_mark.

Ltac hchange_hpull_cont tt :=
  hsimpl; unfold protect; try apply himpl_refl.

Ltac hchange_hsimpl_cont tt :=
  unfold protect; hsimpl; try apply himpl_refl.

  (* TODO DEPRECATED: [instantiate] useful? no longer...*)

Ltac hchange_nosimpl_base E modifier :=
  hchange_core E modifier ltac:(idcont).

Tactic Notation "hchange_nosimpl" constr(E) :=
  hchange_nosimpl_base E __.
Tactic Notation "hchange_nosimpl" "->" constr(E) :=
  hchange_nosimpl_base E himpl_of_eq.
Tactic Notation "hchange_nosimpl" "<-" constr(E) :=
  hchange_nosimpl_base himpl_of_eq_sym.

Ltac hchange_base E modif :=
  hchange_core E modif ltac:(hchange_hpull_cont).

Tactic Notation "hchange" constr(E) :=
  hchange_base E __.
Tactic Notation "hchange" "->" constr(E) :=
  hchange_base E himpl_of_eq.
Tactic Notation "hchange" "<-" constr(E) :=
  hchange_base E himpl_of_eq_sym.

Tactic Notation "hchange" "~" constr(E) :=
  hchange E; auto_tilde.
Tactic Notation "hchange" "*" constr(E) :=
  hchange E; auto_star.

Ltac hchanges_base E modif :=
  hchange_core E modif ltac:(hchange_hsimpl_cont).

Tactic Notation "hchanges" constr(E) :=
  hchanges_base E __.
Tactic Notation "hchanges" "->" constr(E) :=
  hchanges_base E himpl_of_eq.
Tactic Notation "hchange" "<-" constr(E) :=
  hchanges_base E himpl_of_eq_sym.

Tactic Notation "hchanges" "~" constr(E) :=
  hchanges E; auto_tilde.
Tactic Notation "hchanges" "*" constr(E) :=
  hchanges E; auto_star.

Tactic Notation "hchange" constr(E1) "," constr(E2) :=
  hchange E1; try hchange E2.
Tactic Notation "hchange" constr(E1) "," constr(E2) "," constr(E3) :=
  hchange E1; try hchange E2; try hchange E3.
Tactic Notation "hchange" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  hchange E1; try hchange E2; try hchange E3; try hchange E4.



(* ********************************************************************** *)
(** * Demos *)


(* ---------------------------------------------------------------------- *)
(** [rew_heap] demos *)

Lemma rew_heap_demo_with_evar : forall H1 H2 H3,
  (forall H, H1 \* (H \* H2) \* \[] = H3 -> True) -> True.
Proof using.
  introv M. dup 3.
  { eapply M. rewrite hstar_assoc. rewrite hstar_assoc. demo. }
  { eapply M. rew_heap_assoc. demo. }
  { eapply M. rew_heap. demo. }
Abort.


(* ---------------------------------------------------------------------- *)
(** [hstars] demos *)

Lemma hstars_flip_demo : forall H1 H2 H3 H4,
  (forall H, H1 \* H2 \* H3 \* H4 \* \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.

Lemma hstars_flip_demo_0 :
  (forall H, \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.


(* ---------------------------------------------------------------------- *)
(** [hsimpl_hint] demos *)

Lemma hsimpl_demo_hints : exists n, n = 3.
Proof using.
  hsimpl_hint_put (>> 3 true).
  hsimpl_hint_next ltac:(fun x => exists x).
  hsimpl_hint_remove tt.
Abort.


(* ---------------------------------------------------------------------- *)
(** [hstars_pick] demos *)

Lemma demo_hstars_pick_1 : forall H1 H2 H3 H4 Hresult,
  (forall H, H1 \* H2 \* H3 \* H4 = H -> H = Hresult -> True) -> True.
Proof using. 
  introv M. dup 2.
  { eapply M. let L := hstars_pick_lemma 3 in eapply L. demo. }
  { eapply M. let L := hstars_pick_lemma (hstars_last 4) in eapply L. demo. }
Qed.


(* ---------------------------------------------------------------------- *)
(** [hstars_simpl] demos *)

Lemma demo_hstars_simpl_1 : forall H1 H2 H3 H4 H5,
  H2 ==> H5 ->
  H1 \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1.
Proof using. 
  intros. dup.
  { hstars_simpl_start tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_post tt. auto. }
  { hstars_simpl. auto. }
Qed.

Lemma demo_hstars_simpl_2 : forall H1 H2 H3 H4 H5,
  (forall H, H \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1 -> True) -> True.
Proof using. 
  introv M. eapply M. hstars_simpl.
Abort.


(* ---------------------------------------------------------------------- *)
(** [hsimpl_pick] demos *)

Lemma hsimpl_pick_demo : forall (Q:bool->hprop) (P:Prop) H1 H2 H3 Hlw Hlt Hra Hrg Hrt,
  (forall HX HY,  
    Hsimpl ((H1 \* H2 \* H3 \* Q true \* (\[P] \-* HX) \* HY \* \[]), Hlw, Hlt)
           (Hra, Hrg, Hrt)
  -> True) -> True.
Proof using.
  introv M. applys (rm M).
  let L := hstars_pick_lemma 2%nat in set (X:=L).
  eapply hsimpl_pick_lemma. apply X.
  hsimpl_pick 2%nat.
  hsimpl_pick_same H3.
  hsimpl_pick_applied Q.
  hsimpl_pick_same H2.
  hsimpl_pick_unifiable H3.
  hsimpl_pick_unifiable \[True].
  hsimpl_pick_unifiable (\[P] \-* H1).
Abort.


(* ---------------------------------------------------------------------- *)
(** [hpull] and [hsimpl] demos *)

Tactic Notation "hpull0" := hpull_start tt.
Tactic Notation "hsimpl0" := hsimpl_start tt.
Tactic Notation "hsimpl1" := hsimpl_step tt.
Tactic Notation "hsimpl2" := hsimpl_post tt.
Tactic Notation "hsimpll" := hsimpl_step_l tt.
Tactic Notation "hsimplr" := hsimpl_step_r tt.
Tactic Notation "hsimpllr" := hsimpl_step_lr tt.

Notation "'HSIMPL' Hla Hlw Hlt =====> Hra Hrg Hrt" := (Hsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt))
  (at level 69, Hla, Hlw, Hlt, Hra, Hrg, Hrt at level 0,
   format "'[v' 'HSIMPL' '/' Hla  '/' Hlw  '/' Hlt  '/' =====> '/' Hra  '/' Hrg  '/' Hrt ']'").

Lemma hpull_demo : forall H1 H2 H3 H,
  (H1 \* \[] \* (H2 \* \exists (y:int) z (n:nat), \[y = y + z + n]) \* H3) ==> H.
Proof using.
  dup.
  { intros. hpull0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl2. demo. }
  { hpull. intros. demo. }
Abort.

Lemma hsimpl_demo_stars : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  dup 3.
  { hpull. demo. }
  { intros. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. demo. }
  { intros. hsimpl. demo. }
Abort. (* TODO: coq bug, abort should be required, not qed allowed *)

Lemma hsimpl_demo_keep_order : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H3 \* H6 \* H7.
Proof using. intros. hsimpl. demo. Abort.

Lemma hsimpl_demo_stars_top : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 ==> H3 \* H1 \* H2 \* \Top.
Proof using.
  dup.
  { intros. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { intros. hsimpl. }
Abort.

Lemma hsimpl_demo_hint : forall H1 (Q:int->hprop),
  Q 4 ==> Q 3 ->
  H1 \* Q 4 ==> \exists x, Q x \* H1.
Proof using.
  introv W. dup.
  { intros. hsimpl_hint_put (>> 3).
    hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl2. auto. }
  { hsimpl 3. auto. }
Qed.

Lemma hsimpl_demo_stars_gc : forall H1 H2,
  haffine H2 ->
  H1 \* H2 ==> H1 \* \GC.
Proof using.
  dup.
  { intros. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. }
  { intros. hsimpl~. }
Abort.

Lemma hsimpl_demo_evar_1 : forall H1 H2,
  (forall H, H1 \* H2 ==> H -> True) -> True.
Proof using. intros. eapply H. hsimpl. Abort.

Lemma hsimpl_demo_evar_2 : forall H1,
  (forall H, H1 ==> H1 \* H -> True) -> True.
Proof using.
  introv M. dup.
  { eapply M. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { eapply M. hsimpl~. }
Abort.

Lemma hsimpl_demo_htop_both_sides : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top.
Proof using.
  dup.
  { intros. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { intros. hsimpl~. }
Abort.

Lemma hsimpl_demo_htop_multiple : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top \* \Top.
Proof using. intros. hsimpl~. Abort.

Lemma hsimpl_demo_hgc_multiple : forall H1 H2,
  haffine H2 ->
  H1 \* H2 \* \GC ==> H1 \* \GC \* \GC.
Proof using. intros. hsimpl~. Qed.

Lemma hsimpl_demo_hwand : forall H1 H2 H3 H4,
  (H1 \-* (H2 \-* H3)) \* H1 \* H4 ==> (H2 \-* (H3 \* H4)).
Proof using. 
  dup.
  { intros. hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { intros. hsimpl~. }
Qed.

Lemma hsimpl_demo_qwand : forall A (x:A) (Q1 Q2:A->hprop) H1,
  H1 \* (H1 \-* (Q1 \--* Q2)) \* (Q1 x) ==> (Q2 x).
Proof using. intros. hsimpl~. Qed.

Lemma hsimpl_demo_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H1 \* (H3 \-* (H2 \* H3)).
Proof using. intros. hsimpl~. Qed.

Lemma hsimpl_demo_qwand_r : forall A (x:A) (Q1 Q2:A->hprop) H1 H2,
  H1 \* H2 ==> H1 \* (Q1 \--* (Q1 \*+ H2)).
Proof using. intros. hsimpl. Qed.

Lemma hsimpl_demo_hwand_multiple_1 : forall H1 H2 H3 H4 H5,
  H1 \-* H4 ==> H5 ->
  (H2 \* ((H1 \* H2 \* H3) \-* H4)) \* H3 ==> H5.
Proof using. introv M. hsimpl. auto. Qed.

Lemma hsimpl_demo_hwand_multiple_2 : forall H1 H2 H3 H4 H5,
  (H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5))) \* (H2 \-* H3) \* H4 ==> H5.
Proof using. intros. hsimpl. Qed.

Lemma hsimpl_demo_hwand_hempty : forall H1 H2 H3,
  (\[] \-* H1) \* H2 ==> H3.
Proof using. intros. hsimpl. Abort.

Lemma hsimpl_demo_hwand_hstar_hempty : forall H0 H1 H2 H3,
  ((H0 \* \[]) \-* \[] \-* H1) \* H2 ==> H3.
Proof using. intros. hsimpl. rew_heap. Abort.
(* [hsimpl] does not simplify inner [\[] \-* H1], known limitation. *)

Lemma hsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using.
  intros. dup.
  { hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { hsimpl. }
Qed.

Lemma hsimpl_demo_repr_1 : forall p q (R:int->int->hprop),
  p ~> R 3 \* q ~> R 4 ==> \exists n m, p ~> R n \* q ~> R m.
Proof using. 
  intros. dup.
  { hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { hsimpl~. }
Qed.

Lemma hsimpl_demo_repr_2 : forall p (R R':int->int->hprop),
  R = R' ->
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using. introv E. hsimpl. subst R'. hsimpl. Qed.

Lemma hsimpl_demo_repr_3 : forall p (R:int->int->hprop),
  let R' := R in
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using. 
  intros. dup.
  { hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { hsimpl~. }
Qed.

Lemma hsimpl_demo_repr_4 : forall p n m (R:int->int->hprop),
  n = m + 0 ->
  p ~> R n ==> p ~> R m.
Proof using. intros. hsimpl. math. Qed.
 
(* NOTE: in the presence of [let R' := R], it is possible that R'
   is renamed into R during a call to [hsimpl], because
   [remove_empty_heaps_right tt] called from [hsimpl_clean tt]
   invokes [rewrite] which performs a matching upto unification,
   and not syntactically. *) 

Lemma hsimpl_demo_gc_0 : forall H1 H2,
  H1 ==> H2 \* \GC \* \GC.
Proof using. intros. hsimpl. Abort.

Lemma hsimpl_demo_gc_1 : forall H1 H2,
  H1 ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using.
  intros. dup.
  { hsimpl0. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1. hsimpl1.
    hsimpl1. hsimpl1. hsimpl1. hsimpl2. demo. }
  { hsimpl~. demo. }
Abort.

Lemma hsimpl_demo_gc_2 : forall H1 H2 H3,
  H1 \* H2 \* \Top \* \GC \* \Top ==> H3 \* \GC \* \GC.
Proof using. intros. hsimpl. Abort.
  (* Remark: no attempt to collapse [\Top] or [\GC] on the RHS is performed,
     they are dealt with only by cancellation from the LHS *)

Lemma hsimpl_demo_gc_3 : forall H1 H2,
  H1 \* H2 \* \GC \* \GC ==> H2 \* \GC \* \GC \* \GC.
Proof using. intros. hsimpl. haffine. Abort.

Lemma hsimpl_demo_gc_4 : forall H1 H2,
  H1 \* H2 \* \GC  ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using. intros. hsimpl. Abort.


(* ---------------------------------------------------------------------- *)
(** [hchange] demos *)

Lemma hchange_demo_1 : forall H1 H2 H3 H4 H5 H6,
  H1 ==> H2 \* H3 ->
  H1 \* H4 ==> (H5 \-* H6).
Proof using.
  introv M. dup 3.
  { hchange_nosimpl M. hsimpl. demo. }
  { hchange M. hsimpl. demo. }
  { hchanges M. demo. }
Qed.

Lemma hchange_demo_2 : forall A (Q:A->hprop) H1 H2 H3,
  H1 ==> \exists x, Q x \* (H2 \-* H3) ->
  H1 \* H2 ==> \exists x, Q x \* H3.
Proof using.
  introv M. dup 3.
  { hchange_nosimpl M. hsimpl. unfold protect. hsimpl. }
  { hchange M. hsimpl. }
  { hchanges M. }
Qed.

Lemma hchange_demo_hwand_hpure : forall (P:Prop) H1 H2 H3,
  P ->
  H1 \* H3 ==> H2 ->
  (\[P] \-* H1) \* H3 ==> H2.
Proof using.
  introv HP M1. dup 3.
  { hchange (hwand_hpure_l_intro P H1). auto. hchange M1. }
  { hchange hwand_hpure_l_intro. auto. hchange M1. }
  { hchange hwand_hpure_l_intro, M1. auto. }
Qed.

Lemma hchange_demo_4 : forall A (Q1 Q2:A->hprop) H,
  Q1 ===> Q2 ->
  Q1 \*+ H ===> Q2 \*+ H.
Proof using. introv M. hchanges M. Qed.

Lemma hsimpl_demo_hfalse : forall H1 H2,
  H1 ==> \[False] ->
  H1 \* H2 ==> \[False].
Proof using.
  introv M. dup.
  { hchange_nosimpl M. hsimpl0. hsimpl1. hsimpl1. hsimpl1. 
    hsimpl1. hsimpl1. hsimpl1. hsimpl1. }
  { hchange M. }
Qed.

Lemma hchange_demo_hforall_l : forall (Q:int->hprop) H1,
  (\forall x, Q x) \* H1 ==> Q 2 \* \Top.
Proof using.
  intros. hchange (hforall_specialize 2). hsimpl.
Qed.

(* ---------------------------------------------------------------------- *)

End HsimplSetup.
