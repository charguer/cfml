(**

This file formalizes characteristic formulae in weakest-precondition form
for plain Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaSep.
Open Scope heap_scope.

Implicit Types v : val.
Implicit Types t : trm.


(* ********************************************************************** *)
(* * WP generator *)

(* ---------------------------------------------------------------------- *)
(* ** Type of a WP *)

(** A formula is a predicate over a postcondition. *)

Definition formula := (val -> hprop) -> hprop.

Global Instance Inhab_formula : Inhab formula.
Proof using. apply (Inhab_of_val (fun _ => \[])). Qed.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** [wp_triple t Q] defines the weakest-precondition for term [t] 
    and postcondition [Q]. 

    [H ==> wp_triple t Q] is equivalent to [triple t H Q].

    [wp_triple] is defined in terms of the generic definition 
    of [weakestpre], which comes from [SepFunctor], and is defined as:
    [ Definition weakestpre F Q := \exists H, H \* \[F H Q]. ]
*)

Definition wp_triple (t:trm) : formula :=
  weakestpre (triple t).


(* ---------------------------------------------------------------------- *)
(* ** Definition of [local] for WP *)

(** [local F] transforms a weakestpre formula [F], e.g. of the form [wp_triple t],
    into a logically-equivalent formula that smoothly supports applications
    of the structural rule of Separation Logic. The definition is:

[[
Definition local (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).
]]

   The predicate [is_local F] asserts that [F] is a formula that subject the
   structural rules of Separation Logic. This property is captured by requiring
   that [F] be logically equivalent to [is_local F].

[[
Definition is_local (F:formula) :=
  F = local F.
]]

*)

(** Because [local] is later reused in a more general "lifted" settings,
    we need to make the type of formula parameterized by the return type,
    when defining [local]. *)

Definition formula_ (B:Type) := (B -> hprop) -> hprop.

(** The [local] predicate is a predicate transformer that typically
   applies to a WP, and allows for application
   of the frame rule, of the rule of consequence, of the garbage
   collection rule, and of extraction rules for existentials and
   pure facts. *)

Definition local B (F:formula_ B) : formula_ B :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).

(** The [is_local] predicate asserts that a predicate is subject
  to all the rules that the [local] predicate transformer supports. *)

Definition is_local B (F:formula_ B) :=
  F = local F.

(** [is_local_pred S] asserts that [is_local (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition is_local_pred B A (S:A->formula_ B) :=
  forall x, is_local (S x).



(* ---------------------------------------------------------------------- *)
(* ** Elimination rules for [is_local] *)

Section LocalProp.
Variable (B : Type).
Implicit Type Q : B->hprop.
Implicit Type F : formula_ B.

Lemma local_weaken : forall Q' F H Q,
  is_local F ->
  H ==> F Q ->
  Q ===> Q' ->
  H ==> F Q'.
Proof using.
  introv L M W. rewrite (rm L). hchanges (rm M).
  unfold local. hsimpl Q.
  hchanges (>> qwand_of_qimpl W).
  (* TODO: simplify *)
  applys qwand_himpl_r. hsimpl.
Qed.

Lemma local_top : forall F H Q,
  is_local F ->
  H ==> F (Q \*+ \Top) ->
  H ==> F Q.
Proof using.
  introv L M. rewrite L. hchanges (rm M). unfold local.
  hsimpl (Q \*+ \Top). hchanges (qwand_of_qimpl (Q \*+ \Top)).
  hsimpl.
Qed.

Lemma local_frame : forall H1 H2 F H Q,
  is_local F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x) ->
  H ==> F Q.
Proof using.
  introv L W M. rewrites (rm L). hchanges (rm W). hchanges (rm M).
  unfold local. hsimpl (fun x => H2 \-* Q x). (* TODO: simplify *)
  (* TODO: needs hqwand *)
  applys qwand_move_l. intros x. hchanges (hwand_cancel H2).
Qed.

Lemma local_frame_top : forall H1 H2 F H Q,
  is_local F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x \* \Top) ->
  H ==> F Q.
Proof using.
  introv L W M. applys* local_top. applys* local_frame.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [local] for WP *)

(** Local can be erased *)

Lemma local_erase : forall F Q,
  F Q ==> local F Q.
Proof using.
  intros. unfold local. hsimpl. hchanges (qwand_of_qimpl Q). hsimpl.
Qed.

Lemma local_erase' : forall H F Q,
  H ==> F Q ->
  H ==> local F Q.
Proof using.
  introv M. hchanges M. applys local_erase.
Qed.

(** Contradictions can be extracted from local formulae *)

Lemma local_false : forall F Q,
  (forall Q', F Q' ==> \[False]) ->
  (local F Q ==> \[False]).
Proof using.
  introv M. unfold local. hpull ;=> Q'. hchanges (M Q').
Qed.

(** [local] is a covariant transformer w.r.t. predicate inclusion *)

Lemma local_weaken_body : forall F F',
  F ===> F' ->
  local F ===> local F'.
Proof using.
  unfold local. introv M. intros Q. hpull ;=> Q'. hsimpl~ Q'.
Qed.

(** [local] is idempotent, i.e. nested applications
   of [local] are redundant *)

Lemma local_local : forall F,
  local (local F) = local F.
Proof using.
  intros F. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold local. hpull ;=> Q' Q''. hsimpl Q''.
    hchanges hstar_qwand. applys qwand_himpl_r.
    intros x.
    hchanges (qwand_himpl_hwand x Q' (Q \*+ \Top)).
    hchanges (hwand_cancel (Q' x) (Q x \* \Top)). }
  { hchanges local_erase. }
Qed.

(** A definition whose head is [local] satisfies [is_local] *)

Lemma is_local_local : forall F,
  is_local (local F).
Proof using. intros. unfolds. rewrite~ local_local. Qed.

(** Introduction rule for [is_local] on [weakestpre] *)

Lemma is_local_weakestpre : forall (T:hprop->(B->hprop)->Prop),
  SepBasicSetup.is_local T ->
  is_local (weakestpre T).
Proof using.
  introv L. unfold is_local. applys fun_ext_1 ;=> Q.
  applys himpl_antisym.
  { apply~ local_erase'. }
  { unfold local, wp_triple, weakestpre.
    hpull ;=> Q' H M. hsimpl (H \* (Q' \--* Q \*+ \Top)).
    xapply M. hsimpl. intros x. hchange (qwand_himpl_hwand x Q' (Q \*+ \Top)).
    hchange (hwand_cancel (Q' x)). hsimpl. }
Qed. (* LATER: simplify *)

End LocalProp.


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition wp_fail : formula := local (fun Q =>
  \[False]).

Definition wp_val (v:val) : formula := local (fun Q =>
  Q v).

Definition wp_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wp_fail
  | Some v => wp_val v
  end.

Definition wp_seq (F1 F2:formula) : formula := local (fun Q =>
  F1 (fun X => F2 Q)).

Definition wp_let (F1:formula) (F2of:val->formula) : formula := local (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wp_app (t:trm) :=
  local (wp_triple t).

Definition wp_if_val (v:val) (F1 F2:formula) : formula := local (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wp_if (F0 F1 F2:formula) : formula :=
  wp_let F0 (fun v => wp_if_val v F1 F2).

Definition wp_while (F1 F2:formula) : formula := local (fun Q =>
  \forall (R:formula),
  let F := wp_if F1 (wp_seq F2 R) (wp_val val_unit) in
  \[ is_local R /\ F ===> R] \-* (R Q)).

Definition wp_for_val (v1 v2:val) (F1:val->formula) : formula := local (fun Q =>
  \exists (n1:int) (n2:int), \[v1 = val_int n1 /\ v2 = val_int n2] \*
  \forall (S:int->formula),
  let F i := If (i <= n2) then (wp_seq (F1 i) (S (i+1)))
                          else (wp_val val_unit) in
  \[ is_local_pred S /\ (forall i, F i ===> S i)] \-* (S n1 Q)).


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint wp (E:ctx) (t:trm) : formula :=
  let aux := wp E in
  match t with
  | trm_val v => wp_val v
  | trm_var x => wp_var E x
  | trm_fix f x t1 => wp_val (val_fix f x (isubst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => wp_if (aux t0) (aux t1) (aux t2)
  | trm_let x t1 t2 => wp_let (aux t1) (fun X => wp (Ctx.add x X E) t2)
  | trm_app t1 t2 => wp_app (isubst E t)
  | trm_while t1 t2 => wp_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => 
      match t1, t2 with
      | trm_val v1, trm_val v2 => wp_for_val v1 v2 (fun X => wp (Ctx.add x X E) t3)
      | _, _ => wp_fail
      end
  end.



(* ********************************************************************** *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [wp_triple t] is a local formula *)

Lemma is_local_wp_triple : forall t,
  is_local (wp_triple t).
Proof using. intros. applys is_local_weakestpre. applys is_local_triple. Qed.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma triple_eq_himpl_wp_triple : forall H Q t,
  triple t H Q = (H ==> wp_triple t Q).
Proof using. intros. applys weakestpre_eq. applys is_local_triple. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_wp_triple : forall t F,
  (forall Q, triple t (F Q) Q) ->
  F ===> wp_triple t.
Proof using. introv M. intros Q. rewrite~ <- triple_eq_himpl_wp_triple. Qed.

(** Another corrolary of [triple_eq_himpl_wp_triple],
    (not used in the proofs below). *)

Lemma triple_wp_triple : forall t Q,
  triple t (wp_triple t Q) Q.
Proof using. intros. applys weakestpre_pre. applys is_local_triple. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [local] transformer *)

(** The [local] transformer is sound w.r.t. [triple] *)

Lemma triple_local_pre : forall t (F:formula) Q,
  (forall Q, triple t (F Q) Q) ->
  triple t (local F Q) Q.
Proof using.
  introv M. rewrite is_local_triple. unfold SepBasicSetup.local.
  unfold local. hpull ;=> Q'.
  hsimpl (F Q') ((Q' \--* Q \*+ \Top)) Q'. split.
  { applys~ M. }
  { hchanges qwand_cancel. }
Qed.

(** The tactic [remove_local] applies to goal of the form [triple t (local F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_local :=
  match goal with |- triple _ _ ?Q =>
    applys triple_local_pre; try (clear Q; intros Q); xpull; fold wp end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wp] *)

(** [wp_triple_ E t] is a shorthand for [wp_triple (substs E t)] *)

Definition wp_triple_ E t :=
  wp_triple (isubst E t).

(** [wp_sound t] asserts that [wp] is sound for all contexts [E],
    in the sense that the syntactic wp entails the semantics wp:
[[
    forall Q,  wp E t Q ==> wp_triple_ E t Q
]] *)

Definition wp_sound t := forall E,
  wp E t ===> wp_triple_ E t.


(** Soundness of the [wp] for the various constructs *)

Lemma wp_sound_var : forall x,
  wp_sound (trm_var x).
Proof using.
  intros. intros E. applys qimpl_wp_triple. simpl.
  intros Q. unfold wp_var. destruct (Ctx.lookup x E).
  { remove_local. apply~ triple_val. }
  { remove_local. intros; false~. }
Qed.

Lemma wp_sound_val : forall v,
  wp_sound (trm_val v).
Proof using.
  intros. intros E. applys qimpl_wp_triple. simpl.
  intros Q. remove_local. applys~ triple_val.
Qed.

Lemma wp_sound_fix : forall f x t,
  wp_sound (trm_fix f x t).
Proof using.
  intros. intros E. applys qimpl_wp_triple. simpl.
  intros Q. remove_local. lets: triple_fix. applys~ triple_fix.
Qed.

Lemma wp_sound_if : forall F1 F2 F3 E t1 t2 t3,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  F3 ===> wp_triple_ E t3 ->
  wp_if F1 F2 F3 ===> wp_triple_ E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. applys qimpl_wp_triple. simpl. intros Q.
  remove_local. applys triple_if.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros b. simpl. remove_local ;=> b' M. inverts M. case_if.
    { rewrite triple_eq_himpl_wp_triple. applys* M2. }
    { rewrite triple_eq_himpl_wp_triple. applys* M3. } }
  { introv N. applys local_false. intros Q'.
    hpull ;=> v' ->. false* N. hnfs*. }
Qed.

Lemma wp_sound_let : forall F1 F2 E x t1 t2,
  F1 ===> wp_triple_ E t1 ->
  (forall X, F2 X ===> wp_triple_ (Ctx.add x X E) t2) ->
  wp_let F1 F2 ===> wp_triple_ E (trm_let x t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. simpl. intros Q.
  remove_local. applys triple_let.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros X. simpl. rewrite triple_eq_himpl_wp_triple.
    rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma wp_sound_seq : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_seq F1 F2 ===> wp_triple_ E (trm_seq t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. simpl. intros Q.
  remove_local. applys triple_seq.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros X. simpl. rewrite triple_eq_himpl_wp_triple. applys* M2. }
Qed.

Lemma wp_sound_app : forall t1 t2,
  wp_sound (trm_app t1 t2).
Proof using.
  intros. intros E. applys qimpl_wp_triple. simpl.
  intros Q. remove_local.
  rewrite triple_eq_himpl_wp_triple. hsimpl.
Qed.

Lemma wp_sound_while : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_while F1 F2 ===> wp_triple_ E (trm_while t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. simpl. intros Q.
  remove_local. applys triple_hforall.
  set (R := wp_triple (trm_while (isubst E t1) (isubst E t2))).
  exists R. simpl. applys triple_hwand_hpure_l.
  { split.
    { applys is_local_wp_triple. }
    { clears Q. applys qimpl_wp_triple. intros Q.
      applys triple_while_raw. rewrite~ triple_eq_himpl_wp_triple.
      change ((trm_if (isubst E t1) (trm_seq (isubst E t2) (trm_while (isubst E t1) (isubst E t2))) val_unit))
        with (isubst E (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit)).
      applys~ wp_sound_if. 
      { applys* wp_sound_seq. eauto. }
      { intros Q'. applys wp_sound_val. } } }
  { rewrite~ triple_eq_himpl_wp_triple. }
Qed.

Lemma wp_sound_for_val : forall (x:var) v1 v2 F1 E t1,
  (forall X, F1 X ===> wp_triple_ (Ctx.add x X E) t1) ->
  wp_for_val v1 v2 F1 ===> wp_triple_ E (trm_for x v1 v2 t1).
Proof using. Opaque Ctx.add Ctx.rem.
  introv M. applys qimpl_wp_triple. simpl. intros Q.
  remove_local. intros n1 n2 (->&->).
  applys triple_hforall.
  set (S := fun (i:int) => wp_triple (isubst E (trm_for x i n2 t1))).
  exists S. simpl. applys triple_hwand_hpure_l.
  { split.
    { intros r. applys is_local_wp_triple. }
    { clears Q. intros i. applys qimpl_wp_triple. intros Q.
      applys triple_for_raw. fold isubst.
      rewrite~ triple_eq_himpl_wp_triple. case_if.
      { rewrite <- isubst_add_eq_subst1_isubst.
        asserts_rewrite (trm_seq (isubst (Ctx.add x (val_int i) E) t1) (trm_for x (i + 1)%I n2 (isubst (Ctx.rem x E) t1))
          = (isubst (Ctx.add x (val_int i) E) (trm_seq t1 (trm_for x (i + 1)%I n2 t1)))).
        { simpl. rewrite Ctx.rem_anon, Ctx.rem_add_same. auto. }
        applys wp_sound_seq.
        { applys* M. }
        { unfold S. unfold wp_triple_. simpl. rewrite~ Ctx.rem_add_same. } }
      { applys wp_sound_val E. } } }
  { rewrite~ triple_eq_himpl_wp_triple. }
Qed.

Lemma himpl_wp_fail_l : forall Q H,
  wp_fail Q ==> H.
Proof using. intros. unfold wp_fail, local. hpull. Qed.

(** Putting it all together *)

Lemma wp_sound_trm : forall t,
  wp_sound t.
Proof using.
  intros t. induction t; intros E Q.
  { applys wp_sound_val. }
  { applys wp_sound_var. }
  { applys wp_sound_fix. }
  { applys* wp_sound_if. }
  { applys* wp_sound_let. }
  { applys* wp_sound_app. }
  { applys* wp_sound_while. }
  { destruct t1; try solve [ applys himpl_wp_fail_l ].
    destruct t2; try solve [ applys himpl_wp_fail_l ].
    applys* wp_sound_for_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corrolaries of the soundness of [wp] *)

Lemma triple_isubst_wp : forall t E Q,
  triple (isubst E t) (wp E t Q) Q.
Proof using.
  intros. rewrite triple_eq_himpl_wp_triple. applys wp_sound_trm.
Qed.

Lemma triple_isubst_of_wp : forall t E H Q,
  H ==> wp E t Q ->
  triple (isubst E t) H Q.
Proof using. introv M. xchanges M. applys triple_isubst_wp. Qed.

Lemma triple_of_wp : forall (t:trm) H Q,
  H ==> wp Ctx.empty t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- (isubst_empty t). applys~ triple_isubst_of_wp.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Other results *)

(** All [wp] are trivially local by construction
    TODO: useful? *)

Lemma is_local_wp : forall E t,
  is_local (wp E t).
Proof.
  intros. destruct t; try solve [ apply is_local_local ].
  { rename v into x. simpl. unfold wp_var.
    destruct (Ctx.lookup x E); apply is_local_local. }
  { destruct t1; destruct t2; try solve [ apply is_local_local ]. }
Qed.



