(**

This file formalizes characteristic formulae in weakest-precondition form
for lifted Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWP LambdaSepLifted.
Open Scope heap_scope.
Generalizable Variables A.

Implicit Types v w : val.
Implicit Types t : trm.



(* ********************************************************************** *)
(* * WP generator *)


(* ---------------------------------------------------------------------- *)
(* ** Type of a WP *)

(** A formula is a predicate over a post-condition. *)

Definition Formula := forall A (EA:Enc A), (A -> hprop) -> hprop.

Global Instance Inhab_Formula : Inhab Formula.
Proof using. apply (Inhab_of_val (fun _ _ _ => \[])). Qed.

Notation "^ F Q" := ((F:Formula) _ _ Q)
  (at level 45, F at level 0, Q at level 0,
   format "^ F  Q") : lifted_wp_scope.

Open Scope lifted_wp_scope.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** Lifted version of [weakestpre] *)

Definition Weakestpre (T:forall `{Enc A},hprop->(A->hprop)->Prop) : Formula :=
  fun A (EA:Enc A) => weakestpre T.

(** Lifted version of [wp_triple] *)

Definition Wp_Triple (t:trm) : Formula :=
  Weakestpre (@Triple t).

(** Constructor to force the return type of a Formula *)

Definition Formula_typed `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    \exists (Q':A1->hprop), F Q' \* \[PostChange Q' Q].


(* ---------------------------------------------------------------------- *)
(* ** Definition of [Local] for WP *)

(** The [Local] predicate lifts [local]. *)

Definition Local (F:Formula) : Formula :=
  fun A `{EA:Enc A} Q => local (@F A EA) Q.

Lemma local_Local_eq : forall A `{EA:Enc A} (F:Formula),
  local (@Local F A EA) = (@Local F A EA).
Proof using.
  intros. apply fun_ext_1. intros Q.
  unfold Local. rewrite local_local. split~.
Qed.

Lemma is_local_Local : forall A `{EA:Enc A} (F:Formula),
  is_local (@Local F A EA).
Proof using. intros. unfolds. rewrite~ local_Local_eq. Qed.

Hint Resolve is_local_Local.


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition Wp_fail : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \[False]).

Definition Wp_val (v:val) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (V:A), \[v = enc V] \* Q V).

Definition Wp_var (E:ctx) (x:var) : Formula :=
  match Ctx.lookup x E with
  | None => Wp_fail
  | Some v => Wp_val v
  end.

Definition Wp_seq (F1 F2:Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wp_let (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1),
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_let_typed `{EA1:Enc A1} (F1:Formula) (F2of:A1->Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    \exists (Q1:A1->hprop),
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_app (t:trm) : Formula :=
  Local (Wp_Triple t).

Definition Wp_if_val (b:bool) (F1 F2:Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    if b then ^F1 Q else ^F2 Q).

Definition Wp_if (F0 F1 F2:Formula) : Formula :=
  Wp_let_typed F0 (fun (b:bool) => Wp_if_val b F1 F2).

Definition Wp_while (F1 F2:Formula) : Formula :=
  Local (Formula_typed (fun (Q:unit->hprop) =>
    \forall (R:Formula),
    let F := Wp_if F1 (Wp_seq F2 R) (Wp_val val_unit) in
    \[ is_local (@R unit _) /\ (forall Q', ^F Q' ==> ^R Q')] \-* (^R Q))).


(*

Definition Wp_for_val (v1 v2:val) (F3:int->formula) : formula := local (fun Q =>
  \exists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \*
  \forall (S:int->formula),
  let F i := If (i <= n2) then (Wp_seq (F3 i) (S (i+1)))
                          else (Wp_val val_unit) in
  \[ is_local_pred S /\ (forall i, F i ===> S i)] \-* (S n1 Q)).

Definition Wp_for (F1 F2:formula) (F3:int->formula) : formula :=
  Wp_let F1 (fun v1 => Wp_let F2 (fun v2 => Wp_for_val v1 v2 F3)).

Definition Wp_for' (F1 F2:formula) (F3:int->formula) : formula := local (fun Q =>
  F1 (fun v1 => F2 (fun v2 => Wp_for_val v1 v2 F3 Q))).
*)


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint Wp (E:ctx) (t:trm) : Formula :=
  let aux := Wp E in
  match t with
  | trm_val v => Wp_val v
  | trm_var x => Wp_var E x
  | trm_fix f x t1 => Wp_val (val_fix f x (isubst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => Wp_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 =>
     match z with
     | bind_anon => Wp_seq (aux t1) (aux t2)
     | bind_var x => Wp_let (aux t1) (fun `{EA:Enc A} X => Wp (Ctx.add x (enc X) E) t2)
     end
  | trm_app t1 t2 => Wp_app (isubst E t)
  | trm_while t1 t2 => Wp_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => Wp_fail
      (* TODO Wp_for' (aux t1) (aux t2) (fun X => Wp (ctx_add x X E) t3) *)
  end.


(* ********************************************************************** *)
(* * Soundness proof *)


(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [Wp_Triple t] is a local formula *)

Lemma is_local_Wp_Triple : forall `{EA:Enc A} t,
  is_local ((Wp_Triple t) A EA).
Proof using.
  intros. unfolds Wp_Triple. unfolds Weakestpre.
  applys is_local_weakestpre. applys is_local_Triple.
Qed.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma Triple_eq_himpl_Wp_Triple : forall `{EA:Enc A} H (Q:A->hprop) t,
  Triple t H Q = (H ==> ^(Wp_Triple t) Q).
Proof using. intros. applys weakestpre_eq. applys is_local_Triple. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_Wp_Triple : forall t `{EA:Enc A} F,
  (forall Q, Triple t (F Q) Q) ->
  F ===> ((Wp_Triple t) A EA).
Proof using. introv M. intros Q. rewrite~ <- Triple_eq_himpl_Wp_Triple. Qed.



(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [local] transformer *)

(** The [local] transformer is sound w.r.t. [triple] *)

Lemma Triple_local_pre : forall t (F:Formula) `{EA:Enc A} (Q:A->hprop),
  (forall Q, Triple t (^F Q) Q) ->
  Triple t (^(Local F) Q) Q.
Proof using.
  introv M.
  rewrite is_local_Triple. unfold SepBasicSetup.local.
  unfold Local, local. hpull ;=> Q'.
  hsimpl (F A EA Q') ((Q' \--* Q \*+ \Top)) Q'. split.
  { applys~ M. }
  { hchanges qwand_cancel. }
Qed. (* TODO: simplify proof? *)

(** The tactic [remove_Local] applies to goal of the form [triple t (local F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_Local :=
  match goal with |- @Triple _ _ _ _ ?Q =>
    applys Triple_local_pre; try (clear Q; intros Q); fold wp end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wp] *)

(** [Wp_Triple_ E t] is a shorthand for [wp_triple (isubst E t)] *)

Definition Wp_Triple_ E t :=
  Wp_Triple (isubst E t).

(** [Wp_sound t] asserts that [wp] is sound for all contexts [E],
    in the sense that the syntactic wp entails the semantics wp. *)
(*
Definition Wp_sound t := forall E `{EA:Enc A} (Q:A->hprop),
  ^(Wp E t) Q ==> ^(Wp_Triple_ E t) Q.
*)

Notation "F1 ====> F2" := (forall `{EA:Enc A}, F1 A EA ===> F2 A EA)
  (at level 67).

(*
Definition Wp_sound t := forall E `{EA:Enc A},
  (Wp E t) A EA ===> (Wp_Triple_ E t) A EA.
*)
Definition Wp_sound t := forall E,
  (Wp E t) ====> (Wp_Triple_ E t).


(** Soundness of the [wp] for the various constructs *)

Lemma Wp_sound_var : forall x,
  Wp_sound (trm_var x).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_Triple.
  intros Q. unfold Wp_var. simpl. destruct (Ctx.lookup x E).
  { remove_Local. xpull ;=> V EQ. applys* Triple_val. }
  { remove_Local. xpull*. intros; false. 
    (* TODO: decide whether xpull should automatically discard goal
       when extracting false *) }
Qed.

Lemma Wp_sound_val : forall v,
  Wp_sound (trm_val v).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_Triple.
  intros Q. remove_Local. xpull ;=> V EQ.
  simpl. intros. applys* Triple_val.
Qed.

(* DEPRECATED
Lemma Wp_sound_fun : forall x t,
  Wp_sound (trm_fun x t).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_Triple.
  intros Q. remove_Local. xpull ;=> V EQ. simpl.
  applys Triple_enc_val_inv (fun r => \[r = enc V] \* (Q V)).
  { applys Triple_fun. rewrite EQ. hsimpl~. }
  { hpull ;=> X EX. isubst X. hsimpl~. }
Qed.
*)

Lemma Wp_sound_fix : forall f x t,
  Wp_sound (trm_fix f x t).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_Triple.
  intros Q. remove_Local. xpull ;=> V EQ. simpl.
  applys Triple_enc_val_inv (fun r => \[r = enc V] \* (Q V)).
  { applys Triple_fix. rewrite EQ. hsimpl~. }
  { hpull ;=> X EX. subst X. hsimpl~. }
Qed.

Lemma Wp_sound_if : forall F1 F2 F3 E t1 t2 t3,
  F1 ====> (Wp_Triple_ E t1) ->
  F2 ====> (Wp_Triple_ E t2) ->
  F3 ====> (Wp_Triple_ E t3) ->
  Wp_if F1 F2 F3 ====> Wp_Triple_ E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros A EA. applys qimpl_Wp_Triple. intros Q.
  remove_Local. xpull. intros _. simpl. applys Triple_if.
  { rewrite Triple_eq_himpl_Wp_Triple. applys* M1. }
  { intros b. simpl. remove_Local. case_if.
    { rewrite Triple_eq_himpl_Wp_Triple. applys* M2. }
    { rewrite Triple_eq_himpl_Wp_Triple. applys* M3. } }
Qed.

Lemma Wp_sound_seq : forall F1 F2 E t1 t2,
  F1 ====> Wp_Triple_ E t1 ->
  F2 ====> Wp_Triple_ E t2 ->
  Wp_seq F1 F2 ====> Wp_Triple_ E (trm_seq t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_Triple. intros Q.
  remove_Local. simpl. applys Triple_seq.
  { rewrite Triple_eq_himpl_Wp_Triple. applys* M1. }
  { rewrite Triple_eq_himpl_Wp_Triple. applys* M2. }
Qed.

Lemma Wp_sound_let : forall (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) E (x:var) t1 t2,
  F1 ====> Wp_Triple_ E t1 ->
  (forall `{EA:Enc A} (X:A), F2of X ====> Wp_Triple_ (Ctx.add x (enc X) E) t2) ->
  Wp_let F1 (@F2of) ====> Wp_Triple_ E (trm_let x t1 t2).
Proof using.
  Opaque Ctx.rem.
  introv M1 M2. intros A EA. applys qimpl_Wp_Triple. intros Q.
  remove_Local. xpull ;=> A1 EA1. simpl. applys Triple_let.
  { rewrite Triple_eq_himpl_Wp_Triple. applys* M1. }
  { intros X. rewrite Triple_eq_himpl_Wp_Triple.
    unfold Subst1. rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma Wp_sound_app : forall t1 t2,
  Wp_sound (trm_app t1 t2).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_Triple.
  intros Q. remove_Local. simpl.
  rewrite Triple_eq_himpl_Wp_Triple. hsimpl.
Qed.

Lemma Wp_sound_while : forall F1 F2 E t1 t2,
  F1 ====> Wp_Triple_ E t1 ->
  F2 ====> Wp_Triple_ E t2 ->
  Wp_while F1 F2 ====> Wp_Triple_ E (trm_while t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_Triple. intros Q.
  remove_Local. simpl.
  unfold Formula_typed. xpull ;=> Q' C. applys Triple_enc_change (rm C).
  applys Triple_extract_hforall.
  set (R := Wp_Triple (trm_while (isubst E t1) (isubst E t2))).
  exists R. simpl. applys Triple_extract_hwand_hpure_l.
  { split.
    { applys @is_local_Wp_Triple. }
    { clears Q. applys qimpl_Wp_Triple. intros Q.
      applys Triple_while_raw.
      asserts_rewrite~ (
         trm_if (isubst E t1) (trm_seq (isubst E t2) (trm_while (isubst E t1) (isubst E t2))) val_unit
       = isubst E (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit)).
      rewrite Triple_eq_himpl_Wp_Triple. applys~ Wp_sound_if.
      { applys~ Wp_sound_seq. }
      { intros A1 EA1 Q''. applys Wp_sound_val. } } }
  { rewrite~ @Triple_eq_himpl_Wp_Triple. }
Qed.

Lemma himpl_wp_fail_l : forall `{EA:Enc A} (Q:A->hprop) H,
  ^Wp_fail Q ==> H.
Proof using. intros. unfold Wp_fail, Local, local. hpull. Qed.

(** Putting it all together *)

Lemma Wp_sound_trm : forall t,
  Wp_sound t.
Proof using.
  intros t. induction t; intros E Q.
  { applys Wp_sound_val. }
  { applys Wp_sound_var. }
  { applys Wp_sound_fix. }
  { applys* Wp_sound_if. }
  { (* todo factorize? *)
    destruct b as [|x].
    { applys* Wp_sound_seq. }
    { applys* Wp_sound_let. } }
  { applys* Wp_sound_app. }
  { applys* Wp_sound_while. }
  { simpl. intros. intros Q'. applys @himpl_wp_fail_l. }  (* TODO: for loops *)
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corrolaries of the soundness of [wp] *)

Lemma Triple_isubst_Wp : forall t E `{EA:Enc A} (Q:A->hprop),
  Triple (isubst E t) (^(Wp E t) Q) Q.
Proof using.
  intros. rewrite Triple_eq_himpl_Wp_Triple. applys Wp_sound_trm.
Qed.

Lemma Triple_isubst_of_Wp : forall t E H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp E t) Q ->
  Triple (isubst E t) H Q.
Proof using. introv M. xchanges M. applys Triple_isubst_Wp. Qed.

Lemma Triple_of_Wp : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  Triple t H Q.
Proof using.
  introv M. xchanges M. pattern t at 1; rewrite <- (isubst_empty t).
  applys Triple_isubst_Wp.
Qed.




(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

Lemma Substn_eq_isubstn : forall xs (Vs:dyns) t,
  length xs = length Vs ->
  Substn xs Vs t = isubstn xs (encs Vs) t.
Proof using.
  introv E. unfold Substn. rewrite~ isubstn_eq_substn.
  rewrite* length_encs.
Qed.

Lemma Triple_apps_funs_of_Wp : forall F (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Triple_apps_funs. 
  unfolds in N. rewrite* Substn_eq_isubstn.
  applys* Triple_isubst_of_Wp.
Qed.


Lemma Triple_apps_fixs_of_Wp : forall F (f:var) (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  vs = encs Vs ->
  var_fixs_exec f (length Vs) xs ->
  H ==> ^(Wp (combine (f::xs) (encs ((Dyn F)::Vs))) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
  subst. applys* Triple_apps_fixs.
  rewrite~ Substn_eq_isubstn. 
  { applys @Triple_isubst_of_Wp M. }
  { rew_list. math. }
Qed.


(* todo: factorize above two using anon? *)


(* ********************************************************************** *)
(* * Notation for characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for computd WP *)

Notation "'`Fail'" :=
  ((Wp_fail))
  (at level 69) : charac.

Notation "'`Val' v" :=
  ((Wp_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  ((Wp_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  ((Wp_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  ((Wp_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'``Let' x ':=' F1 'in' F2" :=
  ((Wp_let_typed F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '``Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' [ A EA ] x ':=' F1 'in' F2" :=
  ((Wp_let F1 (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' '`Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  ((Wp_app t))
  (at level 68, t at level 0) : charac.

Notation "'`While' F1 'Do' F2 'Done'" :=
  ((Wp_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' '`While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : charac.

(*
Notation "'`For' x '=' n1 'To' n2 'Do' F3 'Done'" :=
  ((Wp_for n1 n2 (fun x => F3)))
  (at level 69, x ident,
   format "'[v' '`For'  x  '='  n1  'To'  n2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : charac.
*)

Open Scope charac.

