(**

This file formalizes characteristic formulae for plain Separation Logic.

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
   format "^ F  Q") : charac.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** Lifted version of [weakestpre] *)

Definition Weakestpre (T:forall `{Enc A},hprop->(A->hprop)->Prop) : Formula :=
  fun A (EA:Enc A) => weakestpre T.

(** Lifted version of [wp_triple] *)

Definition Wp_triple (t:trm) : Formula :=
  Weakestpre (@Triple t).

(** Constructor to force the return type of a Formula *)

Definition Formula_typed `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    Hexists (Q':A1->hprop), F Q' \* \[PostChange Q' Q].


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
    Hexists (V:A), \[v = enc V] \* Q V).

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
    Hexists (A1:Type) (EA1:Enc A1) (Q1:A1->hprop),
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_let_typed `{EA1:Enc A1} (F1:Formula) (F2of:A1->Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    Hexists (Q1:A1->hprop),
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_app (t:trm) : Formula :=
  Local (Wp_triple t).

Definition Wp_if_val (b:bool) (F1 F2:Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    if b then ^F1 Q else ^F2 Q).

Definition Wp_if (F0 F1 F2:Formula) : Formula :=
  Wp_let_typed F0 (fun (b:bool) => Wp_if_val b F1 F2).

Definition Wp_while (F1 F2:Formula) : Formula :=
  Local (Formula_typed (fun (Q:unit->hprop) =>
    Hforall (R:Formula),
    let F := Wp_if F1 (Wp_seq F2 R) (Wp_val val_unit) in
    \[ is_local (@R unit _) /\ (forall Q', ^F Q' ==> ^R Q')] \--* (^R Q))).


(*

Definition Wp_for_val (v1 v2:val) (F3:int->formula) : formula := local (fun Q =>
  Hexists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \*
  Hforall (S:int->formula),
  let F i := If (i <= n2) then (Wp_seq (F3 i) (S (i+1)))
                          else (Wp_val val_unit) in
  \[ is_local_pred S /\ (forall i, F i ===> S i)] \--* (S n1 Q)).

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
  | trm_fix f x t1 => Wp_val (val_fix f x (subst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => Wp_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => 
     match z with
     | bind_anon => Wp_seq (aux t1) (aux t2) 
     | bind_var x => Wp_let (aux t1) (fun `{EA:Enc A} X => Wp (Ctx.add x (enc X) E) t2)
     end
  | trm_app t1 t2 => Wp_app (subst E t)
  | trm_while t1 t2 => Wp_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => Wp_fail
      (* TODO Wp_for' (aux t1) (aux t2) (fun X => Wp (ctx_add x X E) t3) *)
  end.


(* ********************************************************************** *)
(* * Soundness proof *)


(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [Wp_triple t] is a local formula *)

Lemma is_local_Wp_triple : forall `{EA:Enc A} t,
  is_local ((Wp_triple t) A EA).
Proof using.
  intros. unfolds Wp_triple. unfolds Weakestpre.
  applys is_local_weakestpre. applys is_local_Triple.
Qed.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma Triple_eq_himpl_Wp_triple : forall `{EA:Enc A} H (Q:A->hprop) t,
  Triple t H Q = (H ==> ^(Wp_triple t) Q).
Proof using. intros. applys weakestpre_eq. applys is_local_Triple. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_Wp_triple : forall t `{EA:Enc A} F,
  (forall Q, Triple t (F Q) Q) ->
  F ===> ((Wp_triple t) A EA).
Proof using. introv M. intros Q. rewrite~ <- Triple_eq_himpl_Wp_triple. Qed.



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
  hsimpl (F A EA Q') ((Q' \---* Q \*+ \Top)) Q'. split.
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

(** [Wp_triple_ E t] is a shorthand for [wp_triple (subst E t)] *)

Definition Wp_triple_ E t :=
  Wp_triple (subst E t).

(** [Wp_sound t] asserts that [wp] is sound for all contexts [E],
    in the sense that the syntactic wp entails the semantics wp. *)
(*
Definition Wp_sound t := forall E `{EA:Enc A} (Q:A->hprop),
  ^(Wp E t) Q ==> ^(Wp_triple_ E t) Q.
*)

Notation "F1 ====> F2" := (forall `{EA:Enc A}, F1 A EA ===> F2 A EA) 
  (at level 67).

(*
Definition Wp_sound t := forall E `{EA:Enc A},
  (Wp E t) A EA ===> (Wp_triple_ E t) A EA.
*)
Definition Wp_sound t := forall E,
  (Wp E t) ====> (Wp_triple_ E t).


(** Soundness of the [wp] for the various constructs *)

Lemma Wp_sound_var : forall x,
  Wp_sound (trm_var x).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_triple.
  intros Q. unfold Wp_var. simpl. destruct (Ctx.lookup x E).
  { remove_Local. xpull ;=> V EQ. applys* Rule_val. }
  { remove_Local. xpull*. }
Qed.

Lemma Wp_sound_val : forall v,
  Wp_sound (trm_val v).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_triple.
  intros Q. remove_Local. xpull ;=> V EQ.
  simpl. intros. applys* Rule_val.
Qed.

(* DEPRECATED
Lemma Wp_sound_fun : forall x t,
  Wp_sound (trm_fun x t).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_triple.
  intros Q. remove_Local. xpull ;=> V EQ. simpl.
  applys Triple_enc_val_inv (fun r => \[r = enc V] \* (Q V)).
  { applys Rule_fun. rewrite EQ. hsimpl~. }
  { hpull ;=> X EX. subst X. hsimpl~. }
Qed.
*)

Lemma Wp_sound_fix : forall f x t,
  Wp_sound (trm_fix f x t).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_triple.
  intros Q. remove_Local. xpull ;=> V EQ. simpl.
  applys Triple_enc_val_inv (fun r => \[r = enc V] \* (Q V)).
  { applys Rule_fix. rewrite EQ. hsimpl~. }
  { hpull ;=> X EX. subst X. hsimpl~. }
Qed.

Lemma Wp_sound_if : forall F1 F2 F3 E t1 t2 t3,
  F1 ====> (Wp_triple_ E t1) ->
  F2 ====> (Wp_triple_ E t2) ->
  F3 ====> (Wp_triple_ E t3) ->
  Wp_if F1 F2 F3 ====> Wp_triple_ E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros A EA. applys qimpl_Wp_triple. intros Q.
  remove_Local. xpull. intros _. simpl. applys Rule_if.
  { rewrite Triple_eq_himpl_Wp_triple. applys* M1. }
  { intros b. simpl. remove_Local. case_if.
    { rewrite Triple_eq_himpl_Wp_triple. applys* M2. }
    { rewrite Triple_eq_himpl_Wp_triple. applys* M3. } }
Qed.

Lemma Wp_sound_seq : forall F1 F2 E t1 t2,
  F1 ====> Wp_triple_ E t1 ->
  F2 ====> Wp_triple_ E t2 ->
  Wp_seq F1 F2 ====> Wp_triple_ E (trm_seq t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_triple. intros Q.
  remove_Local. simpl. applys Rule_seq.
  { rewrite Triple_eq_himpl_Wp_triple. applys* M1. }
  { rewrite Triple_eq_himpl_Wp_triple. applys* M2. }
Qed.

Lemma Wp_sound_let : forall (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) E (x:var) t1 t2,
  F1 ====> Wp_triple_ E t1 ->
  (forall `{EA:Enc A} (X:A), F2of X ====> Wp_triple_ (Ctx.add x (enc X) E) t2) ->
  Wp_let F1 (@F2of) ====> Wp_triple_ E (trm_let x t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_triple. intros Q.
  remove_Local. xpull ;=> A1 EA1 _. simpl. applys Rule_let.
  { rewrite Triple_eq_himpl_Wp_triple. applys* M1. }
  { intros X. rewrite Triple_eq_himpl_Wp_triple.
    unfold Subst1. 
    (* todo rewrite subst_subst_ctx_rem_same. *)
    skip_rewrite (forall v, subst1 x v (subst (Ctx.rem_var x E) t2) = subst (Ctx.add x v E) t2).
    applys* M2. }
Qed.

Lemma Wp_sound_app : forall t1 t2,
  Wp_sound (trm_app t1 t2).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_triple.
  intros Q. remove_Local. simpl.
  rewrite Triple_eq_himpl_Wp_triple. hsimpl.
Qed.


(* TODO: move *)
Lemma Rule_extract_hforall : forall t B (J:B->hprop) `{EA:Enc A} (Q:A->hprop),
  (exists x, Triple t (J x) Q) ->
  Triple t (hforall J) Q.
Proof using. unfold Triple. introv (x&M). applys* rule_extract_hforall. Qed.

Lemma Rule_extract_hwand_hpure_l : forall t (P:Prop) H `{EA:Enc A} (Q:A->hprop),
  P ->
  Triple t H Q ->
  Triple t (\[P] \--* H) Q.
Proof using. unfold Triple. introv M N. applys* rule_extract_hwand_hpure_l. Qed.


Lemma Wp_sound_while : forall F1 F2 E t1 t2,
  F1 ====> Wp_triple_ E t1 ->
  F2 ====> Wp_triple_ E t2 ->
  Wp_while F1 F2 ====> Wp_triple_ E (trm_while t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_triple. intros Q.
  remove_Local. simpl.
  unfold Formula_typed. xpull ;=> Q' C. applys Triple_enc_change (rm C).
  applys Rule_extract_hforall.
  set (R := Wp_triple (trm_while (subst E t1) (subst E t2))).
  exists R. simpl. applys Rule_extract_hwand_hpure_l.
  { split.
    { applys @is_local_Wp_triple. }
    { clears Q. applys qimpl_Wp_triple. intros Q.
      applys Rule_while_raw. 
      asserts_rewrite~ (
         trm_if (subst E t1) (trm_seq (subst E t2) (trm_while (subst E t1) (subst E t2))) val_unit
       = subst E (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit)).
      rewrite Triple_eq_himpl_Wp_triple. applys~ Wp_sound_if.
      { applys~ Wp_sound_seq. }
      { intros A1 EA1 Q''. applys Wp_sound_val. } } }
  { rewrite~ @Triple_eq_himpl_Wp_triple. }
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

Lemma Triple_subst_Wp : forall t E `{EA:Enc A} (Q:A->hprop),
  Triple (subst E t) (^(Wp E t) Q) Q.
Proof using.
  intros. rewrite Triple_eq_himpl_Wp_triple. applys Wp_sound_trm.
Qed.

Lemma Triple_subst_of_Wp : forall t E H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp E t) Q ->
  Triple (subst E t) H Q.
Proof using. introv M. xchanges M. applys Triple_subst_Wp. Qed.

Lemma Triple_of_Wp : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  Triple t H Q.
Proof using.
  introv M. xchanges M. pattern t at 1; rewrite <- (subst_empty t).
  applys Triple_subst_Wp.
Qed.




(* ********************************************************************** *)
(* * Practical proofs using characteristic formulae *)

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


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

(* DEPRECATED
Lemma Triple_apps_funs_of_Wp : forall F (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Rule_apps_funs. applys* Triple_subst_of_Wp.
Qed.
*)

Lemma Triple_apps_fixs_of_Wp : forall F (f:var) (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  vs = encs Vs ->
  var_fixs_exec f (length Vs) xs ->
  H ==> ^(Wp (combine (f::xs) (encs ((Dyn F)::Vs))) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
   lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
  subst. applys* Rule_apps_fixs. unfold Substn. 
  { applys @Triple_subst_of_Wp M. }
Qed.




(* ---------------------------------------------------------------------- *)
(* ** Registering specifications *)

Notation "'Register_Rule' t" := (Register_goal (Triple t _ _))
  (at level 69) : charac.

Notation "'Register_Spec' f" := (Register_Rule (trm_apps (trm_val f) _))
  (at level 69) : charac.




(* ---------------------------------------------------------------------- *)
(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Rule_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Rule_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide Rule_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Rule_alloc.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Rule_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Rule_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Rule_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Rule_ptr_add.


(* ********************************************************************** *)
(* * Tactics for progressing through proofs *)

(** Extends tactics defined in [LambdaCFTactics.v] *)


(*--------------------------------------------------------*)
(* ** [xdecode_args] : used internally *)

Ltac xdecode_arg v :=
  let W := constr:(decode v) in
  let W' := (eval simpl decode in W) in
  match W' with Dyn ?V' =>
    change (trm_val v) with (trm_val (enc V'))
  end.

Ltac xdecode_args_from_trms ts :=
  match ts with
  | (trm_val (enc ?V))::?ts' => xdecode_args_from_trms ts'
  | (trm_val ?v)::?ts' => xdecode_arg v; xdecode_args_from_trms ts'
  | nil => idtac
  end.

Ltac xdecode_args tt :=
  match goal with |- Triple (trm_apps ?f ?ts) ?H ?Q =>
    xdecode_args_from_trms ts end.


(*--------------------------------------------------------*)
(* ** [xeq_encs] : used internally *)

(** [xeq_encs] solves goal of the form [ [`V1; ..; `VN] = encs ?VS ]. *)

Lemma encs_nil :
  encs nil = @nil val.
Proof using. auto. Qed.

Lemma encs_cons : forall `{EA:Enc A} (V:A) (VS:dyns),
  encs ((Dyn V)::VS) = (enc V)::(encs VS).
Proof using. auto. Qed.

Hint Rewrite <- @encs_nil @encs_cons : rew_encs.

Tactic Notation "rew_encs" :=
  autorewrite with rew_encs.

Ltac xeq_encs_core tt :=
  rew_encs; reflexivity.

(* DEPRECATED
match goal with |- ?vs = encs ?Vs => applys (refl_equal (encs (decodes vs))) end.*)

Tactic Notation "xeq_encs" :=
  xeq_encs_core tt.


(*--------------------------------------------------------*)
(* ** [rew_dyn] *)

Hint Rewrite dyn_to_val_dyn_make @enc_decode enc_dyn_eq : rew_dyn.

Tactic Notation "rew_dyn" :=
  autorewrite with rew_dyn; simpl dyn_value.
Tactic Notation "rew_dyn" "in" hyp(H) :=
  autorewrite with rew_dyn in H; simpl dyn_value in H.
Tactic Notation "rew_dyn" "in" "*" :=
  autorewrite with rew_dyn in *; simpl dyn_value in *.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_from_goal tt ::=
  match goal with |- @Triple ?t _ _ _ _ => xcf_get_fun_from_trm t end.

Ltac xcf_post tt :=
  simpl.

Ltac xcf_trm n ::= (* for WP2 *)
 (*  applys triple_trm_of_wp_iter n; [ xcf_post tt ]. *) fail.


Ltac xcf_basic_fun n f' ::= (* for WP2 *)
  let f := xcf_get_fun tt in
  match f with
  | val_fixs _ _ _ =>
      applys Triple_apps_fixs_of_Wp f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | try xeq_encs
      | reflexivity
      | xcf_post tt ]
  end.

Ltac xcf_prepare_args tt ::=
  rew_nary;
  try xdecode_args tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] *)

Ltac xlocal' :=
  try solve [ apply is_local_local ].
  (*   | apply is_local_wp_triple ]. *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] 

Lemma xlet_lemma : forall Q1 (F1:formula) (F2:val->formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> wp_let F1 F2 Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.

Ltac xlet_core tt ::=
  applys xlet_lemma; [ xlocal' | | ].

*)
(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Lemma xapp_lemma : forall t H `{EA:Enc A} (Q:A->hprop),
  Triple t H Q ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M. applys local_erase'. rewrite~ <- Triple_eq_himpl_Wp_triple.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.


(* ---------------------------------------------------------------------- *)
(* ** Example proof of the [incr] function *)

Module Test.
Import NotationForVariables NotationForTerms.
Open Scope trm_scope.

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.


Lemma rule_incr : forall (p:loc) (n:int),
  Triple (val_incr ``p)
    (p ~~~> n)
    (fun (r:unit) => (p ~~~> (n+1))).
Proof using.
  intros. 
Abort.
(* xcf.


  let f' := xcf_get_fun tt in
  xcf_reveal_fun tt;
  rew_nary;
  rew_vals_to_trms.
eapply @Triple_apps_funs_of_Wp.
  xcf_basic_fun n f'.

lets: Triple_apps_funs_of_Wp.


  match f with
  | val_funs _ _ => (* TODO: use (apply (@..)) instead of applys? same in cflifted *)
      applys Triple_apps_funs_of_Wp
  | val_fixs _ _ _ =>
      applys Triple_apps_fixs_of_Wp f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | reflexivity
      | xcf_post tt ]
  end.


xcf.
  xlet. { xapp. xapplys rule_get. }
  intros x. hpull ;=> E. subst.
  xlet. { xapp. xapplys rule_add. }
  intros y. hpull ;=> E. subst.
  xapp. xapplys rule_set. auto.
Qed.




*)


End Test.

























