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
  (at level 65, F at level 0, Q at level 0,
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
  match ctx_lookup x E with
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
  | trm_fun x t1 => Wp_val (val_fun x (substs (ctx_rem x E) t1))
  | trm_fix f x t1 => Wp_val (val_fix f x (substs (ctx_rem x (ctx_rem f E)) t1))
  | trm_if t0 t1 t2 => Wp_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => Wp_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => Wp_let (aux t1) (fun `{EA:Enc A} X => Wp (ctx_add x (enc X) E) t2)
  | trm_app t1 t2 => Wp_app (substs E t)
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

Lemma triple_local_pre : forall t (F:formula) Q,
  (forall Q, triple t (F Q) Q) ->
  triple t (local F Q) Q.
Proof using.
  introv M.
  rewrite is_local_triple. unfold SepBasicSetup.local.
  unfold local. hpull ;=> Q'.
  hsimpl (F Q') ((Q' \---* Q \*+ \Top)) Q'. split.
  { applys~ M. }
  { hchanges qwand_cancel. }
Qed. (* TODO: simplify proof? *)

(** The tactic [remove_local] applies to goal of the form [triple t (local F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_local :=
  match goal with |- triple _ _ ?Q =>
    applys triple_local_pre; try (clear Q; intros Q); xpull; fold wp end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wp] *)

(** [wp_triple_ E t] is a shorthand for [wp_triple (substs E t)] *)

Definition wp_triple_ E t :=
  wp_triple (substs E t).

(** [wp_sound t] asserts that [wp] is sound for all contexts [E],
    in the sense that the syntactic wp entails the semantics wp. *)

Definition wp_sound t := forall E,
  wp E t ===> wp_triple_ E t.

(** Soundness of the [wp] for the various constructs *)

Lemma triple_wp_var : forall x,
  wp_sound (trm_var x).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. unfold wp_var. rewrite substs_var. destruct (ctx_lookup x E).
  { remove_local. apply~ rule_val. }
  { remove_local. intros; false~. }
Qed.

Lemma triple_wp_val : forall v,
  wp_sound (trm_val v).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_val. applys~ rule_val.
Qed.

Lemma triple_wp_fun : forall x t,
  wp_sound (trm_fun x t).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_fun. applys~ rule_fun.
Qed.

Lemma triple_wp_fix : forall f x t,
  wp_sound (trm_fix f x t).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_fix. applys~ rule_fix.
Qed.

  (* TODO: inline *)
  Lemma wp_if_val_false : forall v F1 F2 Q,
    ~ is_val_bool v ->
    wp_if_val v F1 F2 Q ==> \[False].
  Proof using.
    introv M. applys local_extract_false. intros Q'.
    hpull ;=> v' E. inverts E. false* M. hnfs*.
  Qed.

Lemma triple_wp_if : forall F1 F2 F3 E t1 t2 t3,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  F3 ===> wp_triple_ E t3 ->
  wp_if F1 F2 F3 ===> wp_triple_ E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_if. applys rule_if.
  { unfolds in M1. rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros b. simpl. remove_local ;=> b' M. inverts M. case_if.
    { rewrite triple_eq_himpl_wp_triple. applys* M2. }
    { rewrite triple_eq_himpl_wp_triple. applys* M3. } }
  { intros. applys~ wp_if_val_false. }
Qed.

Lemma triple_wp_seq : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_seq F1 F2 ===> wp_triple_ E (trm_seq t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_seq. applys rule_seq.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros X. rewrite triple_eq_himpl_wp_triple. applys* M2. }
Qed.

Lemma triple_wp_let : forall F1 F2 E x t1 t2,
  F1 ===> wp_triple_ E t1 ->
  (forall X, F2 X ===> wp_triple_ (ctx_add x X E) t2) ->
  wp_let F1 F2 ===> wp_triple_ E (trm_let x t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_let. applys rule_let.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros X. rewrite triple_eq_himpl_wp_triple.
    rewrite subst_substs_ctx_rem_same. applys* M2. }
Qed.

Lemma triple_wp_app : forall t1 t2,
  wp_sound (trm_app t1 t2).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_app. applys triple_wp_triple.
Qed.

Lemma triple_wp_while : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_while F1 F2 ===> wp_triple_ E (trm_while t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_while. applys rule_extract_hforall.
  set (R := weakestpre (triple (trm_while (substs E t1) (substs E t2)))).
  exists R. simpl. applys rule_extract_hwand_hpure_l.
  { split.
    { applys is_local_wp_triple. }
    { clears Q. applys qimpl_wp_triple. intros Q.
      applys rule_while_raw. rewrite <- substs_while. rewrite <- substs_seq.
      rewrite <- (substs_val E). rewrite <- substs_if.
      rewrite triple_eq_himpl_wp_triple. applys~ triple_wp_if.
      { applys~ triple_wp_seq. { unfold wp_triple_. rewrite~ substs_while. } }
      { applys triple_wp_val. } } }
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
  { applys triple_wp_val. }
  { applys triple_wp_var. }
  { applys triple_wp_fun. }
  { applys triple_wp_fix. }
  { applys* triple_wp_if. }
  { applys* triple_wp_seq. }
  { applys* triple_wp_let. }
  { applys* triple_wp_app. }
  { applys* triple_wp_while. }
  { applys himpl_wp_fail_l. }  (* TODO: for loops *)
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corrolaries of the soundness of [wp] *)

Lemma triple_substs_wp : forall t E Q,
  triple (substs E t) (wp E t Q) Q.
Proof using.
  intros. rewrite triple_eq_himpl_wp_triple. applys wp_sound_trm.
Qed.

Lemma triple_substs_of_wp : forall t E H Q,
  H ==> wp E t Q ->
  triple (substs E t) H Q.
Proof using. introv M. xchanges M. applys triple_substs_wp. Qed.

Lemma triple_of_wp : forall (t:trm) H Q,
  H ==> wp ctx_empty t Q ->
  triple t H Q.
Proof using. introv M. xchanges M. applys triple_substs_wp. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Other results *)

(** All [wp] are trivially local by construction
    TODO: useful? *)

Lemma is_local_wp : forall E t,
  is_local (wp E t).
Proof.
  intros. destruct t; try solve [ apply is_local_local ].
  { rename v into x. simpl. unfold wp_var. 
    destruct (ctx_lookup x E); apply is_local_local. }
Qed.




(* ********************************************************************** *)
(* * Practical proofs using characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for computd WP *)

Notation "'`Val' v" :=
  ((wp_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  ((wp_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  ((wp_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  ((wp_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((wp_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  ((wp_app t))
  (at level 68, t at level 0) : charac.

Notation "'`Fail'" :=
  ((wp_fail))
  (at level 69) : charac.

Notation "'`While' F1 'Do' F2 'Done'" :=
  ((wp_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' '`While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : charac.

(* TODO
Notation "'`For' x '=' v1 'To' v2 'Do' F3 'Done'" :=
  ((wp_for v1 v2 (fun x => F3)))
  (at level 69, x ident, (* t1 at level 0, t2 at level 0, *)
   format "'[v' '`For'  x  '='  v1  'To'  v2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : charac.
*)

Open Scope charac.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

Lemma triple_apps_funs_of_wp_iter : forall F (vs:vals) xs t H Q,
  F = val_funs xs t ->
  var_funs_exec (length vs) xs ->
  H ==> wp (LibList.combine xs vs) t Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  lets (_&L&_): N. applys* rule_apps_funs.
  applys* triple_substs_of_wp.
Qed.

Lemma triple_apps_fixs_of_wp_iter : forall f F (vs:vals) xs t H Q,
  F = val_fixs f xs t ->
  var_fixs_exec f (length vs) xs ->
  H ==> wp (LibList.combine (f::xs) (F::vs)) t Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
  applys* rule_apps_fixs. rewrite~ subst_substn.
  applys* triple_substs_of_wp M.
Qed.



(* ---------------------------------------------------------------------- *)
(** ** Database of lemmas *)

(** We here use the notation [Register] and [Provide] from the TLC library.

  Usage of [RegisterSpecGoal], e.g.:

    Hint Extern 1 (RegisterSpecGoal (triple (trm_app2_val (val_prim val_eq) ?x ?y) ?H ?Q)) =>
      Provide rule_eq.

  Usage of [RegisterSpecApp], e.g.:

    Hint Extern 1 (RegisterSpecApp (trm_app2_val (val_prim val_eq) ?x ?y)) =>
      Provide rule_eq.

*)

Notation "'Register_rule' t" := (Register_goal (triple t _ _))
  (at level 69) : charac.

Notation "'Register_spec' f" := (Register_rule (trm_apps (trm_val f) _))
  (at level 69) : charac.


(* ---------------------------------------------------------------------- *)
(** ** Registering specification of primitive functions *)

Hint Extern 1 (Register_spec (val_prim val_ref)) => Provide rule_ref.
Hint Extern 1 (Register_spec (val_prim val_get)) => Provide rule_get.
Hint Extern 1 (Register_spec (val_prim val_set)) => Provide rule_set.
Hint Extern 1 (Register_spec (val_prim val_alloc)) => Provide rule_alloc.
Hint Extern 1 (Register_spec (val_prim val_eq)) => Provide rule_eq.
Hint Extern 1 (Register_spec (val_prim val_add)) => Provide rule_add.
Hint Extern 1 (Register_spec (val_prim val_sub)) => Provide rule_sub.
Hint Extern 1 (Register_spec (val_prim val_ptr_add)) => Provide rule_ptr_add.


(* ********************************************************************** *)
(* * Tactics for progressing through proofs *)

(** Extends tactics defined in [LambdaCFTactics.v] *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_from_goal tt ::=
  match goal with |- triple ?t _ _ => xcf_get_fun_from_trm t end.

Ltac xcf_post tt :=
  simpl.

Ltac xcf_trm n ::= (* for WP2 *)
 (*  applys triple_trm_of_wp_iter n; [ xcf_post tt ]. *) fail.

Ltac xcf_basic_fun n f' ::= (* for WP2 *)
  let f := xcf_get_fun tt in
  match f with
  | val_funs _ _ => (* TODO: use (apply (@..)) instead of applys? same in cflifted *)
      applys triple_apps_funs_of_wp_iter n;
      [ reflexivity | reflexivity | xcf_post tt ]
  | val_fixs _ _ _ =>
      applys triple_apps_fixs_of_wp_iter n f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | reflexivity
      | xcf_post tt ]
  end.


Ltac xcf_basic_fun n f' ::= (* for WP2 *)
  let f := xcf_get_fun tt in
  match f with
  | val_funs _ _ => (* TODO: use (apply (@..)) instead of applys? same in cflifted *)
      applys triple_apps_funs_of_wp_iter;
      [ reflexivity | reflexivity | xcf_post tt ]
  | val_fixs _ _ _ =>
      applys triple_apps_fixs_of_wp_iter f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | reflexivity
      | xcf_post tt ]
  end.

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] *)

Ltac xlocal' :=
  try solve [ apply is_local_local ].
  (*   | apply is_local_wp_triple ]. *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

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


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Lemma xapp_lemma : forall t H Q,
  triple t H Q ->
  H ==> (wp_app t) Q.
Proof using.
  introv M. applys local_erase'. unfold wp_triple, weakestpre. hsimpl~ H.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.


(* ---------------------------------------------------------------------- *)
(* ** Example proof of the [incr] function *)

Open Scope trm_scope.

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.

Lemma rule_incr : forall (p:loc) (n:int),
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. xcf.
  xlet. { xapp. xapplys rule_get. }
  intros x. hpull ;=> E. subst.
  xlet. { xapp. xapplys rule_add. }
  intros y. hpull ;=> E. subst.
  xapp. xapplys rule_set. auto.
Qed.

































