(**

This file formalizes characteristic formulae for plain Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From TLC Require Export LibFix.
From Sep Require Export LambdaSep LambdaCFTactics.
Open Scope heap_scope.

Implicit Types v w : val.
Implicit Types t : trm.



(* ********************************************************************** *)
(* * WP generator *)

(* ---------------------------------------------------------------------- *)
(* ** Type of a WP *)

(** A formula is a predicate over a post-condition. *)

Definition formula := (val -> hprop) -> hprop.

Global Instance Inhab_formula : Inhab formula.
Proof using. apply (Inhab_of_val (fun _ => \[])). Qed.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** Recall the generic definition of [weakestpre] from [SepFunctor]:
[[
    Definition weakestpre F Q :=
      Hexists H, H \* \[F H Q].
]]
*)

Definition wp_triple (t:trm) : formula :=
  weakestpre (triple t).


(* ---------------------------------------------------------------------- *)
(* ** Definition of [local] for WP *)

(** Simple case:

[[
Definition local (F:formula) : formula :=
  fun Q => Hexists Q', F Q' \* (Q' \---* (Q \*+ \Top)).

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
  fun Q => Hexists Q', F Q' \* (Q' \---* (Q \*+ \Top)).

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
  H1 ==> F (fun x => H2 \--* Q x) ->
  H ==> F Q.
Proof using.
  introv L W M. rewrites (rm L). hchanges (rm W). hchanges (rm M).
  unfold local. hsimpl (fun x => H2 \--* Q x). (* TODO: simplify *)
  (* TODO: needs hqwand *)
  applys qwand_move_l. intros x. hchanges (hwand_cancel H2).
Qed.

Lemma local_frame_top : forall H1 H2 F H Q,
  is_local F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \--* Q x \* \Top) ->
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

Lemma local_extract_false : forall F Q,
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
    hpull ;=> Q' H M. hsimpl (H \* (Q' \---* Q \*+ \Top)).
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
  match ctx_lookup x E with
  | None => wp_fail
  | Some v => wp_val v
  end.

(* deprecated
Definition wp_seq (F1 F2:formula) : formula := local (fun Q =>
  F1 (fun r => \[r = val_unit] \* F2 Q)).
*)
Definition wp_seq (F1 F2:formula) : formula := local (fun Q =>
  F1 (fun X => F2 Q)).

Definition wp_let (F1:formula) (F2of:val->formula) : formula := local (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wp_app (t:trm) :=
  local (wp_triple t).

Definition wp_if_val (v:val) (F1 F2:formula) : formula := local (fun Q =>
  Hexists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wp_if (F0 F1 F2:formula) : formula :=
  wp_let F0 (fun v => wp_if_val v F1 F2).

Definition wp_while (F1 F2:formula) : formula := local (fun Q =>
  Hforall (R:formula),
  let F := wp_if F1 (wp_seq F2 R) (wp_val val_unit) in
  \[ is_local R /\ F ===> R] \--* (R Q)).

(* TODO
Definition wp_for_val (v1 v2:val) (F3:int->formula) : formula := local (fun Q =>
  Hexists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \*
  Hforall (S:int->formula),
  let F i := If (i <= n2) then (wp_seq (F3 i) (S (i+1)))
                          else (wp_val val_unit) in
  \[ is_local_pred S /\ (forall i, F i ===> S i)] \--* (S n1 Q)).

Definition wp_for (F1 F2:formula) (F3:int->formula) : formula :=
  wp_let F1 (fun v1 => wp_let F2 (fun v2 => wp_for_val v1 v2 F3)).

Definition wp_for' (F1 F2:formula) (F3:int->formula) : formula := local (fun Q =>
  F1 (fun v1 => F2 (fun v2 => wp_for_val v1 v2 F3 Q))).
*)


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint wp (E:ctx) (t:trm) : formula :=
  let aux := wp E in
  match t with
  | trm_val v => wp_val v
  | trm_var x => wp_var E x
  | trm_fun x t1 => wp_val (val_fun x (substs (ctx_rem x E) t1))
  | trm_fix f x t1 => wp_val (val_fix f x (substs (ctx_rem x (ctx_rem f E)) t1))
  | trm_if t0 t1 t2 => wp_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => wp_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => wp_let (aux t1) (fun X => wp (ctx_add x X E) t2)
  | trm_app t1 t2 => wp_app (substs E t)
  | trm_while t1 t2 => wp_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => wp_fail
      (*wp_for' (aux t1) (aux t2) (fun X => wp (ctx_add x X E) t3) *)
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
    --not needed in the proofs below *)

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
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. unfold wp_var. rewrite substs_var. destruct (ctx_lookup x E).
  { remove_local. apply~ rule_val. }
  { remove_local. intros; false~. }
Qed.

Lemma wp_sound_val : forall v,
  wp_sound (trm_val v).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_val. applys~ rule_val.
Qed.

Lemma wp_sound_fun : forall x t,
  wp_sound (trm_fun x t).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_fun. applys~ rule_fun.
Qed.

Lemma wp_sound_fix : forall f x t,
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

Lemma wp_sound_if : forall F1 F2 F3 E t1 t2 t3,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  F3 ===> wp_triple_ E t3 ->
  wp_if F1 F2 F3 ===> wp_triple_ E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_if. applys rule_if.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros b. simpl. remove_local ;=> b' M. inverts M. case_if.
    { rewrite triple_eq_himpl_wp_triple. applys* M2. }
    { rewrite triple_eq_himpl_wp_triple. applys* M3. } }
  { intros. applys~ wp_if_val_false. }
Qed.

Lemma wp_sound_seq : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_seq F1 F2 ===> wp_triple_ E (trm_seq t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_seq. applys rule_seq.
  { rewrite triple_eq_himpl_wp_triple. applys* M1. }
  { intros X. rewrite triple_eq_himpl_wp_triple. applys* M2. }
Qed.

Lemma wp_sound_let : forall F1 F2 E x t1 t2,
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

Lemma wp_sound_app : forall t1 t2,
  wp_sound (trm_app t1 t2).
Proof using.
  intros. intros E. simpl. applys qimpl_wp_triple.
  intros Q. remove_local.
  rewrite substs_app. rewrite triple_eq_himpl_wp_triple. hsimpl.
Qed.

Lemma wp_sound_while : forall F1 F2 E t1 t2,
  F1 ===> wp_triple_ E t1 ->
  F2 ===> wp_triple_ E t2 ->
  wp_while F1 F2 ===> wp_triple_ E (trm_while t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_triple. intros Q.
  remove_local. rewrite substs_while. applys rule_extract_hforall.
  set (R := wp_triple (trm_while (substs E t1) (substs E t2))).
  exists R. simpl. applys rule_extract_hwand_hpure_l.
  { split.
    { applys is_local_wp_triple. }
    { clears Q. applys qimpl_wp_triple. intros Q.
      applys rule_while_raw. rewrite <- substs_while. rewrite <- substs_seq.
      rewrite <- (substs_val E). rewrite <- substs_if.
      rewrite triple_eq_himpl_wp_triple. applys~ wp_sound_if.
      { applys~ wp_sound_seq. { unfold wp_triple_. rewrite~ substs_while. } }
      { intros Q'. applys wp_sound_val. } } }
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
  { applys wp_sound_fun. }
  { applys wp_sound_fix. }
  { applys* wp_sound_if. }
  { applys* wp_sound_seq. }
  { applys* wp_sound_let. }
  { applys* wp_sound_app. }
  { applys* wp_sound_while. }
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
      applys triple_apps_funs_of_wp_iter;
      [ reflexivity | try xeq_encs | reflexivity | xcf_post tt ]
  | val_fixs _ _ _ =>
      applys triple_apps_fixs_of_wp_iter f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | try xeq_encs |
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






