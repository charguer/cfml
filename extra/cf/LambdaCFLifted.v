(**

This file extends [LambdaCF.v] by "lifting" heap predicates like in
[SepLifted.v], so as to express specifications using logical values,
as opposed to deeply-embedded values. CF are lifted like triples.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Export LambdaCF SepLifted.
From TLC Require Import LibList.
Generalizable Variables A B.

Open Scope charac.

Ltac auto_star ::= jauto.


(* ********************************************************************** *)
(* * Auxiliary definitions *)


(* ---------------------------------------------------------------------- *)
(* ** Type of a formula *)

(** A formula is a binary relation relating a precondition
    and a postcondition. *)

Definition Formula := forall A (EA:Enc A), hprop -> (A -> hprop) -> Prop.

Global Instance Inhab_Formula : Inhab Formula.
Proof using. apply (Inhab_of_val (fun _ _ _ _ => True)). Qed.

Notation "^ F H Q" := ((F:Formula) _ _ H Q)
  (at level 65, F at level 0, H at level 0, Q at level 0,
   format "^ F  H  Q") : charac.

(** Constructor to force the return type of a Formula *)
Definition Formula_typed `{Enc A1} (F : hprop->(A1->hprop)->Prop) : Formula :=
  fun `{Enc A2} H (Q:A2->hprop) =>
    exists (Q':A1->hprop), F H Q' /\ PostChange Q' Q.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of [local] *)

Definition Local (F:Formula) := fun A `{EA:Enc A} H Q =>
   local (F A EA) H Q.

Lemma local_Local_eq : forall A `{EA:Enc A} (F:Formula),
  local (@Local F A EA) = (@Local F A EA).
Proof using.
  intros. apply pred_ext_2. intros H Q.
  unfold Local. rewrite local_local. split~.
Qed.

Lemma is_local_Local : forall A `{EA:Enc A} (F:Formula),
  is_local (@Local F A EA).
Proof using. intros. unfolds. rewrite~ local_Local_eq. Qed.

Hint Resolve is_local_Local.


(* ********************************************************************** *)
(* * Lifted CF *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic Formula
    associated with each term construct. *)

Definition Cf_fail : Formula := fun `{Enc A} H (Q:A->hprop) =>
  False.

Definition Cf_val (v:val) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists V, v = enc V /\ H ==> Q V.

Definition Cf_if_val (v:val) (F1 F2 : Formula) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists (b:bool), v = enc b /\
     (b = true -> ^F1 H Q) /\ (b = false -> ^F2 H Q).

Definition Cf_seq (F1 : Formula) (F2 : Formula) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists (Q1:unit->hprop), ^F1 H Q1 /\ ^F2 (Q1 tt) Q.

Definition Cf_let (F1 : Formula) (F2of : forall `{EA1:Enc A1}, A1 -> Formula) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists (A1:Type) (EA1:Enc A1) (Q1:A1->hprop),
        ^F1 H Q1
     /\ (forall (X:A1), ^(F2of X) (Q1 X) Q).

Definition Cf_let_typed `{EA1:Enc A1} (F1 : Formula) (F2of : A1 -> Formula) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists (Q1:A1->hprop),
        ^F1 H Q1
     /\ (forall (X:A1), ^(F2of X) (Q1 X) Q).

Definition Cf_if (F0 F1 F2 : Formula) : Formula :=
  Cf_let_typed F0 (fun (X:bool) => Local (Cf_if_val (enc X) F1 F2)).

Definition Cf_app (t : trm) : Formula :=
  @Triple t.

(* TODO simplified version to use:
Definition Cf_while (F1 F2 : Formula) : Formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    forall (F:Formula), is_local (@F unit _) ->
      (forall H' (Q':unit->hprop),
         ^(Local (Cf_if F1 (Local (Cf_seq F2 (F:Formula))) (Local (Cf_val val_unit)))) H' Q' ->
         ^(F:Formula) H' Q') ->
      ^(F:Formula) H Q.
*)

Definition Cf_while (F1 F2 : Formula) : Formula :=
  Formula_typed (fun H (Q:unit->hprop) =>
    forall (F:Formula), is_local (@F unit _) ->
      (forall H' (Q':unit->hprop),
         ^(Local (Cf_if F1 (Local (Cf_seq F2 (F:Formula))) (Local (Cf_val val_unit)))) H' Q' ->
         ^(F:Formula) H' Q') ->
      ^(F:Formula) H Q).

(* TODO: this is too weak, for loops must support bounds that are variables *)
Definition Cf_for_val (n1 n2:int) (F1 : int->Formula) : Formula :=
  (* Formula_typed (fun H (Q:unit->hprop) => *)
  fun `{Enc A} H (Q:A->hprop) =>  
    forall (S:int->Formula), (forall i, is_local (@S i unit _)) ->
    let F i := Local (If (i <= n2) then (Local (Cf_seq (F1 i) (S (i+1))))
                             else (Local (Cf_val val_unit))) in
    (forall i H' Q', ^(F i) H' Q' -> ^(S i) H' Q') ->
    ^(S n1) H Q.


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Definition Cf_def Cf (t:trm) : Formula :=
  match t with
  | trm_val v => Local (Cf_val v)
  | trm_var x => Local (Cf_fail) (* unbound variable *)
  | trm_fix f z t1 => Local (Cf_val (val_fix f z t1))
  | trm_if t0 t1 t2 => Local (Cf_if (Cf t0) (Cf t1) (Cf t2))
  | trm_let z t1 t2 =>
     Local (match z with
     | bind_anon => Cf_seq (Cf t1) (Cf t2)
     | bind_var x => Cf_let (Cf t1)
                                (fun `{EA:Enc A} (X:A) => Cf (subst1 x (enc X) t2))
     end)
  | trm_app t1 t2 => Local (Cf_app t)
  | trm_while t1 t2 => Local (Cf_while (Cf t1) (Cf t2))
  | trm_for x t1 t2 t3 => Local (
      match t1, t2 with
      | trm_val (val_int n1), trm_val (val_int n2) =>
            Cf_for_val n1 n2 (fun X => Cf (subst1 x X t3))
      | _, _ => Cf_fail (* not supported *)
      end)
  end.

Definition Cf := FixFun Cf_def.

Lemma Cf_unfold_iter : forall n t,
  Cf t = func_iter n Cf_def Cf t.
Proof using.
  Opaque subst1.
  applys~ (FixFun_fix_iter (measure trm_size)). auto with wf.
  intros f1 f2 t IH. unfold Cf_def.
  destruct t; fequals.
  { fequals~. }
  { destruct b.
    { fequals~. }
    { fequals~. applys~ fun_ext_3. } }
  { fequals~. } 
  { destruct t1; fequals~. destruct v0; fequals~.
    destruct t2; fequals~. destruct v0; fequals~.
    applys~ fun_ext_1. }
Qed.

Lemma Cf_unfold : forall t,
  Cf t = Cf_def Cf t.
Proof using. applys (Cf_unfold_iter 1). Qed.


(* ********************************************************************** *)
(* ** Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Soundness of the CF generator *)

Lemma is_local_Cf : forall A `{EA:Enc A} T,
  is_local ((Cf T) A EA).
Proof.
  intros. rewrite Cf_unfold. destruct T; try apply is_local_local.
Qed.

Definition Sound_for (t:trm) (F:Formula) :=
  forall A (EA:Enc A) H (Q:A->hprop), ^F H Q -> Triple t H Q.

Lemma Sound_for_Local : forall t (F:Formula),
  Sound_for t F ->
  Sound_for t (Local F).
Proof using.
  unfold sound_for. introv SF. intros A EA H Q M.
  rewrite is_local_Triple. applys local_weaken M. applys SF.
Qed.

Lemma Sound_for_Cf : forall (t:trm),
  Sound_for t (Cf t).
Proof using.
  intros t. induction_wf: trm_size t.
  rewrite Cf_unfold. destruct t;
   try (applys Sound_for_Local; intros A EA H Q P).
  { destruct P as (V&E&P). applys* Triple_val. }
  { false. }
  { destruct P as (V&E&P).
    applys Triple_enc_val_inv (fun r => \[r = enc V] \* H).
    { applys Triple_fix. rewrite E. hsimpl~. }
    { intros X. hpull ;=> EX. subst X. hchange P. hsimpl. simple~. } }
  { destruct P as (Q1&P1&P2). applys @Triple_if.
    { applys* IH. }
    { intros b. specializes P2 b. applys Sound_for_Local (rm P2).
      clears A H Q1. intros A EA H Q (b'&P1'&P2'&P3').
      asserts E: (b = b'). { destruct b; destruct b'; auto. }
      clear P1'. subst b'. case_if; applys* IH. } }
  { destruct b as [|x].
    { destruct P as (H1&P1&P2). applys Triple_seq H1.
      { applys~ IH. }
      { intros X. applys~ IH. } }
    { destruct P as (A1&EA1&Q1&P1&P2). applys Triple_let Q1.
      { applys~ IH. }
      { intros X. specializes P2 X.
        unfold Subst1. applys~ IH. } } }
  { auto. }
  { hnf in P. destruct P as (Q'&P&HC). simpls.
    applys Triple_enc_change HC.
    applys P. { xlocal. } clears H Q. intros H Q P.
    applys Triple_while_raw. applys Sound_for_Local (rm P).
    clears A H Q Q'. intros A EA H Q (Q1&P1&P2). applys Triple_if.
    { applys* IH. }
    { intros b. specializes P2 b. applys Sound_for_Local (rm P2).
      clears A H Q1. intros A EA H Q (b'&P1&P2&P3).
      asserts E: (b = b'). { destruct b; destruct b'; auto. }
      clears P1. subst b'. case_if as C.
      { forwards~ P2': (rm P2). applys Sound_for_Local (rm P2').
        clears A H b. intros A EA H Q (H1&P1&P2). applys Triple_seq.
         { applys* IH. }
         { applys P2. } }
      { forwards~ P3': (rm P3). applys Sound_for_Local (rm P3').
        clears A H b. intros A EA H Q (V&E&P). applys* Triple_val. } } }
  { destruct t1; tryfalse. destruct v0; tryfalse.
    destruct t2; tryfalse. destruct v0; tryfalse.
    renames z to n1, z0 to n2.
    (* hnf in P. destruct P as (Q'&P&HC). simpls.
    applys Triple_enc_change HC. *)
    applys P. { intros; xlocal. } (* todo xlocal *)
    clears A H. intros i H Q P. applys Sound_for_Local (rm P).
    clears A H. intros A EA H Q P. applys Triple_for_raw.
    case_if as C.
    { applys Sound_for_Local (rm P). clears A H i.
      intros A EA H Q (H1&P1&P2). applys Triple_seq.
      { applys* IH. unfolds~ Subst1. }
      { applys P2. } }
    { applys Sound_for_Local (rm P). clears A H i.
      intros A EA H Q (V&E&P). applys* Triple_val. } }
Qed.

Theorem Triple_of_Cf : forall (t:trm) A `{EA:Enc A} H (Q:A->hprop),
  ^(Cf t) H Q ->
  Triple t H Q.
Proof using. intros. applys* Sound_for_Cf. Qed.


(* ********************************************************************** *)
(* * Practical proofs using characteristic Formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for characteristic Formulae *)

Notation "'`Fail'" :=
  (Local (Cf_fail))
  (at level 69) : charac.

Notation "'`Val' v" :=
  (Local (Cf_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  (Local (Cf_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  (Local (Cf_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  (Local (Cf_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'``Let' x ':=' F1 'in' F2" :=
  (Local (Cf_let_typed F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '``Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' [ A EA ] x ':=' F1 'in' F2" :=
  (Local (Cf_let F1 (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' '`Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  (Local (Cf_app t))
  (at level 68, t at level 0) : charac.

Notation "'`While' F1 'Do' F2 'Done'" :=
  (Local (Cf_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' '`While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : charac.

Notation "'`For' x '=' n1 'To' n2 'Do' F3 'Done'" :=
  (Local (Cf_for_val n1 n2 (fun x => F3)))
  (at level 69, x ident,
   format "'[v' '`For'  x  '='  n1  'To'  n2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : charac.

Open Scope charac.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

Lemma Triple_trm_of_Cf_iter : forall (n:nat) t A `{EA:Enc A} H (Q:A->hprop),
  func_iter n Cf_def Cf t A EA H Q ->
  Triple t H Q.
Proof using.
  introv M. rewrite <- Cf_unfold_iter in M. applys* Triple_of_Cf.
Qed.

(* todo: factorize with next lemma *)
Lemma Triple_apps_funs_of_Cf_iter : forall n F (Vs:dyns) (vs:vals) xs t A `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  func_iter n Cf_def Cf (Substn xs Vs t) A EA H Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Triple_apps_funs. applys* Triple_trm_of_Cf_iter.
Qed.

Lemma Triple_apps_fixs_of_Cf_iter : forall n F (f:var) (Vs:dyns) (vs:vals) xs t A `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  vs = encs Vs ->
  var_fixs_exec f (length Vs) xs ->
  func_iter n Cf_def Cf (Substn (f::xs) ((Dyn F)::Vs) t) A EA H Q ->
  Triple (trm_apps (val_fixs f xs t) vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  subst. applys* Triple_apps_fixs. applys* Triple_trm_of_Cf_iter.
Qed.

Definition Cf_while_inv (F1 F2 : Formula) := fun (H:hprop) (Q:unit->hprop) =>
  exists (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H',
     wf R
  /\ (H ==> \exists b X, I b X \* H')
  /\ (forall (F:Formula), is_local (@F unit _) -> forall b X,
      (forall b' X', R X' X -> ^F (I b' X') (fun (_:unit) => \exists Y, I false Y)) ->
      ^(Local (Cf_if F1 (Local (Cf_seq F2 F)) (Local (Cf_val val_unit))))
        (I b X) (fun (_:unit) => \exists Y, I false Y))
  /\ ((fun (_:unit) => \exists X, I false X \* H') ===> Q).

Lemma Cf_while_of_Cf_while_inv : forall (F1 F2 : Formula) (H:hprop) (Q:unit->hprop),
  (Cf_while_inv F1 F2) H Q ->
  ^(Cf_while F1 F2) H Q.
Proof using.
  introv (A&I&R&H'&MR&MH&MB&MQ). exists Q; split; [|applys @PostChange_refl].
  intros F LF HF. xchange MH. xpull ;=> b X.
  applys local_frame (I b X) H' (fun (_:unit) => \exists Y, I false Y);
   [ xlocal | | hsimpl | hchanges~ MQ ]. (* todo: change goal order in weakenpost*)
  gen b. induction_wf IH: MR X. intros. applys (rm HF).
  applys MB. xlocal. intros b' X' HR'. applys~ IH.
Qed.



(* DEPRECATED

(* ********************************************************************** *)
(* * CFLifted tactics *)

(** Extends tactics defined in [LambdaCFTactics.v] and [LambdaCF.v] *)

(* ---------------------------------------------------------------------- *)
(* ** Registering specifications *)

Notation "'Register_Rule' t" := (Register_goal (Triple t _ _))
  (at level 69) : charac.

Notation "'Register_Spec' f" := (Register_Rule (trm_apps (trm_val f) _))
  (at level 69) : charac.


(* ---------------------------------------------------------------------- *)
(* ** [xspec] *)

Ltac xspec_context_for f :=
  match goal with
  | H: context [ Triple _ _ _ ] |- _ =>
      match type of H with
      | context [ trm_app (trm_val f) _ ] => generalize H
      | context [ trm_apps (trm_val f) _ ] => generalize H
      end end.

Ltac xspec_context_triple tt :=
  let f := xcf_get_fun_from_goal tt in
  xspec_context_for f.

Ltac xspec_context_formula F :=
  match goal with H: context [ F _ _ _ _ ] |- _ => generalize H end.

Ltac xspec_context G ::=
  match G with
  | Triple _ _ _ => xspec_context_triple tt
  | ?F _ _ _ _ => xspec_context_formula F
  (* last line only for CF lifted *)
  end.


(* ---------------------------------------------------------------------- *)
(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Triple_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide Triple_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.


(*--------------------------------------------------------*)
(* ** [hsimpl] and [xpull] cleanup of boolean reflection *)

Ltac hsimpl_post_before_generalize tt ::=
  autorewrite with rew_bool_eq.

Ltac himpl_post_processing_for_hyp H ::=
  autorewrite with rew_bool_eq in H.

Ltac xpull_post_processing_for_hyp H ::=
  autorewrite with rew_bool_eq in H.


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
(* ** [xeq_enc] : used internally *)

(** [xeq_enc] solves goal of the form [ v = enc ?V ]. *)

(* DEPRECATED
Ltac xeq_enc_core tt :=
  match goal with |- ?v = enc ?V => applys (refl_equal (enc (decode v))) end.
*)

Ltac xeq_enc_core tt :=
  match goal with |- ?v = enc ?V =>
    let W := constr:(decode v) in
    let W' := (eval simpl decode in W) in
    match W' with Dyn ?V' => refine (refl_equal (enc V'))
  end end.

Tactic Notation "xeq_enc" :=
  xeq_enc_core tt.


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


(*--------------------------------------------------------*)
(* ** [xcf] *)

Ltac xcf_get_fun_remove_encs f ::=
  match f with
  | @enc func _ ?f => xcf_get_fun_remove_encs f
  | @enc val _ ?f => xcf_get_fun_remove_encs f
  | _ => constr:(f)
  end.

Ltac xcf_get_fun_from_goal tt ::=
  match goal with |- Triple ?t _ _ => xcf_get_fun_from_trm t end.

Ltac xcf_post tt ::=
  simpl; unfold subst1; simpl; rew_enc_dyn.

Ltac xcf_trm n ::=
  applys Triple_trm_of_Cf_iter n; [ xcf_post tt ].

Ltac xcf_basic_fun n f' ::=
  let f := xcf_get_fun tt in
  match f with
  | val_funs _ _ =>
      applys Triple_apps_funs_of_Cf_iter n;
      [ reflexivity | try xeq_encs | reflexivity | xcf_post tt ]
  | val_fixs _ _ _ =>
      applys Triple_apps_fixs_of_Cf_iter n f';
      [ reflexivity | try xeq_encs | reflexivity | xcf_post tt ]
  end.

Ltac xcf_prepare_args tt ::=
  rew_nary;
  try xdecode_args tt.


(*--------------------------------------------------------*)
(* ** [xval] *)

Ltac xval_nohtop_core tt ::=
  applys local_erase; unfold Cf_val.

(* todo: xval wouldn't work if the postcondition isn't specified
   and the result value has been introduced locally, e.g. with nested lets *)

Lemma xval_htop_evar : forall A (V:A) (EA:Enc A) v H,
  v = enc V ->
  Local (Cf_val v) H (fun (x:A) => \[x = V] \* H).
Proof using.
  introv E. applys local_erase. exists V. split~. hsimpl~.
Qed.

Arguments xval_htop_evar [A].

Lemma xval_htop_lemma : forall A (V:A) (EA:Enc A) v H Q,
  v = enc V ->
  H ==> Q V \* \Top ->
  Local (Cf_val v) H Q.
Proof using.
  introv E M. unfold Cf_val.
  applys~ local_htop_post (Q \*+ \Top).
  applys local_erase. exists~ V.
Qed.

Arguments xval_htop_lemma [A].

(* TODO; simplify proof of original xval_htop_lemma in LambdaCF *)

Lemma xval_htop_as_lemma : forall A (V:A) (EA:Enc A) v H Q,
  v = enc V ->
  (forall (x:A), x = V -> H ==> Q x \* \Top) ->
  Local (Cf_val v) H Q.
Proof using. intros. applys* xval_htop_lemma. Qed.

Ltac xval_basic tt ::=
  match goal with
  | |- Local ?F ?H ?Q => is_evar Q; applys xval_htop_evar; [ try xeq_enc ]
  | _ => applys xval_htop_lemma; [ try xeq_enc | ]
  end.
(* TODO: should we force the ?F to be a Cf_val ?*)


(* warning : all below are modified copy-paste  *)

(* TODO: better factorization of the code by using an auxiliary function
   to test whether the head is a Local Cf_val or something else *)

Ltac xval_template xlet_tactic xval_tactic xlet_cont ::=
  match goal with
  | |- Local (Cf_let _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | |- Local (Cf_if _ _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | _ => xval_tactic tt
  end.


(*--------------------------------------------------------*)
(* ** [xvals ] *)

Ltac xvals_core tt ::=
  match goal with
  | |- Local (Cf_val _) _ _ => xval_basic tt; hsimpl
  | _ => xval_template ltac:(fun tt => xlet) ltac:(xval_basic) ltac:(xapps_let_cont)
  end.


(*--------------------------------------------------------*)
(* ** [xval as ] *)

Ltac xval_as_basic X EX ::=
  match goal with
  | |- Local ?F ?H ?Q => is_evar Q; applys local_erase; applys qimpl_refl
  | _ => applys xval_htop_as_lemma; intros X EX
  end.

Ltac xval_as_core X ::=
  match goal with
  | |- Local (Cf_val _) _ _ => let EX := fresh "E" X in xval_as_basic X EX
  | _ => xval_template ltac:(fun tt => xlet as X) ltac:(xval_basic) ltac:(xapp_as_let_cont)
  end.


(*--------------------------------------------------------*)
(* ** [xval V] *)

Ltac xval_arg V :=
  match goal with
  | |- Local ?F ?H ?Q => is_evar Q; applys xval_htop_evar; [ try reflexivity ]
  | _ => applys (xval_htop_lemma V); [ try reflexivity | ]
  end.

Tactic Notation "xval" constr(V) :=
  xval_arg V.

(*todo: [xvals V] *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt ::=
  applys local_erase; esplit; split.


(*--------------------------------------------------------*)
(* ** [xlet] *)

(* Playing some tricks with the identity function to prevent undesired eager typeclass resolution *)
(* TODO: should no longer be needed *)

Lemma Cf_let_intro' : forall A1 (EA1:id Enc A1) (Q1:A1->hprop) (F1 : Formula) (F2of : forall A1 `{EA1:Enc A1}, A1 -> Formula),
  forall A (EA:id Enc A) H (Q:A->hprop),
  F1 A1 EA1 H Q1 ->
  (forall (X:A1), (@F2of A1 EA1 X) A EA (Q1 X) Q) ->
  (Cf_let F1 (@F2of)) A EA H Q.
Proof using. intros. hnf. exists A1 EA1 Q1. auto. Qed.

Lemma Cf_let_intro : forall A1 (EA1:Enc A1) (Q1:A1->hprop) (F1 : Formula) (F2of : forall A1 `{EA1:Enc A1}, A1 -> Formula),
  forall A (EA:Enc A) H (Q:A->hprop),
  ^F1 H Q1 ->
  (forall (X:A1), ^(F2of A1 X) (Q1 X) Q) ->
  ^(Cf_let F1 F2of) H Q.
Proof using. intros. hnf. exists A1 EA1 Q1. auto. Qed.

Ltac xlet_untyped_core tt :=
  applys local_erase; eapply @Cf_let_intro'.

Ltac xlet_typed_core tt :=
  applys local_erase; esplit; split.

Ltac xlet_core tt ::=
  match goal with
  | |- Local (Cf_let _ _) _ _ => xlet_untyped_core tt
  | |- Local (Cf_let_typed _ _) _ _ => xlet_typed_core tt
  | |- Local (Cf_if _ _ _) _ _ => xlet_typed_core tt
  end.


(*--------------------------------------------------------*)
(* ** xif *)

(*
Ltac xif_core tt ::=
  applys local_erase;
  applys Cf_if_val_bool;
  rew_istrue.
*)
  (* applys Cf_if_val_isTrue ;=> C. *)


(*--------------------------------------------------------*)
(* ** [xfail] *)

Ltac xfail_core tt ::=
  applys local_erase; unfold Cf_fail.


(*--------------------------------------------------------*)
(* ** xapp *)

(* Remark:
  Ltac xapply_core H cont1 cont2 :=
    forwards_nounfold_then H ltac:(fun K =>
      match xpostcondition_is_evar tt with
      | true => eapply local_frame; [ xlocal | sapply K | cont1 tt | try apply qimpl_refl ]
      | false => eapply local_frame_htop; [ xlocal | sapply K | cont1 tt | cont2 tt ]
      end).
*)

Ltac xapp_xapply E cont_post ::=
  match goal with
  | |- ?F ?H ?Q => is_evar Q; xapplys E
  | |- ?F ?H (fun (_:unit) => ?H') => is_evar H'; xapplys E (* TODO: is needed? *)
  | _ =>
     first [ xapply_core E ltac:(fun tt => solve [ hcancel ]) ltac:(cont_post)
           | xapply_core E ltac:(idcont) ltac:(idcont) ]
    (* DEPRECATED xapply_core E ltac:(fun tt => hcancel) ltac:(cont_post)  *)
  end.


(* todo: factorize using a "remove local" tactic *)
Ltac xapp_basic_prepare tt ::=
  unfold Cf_app;
  try match goal with |- @Local _ _ _ _ _ => apply local_erase end;
  rew_nary;
  try xdecode_args tt.

Ltac xapp_template xlet_tactic xapp_tactic xlet_cont ::=
  match goal with
  | |- Local (Cf_let _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- Local (Cf_let_typed _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- Local (Cf_if _ _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- Local (Cf_seq _ _) _ _ => xseq; [ xapp_tactic tt | ]
  | _ => xapp_tactic tt
  end.

(* TODO: find out why sapply is too slow *)
Ltac fast_apply E :=
  first [ eapply E (* | sapply E *) ].

Ltac xapply_core H cont1 cont2 ::=
  forwards_nounfold_then H ltac:(fun K =>
    match xpostcondition_is_evar tt with
    | true => eapply local_frame; [ xlocal | fast_apply K | cont1 tt | try apply qimpl_refl ]
    | false => eapply local_frame_htop; [ xlocal | fast_apply K | cont1 tt | cont2 tt ]
    end).


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwhile] *)

Ltac xpostchange_solve tt :=
  first [ apply PostChange_refl
        | fail 100 "Postcondition not of the expected type" ].

Ltac xformula_typed_elim tt :=
  esplit; split; [ | xpostchange_solve tt ].


Ltac xwhile_template xwhile_tactic xseq_cont ::=
  match goal with
  | |- Local (Cf_seq _ _) _ _ => xseq; [ xwhile_tactic tt | xseq_cont tt ]
  | _ => xwhile_tactic tt
  end.

Ltac xwhile_intros_all R LR HR ::=
  intros R LR HR;
  change (R) with (R:Formula) in *.

Ltac xwhile_basic xwhile_intros_tactic ::=
  applys local_erase;
  xformula_typed_elim tt;
  xwhile_intros_tactic tt.


*)