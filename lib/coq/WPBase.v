(**

This file formalizes characteristic formulae in weakest-precondition form
for plain Separation Logic.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From CFML Require Export SepBase.
Import LibListExec.RewListExec.
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

(** [wp t Q] defines the weakest-precondition for term [t]
    and postcondition [Q].

    [H ==> wp t Q] is equivalent to [triple t H Q].

    [wp] is defined in terms of the generic definition of [weakestpre]:
    [Definition weakestpre F Q := \exists H, H \* \[F H Q].]
    which comes from [LibSepFunctor]. *)

Definition wp (t:trm) : formula :=
  weakestpre (triple t).

(** [wpsubst E t] is a shorthand for [wp (isubst E t)] *)

Definition wpsubst E t :=
  wp (isubst E t).


(* ---------------------------------------------------------------------- *)
(* ** Definition of [struct] for WP *)

(** [formula'] is a generalization of the type [formula], needed to
    anticipate for needs in [WPLifted]. *)

Definition formula' (B:Type) := (B -> hprop) -> hprop.

(** [struct F] asserts that one is able to establish [F Q]
    by establishing [F Q'] for a [Q'] that entails [Q]. *)

Definition structural B (F:formula' B) :=
  forall Q, (\exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ==> F Q.

(** [structural_pred S] asserts that [structural (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition structural_pred B A (S:A->formula' B) :=
  forall x, structural (S x).


(* ---------------------------------------------------------------------- *)
(* ** Rules for [struct] *)

Section Fmklocal.
Variable (B : Type).
Implicit Type Q : B->hprop.
Implicit Type F : formula' B.

(** A introduction rule to establish [struct], exposing the definition *)

Lemma structural_intro : forall F,
  (forall Q, (\exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ==> F Q) ->
  structural F.
Proof using. auto. Qed.

(** Introduction rule for [struct] on [weakestpre] *)

Lemma structural_weakestpre : forall (T:hprop->(B->hprop)->Prop),
  SepBasicSetup.local T ->
  structural (weakestpre T).
Proof using.
  introv L. applys structural_intro. intros Q. unfold weakestpre.
  xpull ;=> Q' H M. xsimpl (H \* (Q' \--* Q \*+ \GC)).
  applys* local_ramified_frame_hgc.
Qed.

(** An elimination rule for [struct] *)

Lemma structural_elim : forall F H Q,
  structural F ->
  (H ==> \exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ->
  H ==> F Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans' N. Qed.

(** An elimination rule for [struct] without [\GC] *)

Lemma structural_elim_nohgc : forall F H Q,
  structural F ->
  (H ==> \exists Q', F Q' \* (Q' \--* Q)) ->
  H ==> F Q.
Proof using.
  introv L M. applys~ structural_elim. xchanges M.
Qed.

(** Other specialized elimination rules *)

Lemma structural_conseq : forall Q' F H Q,
  structural F ->
  H ==> F Q ->
  Q ===> Q' ->
  H ==> F Q'.
Proof using.
  introv L M W. applys~ structural_elim.
  xchange (rm M). xsimpl Q. xchanges W.
Qed.

Lemma structural_hgc : forall F H Q,
  structural F ->
  H ==> F (Q \*+ \GC) ->
  H ==> F Q.
Proof using.
  introv L M. applys~ structural_elim.
  xchange (rm M). xsimpl (Q \*+ \GC).
Qed.

Lemma structural_frame : forall H1 H2 F H Q,
  structural F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x) ->
  H ==> F Q.
Proof using.
  introv L W M. applys~ structural_elim. xchange W. xchanges M.
Qed.

Lemma structural_frame_hgc : forall H1 H2 F H Q,
  structural F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x \* \GC) ->
  H ==> F Q.
Proof using.
  introv L W M. applys* structural_hgc. applys* structural_frame.
Qed.

End Fmklocal.


(* ---------------------------------------------------------------------- *)
(* ** Definition of [mkstruct] for WP *)

(** [mkstruct F] transforms a formula [F] into one that satisfies [struct]. *)

Definition mkstruct B (F:formula' B) : formula' B :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

(** Properties *)

Section Mkstruct.
Variable (B : Type).
Implicit Type Q : B->hprop.
Implicit Type F : formula' B.

(** [mkstruct] can be erased *)

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. repeat xsimpl.
Qed.

(** [mkstruct] is idempotent, i.e. nested applications
   of [mkstruct] are redundant *)

Lemma mkstruct_mkstruct : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  intros F. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkstruct. xpull ;=> Q' Q''. xsimpl Q''. }
  { xchanges mkstruct_erase. }
Qed.

(** A definition whose head is [mkstruct] satisfies [struct] *)

Lemma structural_mkstruct : forall F,
  structural (mkstruct F).
Proof using.
  intros. applys structural_intro. intros Q.
  pattern mkstruct at 1. rewrite <- mkstruct_mkstruct.
  unfold mkstruct. auto.
Qed.

(** A [mkstruct] can be introduced at the head of a formula satisfying [struct] *)

Lemma eq_mkstruct_of_structural : forall F,
  structural F ->
  F = mkstruct F.
Proof using.
  introv L. applys fun_ext_1 ;=> Q. applys himpl_antisym.
  { applys~ mkstruct_erase. }
  { applys~ structural_elim. }
Qed.

(** Contradictions can be extracted from mkstruct formulae *)

Lemma mkstruct_false : forall F Q,
  (forall Q', F Q' ==> \[False]) ->
  (mkstruct F Q ==> \[False]).
Proof using.
  introv M. unfold mkstruct. xpull ;=> Q'. xchange (M Q').
Qed.

(** [mkstruct] is a covariant transformer w.r.t. predicate inclusion *)

Lemma mkstruct_weaken : forall F F',
  F ===> F' ->
  mkstruct F ===> mkstruct F'.
Proof using.
  unfold mkstruct. introv M. intros Q. xpull ;=> Q'. xsimpl~ Q'.
Qed.

(** [mkstruct] can be erased on the left of an entailment if the
    formula on the right is mkstruct. *)

Lemma mkstruct_erase_l : forall F1 F2,
  structural F2 ->
  F1 ===> F2 ->
  mkstruct F1 ===> F2.
Proof using.
  introv LF M. rewrite~ (eq_mkstruct_of_structural LF). applys* mkstruct_weaken.
Qed.

End Mkstruct.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary functions for iterated quantifiers used by
      WP for pattern matching *)

(** [forall_vars Hof G (x1::x2::x3::nil)] produces the proposition
    [forall X1 X2 X3, Hof ((x3,X3)::(x2,X2)::(x1,X1)::(List.rev G))) *)

Fixpoint forall_vars (Hof:ctx->Prop) (G:ctx) (xs:vars) : Prop :=
  match xs with
  | nil => Hof (List.rev G) (* TODO: Ctx.rev *)
  | x::xs' => forall (X:val), forall_vars Hof (Ctx.add x X G) xs'
  end.

Lemma forall_vars_intro : forall xs (Pof:ctx->Prop),
  (forall G, Ctx.dom G = xs -> Pof G) ->
  forall_vars Pof Ctx.empty xs.
Proof using.
  introv M1. cuts N: (forall G1,
    (forall G2, Ctx.dom G2 = xs -> Pof (Ctx.app (LibList.rev G1) G2)) ->
    forall_vars Pof G1 xs).
  { forwards~ K: N (Ctx.empty:ctx). }
  { clears M1. induction xs as [|x xs']; intros G1 HG1.
    { simpl. forwards~ K: HG1 (Ctx.empty:ctx). rewrite Ctx.app_empty_r in K.
      rew_list_exec. auto. }
    { simpl. intros X. rew_ctx. applys IHxs'.
      intros G2 HG2. rewrite <- Ctx.app_rev_add. applys HG1.
      rewrite Ctx.dom_add. fequals. } }
Qed.

(** [hforall_vars Hof G (x1::x2::x3::nil)] produces the heap predicate
    [\forall X1 X2 X3, Hof ((x3,X3)::(x2,X2)::(x1,X1)::(List.rev G))) *)

Fixpoint hforall_vars (Hof:ctx->hprop) (G:ctx) (xs:vars) : hprop :=
  match xs with
  | nil => Hof (Ctx.rev G)
  | x::xs' => \forall (X:val), hforall_vars Hof (Ctx.add x X G) xs'
  end.

Lemma hforall_vars_intro : forall G xs Hof,
  Ctx.dom G = xs ->
  (hforall_vars Hof Ctx.empty xs) ==> Hof G.
Proof using.
  introv DG. cuts N: (forall (G1 G2:ctx),
    Ctx.dom G2 = xs ->
        (hforall_vars Hof G1 xs)
    ==> Hof (Ctx.app (LibList.rev G1) G2)).
  { forwards K: N (Ctx.empty:ctx) G. { auto. }
    rewrite Ctx.app_empty_l in K. applys K. }
  clears G. induction xs as [|x xs']; intros G1 G2 EQ.
  { simpl. rewrite Ctx.rev_eq. forwards~ G2E: (Ctx.dom_eq_nil_inv G2).
     subst. rewrite~ Ctx.app_empty_r. }
  { simpl. destruct G2 as [| (x',X) G']; tryfalse.
    simpl in EQ. invert EQ ;=> Ex EG2. subst x'.
    applys himpl_hforall_l X. rew_ctx.
    rewrite Ctx.app_rev_add. rewrite EG2. applys~ IHxs'. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition wpgen_fail : formula := mkstruct (fun Q =>
  \[False]).

Definition wpgen_val (v:val) : formula := mkstruct (fun Q =>
  Q v).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkstruct (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wpgen_seq (F1 F2:formula) : formula := mkstruct (fun Q =>
  F1 (fun X => F2 Q)).

Definition wpgen_let_aux := wpgen_let.

Definition wpaux_getval wpgen (E:ctx) (t1:trm) (F2of:val->formula) : formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                 | Some v => F2of v
                 | None => wpgen_fail
                 end
  | _ => wpgen_let_aux (wpgen E t1) F2of
  end.

Definition wpgen_constr wpgen (E:ctx) (id:idconstr) : list val -> list trm -> formula :=
  fix mk (rvs : list val) (ts : list trm) : formula :=
    match ts with
    | nil => wpgen_val (val_constr id (List.rev rvs))
    | t1::ts' => wpaux_getval wpgen E t1 (fun v1 => mk (v1::rvs) ts')
    end.

Definition wpgen_app (v0:val) (vs:list val) : formula :=
  mkstruct (wp (trm_apps v0 (trms_vals vs))).

Definition wpaux_apps wpgen (E:ctx) (v0:val) : list val -> list trm -> formula :=
  fix mk (rvs : list val) (ts : list trm) : formula :=
    match ts with
    | nil => wpgen_app v0 (List.rev rvs)
    | t1::ts' => wpaux_getval wpgen E t1 (fun v1 => mk (v1::rvs) ts')
    end.

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := mkstruct (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Definition wpgen_while (F1 F2:formula) : formula := mkstruct (fun Q =>
  \forall (R:formula),
  let F := wpgen_if F1 (wpgen_seq F2 R) (wpgen_val val_unit) in
  \[ structural R /\ F ===> R] \-* (R Q)).

Definition wpgen_for_val (v1 v2:val) (F1:val->formula) : formula := mkstruct (fun Q =>
  \exists (n1:int) (n2:int), \[v1 = val_int n1 /\ v2 = val_int n2] \*
  \forall (S:int->formula),
  let F i := If (i <= n2) then (wpgen_seq (F1 i) (S (i+1)))
                          else (wpgen_val val_unit) in
  \[ structural_pred S /\ (forall i, F i ===> S i)] \-* (S n1 Q)).

Definition wpgen_case_val (F1:formula) (P:Prop) (F2:formula) : formula :=
  mkstruct (fun Q =>
    hand (F1 Q) (\[P] \-* F2 Q)).

Definition wpaux_match wpgen (E:ctx) (v:val) : list (pat*trm) -> formula :=
  fix mk (pts:list(pat*trm)) : formula :=
    match pts with
    | nil => wpgen_fail
    | (p,t)::pts' =>
        let xs := patvars p in
        let F1 (Q:val->hprop) :=
           hforall_vars (fun G => let E' := (Ctx.app G E) in
              \[v = patsubst G p] \-* (wpgen E' t) Q) Ctx.empty xs in
        let P := forall_vars (fun G => v <> patsubst G p) Ctx.empty xs in
        wpgen_case_val F1 P (mk pts')
    end.


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  let aux := wpgen E in
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  | trm_fixs f xs t1 =>
      match xs with
      | nil => wpgen_fail
      | _ => wpgen_val (val_fixs f xs (isubst (Ctx.rem_vars xs (Ctx.rem f E)) t1))
      end
  | trm_constr id ts => wpgen_constr wpgen E id nil ts
  | trm_if t0 t1 t2 => wpaux_getval wpgen E t0 (fun v0 => wpgen_if_val v0 (aux t1) (aux t2))
  | trm_let x t1 t2 => wpgen_let (aux t1) (fun X => wpgen (Ctx.add x X E) t2)
  | trm_apps t0 ts => wpaux_getval wpgen E t0 (fun v0 => wpaux_apps wpgen E v0 nil ts)
  | trm_while t1 t2 => wpgen_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 =>
      wpaux_getval wpgen E t1 (fun v1 =>
        wpaux_getval wpgen E t2 (fun v2 =>
          wpgen_for_val v1 v2 (fun X => wpgen (Ctx.add x X E) t3)))
  | trm_match t0 pts =>
      wpaux_getval wpgen E t0 (fun v0 =>
        wpaux_match wpgen E v0 pts)
  | trm_fail => wpgen_fail
  end.

(* Note: for simplicity, no special handling here of [trm_seq], unlike in [WPLifted]. *)


(* ********************************************************************** *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [wp t] is a mkstruct formula *)

Lemma structural_wp : forall t,
  structural (wp t).
Proof using. intros. applys~ structural_weakestpre. Qed.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma triple_eq_himpl_wp : forall H Q t,
  triple t H Q = (H ==> wp t Q).
Proof using. intros. applys~ weakestpre_eq. Qed.

(** Reformulation of the right-to-left implication above as an implication. *)

Lemma triple_of_wp : forall H Q t,
  H ==> wp t Q ->
  triple t H Q.
Proof using. intros. rewrite* triple_eq_himpl_wp. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_wp_of_triple : forall t F,
  (forall Q, triple t (F Q) Q) ->
  F ===> wp t.
Proof using. introv M. intros Q. rewrite~ <- triple_eq_himpl_wp. Qed.

(** Another corollary of [triple_eq_himpl_wp],
    Remark: it is not used in the proofs below, [triple_of_wp] is more useful. *)

Lemma triple_wp : forall t Q,
  triple t (wp t Q) Q.
Proof using. intros. applys~ weakestpre_pre. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [mkstruct] transformer *)

(** The [mkstruct] transformer is sound w.r.t. [triple] *)

Lemma triple_mkstruct_pre : forall t (F:formula) Q,
  (forall Q, triple t (F Q) Q) ->
  triple t (mkstruct F Q) Q.
Proof using.
  introv M. applys~ local_elim.
  unfold mkstruct. xpull ;=> Q'.
  xsimpl (F Q') ((Q' \--* Q \*+ \GC)) Q'. split~.
  { xsimpl. }
Qed.

(** The tactic [remove_mkstruct] applies to goal of the form [triple t (mkstruct F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q]. *)

Ltac remove_mkstruct :=
  match goal with |- triple _ _ ?Q =>
    applys triple_mkstruct_pre; try (clear Q; intros Q) end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wpgen] *)

(** [wpgen_sound t] asserts that [wpgen] is sound for all contexts [E],
    in the sense that the syntactic wpgen entails the semantics wp:
[[
    forall Q,  wpgen E t Q ==> wpsubst E t Q
]] *)

Definition wpgen_sound t := forall E,
  wpgen E t ===> wpsubst E t.

(** Lemma for [wpgen_fail] *)

Lemma himpl_wpgen_fail_l : forall Q H,
  wpgen_fail Q ==> H.
Proof using. intros. unfold wpgen_fail, mkstruct. xpull. Qed.

Lemma triple_wpgen_fail : forall t Q Q',
  triple t (wpgen_fail Q) Q'.
Proof using.
  intros. apply triple_of_wp. applys himpl_wpgen_fail_l.
Qed.

(** Soundness of the [wpgen] for the various constructs *)

Lemma wpgen_sound_fail :
  wpgen_sound trm_fail.
Proof using. intros. intros E Q. applys himpl_wpgen_fail_l. Qed.

Lemma wpgen_sound_getval : forall E C t1 F2of,
  evalctx C ->
  wpgen_sound t1 ->
  (forall v, F2of v ===> wpsubst E (C (trm_val v))) ->
  wpaux_getval wpgen E t1 F2of ===> wpsubst E (C t1).
Proof using.
  introv HC M1 M2. applys qimpl_wp_of_triple. simpl. intros Q.
  tests C1: (trm_is_val t1).
  { destruct C1 as (v&Et). subst. simpl.
    apply triple_of_wp. applys M2. }
  tests C2: (trm_is_var t1).
  { destruct C2 as (x&Et). subst. simpl. case_eq (Ctx.lookup x E).
    { intros v Ev. rewrites~ (>> isubst_evalctx_trm_var Ev).
      apply triple_of_wp. applys M2. }
    { introv N. remove_mkstruct. xtpull. intros; false. } }
  asserts_rewrite (wpaux_getval wpgen E t1 F2of = wpgen_let (wpgen E t1) F2of).
  { destruct t1; auto. { false C1. hnfs*. } { false C2. hnfs*. } }
  remove_mkstruct. applys~ triple_isubst_evalctx.
  { apply triple_of_wp. applys M1. }
  { intros v. apply triple_of_wp. applys M2. }
Qed.

Lemma wpgen_sound_var : forall x,
  wpgen_sound (trm_var x).
Proof using.
  intros. intros E. applys qimpl_wp_of_triple. simpl.
  intros Q. unfold wpaux_var. destruct (Ctx.lookup x E).
  { remove_mkstruct. apply~ triple_val. }
  { applys~ triple_wpgen_fail. }
Qed.

Lemma wpgen_sound_val : forall v,
  wpgen_sound (trm_val v).
Proof using.
  intros. intros E. applys qimpl_wp_of_triple. simpl.
  intros Q. remove_mkstruct. applys~ triple_val.
Qed.

Lemma wpgen_sound_fixs : forall f xs t,
  wpgen_sound (trm_fixs f xs t).
Proof using.
  intros. intros E. applys qimpl_wp_of_triple. simpl. intros Q.
  destruct xs as [|x xs'].
  { applys~ triple_wpgen_fail. }
  { remove_mkstruct. applys~ triple_fixs. auto_false. }
Qed.

Lemma wpgen_sound_if_val : forall v0 F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpgen_if_val v0 F1 F2 ===> wpsubst E (trm_if v0 t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_of_triple. simpl. intros Q.
  remove_mkstruct. xtpull ;=> b ->. applys triple_if.
  apply triple_of_wp. case_if*.
Qed.

Lemma wpgen_sound_if_trm : forall F1 F2 F3 E t1 t2 t3,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  F3 ===> wpsubst E t3 ->
  wpgen_if F1 F2 F3 ===> wpsubst E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. applys qimpl_wp_of_triple. intros Q.
  simpl. unfold wpgen_if. remove_mkstruct. applys triple_if_trm.
  { apply triple_of_wp. applys M1. }
  { intros v. apply triple_of_wp. applys* wpgen_sound_if_val. }
Qed.

Lemma wpgen_sound_if : forall t1 t2 t3,
  wpgen_sound t1 ->
  wpgen_sound t2 ->
  wpgen_sound t3 ->
  wpgen_sound (trm_if t1 t2 t3).
Proof using.
  intros. intros E. simpl.
  applys~ wpgen_sound_getval (fun t1 => trm_if t1 t2 t3).
  intros v1. applys~ wpgen_sound_if_val.
Qed.

Lemma wpgen_sound_let : forall F1 F2 E x t1 t2,
  F1 ===> wpsubst E t1 ->
  (forall X, F2 X ===> wpsubst (Ctx.add x X E) t2) ->
  wpgen_let F1 F2 ===> wpsubst E (trm_let x t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_of_triple. simpl. intros Q.
  remove_mkstruct. applys triple_let.
  { apply triple_of_wp. applys* M1. }
  { intros X. simpl. apply triple_of_wp.
    rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma wpgen_sound_seq : forall F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpgen_seq F1 F2 ===> wpsubst E (trm_seq t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_of_triple. simpl. intros Q.
  remove_mkstruct. applys triple_seq.
  { apply triple_of_wp. applys* M1. }
  { intros X. simpl. apply triple_of_wp. applys* M2. }
Qed.

Lemma wpgen_sound_apps : forall t0 ts,
  wpgen_sound t0 ->
  (forall t, mem t ts -> wpgen_sound t) ->
  wpgen_sound (trm_apps t0 ts).
Proof using.
  introv IH0 IHts. intros E Q. applys~ wpgen_sound_getval (fun t1 => trm_apps t1 ts).
  fold wpgen. intros v0. clear Q.
  cuts M: (forall rvs,
    wpaux_apps wpgen E v0 rvs ts ===>
    wp (trm_apps v0 ((trms_vals (LibList.rev rvs))++(LibList.map (isubst E) ts)))).
  { unfold wpsubst. simpl. rew_list_exec. applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rew_list_exec. rew_list. apply~ mkstruct_erase_l. applys structural_wp. }
  { specializes IHts' __. { intros t' Ht'. applys* IHts. }
    unfold wpaux_apps. fold (wpaux_apps wpgen E v0). rew_listx.
    forwards~ M: wpgen_sound_getval E (fun t1 => trm_apps v0 (trms_vals (rev rvs) ++ t1 :: ts')).
    2:{ unfold wpsubst in M. rewrite isubst_trm_apps_app in M. applys M. }
    intros v1. applys qimpl_wp_of_triple. intros Q.
    rewrite isubst_trm_apps_args. simpl. apply triple_of_wp.
    forwards M: IHts' (v1::rvs). rewrite app_trms_vals_rev_cons in M. applys M. }
Qed.

Lemma wpgen_sound_while : forall F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpgen_while F1 F2 ===> wpsubst E (trm_while t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wp_of_triple. simpl. intros Q.
  remove_mkstruct.
  set (R := wp (trm_while (isubst E t1) (isubst E t2))).
  applys triple_hforall R. simpl. applys triple_hwand_hpure_l.
  { split.
    { applys structural_wp. }
    { clears Q. applys qimpl_wp_of_triple. intros Q.
      applys triple_while_raw. apply~ triple_of_wp.
      applys* wpgen_sound_if_trm t1 (trm_seq t2 (trm_while t1 t2)) val_unit.
      { applys* wpgen_sound_seq. }
      { intros Q'. applys wpgen_sound_val. } } }
  { apply~ triple_of_wp. }
Qed.

Lemma wpgen_sound_for_val : forall (x:var) v1 v2 F1 E t1,
  (forall X, F1 X ===> wpsubst (Ctx.add x X E) t1) ->
  wpgen_for_val v1 v2 F1 ===> wpsubst E (trm_for x v1 v2 t1).
Proof using. Opaque Ctx.add Ctx.rem. (* TODO: opaque elsewhere *)
  introv M. applys qimpl_wp_of_triple. simpl. intros Q.
  remove_mkstruct. xtpull ;=> n1 n2 (->&->).
  set (S := fun (i:int) => wp (isubst E (trm_for x i n2 t1))).
  applys triple_hforall S. simpl. applys triple_hwand_hpure_l.
  { split.
    { intros r. applys structural_wp. }
    { clears Q. intros i. applys qimpl_wp_of_triple. intros Q.
      applys triple_for_raw. fold isubst.
      apply~ triple_of_wp. case_if.
      { rewrite <- isubst_add_eq_subst1_isubst.
        lets G: wpgen_sound_seq (Ctx.add x (val_int i) E) t1 (trm_for x (i + 1)%I n2 t1) .
        unfold wpsubst in G. simpl in G. rewrite Ctx.rem_anon, Ctx.rem_add_same in G.
        applys (rm G). { applys* M. } { unfolds* S. } }
      { applys wpgen_sound_val E. } } }
  { apply~ triple_of_wp. }
Qed.

Lemma wpgen_sound_for_trm : forall x t1 t2 t3,
  wpgen_sound t1 ->
  wpgen_sound t2 ->
  wpgen_sound t3 ->
  wpgen_sound (trm_for x t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros E Q. simpl.
  applys~ wpgen_sound_getval (fun t1 => trm_for x t1 t2 t3).
  intros v1. applys~ wpgen_sound_getval (fun t2 => trm_for x v1 t2 t3).
  intros v2. applys~ wpgen_sound_for_val.
Qed.

Lemma wpgen_sound_match : forall t0 pts,
  wpgen_sound t0 ->
  (forall p t, mem (p,t) pts -> wpgen_sound t) ->
  wpgen_sound (trm_match t0 pts).
Proof using.
  introv M1 M2. intros E Q. simpl.
  applys~ wpgen_sound_getval (fun t1 => trm_match t1 pts).
  intros v. clears t0 Q.
  induction pts as [|(p,t) pts'].
  { simpl. intros Q. applys himpl_wpgen_fail_l. }
  { simpl. applys qimpl_wp_of_triple. intros Q. remove_mkstruct.
    simpl. applys triple_match.
    { intros G EG Hp. applys triple_hand_l.
      forwards~ IH: M2 p t. clears IHpts' M2. subst v.
      rewrite <- EG. rewrite <- isubst_app_eq_isubst_isubst_rem_vars.
      sets_eq xs: (Ctx.dom G). forwards~ W: hforall_vars_intro G xs.
      applys~ triple_conseq Q W. simpl.
      applys~ triple_hwand_hpure_l.
      applys triple_of_wp. applys IH. }
    { intros Hp. applys triple_hand_r. applys triple_hwand_hpure_l.
      { applys~ forall_vars_intro. }
      applys triple_of_wp. applys IHpts'. { introv M. applys* M2. } } }
Qed.

Lemma wpgen_sound_constr : forall E id ts,
  (forall t, mem t ts -> wpgen_sound t) ->
  wpgen_constr wpgen E id nil ts ===> wpsubst E (trm_constr id ts).
Proof using.
  introv IHwp. cuts M: (forall rvs,
         wpgen_constr wpgen E id rvs ts
    ===> wpsubst E (trm_constr id ((trms_vals (LibList.rev rvs))++ts))).
  { applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rew_list_exec. rew_list. applys qimpl_wp_of_triple.
    simpl. rew_list_exec.
    intros Q. remove_mkstruct. rewrite map_isubst_trms_vals. applys~ triple_constr. }
  { specializes IHts' __. { intros t' Ht'. applys* IHwp. }
    applys~ wpgen_sound_getval (fun t1 => trm_constr id (trms_vals (rev rvs) ++ t1 :: ts')).
    intros v1. fold (wpgen_constr wpgen E id).
    applys qimpl_wp_of_triple. intros Q. rewrite isubst_trm_constr_args.
    apply triple_of_wp.
    forwards M: IHts' (v1::rvs). xchange M. rewrite app_trms_vals_rev_cons.
    unfold wpsubst. rewrite* isubst_trm_constr_args. }
Qed.

(** Putting it all together *)

Lemma wpgen_sound_trm : forall t,
  wpgen_sound t.
Proof using.
  intros t. induction t using trm_induct; intros E Q.
  { applys wpgen_sound_val. }
  { applys wpgen_sound_var. }
  { applys wpgen_sound_fixs. }
  { applys* wpgen_sound_constr. }
  { applys* wpgen_sound_if. }
  { applys* wpgen_sound_let. }
  { applys* wpgen_sound_apps. }
  { applys* wpgen_sound_while. }
  { applys* wpgen_sound_for_trm. }
  { applys* wpgen_sound_match. }
  { applys wpgen_sound_fail. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corollaries of the soundness of [wpgen] *)

Lemma triple_isubst_wpgen : forall t E Q,
  triple (isubst E t) (wpgen E t Q) Q.
Proof using.
  intros. apply triple_of_wp. applys wpgen_sound_trm.
Qed.

Lemma triple_isubst_of_wpgen : forall t E H Q,
  H ==> wpgen E t Q ->
  triple (isubst E t) H Q.
Proof using. introv M. xtchanges M. applys triple_isubst_wpgen. Qed.

Lemma triple_of_wpgen_empty : forall (t:trm) H Q,
  H ==> wpgen Ctx.empty t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- (isubst_empty t). applys~ triple_isubst_of_wpgen.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** All [wpgen] are trivially [struct] by construction *)

(** This property is just a sanity check, it is not exploited
    by the CFML framework. *)

Section FmklocalWpgen.

Hint Extern 1 (structural _) => (apply structural_mkstruct).

Ltac destruct_lookup :=
  match goal with |- context [Ctx.lookup ?x ?E] => destruct~ (Ctx.lookup x E) end.

Tactic Notation "destruct_lookup" "~" :=
  destruct_lookup; auto_tilde.

Lemma structural_wpaux_getval : forall wpgen E t1 F2of,
  structural (wpgen E t1) ->
  (forall v, structural (F2of v)) ->
  structural (wpaux_getval wpgen E t1 F2of).
Proof using.
  introv M1 M2. destruct* t1. { simpl. destruct_lookup~. }
Qed.

Hint Resolve structural_wpaux_getval.

Lemma structural_wpgen : forall E t,
  structural (wpgen E t).
Proof.
  intros. induction t using trm_induct; try solve [ simpl; eauto ].
  { simpl. rename v into x. simpl. unfold wpaux_var. destruct_lookup~. }
  { simpl. destruct~ xs. }
  { simpl. rename l into ts. simpl. generalize (@nil val) as rvs.
    induction ts as [|t' ts']; intros; auto.
    { applys* structural_wpaux_getval. } }
  { simpl. applys* structural_wpaux_getval. intros v0.
    rename l into ts. simpl. generalize (@nil val) as rvs.
    induction ts as [|t' ts']; intros; auto.
    { simpl. generalize (List.rev rvs) as vs. intros.
      unfolds wpaux_apps. destruct~ v0. } }
  { simpl. applys* structural_wpaux_getval. intros v0.
    induction pts as [|(p,t') pts']; intros; auto. }
Qed.

End FmklocalWpgen.


