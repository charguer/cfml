(**

This file formalizes characteristic formulae in weakest-precondition form
for plain Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export SepBase.
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

(** [wpfinal t Q] defines the weakest-precondition for term [t]
    and postcondition [Q].

    [H ==> wpfinal t Q] is equivalent to [triple t H Q].

    [wpfinal] is defined in terms of the generic definition
    of [weakestpre], which comes from [SepFunctor], and is defined as:
    [ Definition weakestpre F Q := \exists H, H \* \[F H Q]. ]
*)

Definition wpfinal (t:trm) : formula :=
  weakestpre (triple t).

(** [wpsubst E t] is a shorthand for [wpfinal (substs E t)] *)

Definition wpsubst E t :=
  wpfinal (isubst E t).


(* ---------------------------------------------------------------------- *)
(* ** Definition of [flocal] for WP *)

(** [formula'] is a generalization of the type [formula], needed to
    anticipate for needs in [WPLifted]. *)

Definition formula' (B:Type) := (B -> hprop) -> hprop.

(** [flocal F] asserts that one is able to establish [F Q]
    by establishing [F Q'] for a [Q'] that entails [Q]. *)

Definition flocal B (F:formula' B) :=
  forall Q, (\exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ==> F Q.

(** [flocal_pred S] asserts that [flocal (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition flocal_pred B A (S:A->formula' B) :=
  forall x, flocal (S x).


(* ---------------------------------------------------------------------- *)
(* ** Rules for [flocal] *)

Section Flocal.
Variable (B : Type).
Implicit Type Q : B->hprop.
Implicit Type F : formula' B.

(** A introduction rule to establish [flocal], exposing the definition *)

Lemma flocal_intro : forall F,
  (forall Q, (\exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ==> F Q) ->
  flocal F.
Proof using. auto. Qed.

(** Introduction rule for [flocal] on [weakestpre] *)

Lemma flocal_weakestpre : forall (T:hprop->(B->hprop)->Prop),
  SepBasicSetup.is_local T ->
  flocal (weakestpre T).
Proof using.
  introv L. applys flocal_intro. intros Q. unfold weakestpre.
  hpull ;=> Q' H M. hsimpl (H \* (Q' \--* Q \*+ \GC)).
  applys* is_local_ramified_frame_hgc.
Qed.

(** An elimination rule for [flocal] *)

Lemma flocal_elim : forall F H Q,
  flocal F ->
  (H ==> \exists Q', F Q' \* (Q' \--* (Q \*+ \GC))) ->
  H ==> F Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans N. Qed.

(** An elimination rule for [flocal] without [\GC] *)

Lemma flocal_elim_nohgc : forall F H Q,
  flocal F ->
  (H ==> \exists Q', F Q' \* (Q' \--* Q)) ->
  H ==> F Q.
Proof using.
  introv L M. applys~ flocal_elim. hchanges M.
Qed.

(** Other specialized elimination rules *)

Lemma flocal_conseq : forall Q' F H Q,
  flocal F ->
  H ==> F Q ->
  Q ===> Q' ->
  H ==> F Q'.
Proof using.
  introv L M W. applys~ flocal_elim.
  hchange (rm M). hsimpl Q. hchanges W.
Qed.

Lemma flocal_hgc : forall F H Q,
  flocal F ->
  H ==> F (Q \*+ \GC) ->
  H ==> F Q.
Proof using.
  introv L M. applys~ flocal_elim.
  hchange (rm M). hsimpl (Q \*+ \GC).
Qed.

Lemma flocal_frame : forall H1 H2 F H Q,
  flocal F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x) ->
  H ==> F Q.
Proof using.
  introv L W M. applys~ flocal_elim. hchange W. hchanges M.
Qed.

Lemma flocal_frame_hgc : forall H1 H2 F H Q,
  flocal F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \-* Q x \* \GC) ->
  H ==> F Q.
Proof using.
  introv L W M. applys* flocal_hgc. applys* flocal_frame.
Qed.

End Flocal.


(* ---------------------------------------------------------------------- *)
(* ** Definition of [mkflocal] for WP *)

(** [mkflocal F] transforms a formula [F] into one that satisfies [flocal]. *)

Definition mkflocal B (F:formula' B) : formula' B :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

(** Properties *)

Section Mkflocal.
Variable (B : Type).
Implicit Type Q : B->hprop.
Implicit Type F : formula' B.

(** [mkflocal] can be erased *)

Lemma mkflocal_erase : forall F Q,
  F Q ==> mkflocal F Q.
Proof using.
  intros. unfold mkflocal. repeat hsimpl.
Qed.

(** [mkflocal] can be erased, with transitivity *)

Lemma mkflocal_erase' : forall H F Q, (* TODO: rename *)
  H ==> F Q ->
  H ==> mkflocal F Q.
Proof using.
  introv M. hchanges M. applys mkflocal_erase.
Qed.

(** [mkflocal] is idempotent, i.e. nested applications
   of [mkflocal] are redundant *)

Lemma mkflocal_mkflocal : forall F,
  mkflocal (mkflocal F) = mkflocal F.
Proof using.
  intros F. applys fun_ext_1. intros Q. applys himpl_antisym.
  { unfold mkflocal. hpull ;=> Q' Q''. hsimpl Q''. intros x. hsimpl. }
  { hchanges mkflocal_erase. }
Qed.

(** A definition whose head is [mkflocal] satisfies [flocal] *)

Lemma flocal_mkflocal : forall F,
  flocal (mkflocal F).
Proof using.
  intros. applys flocal_intro. intros Q.
  pattern mkflocal at 1. rewrite <- mkflocal_mkflocal.
  unfold mkflocal. auto.
Qed.

(** A [mkflocal] can be introduced at the head of a formula satisfying [flocal] *)

Lemma eq_mkflocal_of_flocal : forall F,
  flocal F ->
  F = mkflocal F.
Proof using.
  introv L. applys fun_ext_1 ;=> Q. applys himpl_antisym.
  { applys~ mkflocal_erase. }
  { applys~ flocal_elim. }
Qed.

(** Contradictions can be extracted from mkflocal formulae *)

Lemma mkflocal_false : forall F Q,
  (forall Q', F Q' ==> \[False]) ->
  (mkflocal F Q ==> \[False]).
Proof using.
  introv M. unfold mkflocal. hpull ;=> Q'. hchange (M Q').
Qed.

(** [mkflocal] is a covariant transformer w.r.t. predicate inclusion *)

Lemma mkflocal_weaken : forall F F',
  F ===> F' ->
  mkflocal F ===> mkflocal F'.
Proof using.
  unfold mkflocal. introv M. intros Q. hpull ;=> Q'. hsimpl~ Q'.
Qed.

(** [mkflocal] can be erased on the left of an entailment if the
    formula on the right is mkflocal. *)

Lemma mkflocal_erase_l : forall F1 F2,
  flocal F2 ->
  F1 ===> F2 ->
  mkflocal F1 ===> F2.
Proof using.
  introv LF M. rewrite~ (eq_mkflocal_of_flocal LF). applys* mkflocal_weaken.
Qed.

End Mkflocal.


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
      rewrite~ List_rev_eq. }
    { simpl. intros X. rew_ctx. applys IHxs'.
      intros G2 HG2. rewrite <- Ctx.app_rev_add. applys HG1.
      rewrite Ctx.dom_add. fequals. } }
Qed.

(** [hforall_vars Hof G (x1::x2::x3::nil)] produces the heap predicate
    [\forall X1 X2 X3, Hof ((x3,X3)::(x2,X2)::(x1,X1)::(List.rev G))) *)

Fixpoint hforall_vars (Hof:ctx->hprop) (G:ctx) (xs:vars) : hprop :=
  match xs with
  | nil => Hof (List.rev G) (* TODO: Ctx.rev *)
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
  { simpl. rewrite List_rev_eq. forwards~ G2E: (Ctx.dom_eq_nil_inv G2).
     subst. rewrite~ Ctx.app_empty_r. }
  { simpl. destruct G2 as [| (x',X) G']; tryfalse.
    simpl in EQ. invert EQ ;=> Ex EG2. subst x'.
    applys himpl_hforall_l_for X. rew_ctx.
    rewrite Ctx.app_rev_add. rewrite EG2. applys~ IHxs'. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition wpmk_fail : formula := mkflocal (fun Q =>
  \[False]).

Definition wpmk_val (v:val) : formula := mkflocal (fun Q =>
  Q v).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpmk_fail
  | Some v => wpmk_val v
  end.

Definition wpmk_let (F1:formula) (F2of:val->formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wpmk_seq (F1 F2:formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2 Q)).

Definition wpaux_getval wpmk (E:ctx) (t1:trm) (F2of:val->formula) : formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                        | Some v => F2of v
                        | None => wpmk_fail
                        end
  | _ => wpmk_let (wpmk E t1) F2of
  end.

Definition wpmk_constr wpmk (E:ctx) (id:idconstr) : list val -> list trm -> formula :=
  fix mk (rvs : list val) (ts : list trm) : formula :=
    match ts with
    | nil => wpmk_val (val_constr id (List.rev rvs))
    | t1::ts' => wpaux_getval wpmk E t1 (fun v1 => mk (v1::rvs) ts')
    end.

Definition wpmk_unop_int (v1:val) (F:int->val) : formula := mkflocal (fun Q =>
  \exists n1, \[v1 = val_int n1] \* Q (F n1)).

Definition wpmk_unop_bool (v1:val) (F:bool->val) : formula := mkflocal (fun Q =>
  \exists b1, \[v1 = val_bool b1] \* Q (F b1)).

Definition wpmk_binop_int (v1 v2:val) (F:int->int->val) : formula := mkflocal (fun Q =>
  \exists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \* Q (F n1 n2)).

(* TODO: might not be needed to treat special builtins *)

Definition wpaux_apps_val (v0:val) (vs:vals) : formula :=
  match v0, vs with
  | val_prim val_opp, (v1::nil) => wpmk_unop_int v1 (fun n1 => - n1)
  | val_prim val_neg, (v1::nil) => wpmk_unop_bool v1 (fun b1 => neg b1)
  | val_prim val_eq, (v1::v2::nil) => wpmk_val (isTrue (v1 = v2))
  | val_prim val_neq, (v1::v2::nil) => wpmk_val (isTrue (v1 <> v2))
  | val_prim val_add, (v1::v2::nil) => wpmk_binop_int v1 v2 (fun n1 n2 => n1 + n2)
  | val_prim val_sub, (v1::v2::nil) => wpmk_binop_int v1 v2 (fun n1 n2 => n1 - n2)
  | val_prim val_mul, (v1::v2::nil) => wpmk_binop_int v1 v2 (fun n1 n2 => n1 * n2)
  | _, _ => mkflocal (wpfinal (trm_apps v0 vs))
  end.  (* not included: arithmetic comparisons *)

Definition wpaux_apps wpmk (E:ctx) (v0:val) : list val -> list trm -> formula :=
  fix mk (rvs : list val) (ts : list trm) : formula :=
    match ts with
    | nil => wpaux_apps_val v0 (List.rev rvs)
    | t1::ts' => wpaux_getval wpmk E t1 (fun v1 => mk (v1::rvs) ts')
    end.

Definition wpmk_if_val (v:val) (F1 F2:formula) : formula := mkflocal (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wpmk_if (F0 F1 F2:formula) : formula :=
  wpmk_let F0 (fun v => wpmk_if_val v F1 F2).

Definition wpmk_while (F1 F2:formula) : formula := mkflocal (fun Q =>
  \forall (R:formula),
  let F := wpmk_if F1 (wpmk_seq F2 R) (wpmk_val val_unit) in
  \[ flocal R /\ F ===> R] \-* (R Q)).

Definition wpmk_for_val (v1 v2:val) (F1:val->formula) : formula := mkflocal (fun Q =>
  \exists (n1:int) (n2:int), \[v1 = val_int n1 /\ v2 = val_int n2] \*
  \forall (S:int->formula),
  let F i := If (i <= n2) then (wpmk_seq (F1 i) (S (i+1)))
                          else (wpmk_val val_unit) in
  \[ flocal_pred S /\ (forall i, F i ===> S i)] \-* (S n1 Q)).

Definition wpmk_case_val (F1:formula) (P:Prop) (F2:formula) : formula :=
  mkflocal (fun Q =>
    hand (F1 Q) (\[P] \-* F2 Q)).

Definition wpaux_match wpmk (E:ctx) (v:val) : list (pat*trm) -> formula :=
  fix mk (pts:list(pat*trm)) : formula :=
    match pts with
    | nil => wpmk_fail
    | (p,t)::pts' =>
        let xs := patvars p in
        let F1 (Q:val->hprop) :=
           hforall_vars (fun G => let E' := (Ctx.app G E) in
              \[v = patsubst G p] \-* (wpmk E' t) Q) Ctx.empty xs in
        let P := forall_vars (fun G => v <> patsubst G p) Ctx.empty xs in
        wpmk_case_val F1 P (mk pts')
    end.


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint wpmk (E:ctx) (t:trm) : formula :=
  let aux := wpmk E in
  match t with
  | trm_val v => wpmk_val v
  | trm_var x => wpaux_var E x
  | trm_fixs f xs t1 =>
      match xs with
      | nil => wpmk_fail
      | _ => wpmk_val (val_fixs f xs (isubst (Ctx.rem_vars xs (Ctx.rem f E)) t1))
      end
  | trm_constr id ts => wpmk_constr wpmk E id nil ts
  | trm_if t0 t1 t2 => wpaux_getval wpmk E t0 (fun v0 => wpmk_if_val v0 (aux t1) (aux t2))
  | trm_let x t1 t2 => wpmk_let (aux t1) (fun X => wpmk (Ctx.add x X E) t2)
  | trm_apps t0 ts => wpaux_getval wpmk E t0 (fun v0 => wpaux_apps wpmk E v0 nil ts)
  | trm_while t1 t2 => wpmk_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 =>
      wpaux_getval wpmk E t1 (fun v1 =>
        wpaux_getval wpmk E t2 (fun v2 =>
          wpmk_for_val v1 v2 (fun X => wpmk (Ctx.add x X E) t3)))
  | trm_match t0 pts =>
      wpaux_getval wpmk E t0 (fun v0 =>
        wpaux_match wpmk E v0 pts)
  | trm_fail => wpmk_fail
  end.

(* Note: for simplicity, no special handling here of trm_seq, unlike in WPLifted. *)


(* ********************************************************************** *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [wpfinal t] is a mkflocal formula *)

Lemma flocal_wpfinal : forall t,
  flocal (wpfinal t).
Proof using. intros. applys~ flocal_weakestpre. Qed.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma triple_eq_himpl_wpfinal : forall H Q t,
  triple t H Q = (H ==> wpfinal t Q).
Proof using. intros. applys~ weakestpre_eq. Qed.

(** Reformulation of the right-to-left implication above as an implication. *)

Lemma triple_of_wp : forall H Q t,
  H ==> wpfinal t Q ->
  triple t H Q.
Proof using. intros. rewrite* triple_eq_himpl_wpfinal. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_wpfinal : forall t F,
  (forall Q, triple t (F Q) Q) ->
  F ===> wpfinal t.
Proof using. introv M. intros Q. rewrite~ <- triple_eq_himpl_wpfinal. Qed.

(** Another corrolary of [triple_eq_himpl_wpfinal],
    (not used in the proofs below). *)

Lemma triple_wpfinal : forall t Q,
  triple t (wpfinal t Q) Q.
Proof using. intros. applys~ weakestpre_pre. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [mkflocal] transformer *)

(** The [mkflocal] transformer is sound w.r.t. [triple] *)

Lemma triple_mkflocal_pre : forall t (F:formula) Q,
  (forall Q, triple t (F Q) Q) ->
  triple t (mkflocal F Q) Q.
Proof using.
  introv M. applys~ is_local_elim.
  unfold mkflocal. hpull ;=> Q'.
  hsimpl (F Q') ((Q' \--* Q \*+ \GC)) Q'. split~.
  { hsimpl. }
Qed.

(** The tactic [remove_mkflocal] applies to goal of the form [triple t (mkflocal F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_mkflocal :=
  match goal with |- triple _ _ ?Q =>
    applys triple_mkflocal_pre; try (clear Q; intros Q); xpull; fold wpmk end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wpmk] *)

(** [wpmk_sound t] asserts that [wpmk] is sound for all contexts [E],
    in the sense that the syntactic wpmk entails the semantics wp:
[[
    forall Q,  wpmk E t Q ==> wpsubst E t Q
]] *)

Definition wpmk_sound t := forall E,
  wpmk E t ===> wpsubst E t.

(** Lemma for [wpmk_fail] *)

Lemma himpl_wpmk_fail_l : forall Q H,
  wpmk_fail Q ==> H.
Proof using. intros. unfold wpmk_fail, mkflocal. hpull. Qed.

Lemma qimpl_wpmk_fail_l : forall F,
  wpmk_fail ===> F.
Proof using. intros. intros Q. applys himpl_wpmk_fail_l. Qed.

Lemma triple_wpmk_fail : forall t Q Q',
  triple t (wpmk_fail Q) Q'.
Proof using.
  intros. apply triple_of_wp. applys himpl_wpmk_fail_l.
Qed.

(** Soundness of the [wpmk] for the various constructs *)

Lemma wpmk_sound_getval : forall E C t1 F2of,
  evalctx C ->
  wpmk_sound t1 ->
  (forall v, F2of v ===> wpsubst E (C (trm_val v))) ->
  wpaux_getval wpmk E t1 F2of ===> wpsubst E (C t1).
Proof using.
  introv HC M1 M2. applys qimpl_wpfinal. simpl. intros Q.
  tests C1: (trm_is_val t1).
  { destruct C1 as (v&Et). subst. simpl.
    apply triple_of_wp. applys M2. }
  tests C2: (trm_is_var t1).
  { destruct C2 as (x&Et). subst. simpl. case_eq (Ctx.lookup x E).
    { intros v Ev. rewrites~ (>> isubst_evalctx_trm_var Ev).
      apply triple_of_wp. applys M2. }
    { introv N. remove_mkflocal. intros; false. } }
  asserts_rewrite (wpaux_getval wpmk E t1 F2of = wpmk_let (wpmk E t1) F2of).
  { destruct t1; auto. { false C1. hnfs*. } { false C2. hnfs*. } }
  remove_mkflocal. applys~ triple_isubst_evalctx.
  { apply triple_of_wp. applys M1. }
  { intros v. apply triple_of_wp. applys M2. }
Qed.

Lemma wpmk_sound_fail :
  wpmk_sound trm_fail.
Proof using. intros. intros E Q. applys himpl_wpmk_fail_l. Qed.

Lemma wpmk_sound_var : forall x,
  wpmk_sound (trm_var x).
Proof using.
  intros. intros E. applys qimpl_wpfinal. simpl.
  intros Q. unfold wpaux_var. destruct (Ctx.lookup x E).
  { remove_mkflocal. apply~ triple_val. }
  { applys~ triple_wpmk_fail. }
Qed.

Lemma wpmk_sound_val : forall v,
  wpmk_sound (trm_val v).
Proof using.
  intros. intros E. applys qimpl_wpfinal. simpl.
  intros Q. remove_mkflocal. applys~ triple_val.
Qed.

Lemma wpmk_sound_fixs : forall f xs t,
  wpmk_sound (trm_fixs f xs t).
Proof using.
  intros. intros E. applys qimpl_wpfinal. simpl. intros Q.
  destruct xs as [|x xs'].
  { applys~ triple_wpmk_fail. }
  { remove_mkflocal. applys~ triple_fixs. auto_false. }
Qed.

Lemma wpmk_sound_if_val : forall v0 F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpmk_if_val v0 F1 F2 ===> wpsubst E (trm_if v0 t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wpfinal. simpl. intros Q.
  remove_mkflocal. intros b ->. applys triple_if_bool.
  apply triple_of_wp. case_if*.
Qed.

Lemma wpmk_sound_if_trm : forall F1 F2 F3 E t1 t2 t3,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  F3 ===> wpsubst E t3 ->
  wpmk_if F1 F2 F3 ===> wpsubst E (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. applys qimpl_wpfinal. intros Q.
  simpl. unfold wpmk_if. remove_mkflocal. applys triple_if_trm.
  { apply triple_of_wp. applys M1. }
  { intros v. apply triple_of_wp. applys* wpmk_sound_if_val. }
Qed.

Lemma wpmk_sound_if : forall t1 t2 t3,
  wpmk_sound t1 ->
  wpmk_sound t2 ->
  wpmk_sound t3 ->
  wpmk_sound (trm_if t1 t2 t3).
Proof using.
  intros. intros E. simpl.
  applys~ wpmk_sound_getval (fun t1 => trm_if t1 t2 t3).
  intros v1. applys~ wpmk_sound_if_val.
Qed.

Lemma wpmk_sound_let : forall F1 F2 E x t1 t2,
  F1 ===> wpsubst E t1 ->
  (forall X, F2 X ===> wpsubst (Ctx.add x X E) t2) ->
  wpmk_let F1 F2 ===> wpsubst E (trm_let x t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wpfinal. simpl. intros Q.
  remove_mkflocal. applys triple_let.
  { apply triple_of_wp. applys* M1. }
  { intros X. simpl. apply triple_of_wp.
    rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma wpmk_sound_seq : forall F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpmk_seq F1 F2 ===> wpsubst E (trm_seq t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wpfinal. simpl. intros Q.
  remove_mkflocal. applys triple_seq.
  { apply triple_of_wp. applys* M1. }
  { intros X. simpl. apply triple_of_wp. applys* M2. }
Qed.

Lemma wpmk_sound_redbinop : forall v op v1 v2,
  redbinop op v1 v2 v ->
  wpmk_val v ===> wpfinal (trm_apps op (trms_vals (v1::v2::nil))).
Proof using.
  introv M. applys qimpl_wpfinal; intros Q; simpl.
  remove_mkflocal. applys~ is_local_conseq_frame.
  { applys triple_binop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wpmk_sound_redunop_int : forall (F:int->val) op v1,
  (forall (n1:int), redunop op n1 (F n1)) ->
  wpmk_unop_int v1 F ===> wpfinal (trm_apps op (trms_vals (v1::nil))).
Proof using.
  introv M. applys qimpl_wpfinal; intros Q; simpl.
  remove_mkflocal. intros n1 ->. applys~ is_local_conseq_frame.
  { applys triple_unop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wpmk_sound_redunop_bool : forall (F:bool->val) op v1,
  (forall (b1:bool), redunop op b1 (F b1)) ->
  wpmk_unop_bool v1 F ===> wpfinal (trm_apps op (trms_vals (v1::nil))).
Proof using.
  introv M. applys qimpl_wpfinal; intros Q; simpl.
  remove_mkflocal. intros n1 ->. applys~ is_local_conseq_frame.
  { applys triple_unop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wpmk_sound_redbinop_int : forall (F:int->int->val) op v1 v2,
  (forall (n1 n2:int), redbinop op n1 n2 (F n1 n2)) ->
  wpmk_binop_int v1 v2 F ===> wpfinal (trm_apps op (trms_vals (v1::v2::nil))).
Proof using.
  introv M. applys qimpl_wpfinal; intros Q; simpl.
  remove_mkflocal. intros n1 n2 (->&->). applys~ is_local_conseq_frame.
  { applys triple_binop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wpmk_sound_apps_val : forall v0 vs,
  wpaux_apps_val v0 vs ===> wpfinal (trm_apps v0 vs).
Proof using.
  Hint Constructors redunop redbinop.
  intros.
  asserts Common: (mkflocal (wpfinal (trm_apps v0 vs)) ===> wpfinal (trm_apps v0 vs)).
  { apply~ mkflocal_erase_l. { applys flocal_wpfinal. } }
  intros Q. destruct v0; try solve [ apply Common ].
  rename p into p. destruct p; try solve [ apply Common ];
   destruct vs as [|v1 [|v2 [|]]]; try solve [ apply Common ].
  { applys* wpmk_sound_redunop_bool. }
  { applys* wpmk_sound_redunop_int. }
  { applys* wpmk_sound_redbinop. }
  { applys* wpmk_sound_redbinop. eauto. }
  { applys* wpmk_sound_redbinop_int. }
  { applys* wpmk_sound_redbinop_int. }
  { applys* wpmk_sound_redbinop_int. }
Qed.

Lemma wpmk_sound_apps : forall t0 ts,
  wpmk_sound t0 ->
  (forall t, mem t ts -> wpmk_sound t) ->
  wpmk_sound (trm_apps t0 ts).
Proof using.
  introv IH0 IHts. intros E Q. applys~ wpmk_sound_getval (fun t1 => trm_apps t1 ts).
  fold wpmk. intros v0. clear Q.
  cuts M: (forall rvs,
    wpaux_apps wpmk E v0 rvs ts ===>
    wpfinal (trm_apps v0 ((trms_vals (LibList.rev rvs))++(LibList.map (isubst E) ts)))).
  { unfold wpsubst. simpl. rewrite List_map_eq. applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rewrite List_rev_eq. rew_list. applys wpmk_sound_apps_val. }
  { specializes IHts' __. { intros t' Ht'. applys* IHts. }
    unfold wpaux_apps. fold (wpaux_apps wpmk E v0). rew_listx.
    forwards~ M: wpmk_sound_getval E (fun t1 => trm_apps v0 (trms_vals (rev rvs) ++ t1 :: ts')).
    2:{ unfold wpsubst in M. rewrite isubst_trm_apps_app in M. applys M. }
    intros v1. applys qimpl_wpfinal. intros Q.
    rewrite isubst_trm_apps_args. simpl. apply triple_of_wp.
    forwards M: IHts' (v1::rvs). rewrite app_trms_vals_rev_cons in M. applys M. }
Qed.

Lemma wpmk_sound_while : forall F1 F2 E t1 t2,
  F1 ===> wpsubst E t1 ->
  F2 ===> wpsubst E t2 ->
  wpmk_while F1 F2 ===> wpsubst E (trm_while t1 t2).
Proof using.
  introv M1 M2. applys qimpl_wpfinal. simpl. intros Q.
  remove_mkflocal.
  set (R := wpfinal (trm_while (isubst E t1) (isubst E t2))).
  applys triple_hforall R. simpl. applys triple_hwand_hpure_l.
  { split.
    { applys flocal_wpfinal. }
    { clears Q. applys qimpl_wpfinal. intros Q.
      applys triple_while_raw. apply~ triple_of_wp.
      applys* wpmk_sound_if_trm t1 (trm_seq t2 (trm_while t1 t2)) val_unit.
      { applys* wpmk_sound_seq. eauto. }
      { intros Q'. applys wpmk_sound_val. } } }
  { apply~ triple_of_wp. }
Qed.

Lemma wpmk_sound_for_val : forall (x:var) v1 v2 F1 E t1,
  (forall X, F1 X ===> wpsubst (Ctx.add x X E) t1) ->
  wpmk_for_val v1 v2 F1 ===> wpsubst E (trm_for x v1 v2 t1).
Proof using. Opaque Ctx.add Ctx.rem.
  introv M. applys qimpl_wpfinal. simpl. intros Q.
  remove_mkflocal. intros n1 n2 (->&->).
  set (S := fun (i:int) => wpfinal (isubst E (trm_for x i n2 t1))).
  applys triple_hforall S. simpl. applys triple_hwand_hpure_l.
  { split.
    { intros r. applys flocal_wpfinal. }
    { clears Q. intros i. applys qimpl_wpfinal. intros Q.
      applys triple_for_raw. fold isubst.
      apply~ triple_of_wp. case_if.
      { rewrite <- isubst_add_eq_subst1_isubst.
        lets G: wpmk_sound_seq (Ctx.add x (val_int i) E) t1 (trm_for x (i + 1)%I n2 t1) .
        unfold wpsubst in G. simpl in G. rewrite Ctx.rem_anon, Ctx.rem_add_same in G.
        applys (rm G). { applys* M. } { unfolds* S. } }
      { applys wpmk_sound_val E. } } }
  { apply~ triple_of_wp. }
Qed.

Lemma wpmk_sound_for_trm : forall x t1 t2 t3,
  wpmk_sound t1 ->
  wpmk_sound t2 ->
  wpmk_sound t3 ->
  wpmk_sound (trm_for x t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros E Q. simpl.
  applys~ wpmk_sound_getval (fun t1 => trm_for x t1 t2 t3).
  intros v1. applys~ wpmk_sound_getval (fun t2 => trm_for x v1 t2 t3).
  intros v2. applys~ wpmk_sound_for_val.
Qed.

Lemma wpmk_sound_match : forall t0 pts,
  wpmk_sound t0 ->
  (forall p t, mem (p,t) pts -> wpmk_sound t) ->
  wpmk_sound (trm_match t0 pts).
Proof using.
  introv M1 M2. intros E Q. simpl.
  applys~ wpmk_sound_getval (fun t1 => trm_match t1 pts).
  intros v. clears t0 Q.
  induction pts as [|(p,t) pts'].
  { simpl. intros Q. applys himpl_wpmk_fail_l. }
  { simpl. applys qimpl_wpfinal. intros Q. remove_mkflocal.
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

Lemma wpmk_sound_constr : forall E id ts,
  (forall t, mem t ts -> wpmk_sound t) ->
  wpmk_constr wpmk E id nil ts ===> wpsubst E (trm_constr id ts).
Proof using.
  introv IHwp. cuts M: (forall rvs,
         wpmk_constr wpmk E id rvs ts
    ===> wpsubst E (trm_constr id ((trms_vals (LibList.rev rvs))++ts))).
  { applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rewrite List_rev_eq. rew_list. applys qimpl_wpfinal.
    simpl. rewrite List_map_eq.
    intros Q. remove_mkflocal. rewrite map_isubst_trms_vals. applys~ triple_constr. }
  { specializes IHts' __. { intros t' Ht'. applys* IHwp. }
    applys~ wpmk_sound_getval (fun t1 => trm_constr id (trms_vals (rev rvs) ++ t1 :: ts')).
    intros v1. fold (wpmk_constr wpmk E id).
    applys qimpl_wpfinal. intros Q. rewrite isubst_trm_constr_args.
    apply triple_of_wp.
    forwards M: IHts' (v1::rvs). unfold trms_vals in *. rew_listx~ in M.
    unfold wpsubst in M. rewrite isubst_trm_constr_args in M. apply M. }
Qed.

Lemma wpmk_sound_trm : forall t,
  wpmk_sound t.
Proof using.
  intros t. induction t using trm_induct; intros E Q.
  { applys wpmk_sound_val. }
  { applys wpmk_sound_var. }
  { applys wpmk_sound_fixs. }
  { applys* wpmk_sound_constr. }
  { applys* wpmk_sound_if. }
  { applys* wpmk_sound_let. }
  { applys* wpmk_sound_apps. }
  { applys* wpmk_sound_while. }
  { applys* wpmk_sound_for_trm. }
  { applys* wpmk_sound_match. }
  { applys wpmk_sound_fail. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corrolaries of the soundness of [wpmk] *)

Lemma triple_isubst_wp : forall t E Q,
  triple (isubst E t) (wpmk E t Q) Q.
Proof using.
  intros. apply triple_of_wp. applys wpmk_sound_trm.
Qed.

Lemma triple_isubst_of_wp : forall t E H Q,
  H ==> wpmk E t Q ->
  triple (isubst E t) H Q.
Proof using. introv M. xchanges M. applys triple_isubst_wp. Qed.

Lemma triple_of_wpmk_empty : forall (t:trm) H Q,
  H ==> wpmk Ctx.empty t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- (isubst_empty t). applys~ triple_isubst_of_wp.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** All [wpmk] are trivially [flocal] by construction *)

Section IsLocalWp.

Hint Extern 1 (flocal _) => (apply flocal_mkflocal).

Ltac destruct_lookup :=
  match goal with |- context [Ctx.lookup ?x ?E] => destruct~ (Ctx.lookup x E) end.

Tactic Notation "destruct_lookup" "~" :=
  destruct_lookup; auto_tilde.

Lemma flocal_wpaux_getval : forall wpmk E t1 F2of,
  flocal (wpmk E t1) ->
  (forall v, flocal (F2of v)) ->
  flocal (wpaux_getval wpmk E t1 F2of).
Proof using.
  introv M1 M2. destruct* t1. { simpl. destruct_lookup~. }
Qed.

Hint Resolve flocal_wpaux_getval.

Lemma flocal_wp : forall E t,
  flocal (wpmk E t).
Proof.
  intros. induction t using trm_induct; try solve [ simpl; eauto ].
  { simpl. rename v into x. simpl. unfold wpaux_var. destruct_lookup~. }
  { simpl. destruct~ xs. }
  { simpl. rename l into ts. simpl. generalize (@nil val) as rvs.
    induction ts as [|t' ts']; intros; auto.
    { applys* flocal_wpaux_getval. } }
  { simpl. applys* flocal_wpaux_getval. intros v0.
    rename l into ts. simpl. generalize (@nil val) as rvs.
    induction ts as [|t' ts']; intros; auto.
    { simpl. generalize (List.rev rvs) as vs. intros.
      unfolds wpaux_apps. destruct~ v0.
      destruct~ p; destruct vs as [|v1 [|v2 [ | ]]]; auto. }
    { applys* flocal_wpaux_getval. } }
  { simpl. applys* flocal_wpaux_getval. intros v0.
    induction pts as [|(p,t') pts']; intros; auto. }
Qed.

End IsLocalWp.










==========
(* DEPRECATED
Definition Wpgen_unop_int (v1:val) (F:int->int) : Formula :=
  Local (Formula_typed (fun (Q:int->hprop) =>
    \exists n1, \[v1 = val_int n1] \* Q (F n1))).

Definition Wpgen_unop_bool (v1:val) (F:bool->bool) : Formula :=
  Local (Formula_typed (fun (Q:bool->hprop) =>
    \exists b1, \[v1 = val_bool b1] \* Q (F b1))).

Definition Wpgen_binop_int (v1 v2:val) (F:int->int->int) : Formula :=
  Local (Formula_typed (fun (Q:int->hprop) =>
    \exists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \* Q (F n1 n2))).
*)

(* TODO
  | val_prim val_opp, (v1::nil) => Wpgen_unop_int v1 (fun n1 => - n1)
  | val_prim val_neg, (v1::nil) => Wpgen_unop_bool v1 (fun b1 => neg b1)
  | val_prim val_eq, (v1::v2::nil) => Wpgen_unlifted_val (isTrue (v1 = v2))
  | val_prim val_neq, (v1::v2::nil) => Wpgen_unlifted_val (isTrue (v1 <> v2))
  | val_prim val_add, (v1::v2::nil) => Wpgen_binop_int v1 v2 (fun n1 n2 => n1 + n2)
  | val_prim val_sub, (v1::v2::nil) => Wpgen_binop_int v1 v2 (fun n1 n2 => n1 - n2)
  | val_prim val_mul, (v1::v2::nil) => Wpgen_binop_int v1 v2 (fun n1 n2 => n1 * n2)
*)
(* not included: arithmetic comparisons *)


(* DEPRECATED
Definition Wpgen_getval' Wpgen (E:ctx) (t1:trm) (F2of:forall A1 {EA1:Enc A1},A1->Formula) : Formula :=
  match t1 with
  | trm_val v => Wpgen_letval v F2of
  | trm_var x => match Ctx.lookup x E with
                        | Some v => Wpgen_letval v F2of
                        | None => Wpgen_fail
                        end
  | _ => Wpgen_let (Wpgen E t1) F2of
  end.
*)

(* NEEDED?
Definition Wpgen_getval_val Wpgen (E:ctx) (t1:trm) (F2of:val->Formula) : Formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                        | Some v => F2of v
                        | None => Wpgen_fail
                        end
  | _ => Wpgen_let_trm (Wpgen E t1) F2of
  end.
*)

(** DEPRECATED
    [Wpgen_var] prevents [simpl] from simplifying context lookups, hence we
    inline its definition at the place of use, using a notation.

Notation "'Wpgen_var'' E x" :=
  (match Ctx.lookup x E with
  | None => Wpgen_fail
  | Some v => Wpgen_unlifted_val v
  end) (at level 37, E at level 0, x at level 0).
*)



Definition Wpaux_apps_or_prim Wpgen (E:ctx) (t0:trm) (ts:list trm) : Formula :=
  match t0, ts with
  | trm_val (val_prim val_add), (t1::t2::nil) =>
     Wpaux_getval_int Wpgen E t1 (fun n1 =>
       Wpaux_getval_int Wpgen E t2 (fun n2 =>
         `Formula_cast (fun (Q:int->hprop) => Q (n1 + n2))))
  | _,_ => Wpaux_getval_val Wpgen E t0 (fun v0 => Wpaux_apps Wpgen E v0 nil ts)
  end.


Definition Wpaux_getval_int Wpgen (E:ctx) (t1:trm) (F2of:int->Formula) : Formula :=
  match t1 with
  | trm_val (val_int n) => F2of n
  | _ => Wpaux_getval_typed Wpgen E t1 F2of
  end.

Definition wpgen_unop_int (v1:val) (F:int->val) : formula := mkflocal (fun Q =>
  \exists n1, \[v1 = val_int n1] \* Q (F n1)).

Definition wpgen_unop_bool (v1:val) (F:bool->val) : formula := mkflocal (fun Q =>
  \exists b1, \[v1 = val_bool b1] \* Q (F b1)).

Definition wpgen_binop_int (v1 v2:val) (F:int->int->val) : formula := mkflocal (fun Q =>
  \exists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \* Q (F n1 n2)).
