(**

This file formalizes characteristic formulae in weakest-precondition form
for lifted Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export WPBase SepLifted.
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
   format "^ F  Q") : wp_scope.

Open Scope wp_scope.
Delimit Scope wp_scope with wp.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** Lifted version of [weakestpre] *)

Definition Weakestpre (T:forall `{Enc A},hprop->(A->hprop)->Prop) : Formula :=
  fun A (EA:Enc A) => weakestpre T.

(** Lifted version of [wp_triple] *)

Definition Wp_Triple (t:trm) : Formula :=
  Weakestpre (@Triple t).


(* ---------------------------------------------------------------------- *)
(* ** Constraining the return type *)

(** Constructor to force the return type of a Formula *)

Definition Formula_typed `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    \exists (Q':A1->hprop), F Q' \* \[PostChange Q' Q].

(** [Wp_cast X Q] applies a postcondition [Q] of type [A2->hprop] to a value
    [X] of type [A1], with [X] converted on-the-fly to a value of type [A2]. *)

Definition Wp_cast `{Enc A1} (X:A1) A2 (EA2:Enc A2) (Q:A2->hprop) : hprop :=
  \exists (Y:A2), \[enc X = enc Y] \* Q Y.


(* ---------------------------------------------------------------------- *)
(* ** Definition of [Local] for WP *)

(** The [Local] predicate lifts [local]. *)

Definition Local (F:Formula) : Formula :=
  fun A `{EA:Enc A} Q => flocal (@F A EA) Q.

Lemma flocal_Local_eq : forall A `{EA:Enc A} (F:Formula),
  flocal (@Local F A EA) = (@Local F A EA).
Proof using.
  intros. apply fun_ext_1. intros Q.
  unfold Local. rewrite flocal_flocal. split~.
Qed.

Lemma is_flocal_Local : forall A `{EA:Enc A} (F:Formula),
  is_flocal (@Local F A EA).
Admitted. (* Proof using. intros. applys is_flocal_intro. rewrite~ @flocal_Local_eq. Qed. *)

Hint Resolve is_flocal_Local.


(* ---------------------------------------------------------------------- *)
(* ** Tag for improved pretty-printing of CF *)

Definition is_Wp (F:Formula) : Formula := F.

Notation "'`' F" :=
  ((is_Wp F%wp))
  (at level 69, F at level 100, format "'`' F") : wp_scope.


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

(* DEPRECATED
Definition Wp_val_typed `{EA1:Enc A1} (V:A1) : Formula :=
  Local (fun A (EA:Enc A) Q => Q V1).
*)

Definition WP_var (E:ctx) (x:var) : Formula :=
  match Ctx.lookup x E with
  | None => `Wp_fail
  | Some v => `Wp_val v
  end.

(** DEPRECATED
    [Wp_var] prevents [simpl] from simplifying context lookups, hence we
    inline its definition at the place of use, using a notation. 

Notation "'Wp_var'' E x" :=
  (match Ctx.lookup x E with
  | None => Wp_fail
  | Some v => Wp_val v
  end) (at level 37, E at level 0, x at level 0).
*)

Definition Wp_let (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1),
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_let_typed `{EA1:Enc A1} (F1:Formula) (F2of:A1->Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wp_seq (F1 F2:Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wp_letval (v:val) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1) (V:A1), \[v = enc V] \* ^(F2of V) Q).

Definition Wp_letval_typed `{EA1:Enc A1} (v:val) (F2of:A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (V:A1), \[v = enc V] \* ^(F2of V) Q).

(* DEPRECATED
Definition Wp_getval' Wp (E:ctx) (t1:trm) (F2of:forall A1 {EA1:Enc A1},A1->Formula) : Formula :=
  match t1 with
  | trm_val v => Wp_letval v F2of
  | trm_var x => match Ctx.lookup x E with
                        | Some v => Wp_letval v F2of
                        | None => Wp_fail
                        end
  | _ => Wp_let (Wp E t1) F2of
  end.
*)

Definition WP_getval_typed Wp (E:ctx) `{EA1:Enc A1} (t1:trm) (F2of:A1->Formula) : Formula :=
  match t1 with
  | trm_val v => `Wp_letval_typed v F2of
  | trm_var x => match Ctx.lookup x E with
                        | Some v => `Wp_letval_typed v F2of
                        | None => `Wp_fail
                        end
  | _ => `Wp_let_typed (Wp E t1) F2of
  end.

(* NEEDED?
Definition Wp_getval_val Wp (E:ctx) (t1:trm) (F2of:val->Formula) : Formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                        | Some v => F2of v
                        | None => Wp_fail
                        end
  | _ => Wp_let_typed (Wp E t1) F2of
  end.
*)
Definition WP_getval Wp (E:ctx) (t1:trm) (F2of:val->Formula) : Formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                        | Some v => F2of v
                        | None => `Wp_fail
                        end
  | _ => `Wp_let (Wp E t1) (fun `{EA1:Enc A1} (V1:A1) => F2of (``V1))
  end.

Definition WP_getval_val := WP_getval.

Definition WP_getval_int Wp (E:ctx) (t1:trm) (F2of:int->Formula) : Formula :=
  match t1 with
  | trm_val (val_int n) => F2of n
  | _ => WP_getval_typed Wp E t1 F2of
  end.

Definition WP_constr Wp (E:ctx) (id:idconstr) : list val -> list trm -> Formula := 
  fix mk (rvs : list val) (ts : list trm) : Formula :=
    match ts with
    | nil => `Wp_val (val_constr id (List.rev rvs))
    | t1::ts' => WP_getval Wp E t1 (fun v1 => mk (v1::rvs) ts')
    (* DEPRECATED Wp_getval_val wp E t1 (fun v1 => mk (v1::rvs) ts') *)
    end.

(* DEPRECATED
Definition Wp_unop_int (v1:val) (F:int->int) : Formula := 
  Local (Formula_typed (fun (Q:int->hprop) =>
    \exists n1, \[v1 = val_int n1] \* Q (F n1))).

Definition Wp_unop_bool (v1:val) (F:bool->bool) : Formula := 
  Local (Formula_typed (fun (Q:bool->hprop) =>
    \exists b1, \[v1 = val_bool b1] \* Q (F b1))).

Definition Wp_binop_int (v1 v2:val) (F:int->int->int) : Formula :=
  Local (Formula_typed (fun (Q:int->hprop) =>
    \exists n1 n2, \[v1 = val_int n1 /\ v2 = val_int n2] \* Q (F n1 n2))).
*)

Definition Wp_app (t:trm) : Formula := 
  Local (Wp_Triple t).

(* TODO
  | val_prim val_opp, (v1::nil) => Wp_unop_int v1 (fun n1 => - n1)
  | val_prim val_neg, (v1::nil) => Wp_unop_bool v1 (fun b1 => neg b1)
  | val_prim val_eq, (v1::v2::nil) => Wp_val (isTrue (v1 = v2))
  | val_prim val_neq, (v1::v2::nil) => Wp_val (isTrue (v1 <> v2))
  | val_prim val_add, (v1::v2::nil) => Wp_binop_int v1 v2 (fun n1 n2 => n1 + n2)
  | val_prim val_sub, (v1::v2::nil) => Wp_binop_int v1 v2 (fun n1 n2 => n1 - n2)
  | val_prim val_mul, (v1::v2::nil) => Wp_binop_int v1 v2 (fun n1 n2 => n1 * n2)
*)
(* not included: arithmetic comparisons *)

Definition WP_apps Wp (E:ctx) (v0:func) : list val -> list trm -> Formula := 
  (fix mk (rvs : list val) (ts : list trm) : Formula :=
    match ts with
    | nil => `Wp_app (trm_apps v0 (trms_vals (List.rev rvs)))
    | t1::ts' => WP_getval Wp E t1 (fun v1 => mk (v1::rvs) ts')
    end).

Definition WP_apps_or_prim Wp (E:ctx) (t0:trm) (ts:list trm) : Formula :=
  match t0, ts with
  | trm_val (val_prim val_add), (t1::t2::nil) => 
     WP_getval_int Wp E t1 (fun n1 => 
       WP_getval_int Wp E t2 (fun n2 => 
         `Formula_typed (fun (Q:int->hprop) => Q (n1 + n2))))
  | _,_ => WP_getval_val Wp E t0 (fun v0 => WP_apps Wp E v0 nil ts)
  end.

Definition Wp_if_val (b:bool) (F1 F2:Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    if b then ^F1 Q else ^F2 Q).

Definition WP_if (F0 F1 F2:Formula) : Formula :=
  `Wp_let_typed F0 (fun (b:bool) => `Wp_if_val b F1 F2).

Definition Wp_while (F1 F2:Formula) : Formula :=
  Local (`Formula_typed (fun (Q:unit->hprop) =>
    \forall (R:Formula),
    let F := WP_if F1 (Wp_seq F2 R) (Wp_val val_unit) in
    \[ is_flocal (@R unit _) /\ (forall Q', ^F Q' ==> ^R Q')] \-* (^R Q))).

Definition Wp_for_int (n1 n2:int) (F1:int->Formula) : Formula := 
  Local (Formula_typed (fun (Q:unit->hprop) =>
    \forall (S:int->Formula),
    let F i := If (i <= n2) then (`Wp_seq (F1 i) (S (i+1)))
                            else (`Wp_val val_unit) in
    \[ (forall i, is_flocal (S i unit _)) /\ (forall i Q', ^(F i) Q' ==> ^(S i) Q')] \-* (^(S n1) Q))).



Fixpoint hprop_forall_vars (Hof:ctx->hprop) (G:ctx) (xs:vars) : hprop :=
  match xs with
  | nil => Hof G
  | x::xs' => \forall (X:val), hprop_forall_vars Hof (Ctx.add x X G) xs'
  end.

Fixpoint prop_forall_vars (Hof:ctx->Prop) (G:ctx) (xs:vars) : Prop :=
  match xs with
  | nil => Hof G
  | x::xs' => forall (X:val), prop_forall_vars Hof (Ctx.add x X G) xs'
  end.




Definition Wp_case_val (F1:Formula) (P:Prop) (F2:Formula) : Formula :=
  Local (fun `{Enc A} Q =>
    hand (^F1 Q) (\[P] \-* ^F2 Q)).

Definition WP_match Wp (E:ctx) (v:val) : list (pat*trm) ->  Formula :=
  fix mk (pts:list(pat*trm)) : Formula :=
    match pts with
    | nil => `Wp_fail
    | (p,t)::pts' =>
        let xs := patvars p in
        let F1 A (EA:Enc A) (Q:A->hprop) := 
           hprop_forall_vars (fun G => let E' := (Ctx.app G E) in
              \[v = patsubst G p] \-* ^(Wp E' t) Q) Ctx.empty xs in
        let P := prop_forall_vars (fun G => v <> patsubst G p) Ctx.empty xs in
        Wp_case_val F1 P (mk pts')
    end.
  (* Warning: the body of the cons case above, if put in an auxiliary definition,
     no longer simplifies well using [xwp_simpl] *)


(*
Definition fand (F1 F2:Formula) : Formula :=
  Local (fun `{Enc A} Q => hand (^F1 Q) (^F2 Q)).


Definition Wp_case_val Wp (E:ctx) (v1:val) (p:pat) (t2:trm) (F3:Formula) : Formula :=
  let F1 A (EA:Enc A) (Q:A->hprop) := 
     hprop_forall_pat_vars (fun G => \[v1 = patsubst G p] \-* ^(Wp (Ctx.app G E) t2) Q) Ctx.empty (patvars p) in
  let F2 A (EA:Enc A) (Q:A->hprop) := 
     let P := prop_forall_pat_vars (fun G => v1 <> patsubst G p) Ctx.empty (patvars p) in
     (\[P] \-* ^F3 Q) in
  fand F1 F2.
*)

(* not unfolding all

Definition Wp_case_val Wp (E:ctx) (v1:val) (p:pat) (t2:trm) (F3:Formula) : Formula :=
  let F1 A (EA:Enc A) (Q:A->hprop) := 
     hprop_forall_pat_vars (fun G => \[v1 = patsubst G p] \-* ^(Wp (Ctx.app G E) t2) Q) Ctx.empty (patvars p) in
  let P2 := prop_forall_pat_vars (fun G => v1 <> patsubst G p) Ctx.empty (patvars p) in
  Local (fun `{Enc A} Q => hand (^F1 Q) (\[P2] \-* ^F3 Q) ).


Definition Wp_case_val Wp (E:ctx) (v1:val) (p:pat) (t2:trm) (t3:trm) : Formula :=
  Local (fun `{Enc A} Q => 
    hand (hprop_forall_pat_vars Ctx.empty (patvars p) (fun G => \[v1 = patsubst G p] \-* ^(Wp (Ctx.app G E) t2) Q))
         (\[prop_forall_pat_vars Ctx.empty (patvars p) (fun G => v1 <> patsubst G p)] \-* ^(Wp E t3) Q) ).
*)

(* Not computing so well
Fixpoint hprop_forall_pat_vars (G:ctx) (xs:vars) (Hof:ctx->hprop) : hprop :=
  match xs with
  | nil => Hof G
  | x::xs' => \forall (X:val), hprop_forall_pat_vars (Ctx.add x X G) xs' Hof
  end.

*)


(* Factorized yet obfuscated version:

Definition forall_pat_vars (T:Type) (Forall:(val->T)->T) (K:ctx->T) : ctx -> vars -> T :=
  fix mk (G:ctx) (xs:vars) : T :=
    match xs with
    | nil => K G
    | x::xs' => Forall (fun (X:val) => mk (Ctx.add x X G) xs')
    end.

Definition pforall (F:val->Prop) : Prop := 
  forall (v:val), F v.

Definition Wp_case_val (v1:val) (p:pat) (F1of:ctx->Formula) (F2:Formula) : Formula :=
  Local (fun `{Enc A} Q => 
    hand (forall_pat_vars (@hforall val) (fun G => \[v1 = patsubst G p] \-* ^(F1of G) Q) Ctx.empty (patvars p) )
         (\[forall_pat_vars pforall (fun G => v1 <> patsubst G p) Ctx.empty (patvars p)] \-* ^F2 Q) ).

*)



(* DEPRECATED
Definition Wp_case_val `{EA1:Enc A1} (V1:A1) (p:pat) (F1of:ctx->Formula) (F2:Formula) : Formula :=
  Local (fun `{Enc A} Q => 
    hand (\forall (G:ctx), \[Ctx.dom G = patvars p /\ (enc V1) = patsubst G p] \-* ^(F1of G) Q)
         (\[forall (G:ctx), Ctx.dom G = patvars p -> (enc V1) <> patsubst G p] \-* ^F2 Q) ).


Definition Wp_case_val (v1:val) (p:pat) (F1of:ctx->Formula) (F2:Formula) : Formula :=
  Local (fun `{Enc A} Q => 
    hand (\forall (G:ctx), \[Ctx.dom G = patvars p /\ v1 = patsubst G p] \-* ^(F1of G) Q)
         (\[forall (G:ctx), Ctx.dom G = patvars p -> v1 <> patsubst G p] \-* ^F2 Q) ).
*)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint Wp (E:ctx) (t:trm) : Formula :=
  let aux := Wp E in
  match t with
  | trm_val v => `Wp_val v
  | trm_var x => WP_var E x
  | trm_fixs f xs t1 =>
      match xs with 
      | nil => `Wp_fail
      | _ => `Wp_val (val_fixs f xs (isubst (Ctx.rem_vars xs (Ctx.rem f E)) t1))
      end
  | trm_constr id ts => WP_constr Wp E id nil ts
  | trm_if t0 t1 t2 =>
     WP_getval_typed Wp E t0 (fun b0 => 
       `Wp_if_val b0 (aux t1) (aux t2))
  | trm_let z t1 t2 =>
     match z with
     | bind_anon => `Wp_seq (aux t1) (aux t2)
     | bind_var x => `Wp_let (aux t1) (fun `{EA:Enc A} (X:A) => Wp (Ctx.add x (enc X) E) t2)
     end
  | trm_apps t0 ts => WP_getval_val Wp E t0 (fun v0 => WP_apps Wp E v0 nil ts)
      (* Wp_apps_or_prim Wp E t0 ts *)
  | trm_while t1 t2 => `Wp_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => 
     WP_getval_typed Wp E t1 (fun n1 =>
       WP_getval_typed Wp E t2 (fun n2 =>
         `Wp_for_int n1 n2 (fun n => Wp (Ctx.add x (enc n) E) t3)))
  | trm_match t0 pts =>
      WP_getval Wp E t0 (fun v0 =>
        WP_match Wp E v0 pts)
  | trm_fail => `Wp_fail
  end.

(* LATER: uniformiser t0 vs t1 for trm_if *)


(* ********************************************************************** *)
(* * Soundness proof *)


(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [Wp_Triple t] is a local formula *)

Lemma is_flocal_Wp_Triple : forall `{EA:Enc A} t,
  is_flocal ((Wp_Triple t) A EA).
Proof using.
  intros. unfolds Wp_Triple. unfolds Weakestpre.
  applys is_flocal_weakestpre. applys is_local_Triple.
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

(** Another formulation of the same corrolary --- not currently used *)
Lemma himpl_Wp_Triple_of_Triple : forall A `{EA:Enc A} (Q1:A->hprop) t H1,
  Triple t H1 Q1 ->
  H1 ==> ^(Wp_Triple t) Q1.
Proof using. introv M. rewrite* <- Triple_eq_himpl_Wp_Triple. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [local] transformer *)

(** [The [Local] transformer may be stripped from the postcondition. *)

Lemma Local_erase : forall H F `{EA:Enc A} (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Local F) Q.
Proof using.
  introv M. hchanges M. applys flocal_erase.
Qed.

(** The [Local] transformer is sound w.r.t. [Triple], in other words, it
    may be stripped from the precondition. *)

Lemma Triple_Local_pre : forall t (F:Formula) `{EA:Enc A} (Q:A->hprop),
  (forall Q, Triple t (^F Q) Q) ->
  Triple t (^(Local F) Q) Q.
Proof using.
  introv M. applys~ is_local_elim.
  unfold Local, flocal. hpull ;=> Q'.
  hsimpl (^F Q') ((Q' \--* Q \*+ \GC)) Q'. split~.
  { hsimpl. }
Qed.

(** The tactic [remove_Local] applies to goal of the form [triple t (local F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_Local :=
  match goal with |- @Triple _ _ _ _ ?Q =>
    applys Triple_Local_pre; try (clear Q; intros Q); fold wp end.

(*
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
  set (R := Wp_Triple (trm_while (isubst E t1) (isubst E t2))).
  applys Triple_hforall R. simpl. applys Triple_hwand_hpure_l.
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

Lemma Wp_sound_for_val : forall (x:var) v1 v2 F1 E t1,
  (forall X, F1 X ====> Wp_Triple_ (Ctx.add x X E) t1) ->
  Wp_for_val v1 v2 F1 ====> Wp_Triple_ E (trm_for x v1 v2 t1).
Proof using. Opaque Ctx.add Ctx.rem.
  introv M. intros A EA. applys qimpl_Wp_Triple. intros Q.
  remove_Local. simpl.
  unfold Formula_typed. xpull ;=> Q' n1 n2 (->&->) C.
  applys Triple_enc_change (rm C).
  set (S := fun (i:int) => Wp_Triple (isubst E (trm_for x i n2 t1))).
  applys Triple_hforall S. simpl. applys Triple_hwand_hpure_l.
  { split.
    { intros r. applys @is_local_Wp_Triple. }
    { clears Q. intros i. applys qimpl_Wp_Triple. intros Q.
      applys Triple_for_raw. fold isubst.
      rewrite~ @Triple_eq_himpl_Wp_Triple. case_if.
      { unfold Subst1. rewrite <- isubst_add_eq_subst1_isubst.
        asserts_rewrite (trm_seq (isubst (Ctx.add x (``i) E) t1) (trm_for x (i + 1)%I n2 (isubst (Ctx.rem x E) t1))
          = (isubst (Ctx.add x (``i) E) (trm_seq t1 (trm_for x (i + 1)%I n2 t1)))).
        { simpl. rewrite Ctx.rem_anon, Ctx.rem_add_same. auto. }
        applys Wp_sound_seq.
        { applys* M. }
        { unfold S. unfold Wp_Triple_. simpl. rewrite~ Ctx.rem_add_same. } }
      { applys Wp_sound_val E. } } }
  { rewrite~ @Triple_eq_himpl_Wp_Triple. }
Qed.

Lemma himpl_wp_fail_l : forall `{EA:Enc A} (Q:A->hprop) H,
  ^Wp_fail Q ==> H.
Proof using. intros. unfold Wp_fail, Local, local. hpull. Qed.

(** Putting it all together *)

Lemma Wp_sound_trm : forall t,
  Wp_sound t.
Proof using.
  intros t. induction t; intros E A EA Q.
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
  { destruct t1; try solve [ applys @himpl_wp_fail_l ].
    destruct t2; try solve [ applys @himpl_wp_fail_l ].
    applys* Wp_sound_for_val. }
Qed.
 *)



(* ---------------------------------------------------------------------- *)
(* ** Corrolaries of the soundness of [wp] *)

Lemma Triple_isubst_Wp : forall t E `{EA:Enc A} (Q:A->hprop),
  Triple (isubst E t) (^(Wp E t) Q) Q.
Proof using. Admitted. (* TODO
  intros. rewrite Triple_eq_himpl_Wp_Triple. applys Wp_sound_trm.
Qed.*)

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

(* not used *)
Lemma Wp_Triple_of_Wp : forall t H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  H ==> ^(Wp_Triple t) Q.
Proof using. introv M. applys himpl_weakestpre. applys* Triple_of_Wp. Qed.

Lemma himpl_wp_app_of_Triple : forall A `{EA:Enc A} (Q:A->hprop) t H,
  Triple t H Q ->
  H ==> ^(Wp_app t) Q.
Proof using. intros. applys Local_erase. rewrite~ <- Triple_eq_himpl_Wp_Triple. Qed.


(* ********************************************************************** *)
(* * Notation for characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for computed WP *)

Notation "'Fail'" :=
  ((Wp_fail))
  (at level 69) : wp_scope.

Notation "'Val' v" :=
  ((Wp_val v))
  (at level 69) : wp_scope.

Notation "'Return' F " :=
  (Formula_typed F)
  (at level 68) : wp_scope.

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((Wp_let_typed F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Let' [ A EA ] x ':=' F1 'in' F2" :=
  ((Wp_let F1 (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' 'Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 ;;; F2" :=
  ((Wp_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'`Letval' x ':=' v 'in' F2" :=
  ((Wp_letval_typed v (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Letval'  x  ':='  v  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Letval' [ A EA ] x ':=' v 'in' F2" :=
  ((Wp_letval v (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' 'Letval'  [ A  EA ]  x  ':='  v  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.
 
(*
Notation "'App' f t1 " :=
  (Wp_app (trm_apps f (t1::nil)))
  (at level 68, f, t1 at level 0) : wp_scope.

Notation "'App' f t1 t2 " :=
  (Wp_app (trm_apps f (t1::t2::nil)))
  (at level 68, f, t1, t2 at level 0) : wp_scope.

Notation "'App' f t1 t2 t3 " :=
  (Wp_app (trm_apps f (t1::t2::t3::nil)))
  (at level 68, f, t1, t2, t3 at level 0) : wp_scope.
*)

Notation "'App' f v1 " :=
  ((Wp_app (trm_apps f (trms_vals (v1::nil)))))
  (at level 68, f, v1 at level 0) : wp_scope.

Notation "'App' f v1 v2 " :=
  ((Wp_app (trm_apps f (trms_vals (v1::v2::nil)))))
  (at level 68, f, v1, v2 at level 0) : wp_scope.

Notation "'App' f v1 v2 v3 " :=
  ((Wp_app (trm_apps f (trms_vals (v1::v2::v3::nil)))))
  (at level 68, f, v1, v2, v3 at level 0) : wp_scope.

(* TODO: recursive notation for App *)

Notation "'Ifval' b 'Then' F1 'Else' F2" :=
  ((Wp_if_val b F1 F2))
  (at level 69) : wp_scope.

(* DEPRECATED
Notation "'If' F0 'Then' F1 'Else' F2" :=
  ((Wp_if F0 F1 F2))
  (at level 69, F0 at level 0) : wp_scope.
*)

Notation "'While' F1 'Do' F2 'Done'" :=
  ((Wp_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' 'While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : wp_scope.

Notation "'For' x '=' n1 'To' n2 'Do' F3 'Done'" :=
  ((Wp_for_int n1 n2 (fun x => F3)))
  (at level 69, x ident,
   format "'[v' 'For'  x  '='  n1  'To'  n2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : wp_scope.


Notation "'Case' v '=' vp ''=>' F1 ''|' F2" :=
  ((Wp_case_val (fun A EA Q => \[v = vp%val] \-* F1 A EA Q) (v <> vp%val) F2))
  (at level 69, v, vp at level 69,
   format "'[v' 'Case'  v  '='  vp  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.

Notation "'Case' v '=' vp [ x1 ] ''=>' F1 ''|' F2" :=
  ((Wp_case_val (fun A EA Q => \forall x1, \[v = vp%val] \-* F1 A EA Q) (forall x1, v <> vp%val) F2))
  (at level 69, v, vp at level 69, x1 ident,
   format "'[v' 'Case'  v  '='  vp  [ x1 ]  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.

Notation "'Case' v '=' vp [ x1 x2 ] ''=>' F1 ''|' F2" :=
  ((Wp_case_val (fun A EA Q => \forall x1 x2, \[v = vp%val] \-* F1 A EA Q) (forall x1 x2, v <> vp%val) F2))
  (at level 69, v, vp at level 69, x1 ident, x2 ident,
   format "'[v' 'Case'  v  '='  vp  [ x1  x2 ]  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.


(* DEPRECATED
Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 ''=>' F2" :=
  (Case v = vp1%val Then F1 Else 
   is_Wp (Case v = vp2%val Then F2 Else 
   is_Wp (Fail))) (at level 69, v, vp1, vp2 at level 69,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 [ x21 ] ''=>' F2" :=
  (Case v = vp1%val Then F1 Else 
   is_Wp (Case v = vp2%val [ x21 ] Then F2 Else 
   is_Wp (Fail))) (at level 69, v, vp1, vp2 at level 69, x21 ident,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  [ x21 ]  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 [ x21 x22 ] ''=>' F2" :=
  (Case v = vp1%val Then F1 Else 
   is_Wp (Case v = vp2%val [ x21 x22 ] Then F2 Else 
   is_Wp (Fail))) (at level 69, v, vp1, vp2 at level 0, x21 ident, x22 ident,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  [ x21  x22 ]  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' Fof 'End'" :=
  ((Wp_match_val v Fof))
  (at level 69,
   format "'[v' 'Match_'  v  'With'  '/' '[' Fof ']' '/'  'End' ']'")
   : wp_scope.


*)


(* NEEDED?
Notation "'Apptrm' t " :=
  ((Wp_app t))
  (at level 68, t at level 0) : wp_scope.
*)


