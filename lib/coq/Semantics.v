(**

This file describes the syntax and semantics of a lambda calculus
with mutable heap. The language includes recursive functions, and a
couple of primitive functions. Records and arrays operations are
encoded using pointer arithmetics, and using the [alloc] operation
which allocates at once a requested number of consecutive memory cells.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require Export LibString LibList LibCore.
From CFML Require Export LibSepBind LibSepTLCbuffer.
From CFML Require Import LibSepFmap.
Module Fmap := LibSepFmap.

Import LibListExec.RewListExec.
Open Scope string_scope.


(* ********************************************************************** *)
(* * Source language syntax *)


(* ---------------------------------------------------------------------- *)
(** Representation of locations and fields *)

Definition loc : Type := nat.

Definition null : loc := 0%nat.

Definition field : Type := nat.

Definition idconstr : Type := var.

Global Opaque field loc.


(* ---------------------------------------------------------------------- *)
(** Syntax of the source language *)

(** Remark: [ref v] is equivalent to [let p = alloc 1 in set p v; p]. *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_alloc : prim
  | val_dealloc : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_neq : prim
  | val_sub : prim
  | val_add : prim
  | val_mul : prim
  | val_mod : prim
  | val_div : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim.

Inductive pat : Type :=
  | pat_var : var -> pat
  | pat_unit : pat
  | pat_bool : bool -> pat
  | pat_int : int -> pat
  | pat_constr : idconstr -> list pat -> pat.

  (* Note: [pat_any] can be encoded as [pat_var x] for a fresh [x].
    [pat_bool] and [pat_int] can be simulated using conditionals. *)

Inductive val : Type :=
  | val_uninitialized : val
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fixs : bind -> list var -> trm -> val
  | val_constr : idconstr -> list val -> val
  | val_header : nat -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fixs : bind -> list var -> trm -> trm
  | trm_constr : idconstr -> list trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_let : bind -> trm -> trm -> trm
  | trm_apps : trm -> list trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm
  | trm_match : trm -> list (pat * trm) -> trm
  | trm_fail : trm.

(** The state is a finite map from location to values. *)

Definition state : Type := fmap loc val.

(** Shorthand [vars], [fields], [vals] and [trms] for lists of items. *)

Definition fields : Type := list field.
Definition vals : Type := list val.
Definition trms : Type := list trm.

(** The type of patterns is inhabited *)

Global Instance Inhab_pat : Inhab pat.
Proof using. apply (Inhab_of_val pat_unit). Qed.

(** The type of values is inhabited *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** The type of terms is inhabited *)

Global Instance Inhab_trm : Inhab trm.
Proof using. apply (Inhab_of_val (trm_val val_unit)). Qed.


(** Values into terms *)

Definition trm_is_val (t:trm) : Prop :=
  exists v, t = trm_val v.

Definition trm_is_var (t:trm) : Prop :=
  exists x, t = trm_var x.



(* ---------------------------------------------------------------------- *)
(** Encoded constructs *)

(** Sequence *)

Notation trm_seq := (trm_let bind_anon).

(** Non-recursive functions *)

Notation trm_funs := (trm_fixs bind_anon).

Notation val_funs := (val_fixs bind_anon).

(** Unary functions *)

Definition val_fix f x t1 :=
  val_fixs f (x::nil) t1.

Definition trm_fix f x t1 :=
  trm_fixs f (x::nil) t1.

Definition trm_app t0 t1 :=
  trm_apps t0 (t1::nil).

Notation val_fun := (val_fix bind_anon).

Notation trm_fun := (trm_fix bind_anon).


(** Rewriting for encoded constructs *)

Lemma val_fun_fold : forall x t,
  val_funs (x::nil) t = val_fun x t.
Proof using. auto. Qed.

Lemma val_fix_fold : forall f x t,
  val_fixs f (x::nil) t = val_fix f x t.
Proof using. auto. Qed.

Lemma trm_fun_fold : forall x t,
  trm_funs (x::nil) t = trm_fun x t.
Proof using. auto. Qed.

Lemma trm_fix_fold : forall f x t,
  trm_fixs f (x::nil) t = trm_fix f x t.
Proof using. auto. Qed.

Lemma trm_seq_fold : forall t1 t2,
  trm_let bind_anon t1 t2 = trm_seq t1 t2.
Proof using. auto. Qed.

Lemma trm_app_fold : forall t1 t2,
  trm_apps t1 (t2::nil) = trm_app t1 t2.
Proof using. auto. Qed.

Hint Rewrite val_fun_fold val_fix_fold trm_fun_fold trm_fix_fold
             trm_seq_fold trm_app_fold : rew_trm.

Tactic Notation "rew_trm" := autorewrite with rew_trm.
Tactic Notation "rew_trm" "in" hyp(H) := autorewrite with rew_trm in H.
Tactic Notation "rew_trm" "in" "*" := autorewrite with rew_trm in *.


(* ---------------------------------------------------------------------- *)
(** Coercions *)

(** Parsing facility: coercions from list of values to list of terms *)

Coercion trms_vals (vs:vals) : list trm :=
  LibListExec.map trm_val vs.

Lemma trms_vals_fold_start : forall v,
  (trm_val v)::nil = trms_vals (v::nil).
Proof using. auto. Qed.

Lemma trms_vals_fold_next : forall v vs,
  (trm_val v)::(trms_vals vs) = trms_vals (v::vs).
Proof using. auto. Qed.

Hint Rewrite trms_vals_fold_start trms_vals_fold_next : rew_trms_vals.

Tactic Notation "rew_trms_vals" :=
  autorewrite with rew_trms_vals.

Import LibList.

Lemma app_trms_vals_rev_cons : forall v vs ts,
  trms_vals (rev (v::vs)) ++ ts = trms_vals (rev vs) ++ trm_val v :: ts.
Proof using. intros. unfold trms_vals. rew_list_exec. rew_listx~. Qed.

(** Parsing facility: coercions for constructors *)

Coercion pat_var : var >-> pat.
Coercion pat_bool : bool >-> pat.
Coercion pat_int : Z >-> pat.

Coercion val_unit' (u:unit) : val := val_unit.
Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.

(** Parsing facility: using term syntax to parse patterns *)

Fixpoint trm_to_pat (t:trm) : pat :=
  match t with
  | trm_var x => pat_var (x:var)
  | trm_constr id ts => pat_constr id (LibListExec.map trm_to_pat ts)
  | trm_val (val_unit) => pat_unit
  | trm_val (val_bool b) => pat_bool b
  | trm_val (val_int n) => pat_int n
  | _ => arbitrary
  end.

Coercion trm_to_pat : trm >-> pat.

(** Parsing facility: coercions for turning [t1 t2 t3]
    into [trm_apps t1 (t2::t3::nil)] *)

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.


(* ---------------------------------------------------------------------- *)
(** A computable inverse function for [trms_vals] *)

Fixpoint trms_to_vals_rec (acc:vals) (ts:trms) : option vals :=
  match ts with
  | nil => Some (List.rev acc)
  | trm_val v :: ts' => trms_to_vals_rec (v::acc) ts'
  | _ => None
  end.

Definition trms_to_vals (ts:trms) : option vals :=
  trms_to_vals_rec nil ts.

Lemma trms_to_vals_rec_spec : forall ts vs acc,
  trms_to_vals_rec acc ts = Some vs ->
  trms_vals (List.rev acc) ++ ts = trms_vals vs.
Proof using.
  intros ts. induction ts as [|t ts']; simpl; introv E.
  { inverts E. rew_list~. }
  { destruct t; inverts E as E. forwards IH: IHts' E.
    rewrite LibListExec.rev_eq in *. unfold trms_vals in *.
    rew_list_exec in *. rew_listx~ in IH. }
Qed.

Lemma trms_to_vals_spec : forall ts vs,
  trms_to_vals ts = Some vs ->
  ts = trms_vals vs.
Proof using. intros. rewrites* <- (>> trms_to_vals_rec_spec ts vs (@nil val)). Qed.


(* ---------------------------------------------------------------------- *)
(** Induction principle for terms *)

(** The following section provides support for
   [induction t using trm_induct] to conduct induction over terms
   and provide a useful induction hypothesis for the case of [trm_constr]. *)

(** An induction principle for [trm] *)

Section Trm_induct.
(* Obtained from [Print trm_ind] then manual editing for introducing [Q]. *)
Variables
  (P : trm -> Prop)
  (Q : list trm -> Prop)
  (Q1 : Q nil)
  (Q2 : forall t l, P t -> Q l -> Q (t::l))
  (f : forall (v : val), P v)
  (f0 : forall (v : var), P v)
  (f1 : forall (b : bind) (xs : list var) (t : trm), P t -> P (trm_fixs b xs t))
  (f2 : forall (i : idconstr) (l : list trm), Q l -> P (trm_constr i l))
  (f3 : forall (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_if t t0 t1))
  (f4 : forall (b : bind) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0))
  (f5 : forall (t : trm), P t -> forall (l : list trm), Q l -> P (trm_apps t l))
  (f6 : forall (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_while t t0))
  (f7 : forall (v : var) (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_for v t t0 t1))
  (f8 : forall (t : trm), P t -> forall (pts : list (pat * trm)), Q (LibList.map snd pts) -> P (trm_match t pts))
  (f9 : P trm_fail).

Definition trm_induct_gen := fix F (t : trm) : P t :=
  let trm_list_induct := fix f (l : list trm) : Q l :=
      match l as x return Q x with
      | nil   => Q1
      | t::l' => Q2 (F t) (f l')
      end in
  match t as t0 return (P t0) with
  | trm_val v => @f v
  | trm_var v => @f0 v
  | trm_fixs b xs t0 => @f1 b xs t0 (F t0)
  | trm_constr i l => @f2 i l (trm_list_induct l)
  | trm_if t0 t1 t2 => @f3 t0 (F t0) t1 (F t1) t2 (F t2)
  | trm_let b t0 t1 => @f4 b t0 (F t0) t1 (F t1)
  | trm_apps t0 l => @f5 t0 (F t0) l (trm_list_induct l)
  | trm_while t0 t1 => @f6 t0 (F t0) t1 (F t1)
  | trm_for v t0 t1 t2 => @f7 v t0 (F t0) t1 (F t1) t2 (F t2)
  | trm_match t0 pts => @f8 t0 (F t0) pts ((fix trm_list_induct (l : list (pat*trm)) : Q (LibList.map snd l) :=
      match l as x return Q (LibList.map snd x) with
      | nil   => Q1
      | (p,t)::l' => Q2 (F t) (trm_list_induct l')
      end) pts)
  | trm_fail => @f9
  end.

End Trm_induct.

Lemma trm_induct : forall P : trm -> Prop,
  (forall v : val, P v) ->
  (forall v : var, P v) ->
  (forall (b : bind) (xs : list var) (t : trm), P t -> P (trm_fixs b xs t)) ->
  (forall (i : idconstr) (l : list trm), (forall t, mem t l -> P t) -> P (trm_constr i l)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_if t t0 t1)) ->
  (forall (b : bind) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0)) ->
  (forall t : trm, P t -> forall (l : list trm), (forall t, mem t l -> P t) -> P (trm_apps t l)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> P (trm_while t t0)) ->
  (forall (v : var) (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_for v t t0 t1)) ->
  (forall t : trm, P t -> forall pts, (forall p t, mem (p,t) pts -> P t) -> P (trm_match t pts)) ->
  P trm_fail ->
  forall t : trm, P t.
Proof using.
  hint mem_map'.
  intros. gen t. eapply trm_induct_gen with (Q := fun l =>
    forall t, mem t l -> P t); eauto.
  { introv M. inverts M. }
  { introv M1 M2 M3. inverts~ M3. }
  (* for match case:
     rename H8 into Hm. applys~ Hm. intros pi ti Mi. applys M2. applys mem_map Mi. *)
Qed.



(* ********************************************************************** *)
(* * Definition of substitution *)

(* ---------------------------------------------------------------------- *)
(** Variables from a pattern *)

Fixpoint patvars (p:pat) : vars :=
  match p with
  | pat_var x => x::nil
  | pat_unit => nil
  | pat_bool b => nil
  | pat_int n => nil
  | pat_constr id ps => List.fold_right (fun p acc => List.app (patvars p) acc) nil ps
  end.


(* ---------------------------------------------------------------------- *)
(** Definition of standard capture-avoiding substitution *)

(** Substitution of a variable with a value. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t :=
    subst y w t in
  let aux_no_capture z t :=
    If z = bind_var y then t else aux t in
  let aux_no_captures xs t :=
    If LibList.mem y xs then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => If x = y then trm_val w else t
  | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                        aux_no_captures xs t1)
  | trm_constr id ts => trm_constr id (LibListExec.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (aux_no_capture z t2)
  | trm_apps t0 ts => trm_apps (aux t0) (LibListExec.map aux ts)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  | trm_match t0 pts => trm_match (aux t0) (LibListExec.map (fun '(pi,ti) =>
       (pi, aux_no_captures (patvars pi) ti)) pts)
  | trm_fail => trm_fail
  end.

(** Recall from [LibSepBind.v] that a value of type [bind] is either
    a variable of the form [bind_var x] or the anonymous binder [bind_anon] *)

(** [subst1 z v t] substitutes [z] with [v] in [t],
    or do nothing if [z] is the anonymous binder. *)

Definition subst1 (z:bind) (v:val) (t:trm) :=
  match z with
  | bind_anon => t
  | bind_var x => subst x v t
  end.

(** [subst2] is a shorthand that iterates two calls to [subst1]. *)

Definition subst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   subst1 z2 v2 (subst1 z1 v1 t).

(** [substn xs vs t] is an iterated version of [subst].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Fixpoint substn (xs:vars) (vs:vals) (t:trm) : trm :=
  match xs,vs with
  | x::xs', v::vs' => substn xs' vs' (subst x v t)
  | _,_ => t
  end.


(* ---------------------------------------------------------------------- *)
(** Definition of iterated substitution *)

(** To efficiently compute characteristic formulae, we introduce an
    n-ary substitution function. *)

(** [ctx] is the type of bindings from variables to values, using a
    definition from [LibSepBind.v]. *)

Definition ctx := Ctx.ctx val.

(** [isubst E t] substitutes all the bindings from [E] inside [t]. *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  let aux := isubst E in
  match t with
  | trm_val v => trm_val v
  | trm_var x => match Ctx.lookup x E with
                 | None => t
                 | Some v => v
                 end
  | trm_fixs f xs t1 => trm_fixs f xs (isubst (Ctx.rem_vars xs (Ctx.rem f E)) t1)
  | trm_constr id ts => trm_constr id (LibListExec.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (isubst (Ctx.rem z E) t2)
  | trm_apps t0 ts => trm_apps (aux t0) (LibListExec.map aux ts)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (isubst (Ctx.rem x E) t3)
  | trm_match t0 pts => trm_match (aux t0) (LibListExec.map (fun '(pi,ti) =>
       (pi, isubst (Ctx.rem_vars (patvars pi) E) ti)) pts)
  | trm_fail => trm_fail
  end.

(** Recall that [one z v] is a shorthand for [add z v empty], and that
    [add] ignores anonymous binders. *)

(** [isubstn xs vs t] is a shorthand for [substs (List.combine xs vs) t].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Definition isubstn (xs:vars) (vs:vals) (t:trm) : trm :=
  isubst (LibList.combine xs vs) t.


(* ---------------------------------------------------------------------- *)
(** Distribution of [subst] over n-ary functions *)

Lemma subst_trm_funs : forall y w xs t,
  var_fresh y xs ->
  subst1 y w (trm_funs xs t) = trm_funs xs (subst1 y w t).
Proof using.
  introv N. simpls. repeat case_if.
  { false* var_fresh_mem_inv. }
  { auto. }
Qed.

Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. simpls. case_var.
  { false* var_fresh_mem_inv. }
  { auto. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Relationship between substitution and iterated substitution *)

(** [isubst] with [empty] changes nothing. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros. induction t using trm_induct; simpl;
   try solve [ repeat rewrite Ctx.rem_empty; fequals* ].
  { rew_ctx. rewrite Ctx.rem_empty. rewrite Ctx.rem_vars_nil. rewrite~ IHt. }
  { rew_list_exec. fequals. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { rew_list_exec. fequals. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { rew_list_exec. fequals. induction pts as [|[pi ti] l'].
    { auto. }
    { rew_listx. rewrite Ctx.rem_vars_nil. fequals*. fequals*. } }
Qed.

Lemma isubst_empty : forall t,
  isubst Ctx.empty t = t.
Proof using. applys isubst_nil. Qed.

(** [isubst] with [add] is like calling [subst] first *)

Lemma isubst_cons : forall x v E t,
  isubst ((x,v)::E) t = isubst E (subst x v t).
Proof using.
  intros. rew_ctx. gen E.
  induction t using trm_induct; intros; simpl; try solve [ fequals* ].
  { case_var~. }
  { rename b into f. rew_ctx. fequals. simpl. rew_ctx. case_if.
    { subst. rewrite~ Ctx.rem_add_same. }
    { rewrite~ Ctx.rem_add_neq. case_if.
      { rewrite~ Ctx.rem_vars_add_mem. }
      { rewrite~ Ctx.rem_vars_add_not_mem. } } }
  { rename H into IH. rew_list_exec. rew_ctx. fequals.
    induction l as [|t' l'].
    { auto. }
    { rew_listx. rewrite* IHl'. fequals*. } }
  { rew_ctx. fequals. case_if.
    { subst. rewrite* Ctx.rem_add_same. }
    { rewrite* Ctx.rem_add_neq. } }
  { rename H into IH. rew_list_exec. rew_ctx. fequals.
    induction l as [|t' l'].
    { auto. }
    { rew_listx. rewrite* IHl'. fequals*. } }
  { rew_ctx. fequals. case_var~. }
  { rew_ctx. fequals. rew_list_exec. rewrite map_map. applys map_congr.
    intros [pi ti] Mi. fequals. case_if.
    { rewrite~ Ctx.rem_vars_add_mem. }
    { rewrite* Ctx.rem_vars_add_not_mem. } }
Qed.

Lemma isubst_add : forall z v E t,
  isubst (Ctx.add z v E) t = isubst E (subst1 z v t).
Proof using.
  intros. destruct z as [|x].
  { auto. }
  { applys~ isubst_cons. }
Qed.

(** Distribution of [substn] on [nil] and [cons] lists *)

Lemma substn_nil : forall t,
  substn nil nil t = t.
Proof using. auto. Qed.

Lemma substn_cons : forall x xs v vs t,
  substn (x::xs) (v::vs) t = substn xs vs (subst1 x v t).
Proof using. auto. Qed.

(** Distribution of [isubstn] on [nil] and [cons] lists *)

Lemma isubstn_nil : forall t,
  isubstn nil nil t = t.
Proof using. intros. unfold isubstn. simpl. rew_ctx. apply isubst_empty. Qed.

Lemma isubstn_cons : forall x xs v vs t,
  isubstn (x::xs) (v::vs) t = isubstn xs vs (subst1 x v t).
Proof using.
  intros. unfold isubstn. rewrite combine_cons. rewrite~ isubst_cons.
Qed.

(** [isubstn] matches [substn] *)

Lemma isubstn_eq_substn : forall xs vs t,
  length xs = length vs ->
  isubstn xs vs t = substn xs vs t.
Proof using.
  introv E. gen t. list2_ind~ xs vs; intros.
  { rewrite* isubstn_nil. }
  { rewrite* isubstn_cons. }
Qed.

(** Substitutions for two distinct variables commute. *)

Lemma subst_subst_neq : forall x1 x2 v1 v2 t,
  x1 <> x2 ->
  subst x2 v2 (subst x1 v1 t) = subst x1 v1 (subst x2 v2 t).
Proof using.
  introv N. induction t using trm_induct; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  { repeat case_if; simpl; repeat case_if~. }
  { fequals. rew_list_exec. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { fequals. rew_list_exec. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { fequals. rew_list_exec. repeat rewrite map_map. applys map_congr.
    intros [pi ti] Mi. fequals. repeat case_if; eauto. }
Qed.

(** Substituting for a variable that has just been substituted
    does not further modify the term. *)

Lemma subst_subst_same : forall x v1 v2 t,
  subst x v2 (subst x v1 t) = subst x v1 t.
Proof using.
  intros. induction t using trm_induct; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  { fequals. rew_list_exec. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { fequals. rew_list_exec. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { fequals. rew_list_exec. repeat rewrite map_map. applys map_congr.
    intros [pi ti] Mi. fequals. repeat case_if; eauto. }
Qed.

(** A step of an iterated substitution can be postponed until the end
    if we remove its variable from the context. *)

Lemma isubst_subst_eq_subst_isubst_rem : forall (x:var) v E t,
  isubst E (subst x v t) = subst x v (isubst (Ctx.rem x E) t).
Proof using.
  intros. gen t. induction E as [| (y,w) E']; intros; rew_ctx.
  { rewrite Ctx.rem_empty. do 2 rewrite isubst_empty. auto. }
  { tests EQ: (x = y).
    { rewrite Ctx.rem_add_same. rewrite isubst_add. unfold subst1.
      rewrite subst_subst_same. rewrite* IHE'. }
    { rewrite Ctx.rem_add_neq; auto_false. do 2 rewrite isubst_add.
      unfold subst1. rewrite* subst_subst_neq. } }
Qed.

Lemma isubst_add_eq_subst1_isubst : forall z v E t,
  isubst (Ctx.add z v E) t = subst1 z v (isubst (Ctx.rem z E) t).
Proof using.
  intros. destruct z as [|x].
  { auto. }
  { rewrite isubst_add. unfold subst1.
    rewrite* isubst_subst_eq_subst_isubst_rem. }
Qed.

(** A multisubstitution can be postponed until the end
    if we remove its variables from the context. *)

(* currently not used *)
Lemma isubst_app_eq_isubst_isubst : forall G E t,
  isubst (Ctx.app G E) t = isubst E (isubst G t).
Proof using.
  intros G. induction G as [|(y,w) G']; intros; simpl.
  { rewrite~ isubst_nil. }
  { do 2 rewrite isubst_cons. rewrite~ IHG'. }
Qed.

Lemma isubst_app_eq_isubst_isubst_rem_vars : forall G E t,
  isubst (Ctx.app G E) t = isubst G (isubst (Ctx.rem_vars (Ctx.dom G) E) t).
Proof using.
  rewrite Ctx.rem_vars_eq_rem_vars'.
  intros G. induction G as [|(y,w) G']; intros; simpl.
  { rewrite~ isubst_nil. }
  { do 2 rewrite isubst_cons.
    rewrite IHG'. fequals. rewrite Ctx.rem_var_eq_rem.
    rewrite~ <- isubst_subst_eq_subst_isubst_rem. }
Qed.

(** Only the substitution applied to a variable or a value can produce a value *)

Lemma isubst_not_val_not_var : forall E t,
  ~ trm_is_val t ->
  ~ trm_is_var t ->
  ~ trm_is_val (isubst E t).
Proof using.
  introv N1 N2 N3. destruct t; simpls;
    try solve [ destruct N3 as (v'&Ev'); false ].
  { false. }
  { false N2. hnfs*. }
Qed.

(** Substitution on list of values is the identity *)

Lemma map_isubst_trms_vals : forall E vs,
  LibList.map (isubst E) (trms_vals vs) = trms_vals vs.
Proof using.
  intros. induction vs as [|v vs']; simpl.
  { auto. }
  { unfold trms_vals. rew_listx. simpl. fequals*. }
Qed.

(** Substitution lemma for nary constructors and applications *)

Lemma isubst_trm_constr_args : forall E id vs t ts,
  isubst E (trm_constr id (trms_vals vs ++ t :: ts)) =
  trm_constr id (trms_vals vs ++ isubst E t :: LibList.map (isubst E) ts).
Proof using.
  intros. simpl. fequals. rew_list_exec. rew_listx.
  rewrite map_isubst_trms_vals. fequals.
Qed.

Lemma isubst_trm_apps_app : forall E t0 vs ts,
  isubst E (trm_apps t0 (trms_vals vs ++ ts)) =
  trm_apps (isubst E t0) (trms_vals vs ++ LibList.map (isubst E) ts).
Proof using.
  intros. simpl. fequals. rew_list_exec. rew_listx.
  rewrite map_isubst_trms_vals. fequals.
Qed.

Lemma isubst_trm_apps_args : forall E t0 vs t ts,
  isubst E (trm_apps t0 (trms_vals vs ++ t :: ts)) =
  trm_apps (isubst E t0) (trms_vals vs ++ isubst E t :: LibList.map (isubst E) ts).
Proof using. intros. rewrite isubst_trm_apps_app. fequals. Qed.


(* ---------------------------------------------------------------------- *)
(** Pattern substitution *)

(** [patsubst G p] computes the value obtained by instantiating the
    pattern [p] with the bindings from [G]. *)

Fixpoint patsubst (G:ctx) (p:pat) : val :=
  match p with
  | pat_var x =>
      (* Ctx.lookup_or_arbitrary x G ==> fails to compute (why?) *)
        match Ctx.lookup x G with
      | None => val_unit (* arbitrary *)
      | Some v => v
      end
  | pat_unit => val_unit
  | pat_bool b => val_bool b
  | pat_int n => val_int n
  | pat_constr id ps => val_constr id (List.map (patsubst G) ps)
  end.


(* ********************************************************************** *)
(* * Source language semantics *)

Implicit Types p : pat.
Implicit Types t : trm.
Implicit Types v : val.
Implicit Types ts : trms.
Implicit Types vs : vals.
Implicit Types l : loc.
Implicit Types i : field.
Implicit Types b : bool.
Implicit Types n : int.
Implicit Types x : var.
Implicit Types f : bind.
Implicit Types z : bind.
Implicit Types G : ctx.


(* ---------------------------------------------------------------------- *)
(* ** Evaluation contexts *)

(** Evaluation contexts *)

(* LATER: it might be interesting to allow or to prove context composition.
[[
  | evalctx_compose : forall C1 C2,
      evalctx C1 ->
      evalctx C2 ->
      evalctx (fun t => C1 (C2 t))
]]
*)

(* LATER: the use of Coq functions to describe contexts causes some
   complications related to unification. It might work better to use
   first-order contexts, together with an evaluation function for
   applying a context to its argument. This would allow in particular
   to define the notion of substitution into an evaluation context:
[[
    Lemma isubst_evalctx : forall E C t,
      evalctx C ->
        isubst E (evalctx_apply C t)
      = evalctx_apply (evalctx_subst E C) (isubst E t).
]]
*)

Inductive evalctx : (trm -> trm) -> Prop :=
  | evalctx_constr : forall id vs ts,
      evalctx (fun t1 => trm_constr id ((trms_vals vs)++t1::ts))
  | evalctx_let : forall z t2,
      evalctx (fun t1 => trm_let z t1 t2)
  | evalctx_if : forall t2 t3,
      evalctx (fun t1 => trm_if t1 t2 t3)
  | evalctx_apps_fun : forall t2 ts,
      evalctx (fun t0 => trm_apps t0 ts)
  | evalctx_apps_arg : forall v0 vs ts,
      evalctx (fun t1 => trm_apps v0 ((trms_vals vs)++t1::ts))
  | evalctx_for1 : forall x t2 t3,
      evalctx (fun t1 => trm_for x t1 t2 t3)
  | evalctx_for2 : forall x v1 t3,
      evalctx (fun t2 => trm_for x v1 t2 t3)
  | evalctx_match : forall pts,
      evalctx (fun t0 => trm_match t0 pts).

(** Substitution for variables in evaluation contexts *)

Lemma isubst_evalctx_trm_var : forall E C x v,
  evalctx C ->
  Ctx.lookup x E = Some v ->
  isubst E (C (trm_var x)) = isubst E (C v).
Proof using.
  introv HC HE. inverts HC;
   try solve [ simpl; rewrite~ HE ].
  { do 2 rewrite isubst_trm_constr_args. simpl; rewrite~ HE. }
  { do 2 rewrite isubst_trm_apps_args. simpl; rewrite~ HE. }
Qed.

(** The application of an evaluation context yield not a value *)

Lemma evalctx_not_val : forall C t v,
  evalctx C ->
  C t <> v.
Proof using. introv HC N. inverts HC; tryfalse. Qed.

(** Derived *)

Lemma evalctx_app_arg : forall v0,
  evalctx (fun t1 : trm => trm_apps v0 (t1::nil)).
Proof using. intros. applys evalctx_apps_arg (@nil val) (@nil trm). Qed.


(* ---------------------------------------------------------------------- *)
(** Big-step evaluation *)

Section Red.

Local Open Scope fmap_scope.

(** Evaluation rules for unary operations *)

Inductive evalunop : prim -> val -> val -> Prop :=
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (val_bool (neg b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (val_int (- n1)).

(** Evaluation rules for binary operations *)

Inductive evalbinop : prim -> val -> val -> val -> Prop :=
  | evalbinop_ptr_add : forall l' l n,
      (l':nat) = (l:nat) + n :> int ->
      evalbinop val_ptr_add (val_loc l) (val_int n) (val_loc l')
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (val_bool (isTrue (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (val_bool (isTrue (v1 <> v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2) (val_int (n1 + n2))
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2) (val_int (n1 - n2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2) (val_int (n1 * n2))
  | evalbinop_div : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_div (val_int n1) (val_int n2) (val_int (Z.quot n1 n2))
  | evalbinop_mod : forall n1 n2,
      n2 <> 0 ->
      evalbinop val_mod (val_int n1) (val_int n2) (val_int (Z.rem n1 n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2) (val_bool (isTrue (n1 <= n2)))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2) (val_bool (isTrue (n1 < n2)))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2) (val_bool (isTrue (n1 >= n2)))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2) (val_bool (isTrue (n1 > n2))).

Inductive eval : state -> trm -> state -> val -> Prop :=
  (* [eval] for evaluation contexts;
     See lemma [eval_evalctx] for a proof that this rule holds
     in fact also when the context argument is a value, that is,
     it holds without the assumtion [~ trm_is_val t1]. *)
  | eval_evalctx_not_val : forall t1 m1 m2 m3 C v1 r,
      evalctx C ->
      ~ trm_is_val t1 ->
      eval m1 t1 m2 v1 ->
      eval m2 (C v1) m3 r ->
      eval m1 (C t1) m3 r
  (* [eval] for language constructs *)
  | eval_val : forall m v,
      eval m v m v
  | eval_fixs : forall m f xs t1,
      xs <> nil ->
      eval m (trm_fixs f xs t1) m (val_fixs f xs t1)
  | eval_constr : forall m id vs,
      eval m (trm_constr id (trms_vals vs)) m (val_constr id vs)
  | eval_if : forall m1 m2 b r t1 t2,
      eval m1 (if b then t1 else t2) m2 r ->
      eval m1 (trm_if (val_bool b) t1 t2) m2 r
  | eval_let : forall m1 m2 z v1 t2 r,
      eval m1 (subst1 z v1 t2) m2 r ->
      eval m1 (trm_let z v1 t2) m2 r
  | eval_apps_funs_fixs : forall m1 m2 f xs t3 v0 vs r,
      v0 = val_fixs f xs t3 ->
      var_fixs f xs (length vs) ->
      eval m1 (substn xs vs (subst1 f v0 t3)) m2 r ->
      eval m1 (trm_apps v0 vs) m2 r
  | eval_while : forall m1 m2 t1 t2 r,
      eval m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      eval m1 (trm_while t1 t2) m2 r
  | eval_for : forall m1 m2 (x:var) n1 n2 t3 r, (* restricted to value arguments *)
      eval m1 (
        If (n1 <= n2)
          then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
          else val_unit) m2 r ->
      eval m1 (trm_for x n1 n2 t3) m2 r
  | eval_match_yes : forall m1 m2 v G p t1 pts r,
      Ctx.dom G = patvars p ->
      v = patsubst G p ->
      eval m1 (isubst G t1) m2 r ->
      eval m1 (trm_match v ((p,t1)::pts)) m2 r
  | eval_match_no : forall m1 m2 v p t1 pts r,
      (forall G, Ctx.dom G = patvars p -> v <> patsubst G p) ->
      eval m1 (trm_match v pts) m2 r ->
      eval m1 (trm_match v ((p,t1)::pts)) m2 r
  (* [eval] for applied primitives *)
  | eval_unop : forall op m v1 v,
      evalunop op v1 v ->
      eval m (op v1) m v
  | eval_binop : forall op m v1 v2 v,
      evalbinop op v1 v2 v ->
      eval m (op v1 v2) m v
  | eval_ref : forall m v l,
      ~ Fmap.indom m l ->
      l <> null ->
      eval m (val_ref v) (Fmap.update m l v) (val_loc l)
  | eval_get : forall m l,
      Fmap.indom m l ->
      eval m (val_get (val_loc l)) m (Fmap.read m l)
  | eval_set : forall m l v,
      Fmap.indom m l ->
      eval m (val_set (val_loc l) v) (Fmap.update m l v) val_unit
  | eval_free : forall m l,
      Fmap.indom m l ->
      eval m (val_free (val_loc l)) (Fmap.remove m l) val_unit
  | eval_alloc : forall k n ma mb l,
      mb = Fmap.conseq (LibList.make k val_uninitialized) l ->
      n = nat_to_Z k ->
      l <> null ->
      Fmap.disjoint ma mb ->
      eval ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  | eval_dealloc : forall (n:int) vs ma mb l,
      mb = Fmap.conseq vs l ->
      n = LibList.length vs ->
      Fmap.disjoint ma mb ->
      eval (mb \+ ma) (val_dealloc (val_int n) (val_loc l)) ma val_unit.

End Red.

(* LATER: generalization to support for-loops not in A-normal form:
[[

  | eval_for : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      eval m1 (
        (trm_seq (trm_let x n1 t3) (trm_for x (n1+1) n2 t3))
        val_unit) m2 r ->
      eval m1 (trm_for x n1 n2 t3) m2 r

  | eval_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (not_is_val t1 \/ not_is_val t2) ->
      eval m1 t1 m2 v1 ->
      eval m2 t2 m3 v2 ->
      eval m3 (trm_for x v1 v2 t3) m4 r ->
      eval m1 (trm_for x t1 t2 t3) m4 r

  Definition trm_is_val (t:trm) : Prop :=
    match t with
    | trm_val v => True
    | _ => False
    end.
]]
*)


(* ---------------------------------------------------------------------- *)
(* ** Derived rules *)

Section Derived.
Hint Constructors evalctx.
Hint Resolve evalctx_app_arg.

(** Rules for state *)

Lemma eval_ref_sep : forall s1 s2 v l,
  l <> null ->
  s2 = Fmap.single l v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc l).
Proof using.
  introv Nl -> D. forwards Dv: Fmap.indom_single l v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed.

(* Note: [Fmap.disjoint s1 s2] is not needed, and in fact too
   restrictive, because [Fmap.agree s1 s2] would be sufficient. *)

Lemma eval_get_sep : forall s s1 s2 l v,
  s = Fmap.union s1 s2 ->
  s1 = Fmap.single l v ->
  eval s (val_get (val_loc l)) s v.
Proof using.
  introv -> ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_get.
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_set_sep : forall s s' h1 h1' h2 l v v',
  s = Fmap.union h1 h2 ->
  h1 = Fmap.single l v ->
  Fmap.disjoint h1 h2 ->
  s' = Fmap.union h1' h2 ->
  h1' = Fmap.single l v' ->
  eval s (val_set (val_loc l) v') s' val_unit.
Proof using.
  introv -> -> D -> ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_set.
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_free_sep : forall s1 s2 v l,
  s1 = Fmap.union (Fmap.single l v) s2 ->
  Fmap.disjoint (Fmap.single l v) s2 ->
  eval s1 (val_free l) s2 val_unit.
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_free.
  { rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys Fmap.disjoint_inv_not_indom_both D Dl.
    applys Fmap.indom_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

(** Generalization of the evaluation context rule for terms
    that might already be values *)

Lemma eval_evalctx : forall m1 m2 m3 t1 v1 C r,
  evalctx C ->
  eval m1 t1 m2 v1 ->
  eval m2 (C v1) m3 r ->
  eval m1 (C t1) m3 r.
Proof using.
  introv HC M1 M2. tests CV: (trm_is_val t1).
  { destruct CV as (v'&Ev'). subst. inverts M1.
    { false evalctx_not_val; eauto. }
    { auto. } }
  { applys* eval_evalctx_not_val C. }
Qed.

(** Other derived rules *)

Lemma eval_funs : forall m xs t,
  xs <> nil ->
  eval m (trm_funs xs t) m (val_funs xs t).
Proof using. introv N. applys* eval_fixs. Qed.

Lemma eval_fix : forall m f x t1,
  eval m (trm_fix f x t1) m (val_fix f x t1).
Proof using. intros. applys* eval_fixs. auto_false. Qed.

Lemma eval_fun : forall m x t1,
  eval m (trm_fun x t1) m (val_fun x t1).
Proof using. intros. apply eval_fix. Qed.

Lemma eval_let_trm : forall m1 m2 m3 z t1 t2 v1 r,
  eval m1 t1 m2 v1 ->
  eval m2 (subst1 z v1 t2) m3 r ->
  eval m1 (trm_let z t1 t2) m3 r.
Proof using.
  introv M1 M2. applys* eval_evalctx (fun t1 => trm_let z t1 t2).
  applys* eval_let.
Qed.

Lemma eval_if_trm : forall m1 m2 m3 b r t0 t1 t2,
  eval m1 t0 m2 (val_bool b) ->
  eval m2 (if b then t1 else t2) m3 r ->
  eval m1 (trm_if t0 t1 t2) m3 r.
Proof using.
  introv M1 M2. applys* eval_evalctx (fun t0 => trm_if t0 t1 t2).
  applys* eval_if.
Qed.

Lemma eval_constr_trm : forall m1 m2 m3 id ts vs t1 v1 r,
  eval m1 t1 m2 v1 ->
  eval m2 (trm_constr id ((trms_vals vs)++(trm_val v1)::ts)) m3 r ->
  eval m1 (trm_constr id ((trms_vals vs)++t1::ts)) m3 r.
Proof using.
  introv M1 M2.
  applys* eval_evalctx (fun t1 => trm_constr id ((trms_vals vs)++t1::ts)).
Qed.

Lemma eval_match_trm : forall m1 m2 m3 v1 t1 pts r,
  eval m1 t1 m2 v1 ->
  eval m2 (trm_match v1 pts) m3 r ->
  eval m1 (trm_match t1 pts) m3 r.
Proof using.
  introv M1 M2. applys* eval_evalctx (fun t0 => trm_match t0 pts).
Qed.

Lemma eval_apps_funs : forall m1 m2 xs t3 v0 vs r,
  v0 = val_funs xs t3 ->
  var_funs xs (length vs) ->
  eval m1 (substn xs vs t3) m2 r ->
  eval m1 (trm_apps v0 vs) m2 r.
Proof using.
  introv Hf Hxs M. applys* eval_apps_funs_fixs.
Qed.

Lemma eval_apps_fixs : forall m1 m2 (f:bind) xs t3 v0 vs r,
  v0 = val_fixs f xs t3 ->
  var_fixs f xs (length vs) ->
  eval m1 (substn xs vs (subst1 f v0 t3)) m2 r ->
  eval m1 (trm_apps v0 vs) m2 r.
Proof using.
  introv Hf Hxs M. applys* eval_apps_funs_fixs.
Qed.

Lemma eval_app : forall m1 m2 f x t3 v1 v2 r,
  v1 = val_fix f x t3 ->
  f <> x ->
  eval m1 (subst2 f v1 x v2 t3) m2 r ->
  eval m1 (trm_app v1 v2) m2 r.
Proof using.
  introv EQ N M. destruct f as [|f].
  { applys* eval_apps_funs (v2::nil).
    { simpls. splits; auto_false. splits*. } }
  { applys* eval_apps_fixs (v2::nil).
    { simpls. splits; auto_false. splits*. simpls. case_var~. } }
Qed.

Lemma eval_app_trm : forall m1 m2 m3 m4 t1 t2 f x t3 v1 v2 r,
  eval m1 t1 m2 v1 ->
  eval m2 t2 m3 v2 ->
  v1 = val_fix f x t3 ->
  f <> x ->
  eval m3 (subst2 f v1 x v2 t3) m4 r ->
  eval m1 (trm_app t1 t2) m4 r.
Proof using.
  introv M1 M2 EQ N M3. applys* eval_evalctx (fun t1 => trm_apps t1 (t2::nil)).
  applys* eval_evalctx (fun t2 => trm_apps v1 (t2::nil)). applys* eval_app.
Qed.

Lemma eval_app_fun : forall m1 m2 m3 m4 t1 t2 x t3 v1 v2 r,
  eval m1 t1 m2 v1 ->
  eval m2 t2 m3 v2 ->
  v1 = val_fun x t3 ->
  eval m3 (subst1 x v2 t3) m4 r ->
  eval m1 (trm_app t1 t2) m4 r.
Proof using. intros. applys* eval_app_trm. auto_false. Qed.

Lemma eval_seq : forall m1 m2 m3 t1 t2 r1 r,
  eval m1 t1 m2 r1 ->
  eval m2 t2 m3 r ->
  eval m1 (trm_seq t1 t2) m3 r.
Proof using. introv M1 M2. applys* eval_let_trm. Qed.

Lemma eval_ptr_add_nat : forall m l (f : nat),
  eval m (val_ptr_add (val_loc l) (val_int f)) m (val_loc (l+f)%nat).
Proof using. intros. applys* eval_binop. applys* evalbinop_ptr_add. math. Qed.

Lemma eval_for_le : forall m1 m2 m3 x n1 n2 t3 v1 r,
  n1 <= n2 ->
  eval m1 (subst1 x n1 t3) m2 v1 ->
  eval m2 (trm_for x (n1+1) n2 t3) m3 r ->
  eval m1 (trm_for x n1 n2 t3) m3 r.
Proof using.
  introv N M1 M2. applys eval_for. case_if.
  { applys eval_seq. applys M1. applys M2. }
  { false; math. }
Qed.

Lemma eval_for_gt : forall m x n1 n2 t3,
  n1 > n2 ->
  eval m (trm_for x n1 n2 t3) m val_unit.
Proof using.
  introv N. applys eval_for. case_if.
  { false; math. }
  { applys eval_val. }
Qed.

End Derived.


(* ********************************************************************** *)
(* * Size of a term *)

(* ---------------------------------------------------------------------- *)
(** Size of a term, where all values counting for one unit. *)

(** The definition of size can be useful for non-structural inductions *)

(* LATER: define and use the [List.sum] function instead of [List.fold_right]. *)

Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fixs f xs t1 => 1 + trm_size t1
  | trm_constr id ts => 1 + List.fold_right (fun t acc => (acc + trm_size t)%nat) 0%nat ts
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_apps t0 ts => 1 + trm_size t0 + List.fold_right (fun t acc => (acc + trm_size t)%nat) 0%nat ts
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  | trm_match t0 pts => 1 + trm_size t0 + List.fold_right (fun '(p,t) acc => (acc + trm_size t)%nat) 0%nat pts
  | trm_fail => 1
  end.

Lemma trm_size_isubst : forall t E,
  trm_size (isubst E t) = trm_size t.
Proof using.
  intros t. induction t using trm_induct; intros; simpl; repeat case_if; auto.
  { destruct~ (Ctx.lookup v E). }
  { rew_list_exec. fequals. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { rew_list_exec. fequals. fequals. induction l as [|t' l'].
    { auto. }
    { rew_listx. fequals*. } }
  { rew_list_exec. fequals. fequals. induction pts as [|[pi ti] pts'].
    { auto. }
    { rew_listx. fequals*. } }
Qed.

(** Hint for induction on size. Proves subgoals of the form
    [measure trm_size t1 t2], when [t1] and [t2] may have some
    structure or involve substitutions. *)

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; math.

Hint Extern 1 (measure trm_size _ _) => solve_measure_trm_size tt.


(* ********************************************************************** *)
(* * Notation for terms *)

(* ---------------------------------------------------------------------- *)
(** Optional coercion from string to variables *)

Module CoercionsFromStrings.

Coercion string_to_var (x:string) : var := x.

End CoercionsFromStrings.


(* ---------------------------------------------------------------------- *)
(** Notation for concrete programs *)

Declare Scope val_scope.
Declare Scope pat_scope.
Declare Scope trm_scope.

Notation "'dummy_val'" := True (only parsing) : val_scope.
Notation "'dummy_pat'" := True (only parsing) : pat_scope.
Notation "'dummy_trm'" := True (only parsing) : trm_scope.


Delimit Scope val_scope with val.
Delimit Scope pat_scope with pat.
Delimit Scope trm_scope with trm.

Module NotationForTerms.

(** Note: below, many occurrences of [x] have type [bind], and not [var] *)

Notation "''App' f x1 .. xn" :=
  (trm_apps f (@cons trm x1 .. (@cons trm xn (@nil trm)) ..))
  (at level 69, f, x1, xn at level 0, format "''App'  f  x1  ..  xn") : trm_scope.

Notation "''VCstr' C" :=
  (val_constr C nil)
  (at level 69, C at level 0, format "''VCstr'  C") : val_scope.

(* Note: due to a bug affecting Coq 8.8, we use the notation 'VCstr' and not 'Cstr'
   to avoid a conflict. (https://github.com/coq/coq/issues/8106) *)

Notation "''VCstr' C x1 .. xn" :=
  (val_constr C (@cons val x1 .. (@cons val xn (@nil val)) ..))
  (at level 69, C, x1, xn at level 0, format "''VCstr'  C  x1  ..  xn") : val_scope.

Notation "''Cstr' C" :=
  (trm_constr C nil)
  (at level 69, C at level 0, format "''Cstr'  C") : trm_scope.

Notation "''Cstr' C x1 .. xn" :=
  (trm_constr C (@cons trm x1 .. (@cons trm xn (@nil trm)) ..))
  (at level 69, C, x1, xn at level 0, format "''Cstr'  C  x1  ..  xn") : trm_scope.

(** Note: using [If_] instead of [If] to avoid parsing conflict *)

Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Let' 'Rec' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (at level 69, f, x1 at level 0, right associativity,
  format "'[v' '[' 'Let'  'Rec'  f  x1  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Let' 'Rec' f x1 x2 .. xn ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 .. (trm_fun xn t1) ..) t2))
  (at level 69, f, x1, x2, xn at level 0, right associativity,
  format "'[v' '[' 'Let'  'Rec'  f  x1  x2  ..  xn  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

(* LATER: the display associated with the above definition might need to be fixed.
   Here is how to test the issue:
[[
       Definition test2 := Let Rec 'f 'x 'y := val_unit in val_unit.
       Print test2.
]]
*)

Notation "t1 '';' t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity,
   format "'[v' '[' t1 ']'  '';'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x1 .. xn ':=' t" :=
  (val_fixs f (cons x1 .. (cons xn nil) ..) t)
  (at level 69, f, x1, xn at level 0, format "'Fix'  f  x1  ..  xn  ':='  t") : val_scope.

Notation "'Fix_' f x1 .. xn ':=' t" :=
  (trm_fixs f (cons x1 .. (cons xn nil) ..) t)
  (at level 69, f, x1, xn at level 0, format "'Fix_'  f  x1  ..  xn  ':='  t") : trm_scope.

Notation "'Fun' x1 .. xn ':=' t" :=
  (val_funs (cons x1 .. (cons xn nil) ..) t)
  (at level 69, x1, xn at level 0, format "'Fun'  x1  ..  xn  ':='  t") : val_scope.

Notation "'Fun_' x1 .. xn ':=' t" :=
  (trm_funs (cons x1 .. (cons xn nil) ..) t)
  (at level 69, x1, xn at level 0, format "'Fun_'  x1  ..  xn  ':='  t") : trm_scope.

Notation "'LetFun' f x1 .. xn ':=' t1 'in' t2" :=
  (trm_let f (trm_funs (cons x1 .. (cons xn nil) ..) t1) t2)
  (at level 69, f, x1, xn at level 0, format "'LetFun'  f  x1  ..  xn  ':='  t1  'in'  t2") : trm_scope.

Notation "'LetFix' f x1 .. xn ':=' t1 'in' t2" :=
  (trm_let f (trm_fixs f (cons x1 .. (cons xn nil) ..) t1) t2)
  (at level 69, f, x1, xn at level 0, format "'LetFix'  f  x1  ..  xn  ':='  t1  'in'  t2") : trm_scope.

Notation "'While' t1 'Do' t2 'Done'" :=
  (trm_while t1 t2)
  (at level 69, t2 at level 68,
   format "'[v' 'While'  t1  'Do'  '/' '[' t2 ']' '/'  'Done' ']'")
   : trm_scope.

Notation "'For' x ':=' t1 'To' t2 'Do' t3 'Done'" :=
  (trm_for x t1 t2 t3)
  (at level 69, x at level 0, (* t1 at level 0, t2 at level 0, *)
   format "'[v' 'For'  x  ':='  t1  'To'  t2  'Do'  '/' '[' t3 ']' '/'  'Done' ']'")
  : trm_scope.

Notation "'Fail" := trm_fail : trm_scope.

Definition trm_case (p:pat) (t:trm) := (p,t).

Notation "p '=> t" :=
  (trm_case p t)
  (at level 70) : trm_scope.

Notation "'Match' t 'With' c1 ''|' .. ''|' cn 'End'" :=
  (trm_match t (cons c1 .. (cons cn nil) ..))
  (at level 69) : trm_scope.

Notation "'Match' t 'With' ''|' c1 ''|' .. ''|' cn 'End'" :=
  (trm_match t (cons c1 .. (cons cn nil) ..))
  (at level 69) : trm_scope.

Notation "'ref t" :=
  (val_ref t)
  (at level 57) : trm_scope.

Notation "'free t" :=
  (val_free t)
  (at level 57) : trm_scope.

Notation "'! t" :=
  (val_get t)
  (at level 57) : trm_scope.

Notation "t1 ':= t2" :=
  (val_set t1 t2)
  (at level 57) : trm_scope.

Notation "'not t" :=
  (val_neg t)
  (at level 57) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (at level 57) : trm_scope.

Notation "t1 '+ t2" :=
  (val_add t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '- t2" :=
  (val_sub t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '* t2" :=
  (val_mul t1 t2)
  (at level 57) : trm_scope.

Notation "t1 '/ t2" :=
  (val_div t1 t2)
  (at level 57) : trm_scope.

(* LATER
Notation "x `/` y" := (Z.quot x y)
  (at level 59, right associativity) : trm_scope.

Notation "x `mod` y" := (Z.rem x y)
  (at level 59, no associativity) : trm_scope.
*)

Notation "t1 '= t2" :=
  (val_eq t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '<> t2" :=
  (val_neq t1 t2)
  (at level 58) : trm_scope.

(* LATER
Notation "t1 '!= t2" :=
  (val_neq t1 t2)
  (at level 58) : trm_scope.
*)

Notation "t1 '<= t2" :=
  (val_le t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '< t2" :=
  (val_lt t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '>= t2" :=
  (val_ge t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '> t2" :=
  (val_gt t1 t2)
  (at level 60) : trm_scope.

Notation "'()" := val_unit : val_scope.

Notation "''None'" :=
  (trm_constr "None" nil)
  (at level 0) : trm_scope.

Notation "''Some' t1" :=
  (trm_constr "some" (t1:trm)::nil)
  (at level 57) : trm_scope.

Notation "''None'" :=
  (val_constr "none" nil)
  (at level 0, only printing) : val_scope.

Notation "''Some' t1" :=
  (val_constr "some" (t1::nil))
  (at level 57, only printing) : val_scope.

(*
Notation "''None'" :=
  (pat_constr "none" nil)
  (at level 0, only printing) : pat_scope.

Notation "''Some' p1" :=
  (pat_constr "some" (p1::nil))
  (at level 57, only printing) : pat_scope.
*)

Notation "''nil'" :=
  (trm_constr "nil" nil)
  (at level 0) : trm_scope.

Notation "t1 ':: t2" :=
  (trm_constr "cons" ((t1:trm)::(t2:trm)::nil))
  (at level 57) : trm_scope.

Notation "''nil'" :=
  (val_constr "nil" (@nil _))
  (at level 0) : val_scope.

Notation "v1 ':: v2" :=
  (val_constr "cons" ((v1:val)::(v2:val)::nil))
  (at level 57) : val_scope.

(*
Notation "''nil'" :=
  (pat_constr "nil" nil)
  (at level 0, only printing) : pat_scope.

Notation "p1 ':: p2" :=
  (pat_constr "cons" (p1::p2::nil))
  (at level 57, only printing) : pat_scope.
*)

Open Scope pat_scope.
Open Scope val_scope.
Open Scope trm_scope.




(* ---------------------------------------------------------------------- *)
(* Demo for the above notation: *)
(*

  Open Scope trm_scope.
  Import NotationForVariables.
  Definition test_vf1 : val := (val_funs ('x::nil) val_unit).
  Print test_vf1.
  Definition test_vf3 : val := (val_funs ('x::'y::'z::nil) val_unit).
  Print test_vf3.
  Definition test_f3 : trm := Fun_ 'x 'y 'z := val_unit.
  Print test_f3.
  Definition test_lf1 := LetFix 'f 'x1 := val_unit in val_unit.
  Print test_lf1.
  Definition test_lf2 := LetFix 'f 'x1 'x2 := val_unit in val_unit.
  Print test_lf2.


  Definition val_mlist_length : val :=
  Fix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| 'Cstr "nil" '=> 0
    '| 'Cstr "cons" 'x 'q '=> 1 '+ 'f 'q
    End.
  Print val_mlist_length.

  Parameter val_is_empty val_push val_pop : val.

  Definition val_rev_append : val :=
  Fix 'f 'p1 'p2 :=
    If_ val_is_empty 'p1 Then '() Else
       Let 'x := val_pop 'p1 in
       val_push 'p2 'x ';
       'f 'p1 'p2.
  Print val_rev_append.

  Definition val_rev_append_with_App : val :=
  Fix 'f 'p1 'p2 :=
    If_ 'App val_is_empty 'p1 Then '() Else
       Let 'x := 'App val_pop 'p1 in
       'App val_push 'p2 'x ';
       'App 'f 'p1 'p2.
  Print val_rev_append2.

*)


(* ---------------------------------------------------------------------- *)

End NotationForTerms.


(* ---------------------------------------------------------------------- *)
(* Builtin *)

Section DerivedBuiltin.

Import NotationForTerms NotationForVariables.

Definition val_ignore : val :=
  Fun 'x := '().

Definition val_and : val :=
  Fun 'x 'y :=
    If_ 'x Then 'y Else false.

Definition val_or : val :=
  Fun 'x 'y :=
    If_ 'x Then true Else 'y.

Definition val_abs : val :=
  Fun 'x :=
    If_ 'x '< 0 Then '- 'x Else 'x.

Definition val_min : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'x Else 'y.

Definition val_max : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'y Else 'x.

End DerivedBuiltin.

(* FUTURE USE?

Fixpoint list_forall2_exec A1 A2 (f:A1->A2->bool) (l1:list A1) (l2:list A2) : bool :=
  match l1, l2 with
  | nil, nil => true
  | x1::t1, x2::t2 => f x1 x2 && list_forall2_exec t1 t2
  | _, _ => false
  end.

Definition vars_eq (xs:vars) (ys:vars) : bool :=
  list_forall2_exec var_eq xs ys.

Definition bind_eq (za:bind) (zb:bind) : bool :=
  match za, zb with
  | bind_anon, bind_anon => true
  | bind_var xa, bind_var xb => var_eq xa xb
  | _, _ => false
  end.

Definition eq_bool_exec (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Fixpoint eq_int_exec (n1 n2 : int) : bool :=
  match n1, n2 with
  | O, O => true
  | S m1, S m2 => eq_int_exec m1 m2
  | _, _ => false
  end.

Definition eq_prim_exec

(*  | val_prim_derived : var -> val -> val*)

Fixpoint eq_val_exec (v:val) (w:val) : bool :=
  let aux := eq_val_exec in
  let auxs := list_forall2_exec aux in
  match v, w with
  | val_uninitialized, val_uninitialized => true
  | val_unit, val_unit => true
  | val_bool ba, val_bool bb => eq_bool_exec ba bb
  | val_int na, val_int nb => eq_int_exec na nb
  | val_loc na, val_loc nb => eq_int_exec na nb
  | val_prim pa, val_prim pb => eq_prim_exec pa pb
  | val_prim_derived xa va, val_prim_derived xb vb =>
      var_eq xa xb && aux va vb
  | val_fixs za xsa ta, val_fixs zb xsb tb =>
      bind_eq za zb && vars_eq xsa xsb && aux ta tb
  | val_constr ida vsa, val_constr idb vsb =>
      var_eq ida idb && auxs vsa vsb
  | val_header na va, val_header nb vb =>
      eq_int_exec na nb && aux va vb

with eq_trm_exec (t:trm) (u:trm) : bool :=
  let aux := eq_trm_exec in
  let auxs := list_forall2_exec aux in
  match t, u with
  | trm_val v, trm_val w => val_eq v w
  | trm_var xa, trm_var xb => var_eq xa xb
  | trm_fixs f xs t, trm_fixs g ys u =>
      bind_eq f g && vars_eq xs ys && aux t u
  | trm_constr ida ts, trm_constr idb us =>
      var_eq ida idb && auxs ts us
  | trm_if t0 t1 t2, trm_if u0 u1 u2 =>
      aux t0 u0 && aux t1 u1 && aux t2 u2
  | trm_let za t1 t2, trm_let zb u1 u2 =>
      bind_eq za zb && aux t1 u1 && aux t2 u2
  | trm_apps t0 ts, trm_apps u0 us =>
      aux t0 u0 && auxs ts us
  | trm_while t1 t2, trm_while u1 u2 =>
      aux t1 u1 && aux t2 u2
  | trm_for xa t1 t2 t3, trm_for xb u1 u2 u3 =>
      var_eq xa xb && aux t1 u1 && aux t2 u2 && aux t3 u3
  | trm_match t0 ptsa, trm_match u0 ptsb =>
      aux t0 u0 && list_forall2_exec eq_branch_exec ptsa ptsb
  | trm_fail, trm_fail => true
  | _, _ => false
  end

with eq_branch_exec (pta ptb : (pat*trm)) : bool :=
  match pta, ptb with
  | (pa,ta), (pb,tb) => eq_pat_exec pa pb && eq_trm_exec ta tb
  end

with eq_pat_exec (p q : pat) : bool :=
  match p, q with
  | pat_var xa, pat_var xb => var_eq xa xb
  | pat_unit, pat_unit => true
  | pat_bool ba, pat_bool bb => eq_bool_exec ba bb
  | pat_int na, pat_int nb => eq_int_exec na nb
  | pat_constr ida psa, pat_constr idb psb =>
      var_eq ida idb && list_forall2_exec eq_pat_exec psa psb
  end.

*)