(**

This file describes the syntax and semantics of a lambda calculus
with mutable heap. The language includes recursive functions, and a
couple of primitive functions. Records and arrays operations are
encoded using pointer arithmetics, and using the [alloc] operation
which allocates at once a requested number of consecutive memory cells.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibString LibList LibCore.
From Sep Require Export Fmap Bind TLCbuffer.
Open Scope string_scope.


(* ********************************************************************** *)
(* * Source language syntax *)


(* ---------------------------------------------------------------------- *)
(** Representation of locations and fields *)

Definition loc := nat.

Definition null : loc := 0%nat.

Definition field := nat.

Definition idconstr := nat.

Global Opaque field loc.


(* ---------------------------------------------------------------------- *)
(** Syntax of the source language *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_alloc : prim
  | val_eq : prim
  | val_sub : prim
  | val_add : prim
  | val_ptr_add : prim.

Inductive pat : Type :=
  | pat_var : var -> pat (* not very useful for the moment, but let's have it *)
  | pat_constr : idconstr -> list var -> pat. (* non recursive, for the moment *)

  (* Note: [pat_any] can be encoded as [pat_var x] for a fresh [x].
    [pat_bool] and [pat_int] can be simulated using conditionals. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : bind -> bind -> trm -> val
  | val_constr : idconstr -> list val -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : bind -> bind -> trm -> trm
  | trm_constr : idconstr -> list trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_let : bind -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm
  | trm_case : trm -> pat -> trm -> trm -> trm
  | trm_fail : trm.
  
  (* Note: [match v with p1 -> t1 | p2 -> t2] is encoded as 
     [trm_case v p1 t1 (trm_case v p2 t2 trm_fail)] *)

(** The type of values is inhabited *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** Encoded constructs *)

Notation trm_seq := (trm_let bind_anon).
Notation trm_fun := (trm_fix bind_anon).
Notation val_fun := (val_fix bind_anon).

(** Values into terms *)

Notation trms_vals := (LibList.map trm_val).

Definition trm_is_val (t:trm) : Prop :=
  exists v, t = trm_val v.

Definition trm_is_var (t:trm) : Prop :=
  exists x, t = trm_var x.

(** Shorthand [vars], [vals] and [trms] for lists of items. *)

Definition vals : Type := list val.
Definition trms : Type := list trm.


(* ---------------------------------------------------------------------- *)
(** Coercions *)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.


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
  (f : forall v : val, P v) 
  (f0 : forall v : var, P v)
  (f1 : forall (b b0 : bind) (t : trm), P t -> P (trm_fix b b0 t))
  (f2 : forall (i : idconstr) (l : list trm), Q l -> P (trm_constr i l))
  (f3 : forall t : trm, P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_if t t0 t1))
  (f4 : forall (b : bind) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0))
  (f5 : forall t : trm, P t -> forall t0 : trm, P t0 -> P (t t0))
  (f6 : forall t : trm, P t -> forall t0 : trm, P t0 -> P (trm_while t t0))
  (f7 : forall (v : var) (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_for v t t0 t1))
  (f8 : forall t : trm, P t -> forall (p : pat) (t0 : trm), P t0 -> forall t1 : trm, P t1 -> P (trm_case t p t0 t1))
  (f9 : P trm_fail).

Definition trm_induct_gen := fix F (t : trm) : P t :=
  match t as t0 return (P t0) with
  | trm_val v => @f v
  | trm_var v => @f0 v
  | trm_fix b b0 t0 => @f1 b b0 t0 (F t0)
  | trm_constr i l => @f2 i l ((fix trm_list_induct (l : list trm) : Q l :=
      match l as x return Q x with
      | nil   => Q1
      | t::l' => Q2 (F t) (trm_list_induct l')
      end) l)
  | trm_if t0 t1 t2 => @f3 t0 (F t0) t1 (F t1) t2 (F t2)
  | trm_let b t0 t1 => @f4 b t0 (F t0) t1 (F t1)
  | trm_app t0 t1 => @f5 t0 (F t0) t1 (F t1)
  | trm_while t0 t1 => @f6 t0 (F t0) t1 (F t1)
  | trm_for v t0 t1 t2 => @f7 v t0 (F t0) t1 (F t1) t2 (F t2)
  | trm_case t0 p t1 t2 => @f8 t0 (F t0) p t1 (F t1) t2 (F t2)
  | trm_fail => @f9
  end.

End Trm_induct.

Lemma trm_induct : forall P : trm -> Prop,
  (forall v : val, P v) ->
  (forall v : var, P v) ->
  (forall (b b0 : bind) (t : trm), P t -> P (trm_fix b b0 t)) ->
  (forall (i : idconstr) (l : list trm), (forall t, mem t l -> P t) -> P (trm_constr i l)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_if t t0 t1)) ->
  (forall (b : bind) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> P (t t0)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> P (trm_while t t0)) ->
  (forall (v : var) (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_for v t t0 t1)) ->
  (forall t : trm, P t -> forall (p : pat) (t0 : trm), P t0 -> forall t1 : trm, P t1 -> P (trm_case t p t0 t1)) ->
  P trm_fail -> 
  forall t : trm, P t.
Proof using.
  intros. gen t. eapply trm_induct_gen with (Q := fun l =>
    forall t, mem t l -> P t); auto.
  { introv M. inverts M. }
  { introv M1 M2 M3. inverts~ M3. }
Qed.



(* ********************************************************************** *)
(* * Definition of substitution *)

(* ---------------------------------------------------------------------- *)
(** Variables from a pattern *)

Definition patvars (p:pat) : vars :=
  match p with
  | pat_var x => x::nil
  | pat_constr id xs => xs
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
  | trm_fix f z t1 => trm_fix f z (If f = y then t1 else
                                   aux_no_capture z t1)
  | trm_constr id ts => trm_constr id (List.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (aux_no_capture z t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  | trm_case t1 p t2 t3 => trm_case (aux t1) p (aux_no_captures (patvars p) t2) (aux t3)
  | trm_fail => trm_fail
  end.

(** Recall from [Bind.v] that a value of type [bind] is either
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
    definition from [Bind.v]. *)

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
  | trm_fix f z t1 => trm_fix f z (isubst (Ctx.rem z (Ctx.rem f E)) t1)
  | trm_constr id ts => trm_constr id (List.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (isubst (Ctx.rem z E) t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (isubst (Ctx.rem x E) t3)
  | trm_case t1 p t2 t3 => trm_case (aux t1) p (isubst (Ctx.rem_vars (patvars p) E) t2) (aux t3)
  | trm_fail => trm_fail
  end.

(** Recall that [one z v] is a shorthand for [add z v empty], and that
    [add] ignores anonymous binders. *)

(** [isubst1 z v t] replaces occurences of binder [z] with [v] in [t]. *)

Definition isubst1 (z:bind) (v:val) (t:trm) :=
  isubst (Ctx.one z v) t.

(** [isubst2 z1 v1 z2 v2 t] is similar. *)

Definition isubst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   isubst (Ctx.add z1 v1 (Ctx.one z2 v2)) t.

(** [isubstn xs vs t] is a shorthand for [substs (List.combine xs vs) t].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Definition isubstn (xs:vars) (vs:vals) (t:trm) : trm :=
  isubst (LibList.combine xs vs) t.


(* ---------------------------------------------------------------------- *)
(** Relationship between substitution and iterated substitution *)

(** [isubst] with [empty] changes nothing. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros. induction t using trm_induct; simpl;
   try solve [ repeat rewrite Ctx.rem_empty; fequals* ].
  { rewrite List_map_eq. fequals. induction l as [|t l'].
    { auto. }
    { rew_listx. fequals*. } }
  { rewrite Ctx.rem_vars_nil, IHt1, IHt2, IHt3. auto. }
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
  { rewrite var_eq_spec. do 2 case_if*. }
  { rew_ctx. fequals. case_if.
    { subst. rewrite* Ctx.rem_add_same. }
    { rewrites* (>> Ctx.rem_add_neq b). case_if.
      { subst. rewrite* Ctx.rem_add_same. }
      { rewrite* Ctx.rem_add_neq. } } }
  { rename H into IH. repeat rewrite List_map_eq. rew_ctx. fequals.
    induction l as [|t l'].
    { auto. }
    { rew_listx. rewrite* IHl'. fequals*. } }
  { rew_ctx. fequals. case_if.
    { subst. rewrite* Ctx.rem_add_same. }
    { rewrite~ Ctx.rem_add_neq. } }
  { rew_ctx. fequals. rewrite var_eq_spec. do 2 case_if*. }
  { rew_ctx. fequals. case_if.  
    { rewrite~ Ctx.rem_vars_add_mem. }
    { rewrite~ Ctx.rem_vars_add_not_mem. } }
Qed.

Lemma isubst_add : forall z v E t,
  isubst (Ctx.add z v E) t = isubst E (subst1 z v t).
Proof using.
  intros. destruct z as [|x].
  { auto. }
  { applys~ isubst_cons. }
Qed.

(** [isubst1] matches [subst1] *)

Lemma isubst1_eq_subst1 : forall z v t,
  isubst1 z v t = subst1 z v t.
Proof using.
  intros. unfold isubst1, Ctx.one.
  rewrite isubst_add, isubst_empty. auto.
Qed.

(** Reformulation of the definition of [subst2] *)

Lemma subst2_eq_subst1_subst1 : forall x1 x2 v1 v2 t,
  subst2 x1 v1 x2 v2 t = subst1 x2 v2 (subst1 x1 v1 t).
Proof using. auto. Qed.

(** Reformulation of the definition of [isubst2] *)

Lemma isubst2_eq_isubst1_isubst1 : forall x1 x2 v1 v2 t,
  isubst2 x1 v1 x2 v2 t = isubst1 x2 v2 (isubst1 x1 v1 t).
Proof using.
  intros. unfold isubst2. rewrite~ isubst_add.
  rewrites (>> isubst1_eq_subst1 x1). auto.
Qed.

(** [isubst2] matches [subst2] *)

Lemma isubst2_eq_subst2 : forall z1 v1 z2 v2 t,
  isubst2 z1 v1 z2 v2 t = subst2 z1 v1 z2 v2 t.
Proof using.
  intros. rewrite isubst2_eq_isubst1_isubst1, subst2_eq_subst1_subst1.
  do 2 rewrite isubst1_eq_subst1. auto.
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

(** [isubst1 z v t] returns [t] unchanged when [z] is anonymous. *)

Lemma isubst1_anon : forall v t,
  isubst1 bind_anon v t = t.
Proof using.
  intros. unfold isubst1, Ctx.one, Ctx.add. rewrite~ isubst_empty.
Qed.

(** Substitutions for two distinct variables commute. *)

Lemma subst_subst_neq : forall x1 x2 v1 v2 t,
  x1 <> x2 ->
  subst x2 v2 (subst x1 v1 t) = subst x1 v1 (subst x2 v2 t).
Proof using.
  introv N. induction t using trm_induct; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  { repeat case_if; simpl; repeat case_if~. }
  { fequals. repeat rewrite List_map_eq. induction l as [|t l'].
    { auto. }
    { rew_listx. fequals*. } }
Qed.

(** Substituting for a variable that has just been substituted
    does not further modify the term. *)

Lemma subst_subst_same : forall x v1 v2 t,
  subst x v2 (subst x v1 t) = subst x v1 t.
Proof using.
  intros. induction t using trm_induct; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  { fequals. repeat rewrite List_map_eq. induction l as [|t l'].
    { auto. }
    { rew_listx. fequals*. } }
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
  { rew_listx. simpl. fequals. } 
Qed.

(** Substitution lemma for constructors *)

Lemma isubst_trm_constr_args : forall E id vs t ts,
  isubst E (trm_constr id (trms_vals vs ++ t :: ts)) = 
  trm_constr id (trms_vals vs ++ isubst E t :: LibList.map (isubst E) ts).
Proof using.
  intros. simpl. fequals. rewrite List_map_eq. rew_listx. 
  rewrite map_isubst_trms_vals. fequals.
Qed.


(* ---------------------------------------------------------------------- *)
(** Pattern substitution *)

(** [patsubst G p] computes the value obtained by instantiating the
    pattern [p] with the bindings from [G]. *)

Definition patsubst (G:ctx) (p:pat) : val :=
  let get x := Ctx.lookup_or_arbitrary x G in
  match p with
  | pat_var x => get x
  | pat_constr id xs => val_constr id (LibList.map get xs)
  end.


(* ********************************************************************** *)
(* * Source language semantics *)

Implicit Types p : pat.
Implicit Types t : trm.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types i : field.
Implicit Types b : bool.
Implicit Types n : int.
Implicit Types x : var.
Implicit Types z : bind.
Implicit Types G : ctx.

(* ---------------------------------------------------------------------- *)
(* ** State *)

Definition state := fmap loc val.


(* ---------------------------------------------------------------------- *)
(* ** Evaluation contexts *)

(** Evaluation contexts *)

Inductive evalctx : (trm -> trm) -> Prop :=
  | evalctx_constr : forall id vs ts,
      evalctx (fun t1 => trm_constr id ((trms_vals vs)++t1::ts))
  | evalctx_let : forall z t2,
      evalctx (fun t1 => trm_let z t1 t2)
  | evalctx_if : forall t2 t3,
      evalctx (fun t1 => trm_if t1 t2 t3)
  | evalctx_app1 : forall t2,
      evalctx (fun t1 => trm_app t1 t2)
  | evalctx_app2 : forall v1,
      evalctx (fun t2 => trm_app v1 t2)
(* LATER  | evalctx_app2 : forall t1,
      evalctx (fun t2 => trm_app t1 t2)
  | evalctx_app1 : forall t2,
      evalctx (fun t1 => trm_app t1 t2) *)
  | evalctx_for1 : forall x t2 t3,
      evalctx (fun t1 => trm_for x t1 t2 t3)
  | evalctx_for2 : forall x v1 t3,
      evalctx (fun t2 => trm_for x v1 t2 t3)
  | evalctx_case : forall p t2 t3,
      evalctx (fun t1 => trm_case t1 p t2 t3).

(** Substitution for variables in evaluation contexts *)

Lemma isubst_evalctx_trm_var : forall E C x v,
  evalctx C ->
  Ctx.lookup x E = Some v ->
  isubst E (C (trm_var x)) = isubst E (C v).
Proof using. 
  introv HC HE. inverts HC; 
   try solve [ simpl; rewrite~ HE ].
  { do 2 rewrite isubst_trm_constr_args. simpl; rewrite~ HE. }
Qed.

(* TODO: LATER use an inductive grammar of evalcxt,
   plus a applyctx function to perform the substitution,
   so as to be able to define the notion of substitution
   into an evaluation context 

    Lemma isubst_evalctx : forall E C t,
      evalctx C ->
        isubst E (evalctx_apply C t) 
      = evalctx_apply (evalctx_subst E C) (isubst E t).
    Proof using. 
      introv HC. inverts HC.
Qed.
*)

(** The application of an evaluation context yield not a value *)

Lemma evalctx_not_val : forall C t v,
  evalctx C ->
  C t <> v.
Proof using. introv HC N. inverts HC; tryfalse. Qed.


(* ---------------------------------------------------------------------- *)
(** Big-step evaluation *)

Section Red.

Local Open Scope fmap_scope.

(** Evaluation rules for binary operations *)

Inductive redbinop : prim -> val -> val -> val -> Prop :=
  | redbinop_add : forall n1 n2 n',
      n' = n1 + n2 ->
      redbinop val_add (val_int n1) (val_int n2) (val_int n')
  | redbinop_sub : forall n1 n2 n',
      n' = n1 - n2 ->
      redbinop val_sub (val_int n1) (val_int n2) (val_int n')
  | redbinop_ptr_add : forall l' l n,
      (l':nat) = (l:nat) + n :> int ->
      redbinop val_ptr_add (val_loc l) (val_int n) (val_loc l')
  | redbinop_eq : forall v1 v2,
      redbinop val_eq v1 v2 (val_bool (isTrue (v1 = v2))).

(** Evaluation rules for terms in A-normal form. *)
    (* TODO: add rules to evaluate terms not in A-normal form. *)

Inductive red : state -> trm -> state -> val -> Prop :=
  (* [red] for evaluation contexts *)
  | red_evalctx_not_val : forall t1 m1 m2 m3 C v1 r, 
      evalctx C ->
      ~ trm_is_val t1 -> (* this premise later proved to be optional *)
      red m1 t1 m2 v1 ->
      red m2 (C v1) m3 r ->
      red m1 (C t1) m3 r
  (* [red] for language constructs *)
  | red_val : forall m v,
      red m v m v
  | red_fix : forall m f z t1,
      red m (trm_fix f z t1) m (val_fix f z t1)
  | red_constr : forall m id vs,
      red m (trm_constr id (trms_vals vs)) m (val_constr id vs)
  | red_if : forall m1 m2 b r t1 t2,
      red m1 (if b then t1 else t2) m2 r ->
      red m1 (trm_if (val_bool b) t1 t2) m2 r
  | red_let : forall m1 m2 z v1 t2 r,
      red m1 (subst1 z v1 t2) m2 r ->
      red m1 (trm_let z v1 t2) m2 r
  | red_app : forall m1 m2 f z t3 v1 v2 r,
      v1 = val_fix f z t3 ->
      red m1 (subst2 f v1 z v2 t3) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_while : forall m1 m2 t1 t2 r,
      red m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      red m1 (trm_while t1 t2) m2 r
  | red_for : forall m1 m2 (x:var) n1 n2 t3 r, (* restricted to value arguments *)
      red m1 (
        If (n1 <= n2)
          then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
          else val_unit) m2 r ->
      red m1 (trm_for x n1 n2 t3) m2 r
  | red_case_match : forall m1 m2 v G p t2 t3 r,
      Ctx.dom G = patvars p ->
      v = patsubst G p ->
      red m1 (isubst G t2) m2 r ->
      red m1 (trm_case v p t2 t3) m2 r
  | red_case_mismatch : forall m1 m2 v p t2 t3 r,
      (forall G, Ctx.dom G = patvars p -> v <> patsubst G p) ->
      red m1 t3 m2 r ->
      red m1 (trm_case v p t2 t3) m2 r
  (* [red] for applied primitives *)
  | red_binop : forall op m v1 v2 v,
      redbinop op v1 v2 v ->
      red m (op v1 v2) m v
  | red_ref : forall ma mb v l,
      mb = (fmap_single l v) ->
      l <> null ->
      \# ma mb ->
      red ma (val_ref v) (mb \+ ma) (val_loc l)
  | red_get : forall m l v,
      fmap_data m l = Some v ->
      red m (val_get (val_loc l)) m v
  | red_set : forall m m' l v,
      m' = fmap_update m l v ->
      red m (val_set (val_loc l) v) m' val_unit
  | red_alloc : forall k n ma mb l,
      mb = fmap_conseq l k val_unit ->
      n = nat_to_Z k ->
      l <> null ->
      \# ma mb ->
      red ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l).

End Red.

  (* Note: there is no reduction rule for [trm_fail]. *)


  (*  --- TODO

  Remark: alternative for red_for rules.
    | red_for : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
        red m1 (
          (trm_seq (trm_let x n1 t3) (trm_for x (n1+1) n2 t3))
          val_unit) m2 r ->
        red m1 (trm_for x n1 n2 t3) m2 r

  | red_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (not_is_val t1 \/ not_is_val t2) ->
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_for x v1 v2 t3) m4 r ->
      red m1 (trm_for x t1 t2 t3) m4 r

  Definition trm_is_val (t:trm) : Prop :=
  match t with
  | trm_val v => True
  | _ => False
  end.

  *)


(* ---------------------------------------------------------------------- *)
(* ** Derived rules *)

Section Derived.
Hint Constructors evalctx.

(** Generalization of the evaluation context rule for terms
    that might already be values *)

Lemma red_evalctx : forall m1 m2 m3 t1 v1 C r,
  evalctx C ->
  red m1 t1 m2 v1 ->
  red m2 (C v1) m3 r ->
  red m1 (C t1) m3 r.
Proof using.
  introv HC M1 M2. tests CV: (trm_is_val t1).
  { destruct CV as (v'&Ev'). subst. inverts M1.
    { false evalctx_not_val; eauto. } 
    { auto. } }
  { applys* red_evalctx_not_val C. }
Qed.

(** Other derived rules *)

Lemma red_let_trm : forall m1 m2 m3 z t1 t2 v1 r,
  red m1 t1 m2 v1 ->
  red m2 (subst1 z v1 t2) m3 r ->
  red m1 (trm_let z t1 t2) m3 r.
Proof using.
  introv M1 M2. applys* red_evalctx (fun t1 => trm_let z t1 t2).
  applys* red_let. 
Qed.

Lemma red_if_trm : forall m1 m2 m3 b r t0 t1 t2,
  red m1 t0 m2 (val_bool b) ->
  red m2 (if b then t1 else t2) m3 r ->
  red m1 (trm_if t0 t1 t2) m3 r.
Proof using.
  introv M1 M2. applys* red_evalctx (fun t0 => trm_if t0 t1 t2).
  applys* red_if. 
Qed.

Lemma red_constr_trm : forall m1 m2 m3 id ts vs t1 v1 r,
  red m1 t1 m2 v1 ->
  red m2 (trm_constr id ((trms_vals vs)++(trm_val v1)::ts)) m3 r ->
  red m1 (trm_constr id ((trms_vals vs)++t1::ts)) m3 r.
Proof using.
  introv M1 M2. 
  applys* red_evalctx (fun t1 => trm_constr id ((trms_vals vs)++t1::ts)).
Qed.

Lemma red_app_trm : forall m1 m2 m3 m4 t1 t2 f z t3 v1 v2 r,
  red m1 t1 m2 v1 ->
  red m2 t2 m3 v2 ->
  v1 = val_fix f z t3 ->
  red m3 (subst2 f v1 z v2 t3) m4 r ->
  red m1 (trm_app t1 t2) m4 r.
Proof using. 
  introv M1 M2 EQ M3. applys* red_evalctx (fun t1 => trm_app t1 t2).
  applys* red_evalctx (fun t2 => trm_app v1 t2). applys* red_app.
Qed.

Lemma red_case_trm : forall m1 m2 m3 v1 t1 p t2 t3 r,
  red m1 t1 m2 v1 ->
  red m2 (trm_case v1 p t2 t3) m3 r ->
  red m1 (trm_case t1 p t2 t3) m3 r.
Proof using.
  introv M1 M2. applys* red_evalctx (fun t1 => trm_case t1 p t2 t3).
Qed.

Lemma red_fun : forall m x t1,
  red m (trm_fun x t1) m (val_fun x t1).
Proof using. intros. apply red_fix. Qed.

Lemma red_app_fun : forall m1 m2 m3 m4 t1 t2 z t3 v1 v2 r,
  red m1 t1 m2 v1 ->
  red m2 t2 m3 v2 ->
  v1 = val_fun z t3 ->
  red m3 (subst1 z v2 t3) m4 r ->
  red m1 (trm_app t1 t2) m4 r.
Proof using. intros. applys* red_app_trm. Qed.

Lemma red_seq : forall m1 m2 m3 t1 t2 r1 r,
  red m1 t1 m2 r1 ->
  red m2 t2 m3 r ->
  red m1 (trm_seq t1 t2) m3 r.
Proof using. introv M1 M2. applys* red_let_trm. Qed.

Lemma red_ptr_add_nat : forall m l (f : nat),
  red m (val_ptr_add (val_loc l) (val_int f)) m (val_loc (l+f)%nat).
Proof using. intros. applys* red_binop. applys* redbinop_ptr_add. math. Qed.

Lemma red_if_bool : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using. introv M1. applys* red_if. Qed.

Lemma red_for_le : forall m1 m2 m3 x n1 n2 t3 v1 r,
  n1 <= n2 ->
  red m1 (subst1 x n1 t3) m2 v1 ->
  red m2 (trm_for x (n1+1) n2 t3) m3 r ->
  red m1 (trm_for x n1 n2 t3) m3 r.
Proof using.
  introv N M1 M2. applys red_for. case_if.
  { applys red_seq. applys M1. applys M2. }
  { false; math. }
Qed.

Lemma red_for_gt : forall m x n1 n2 t3,
  n1 > n2 ->
  red m (trm_for x n1 n2 t3) m val_unit.
Proof using.
  introv N. applys red_for. case_if.
  { false; math. }
  { applys red_val. }
Qed.

End Derived.

(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red], defined in file [Fmap] for proving [red] goals
      modulo equalities between states, gets instantiated here. *)

Ltac fmap_red_base tt ::=
  match goal with H: red _ ?t _ _ |- red _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.



(* ********************************************************************** *)
(* * N-ary functions and applications *)

(** [trm_apps t ts] denotes a n-ary application of [t] to the
    arguments from the list [ts].

    [trm_funs xs t] denotes a n-ary function with arguments [xs]
    and body [t].

    [trm_fixs f xs t] denotes a n-ary recursive function [f]
    with arguments [xs] and body [t].

  The tactic [rew_nary] can be used to convert terms in the goal
  to using the nary constructs wherever possible.

  The operation [substn xs vs t] substitutes the variables [xs]
  with the values [vs] inside the term [t].
*)


(* ---------------------------------------------------------------------- *)
(** Coercions from values to terms *)

Coercion vals_to_trms (vs:vals) : trms :=
  List.map trm_val vs.

(** Tactic [rew_vals_to_trms] to fold the coercion where possible *)

Lemma vals_to_trms_fold_start : forall v,
  (trm_val v)::nil = vals_to_trms (v::nil).
Proof using. auto. Qed.

Lemma vals_to_trms_fold_next : forall v vs,
  (trm_val v)::(vals_to_trms vs) = vals_to_trms (v::vs).
Proof using. auto. Qed.

Hint Rewrite vals_to_trms_fold_start vals_to_trms_fold_next
  : rew_vals_to_trms.

Tactic Notation "rew_vals_to_trms" :=
  autorewrite with rew_vals_to_trms.


(* ---------------------------------------------------------------------- *)
(** N-ary applications and N-ary functions *)

(** [trm_apps t (t1::...tn::nil] describes the application term
    [t t1 .. tn]. *)

Fixpoint trm_apps (tf:trm) (ts:trms) : trm :=
  match ts with
  | nil => tf
  | t::ts' => trm_apps (trm_app tf t) ts'
  end.

(** [trm_fixs f (x1::...xn::nil) t] describes the function term
    [trm_fix f x1 (trm_fun x2 ... (trm_fun xn t) ..)]. *)

Fixpoint trm_fixs (f:bind) (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fix f x (trm_fixs bind_anon xs' t)
  end.

(** [val_fixs f (x1::...xn::nil) t] describes the function value
    [val_fix f x1 (trm_fun x2 ... (trm_fun xn t) ..)]. *)

Definition val_fixs (f:bind) (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fix f x (trm_fixs bind_anon xs' t)
  end.

(** [trm_funs (x1::...xn::nil) t] describes the function term
    [trm_fun x1 (trm_fun x2 ... (trm_fun xn t) ..)]. *)

Notation trm_funs := (trm_fixs bind_anon).

(** [val_fun (x1::...xn::nil) t] describes the function value
    [val_fun x1 (trm_fun x2 ... (trm_fun xn t) ..)]. *)

Notation val_funs := (val_fixs bind_anon).


(* ---------------------------------------------------------------------- *)
(** Distribution of [subst] over n-ary functions *)

Lemma subst_trm_funs : forall y w xs t,
  var_fresh y xs ->
  subst1 y w (trm_funs xs t) = trm_funs xs (subst1 y w t).
Proof using.
  introv N. unfold subst1. induction xs as [|x xs']; simpls; fequals.
  { rewrite var_eq_spec in *. case_if. do 2 case_if. rewrite~ <- IHxs'. }
Qed.

Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. destruct xs as [|x xs'].
  { auto. }
  { unfold subst1. simpls. repeat rewrite var_eq_spec in *.
    do 2 case_if in N. do 2 case_if~. fequals. applys* subst_trm_funs. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Reduction rules for n-ary functions *)

Lemma red_funs : forall m xs t,
  xs <> nil ->
  red m (trm_funs xs t) m (val_funs xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fun.
Qed.

Lemma red_fixs : forall m f xs t,
  xs <> nil ->
  red m (trm_fixs f xs t) m (val_fixs f xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fix.
Qed.


(* ---------------------------------------------------------------------- *)
(** Reduction rules for n-ary applications *)

(* Internal lemma *)

Lemma red_app_funs_val_ind : forall xs vs m1 m2 tf t r,
  red m1 tf m1 (val_funs xs t) ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  introv M1 M2 (F&L&N). gen tf t r m1 m2 F N. list2_ind~ xs vs; intros.
  { false. }
  { rename xs1 into xs', x1 into x1, x2 into v1, xs2 into vs', H0 into IH.
    simpl in F. rew_istrue in F. destruct F as (F1&F').
    tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'.
      simpls. applys* red_app_trm. applys* red_val.
      (* BIND rewrite subst2_eq_subst1_subst1, subst1_anon. auto. *) }
    { rewrite substn_cons in M2. applys~ IH M2. applys* red_app_trm.
      { applys* red_val. }
      { (* BIND simpl. rewrite subst2_eq_subst1_subst1, subst1_anon. *)
        rewrite~ subst_trm_funs. applys~ red_funs. } } }
Qed.

(** Reduction rule for n-ary functions *)

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv R M N. applys* red_app_funs_val_ind.
  { subst. apply~ red_val. }
Qed.

(** Reduction rule for n-ary recursive functions *)

Lemma red_app_fixs_val : forall xs (vs:vals) m1 m2 vf (f:var) t r,
  vf = val_fixs f xs t ->
  red m1 (substn (f::xs) (vf::vs) t) m2 r ->
  var_fixs f (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv E M (N&L&P). destruct xs as [|x xs']. { false. }
  { destruct vs as [|v vs']; rew_list in *. { false; math. } clear P.
    destruct N as (N1&N2&N3). simpls. case_if.
    tests C':(xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      subst vf. simpls. hint red_val. applys* red_app. }
    { applys~ red_app_funs_val_ind.
      { hint red_val. applys* red_app.
        rewrite subst2_eq_subst1_subst1. do 2 rewrite~ subst_trm_funs.
        applys* red_funs. }
      { (* BIND do 2 rewrite substn_cons in M. *) applys M. }
      { splits*. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Rewriting lemmas and tactics to "fold" n-ary functions. *)

(** The tactic [rew_nary] introduce [trm_apps] and [trm_fixs]
    in place of nested applications of [trm_app] and [trm_fun]. *)

Lemma trm_apps_fold_start : forall t1 t2,
  trm_app t1 t2 = trm_apps t1 (t2::nil).
Proof using. auto. Qed.

Lemma trm_apps_fold_next : forall t1 t2 t3s,
  trm_apps (trm_app t1 t2) t3s = trm_apps t1 (t2::t3s).
Proof using. auto. Qed.

Lemma trm_apps_fold_concat : forall t1 t2s t3s,
  trm_apps (trm_apps t1 t2s) t3s = trm_apps t1 (List.app t2s t3s).
Proof using.
  intros. gen t1; induction t2s; intros. { auto. }
  { rewrite <- trm_apps_fold_next. simpl. congruence. }
Qed.

Lemma trm_fixs_fold_start : forall f x t,
  trm_fix f x t = trm_fixs f (x::nil) t.
Proof using. auto. Qed.

(* subsumed by iteration of trm_funs_fold_next *)
Lemma trm_funs_fold_app : forall xs ys t,
  trm_funs xs (trm_funs ys t) = trm_funs (List.app xs ys) t.
Proof using.
  intros. induction xs. { auto. } { simpl. congruence. }
Qed.

(* for innermost-first rewriting strategy
Lemma trm_fixs_fold_next : forall f x xs t,
  trm_fixs f (x::nil) (trm_funs xs t) = trm_fixs f (x::xs) t.
Proof using. auto. Qed.
*)

Lemma trm_fixs_fold_app : forall f x xs ys t,
  trm_fixs f (x::xs) (trm_funs ys t) = trm_fixs f (x :: List.app xs ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_start : forall f x t,
  val_fix f x t = val_fixs f (x::nil) t.
Proof using. auto. Qed.

Lemma val_fixs_fold_app : forall f x xs ys t,
  val_fixs f (x::xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_app' : forall f x xs ys t,
  val_fixs f (List.app (x::nil) xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Hint Rewrite
  trm_apps_fold_start trm_apps_fold_next trm_apps_fold_concat
  trm_fixs_fold_start trm_fixs_fold_app
  val_fixs_fold_start val_fixs_fold_app val_fixs_fold_app' : rew_nary.

Tactic Notation "rew_nary" :=
  autorewrite with rew_nary; simpl List.app.
Tactic Notation "rew_nary" "in" hyp(H) :=
  autorewrite with rew_nary in H; simpl List.app in H.
Tactic Notation "rew_nary" "in" "*" :=
  autorewrite with rew_nary in *; simpl List.app in *.
  (* rewrite_strat (any (innermost (hints rew_nary))).
     => way too slow! *)

(* Demos:
Lemma rew_nary_demo_1 : forall (f x y z:var) t1 t2 v,
  val_fix f x (trm_fun y (trm_fun z (f t1 x y t2))) = v.
Proof using. intros. rew_nary. Abort.

Lemma rew_nary_demo_2 : forall f x1 x2 v,
  val_fun f (trm_fun x1 (trm_fun x2 (x1 x2))) = v.
Proof using. intros. rew_nary. Abort.
*)


(* ********************************************************************** *)
(* * Size of a term *)

(* ---------------------------------------------------------------------- *)
(** Size of a term, where all values counting for one unit. *)

(** The definition of size can be useful for some tricky inductions *)

Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fix f x t1 => 1 + trm_size t1
  | trm_constr id ts => 1 + List.fold_right (fun t acc => (acc + trm_size t)%nat) 0%nat ts (* TODO: list_sum *)
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_app t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  | trm_case t1 p t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  | trm_fail => 1
  end.

Lemma trm_size_isubst : forall t E,
  trm_size (isubst E t) = trm_size t.
Proof using.
  intros t. induction t using trm_induct; intros; simpl; repeat case_if; auto.
  { destruct~ (Ctx.lookup v E). }
  { repeat rewrite List_fold_right_eq. repeat rewrite List_map_eq.
    fequals. induction l as [|t l'].
    { auto. }
    { rew_listx. fequals*. } }
Qed.

Lemma trm_size_isubst1 : forall t z v,
  trm_size (isubst1 z v t) = trm_size t.
Proof using. intros. applys trm_size_isubst. Qed.

(** Hint for induction on size. Proves subgoals of the form
    [measure trm_size t1 t2], when [t1] and [t2] may have some
    structure or involve substitutions. *)

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_isubst1; math.

Hint Extern 1 (measure trm_size _ _) => solve_measure_trm_size tt.


(* ********************************************************************** *)
(* * Notation for terms *)

(* ---------------------------------------------------------------------- *)
(** Notation for concrete programs *)

Module NotationForTerms.

(** Note: below, many occurences of [x] have type [bind], and not [var] *)

Notation "'()" := val_unit : trm_scope.

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

  (* LATER: the above might need to be fixed. Here is how to test it:
     Definition test2 := Let Rec 'f 'x 'y := val_unit in val_unit.
     Print test2. *)

Notation "t1 ;;; t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity, only parsing,
   format "'[v' '[' t1 ']'  ;;;  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x1 ':=' t" :=
  (trm_fix f x1 t)
  (at level 69, f, x1 at level 0) : trm_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (at level 69, f, x1, x2 at level 0) : trm_scope.

Notation "'Fix' f x1 x2 .. xn ':=' t" :=
  (trm_fix f x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (at level 69, f, x1, x2, xn at level 0) : trm_scope.

Notation "'ValFix' f x1 ':=' t" :=
  (val_fix f x1 t)
  (at level 69, f, x1 at level 0) : trm_scope.

Notation "'ValFix' f x1 x2 .. xn ':=' t" :=
  (val_fix f x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (at level 69, f, x1, x2, xn at level 0) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'Fun' x1 x2 .. xn ':=' t" :=
  (trm_fun x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (at level 69, x1, x2, xn at level 0) : trm_scope.

Notation "'ValFun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'ValFun' x1 x2 .. xn ':=' t" :=
  (val_fun x1 (trm_fun x2 .. (trm_fun xn t) ..))
  (at level 69, x1, x2, xn at level 0) : trm_scope.

Notation "'LetFun' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

Notation "'LetFun' f x1 x2 .. xn ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 .. (trm_fun xn t1) ..)) t2)
  (at level 69, f, x1, x2, xn at level 0) : trm_scope.

Notation "'LetFix' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

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

Notation "'ref t" :=
  (val_ref t)
  (at level 67) : trm_scope.

Notation "'! t" :=
  (val_get t)
  (at level 67) : trm_scope.

Notation "t1 ':= t2" :=
  (val_set t1 t2)
  (at level 67) : trm_scope.

Notation "t1 '+ t2" :=
  (val_add t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '- t2" :=
  (val_sub t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '= t2" :=
  (val_eq t1 t2)
  (at level 69) : trm_scope.


(* Demo for the above notation:

  Open Scope trm_scope.
  Import NotationForVariables.
  Definition test := Fun 'x := val_unit.
  Definition test2 := Fun 'x 'y 'z := val_unit.
  Definition test1 := Fix 'f 'x1 := val_unit.
  Definition test2 := Fix 'f 'x1 'x2 := val_unit.
  Print test2.
  Definition test1 := LetFix 'f 'x1 := val_unit in val_unit.
  Definition test2 := LetFix 'f 'x1 'x2 := val_unit in val_unit.
*)

End NotationForTerms.



