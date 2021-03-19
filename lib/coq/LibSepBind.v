(**

This file describes the representation of binders and contexts.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require LibListExec.
From TLC Require Export LibString LibList LibCore.
From CFML Require Import LibSepFmap LibSepTLCbuffer.
Module Fmap := LibSepFmap.
From CFML Require Export LibSepVar.
Open Scope string_scope.
Generalizable Variables A.


(* ********************************************************************** *)
(* * Binders *)

(** A binder is either a variable or the anonymous binder. *)

Inductive bind : Type :=
  | bind_anon : bind
  | bind_var : var -> bind.

(** Variables and strinsg can be coerced to binders. *)

Coercion bind_var : var >-> bind.
Coercion bind_var' (x:string) : bind := bind_var x.


(* ********************************************************************** *)
(* * List of binders *)


(** [var_fixs f xs n] asserts that [f::xs] consists of [n+1]
    distinct variables. *)

Definition var_fixs (f:bind) (xs:vars) (n:nat) : Prop :=
     match f with
     | bind_anon => var_distinct xs
     | bind_var x => var_distinct (x::xs)
     end
  /\ length xs = n
  /\ xs <> nil.

(** Computable version of [var_fixs] *)

Definition var_fixs_exec (f:bind) (xs:vars) (n:nat) : bool :=
     LibNat.beq n (LibListExec.length xs)
  && LibListExec.is_not_nil xs
  && match f with
     | bind_anon => var_distinct_exec xs
     | bind_var x => var_distinct_exec (x::xs)
     end.

Lemma var_fixs_exec_eq : forall f xs (n:nat),
  var_fixs_exec f xs n = isTrue (var_fixs f xs n).
Proof using.
  intros. unfold var_fixs_exec, var_fixs.
  rewrite LibNat.beq_eq.
  rewrite LibListExec.is_not_nil_eq.
  rewrite LibListExec.length_eq.
  destruct f as [|x]; rewrite var_distinct_exec_eq; extens; rew_istrue; iff*.
Qed.


(* ********************************************************************** *)
(* * Contexts *)

Module Ctx.

(* ---------------------------------------------------------------------- *)
(** Definition of contexts *)

(** A context associate variables with values. *)

(** [ctx] describes a list of bindings *)

Definition ctx (A:Type) : Type :=
  list (var * A).

(* ---------------------------------------------------------------------- *)
(** Operations of contexts *)

(** [dom E] gives the list of variables bound by [E] *)

Fixpoint dom A (E:ctx A) : vars :=
  match E with
  | nil => nil
  | (y,v)::E' => y::(dom E')
  end.

(** [empty] describes the empty context *)

Definition empty A : ctx A :=
  @nil _.

Arguments empty {A}.

(** [add z v E] is defined as:
    - [E] if [z] is the anonymous binder
    - [E] extended with the pair [(x,v)] if [z] is a variable [x]. *)

Definition add A (z:bind) (v:A) (E:ctx A) : ctx A :=
  match z with
  | bind_anon => E
  | bind_var x => (x,v)::E
  end.

(** [one z v] is a shorthand for [add z v empty] *)

Definition one A (z:bind) (v:A) : ctx A :=
  add z v empty.

(** [rem x E] removes all bindings on [x] stored in [E] *)

Fixpoint rem_var A (x:var) (E:ctx A) : ctx A :=
  match E with
  | nil => nil
  | (y,v)::E' =>
      let E'' := rem_var x E' in
      if var_eq x y then E'' else (y,v)::E''
  end.

Definition rem A (z:bind) (E:ctx A) : ctx A :=
  match z with
  | bind_anon => E
  | bind_var x => rem_var x E
  end.

(** [lookup x E] returns
    - [None] if [x] is not bound in [E]
    - [Some v] if [x] is bound to [v] in [E]. *)

Fixpoint lookup A (x:var) (E:ctx A) : option A :=
  match E with
  | nil => None
  | (y,v)::E' => if var_eq x y
                   then Some v
                   else lookup x E'
  end.

(** [fresh x E] asserts that [x] is not bound in [E] *)

Definition fresh A (x:var) (E:ctx A) : Prop :=
  lookup x E = None.

(** More operations follow, to support pattern matching *)

(** [rem_vars xs E] removes several variables from [E]. *)

Fixpoint rem_vars A (xs:list var) (E:ctx A) : ctx A :=
  match xs with
  | nil => E
  | x::xs' => rem_vars xs' (rem_var x E)
  end.

(* Alternative definition to [rem_vars] (not tail-recursive) *)

Fixpoint rem_vars' A (xs:list var) (E:ctx A) : ctx A :=
  match xs with
  | nil => E
  | x::xs' => rem_var x (rem_vars' xs' E)
  end.

(** [one_var x v] consists of a single binding from variable [x]
    to the value [v]. *)

Definition one_var A (x:var) (v:A) : ctx A :=
  (x,v)::nil.

(** [combine xs vs] binds the variables [xs] to the values [vs].
    The two lists should have equal lengths, and the [xs] should be distinct
    from each others. *)

Definition combine A (xs:list var) (vs:list A) : ctx A :=
  LibListExec.combine xs vs.

(** [rev E] reverses the order of the bindings in [E]. *)

Definition rev A (E:ctx A) : ctx A :=
  LibListExec.rev E.

(** [app E1 E2] appends two contexts.
    Binders from [E1] may shadow those from [E2]. *)

Definition app A (E1 E2:ctx A) : ctx A :=
  LibListExec.app E1 E2.

(** [lookup_or_arbitrary x E] returns
    - [v] is [x] is bound to [v] in [E],
    - [arbitrary] if [x] is not bound in [E]. *)

Definition lookup_or_arbitrary A `{Inhab A} (x:var) (E:ctx A) : A :=
  match lookup x E with
  | None => arbitrary
  | Some v => v
  end.


(* ---------------------------------------------------------------------- *)
(** Properties of operations on contexts *)

Section CtxOps.
Variables (A : Type).
Implicit Type (E : ctx A).


(* ---------------------------------------------------------------------- *)
(** Lemmas to reintroduce contexts *)

Lemma nil_eq_ctx_empty :
  @nil (prod var A) = empty.
Proof using. auto. Qed.

Lemma cons_eq_ctx_add : forall x v E,
  (x,v)::E = add x v E.
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of operations on contexts  *)

(** [dom] *)

Lemma dom_eq_nil_inv : forall E,
  dom E = nil ->
  E = empty.
Proof using. introv M. destruct E as [|(x,v) E']; auto_false. Qed.

Lemma dom_add : forall E (x:var) X,
  dom (add x X E) = x :: dom E.
Proof using. auto. Qed.

(** [app] *)

Lemma app_empty_l : forall E,
  app empty E = E.
Proof using. intros. unfold app, empty. rewrite LibListExec.app_eq. rew_list~. Qed.

Lemma app_empty_r : forall E,
  app E empty = E.
Proof using. intros. unfold app, empty. rewrite LibListExec.app_eq. rew_list~. Qed.

Lemma app_rev_add : forall E1 E2 x X,
   app (LibList.rev E1) (add x X E2)
 = app (LibList.rev (add x X E1)) E2.
Proof using.
  intros. unfolds app. unfolds add.
  destruct x as [|x]. auto.
  rewrite LibListExec.app_eq. rew_list~.
Qed.

(** [fresh] *)

Lemma fresh_inv : forall (x1 x2:var) v E,
  fresh x1 (add x2 v E) ->
  x1 <> x2 /\ fresh x1 E.
Proof using. introv M. unfolds fresh. simpls. case_var~. Qed.

(** [rev] *)

Lemma rev_eq : forall E,
  rev E = LibList.rev E.
Proof using. intros. unfold rev. rewrite~ LibListExec.rev_eq. Qed.

(** [rem_var] and [rem] *)

Lemma rem_var_eq_rem : forall x E,
  rem_var x E = rem x E.
Proof using. auto. Qed.

Lemma rem_anon : forall E,
  Ctx.rem bind_anon E = E.
Proof using. auto. Qed.

Lemma rem_empty : forall z,
  rem z (@empty A) = empty.
Proof using. intros. destruct z as [|x]; auto. Qed.

(** [rem] interacts with [add] *)

Lemma rem_add_same : forall z v E,
  rem z (add z v E) = rem z E.
Proof using.
  intros. destruct z as [|x].
  { auto. }
  { simpl. case_var~. }
Qed.

Lemma rem_add_neq : forall z1 z2 v E,
  z1 <> z2 ->
  rem z1 (add z2 v E) = add z2 v (rem z1 E).
Proof using.
  intros. destruct z2 as [|x2].
  { auto. }
  { destruct z1 as [|x1].
    { auto. }
    { simpl. case_var~. } }
Qed.

(** [rem] interacts with [fresh] *)

Lemma rem_fresh : forall x E,
  fresh x E ->
  rem x E = E.
Proof using.
  introv M. unfold rem. induction E as [|(y,v) E'].
  { auto. }
  { simpls. lets (N1&N2): fresh_inv (rm M). case_var. fequals*. }
Qed.

(** [rem] interact with [rem] and [rem_vars] *)

Lemma rem_var_rem_var : forall x y E,
  rem_var x (rem_var y E) = rem_var y (rem_var x E).
Proof using.
  intros. induction E as [| (z,w) E']; simpl.
  { auto. }
  { repeat case_var; simpl; repeat case_var; auto. { fequals*. } }
Qed.

Lemma rem_var_rem_vars : forall xs x E,
  rem_var x (rem_vars xs E) = rem_vars xs (rem_var x E).
Proof using.
  intros xs. induction xs as [|y xs']; intros; simpl.
  { auto. }
  { rewrite rem_var_rem_var. rewrite~ IHxs'. }
Qed.

(** [rem_vars] *)

Lemma rem_vars_eq_rem_vars' :
  @rem_vars A = @rem_vars' A.
Proof using.
  applys fun_ext_2. intros xs. induction xs as [|x xs']; intros E; simpl.
  { auto. }
  { rewrite <- rem_var_rem_vars. rewrite~ IHxs'. }
Qed.

Lemma rem_vars_nil : forall xs,
  rem_vars xs (nil:ctx A) = nil.
Proof using. intros. induction xs; simpl. { auto. } { rewrite~ IHxs. } Qed.

(** [rem_vars] interacts with [add] *)

Lemma rem_vars_add_mem : forall x v xs E,
  mem x xs ->
  rem_vars xs (Ctx.add x v E) = rem_vars xs E.
Proof using.
  introv M. gen E. induction xs as [|y xs']; intros.
  { inverts M. }
  { simpl. case_var.
    { auto. }
    { inverts M; tryfalse. rewrite cons_eq_ctx_add. rewrite~ IHxs'. } }
Qed.

Lemma rem_vars_add_not_mem : forall x v xs E,
  ~ mem x xs ->
  rem_vars xs (Ctx.add x v E) = add x v (rem_vars xs E).
Proof using.
  introv M. gen E. induction xs as [|y xs']; intros.
  { auto. }
  { simpl. lets (N&M'): not_mem_cons_inv (rm M). case_var.
    rewrite cons_eq_ctx_add. rewrite~ IHxs'. }
Qed.

(* LATER: would it be easier to do all proofs using [rem_vars']? *)

(** [lookup_or_arbitrary] *)

Lemma lookup_or_arbitrary_cons : forall `{Inhab A} x y v (E:ctx A),
  lookup_or_arbitrary x ((y,v)::E) = If x = y then v else lookup_or_arbitrary x E.
Proof using.
  intros. unfold lookup_or_arbitrary. simpl lookup. repeat case_var; auto.
Qed.

Lemma lookup_or_arbitrary_cons_same : forall `{Inhab A} x v (E:ctx A),
  lookup_or_arbitrary x ((x,v)::E) = v.
Proof using. intros. rewrite~ lookup_or_arbitrary_cons. case_if~. Qed.

Lemma lookup_or_arbitrary_cons_neq : forall `{Inhab A} x y v (E:ctx A),
  x <> y ->
  lookup_or_arbitrary x ((y,v)::E) = lookup_or_arbitrary x E.
Proof using. intros. rewrite~ lookup_or_arbitrary_cons. case_if~. Qed.

End CtxOps.

End Ctx.

(* LATER: Coq issue: how to place this rewrite base and tactics inside the
   module and still be able to use it without importing the module? *)

Hint Rewrite Ctx.nil_eq_ctx_empty Ctx.cons_eq_ctx_add Ctx.rem_var_eq_rem : rew_ctx.

Tactic Notation "rew_ctx" :=
  autorewrite with rew_ctx.
Tactic Notation "rew_ctx" "in" hyp(H) :=
  autorewrite with rew_ctx in H.
Tactic Notation "rew_ctx" "in" "*" :=
  autorewrite with rew_ctx in *.
