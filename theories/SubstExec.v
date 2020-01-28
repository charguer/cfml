(**

This file contains a computable definition for [subst].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Semantics.
Open Scope string_scope.

(** [subst_exec] is like [subst] except that it computes with [simpl]. *)

Fixpoint subst_exec (y:var) (w:val) (t:trm) : trm :=
  let aux t :=
    subst_exec y w t in
  let bind_no_capture z t t' :=
    match z with
    | bind_anon => t'
    | bind_var x => if var_eq x y then t else t'
    end in
  let aux_no_capture z t :=
    bind_no_capture z t (aux t) in
  let aux_no_captures xs t :=
    if mem_exec var_eq y xs then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if var_eq x y then trm_val w else t
  | trm_fixs f xs t1 => trm_fixs f xs (bind_no_capture f t1 (aux_no_captures xs t1))
  | trm_constr id ts => trm_constr id (List.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (aux_no_capture z t2)
  | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  | trm_match t0 pts => trm_match (aux t0) (List.map (fun '(pi,ti) =>
       (pi, aux_no_captures (patvars pi) ti)) pts)
  | trm_fail => trm_fail
  end.

(** Proof of equivalence between [subst_exec] and [subst].
    First, a few auxiliary lemmas. Then, then induction. *)

Lemma eq_exec_var_eq : eq_exec var_eq.
Proof using. intros x y. rewrite~ var_eq_spec. Qed.

Lemma if_var_eq_spec : forall x y A (X Y:A),
  (if var_eq x y then X else Y) = (If x = y then X else Y).
Proof using. intros. rewrite var_eq_spec, if_classicT_eq_if_isTrue. auto. Qed.

Lemma mem_exec_var_eq_eq : forall y xs,
  mem_exec var_eq y xs = isTrue (mem y xs).
Proof using. intros. applys mem_exec_eq. applys eq_exec_var_eq. Qed.

Lemma subst_exec_eq_subst :
  subst_exec = subst.
Proof using.
  applys fun_ext_3. intros y w t. induction t using trm_induct; simpl; fequals.
  { rewrite~ if_var_eq_spec. }
  { rewrite mem_exec_var_eq_eq. destruct b; [|try rewrite if_var_eq_spec];
    repeat case_if; tryfalse; auto. }
  { rewrite List_map_eq. applys* map_congr. }
  { destruct b; [|try rewrite if_var_eq_spec];
    repeat case_if; tryfalse; auto. }
  { rewrite List_map_eq. applys~ map_congr. }
  { rewrite if_var_eq_spec. repeat case_if; auto. }
  { rewrite List_map_eq. applys map_congr. intros (pi,ti) Mi. fequals.
    rewrite mem_exec_var_eq_eq. rewrite if_classicT_eq_if_isTrue. case_if*. }
Qed.
