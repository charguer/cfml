(**

This file formalizes Hoare Logic:

- definition of Hoare triple (total correctness)
- structural rules for Hoare triples
- reasoning rule for term constructs.

It does not include reasoning rules for primitive operations on the heap,
because these are more naturally expressed directly in Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export Semantics.
Open Scope fmap_scope.



(* ********************************************************************** *)
(** * Definition of Hoare triples *)

Definition hoare (t:trm) (H:state->Prop) (Q:val->state->Prop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.

Implicit Types H : state->Prop.
Implicit Types f : bind.
Implicit Types v w : val.
Implicit Types t : trm.
Implicit Types vs : vals.

(* ---------------------------------------------------------------------- *)
(* ** Tactic [himpl_fold] *)

(** [himpl_fold] applies to a goal of the form [H1 h].
    It searches the context for an assumption of the from [H2 h],
    then replaces the goal with [H1 ==> H2].
    It also deletes the assumption [H2 h]. *)

Ltac himpl_fold_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    applys himpl_inv N; clear N end.

Tactic Notation "himpl_fold" := himpl_fold_core tt.
Tactic Notation "himpl_fold" "~" := himpl_fold; auto_tilde.
Tactic Notation "himpl_fold" "*" := himpl_fold; auto_star.


(* ********************************************************************** *)
(** * Hoare structural rules *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h.
  { himpl_fold~. }
  exists h' v. splits~. { himpl_fold. auto. }
Qed.

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.


(* ********************************************************************** *)
(** * Hoare rules for term constructs *)

Lemma hoare_evalctx : forall C t1 H Q Q1,
  evalctx C ->
  hoare t1 H Q1 ->
  (forall v, hoare (C v) (Q1 v) Q) ->
  hoare (C t1) H Q.
Proof using.
  introv HC M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_evalctx R2. }
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys eval_val. }
  { himpl_fold~. }
Qed.

Lemma hoare_fixs : forall f xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  hoare (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros h Hh. exists. splits.
  { applys~ eval_fixs. }
  { himpl_fold~. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using. introv M. applys hoare_fixs; auto_false. Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using. introv M. applys hoare_fixs; auto_false. Qed.

Lemma hoare_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  hoare (trm_constr id (trms_vals vs)) H Q.
Proof using.
  introv M. intros h Hh. exists h (val_constr id vs). splits.
  { applys eval_constr. }
  { himpl_fold~. }
Qed.

Lemma hoare_constr_trm : forall id ts t1 vs H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (trm_constr id ((trms_vals vs)++(trm_val v)::ts)) (Q1 v) Q) ->
  hoare (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. intros h Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_constr_trm R2. }
Qed.


Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let_trm R2. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using. introv M1 M2. applys* hoare_let. Qed.

Lemma hoare_if_case : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.

Lemma hoare_if_trm : forall Q1 t0 t1 t2 H Q,
  hoare t0 H Q1 ->
  (forall v, hoare (trm_if v t1 t2) (Q1 v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* hoare_evalctx (fun t0 => trm_if t0 t1 t2).
  { constructor. }
Qed.

Lemma hoare_apps_funs : forall xs F vs t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length vs) xs ->
  hoare (substn xs vs t1) H Q ->
  hoare (trm_apps F vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* eval_apps_funs. }
Qed.

Lemma hoare_apps_fixs : forall xs (f:var) F vs t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length vs) xs ->
  hoare (substn (f::xs) (F::vs) t1) H Q ->
  hoare (trm_apps F vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* eval_apps_fixs. }
Qed.

Lemma hoare_while_raw : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* eval_while. }
Qed.

Lemma hoare_for_raw : forall (x:var) (n1 n2:int) t3 H Q,
  hoare (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  hoare (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* eval_for. }
Qed.

Lemma hoare_match : forall v p t1 pts H Q,
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> hoare (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> hoare (trm_match v pts) H Q) ->
  hoare (trm_match v ((p,t1)::pts)) H Q.
Proof using.
  introv M1 M2 Hh. tests C: (exists (G:ctx), Ctx.dom G = patvars p /\ v = patsubst G p).
  { destruct C as (G&DG&Ev). forwards* (h1'&v1&R1&K1): (rm M1).
    exists h1' v1. splits~. { applys~ eval_match_yes R1. } }
  { forwards* (h1'&v1&R1&K1): (rm M2).
    exists h1' v1. splits~. { applys~ eval_match_no R1.
      intros G HG. specializes C G. rew_logic in C. destruct* C. } }
Qed.

Lemma hoare_case_trm : forall t1 pts H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (trm_match v pts) (Q1 v) Q) ->
  hoare (trm_match t1 pts) H Q.
Proof using.
  introv M1 M2. intros h Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_match_trm R2. }
Qed.

