

(* TODO: not used, to update

(* ---------------------------------------------------------------------- *)
(** Reformulation of the rule for N-ary functions *)

Definition spec_funs (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:vals), length xs = length Xs ->
    triple (substn xs Xs t1) ===> triple (trm_apps F Xs).

Lemma spec_funs_val_funs : forall xs t1,
  var_distinct xs ->
  xs <> nil ->
  spec_funs xs t1 (val_funs xs t1).
Proof using. introv D N L M. applys* rule_apps_funs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Reformulation of the rule for N-ary recursive functions *)

Definition spec_fixs (f:var) (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:vals), length xs = length Xs ->
    triple (subst1 f F (substn xs Xs t1)) ===> triple (trm_apps F Xs).

Lemma spec_fixs_val_fixs : forall f xs t1,
  var_distinct (f::xs) ->
  xs <> nil ->
  spec_fixs f xs t1 (val_fixs f xs t1).
Proof using. introv D N L M. applys* rule_apps_fixs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of one argument *)

Lemma rule_app_fun : forall x F V t1 H Q,
  F = (val_fun x t1) ->
  triple (subst x V t1) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_fun. }
Qed.

Definition spec_fun (x:var) (t1:trm) (F:val) :=
  forall X, triple (subst x X t1) ===> triple (trm_app F X).

Lemma spec_fun_val_fun : forall x t1,
  spec_fun x t1 (val_fun x t1).
Proof using. introv. intros X H Q M. applys* rule_app_fun. Qed.

Lemma rule_fun_spec : forall x t1 H Q,
  (forall (F:val), spec_fun x t1 F -> H ==> Q F) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fun x t1).
  { applys spec_fun_val_fun. }
  { applys~ rule_fun. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Recursive functions of one argument *)

Lemma rule_app_fix : forall f x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst f F (subst x V t1)) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_fix. }
Qed.

Definition spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X, triple (subst f F (subst x X t1)) ===> triple (trm_app F X).

Lemma spec_fix_val_fix : forall f x t1,
  spec_fix f x t1 (val_fix f x t1).
Proof using. introv. intros X H Q M. applys* rule_app_fix. Qed.

Lemma rule_fix_spec : forall f x t1 H Q,
  (forall (F:val), spec_fix f x t1 F -> H ==> Q F) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fix f x t1).
  { applys spec_fix_val_fix. }
  { applys~ rule_fix. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of two arguments *)

Notation "'val_fun2' x1 x2 t" := (val_fun x1 (trm_fun x2 t))
  (at level 69, x1 ident, x2 ident, only parsing).

Lemma red_app_fun2 : forall m1 m2 vf v1 v2 x1 x2 t r,
  vf = val_fun2 x1 x2 t ->
  red m1 (subst x2 v2 (subst x1 v1 t)) m2 r ->
  x1 <> x2 ->
  red m1 (vf v1 v2) m2 r.
Proof using.
  hint red_val.
  introv E M N. subst. applys~ red_app_arg.
  { applys~ red_app_fun. simpl. case_if. applys red_fun. }
  { applys~ red_app_fun. }
Qed.

Definition spec_fun2 (x1 x2:var) (t1:trm) (F:val) :=
  forall X1 X2, triple (subst x2 X2 (subst x1 X1 t1)) ===> triple (F X1 X2).

Lemma rule_app_fun2 : forall x1 x2 F V1 V2 t1 H Q,
  F = val_fun2 x1 x2 t1 ->
  x1 <> x2 ->
  triple (subst x2 V2 (subst x1 V1 t1)) H Q ->
  triple (F V1 V2) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys* red_app_fun2. }
Qed.

Lemma spec_fun2_val_fun2 : forall x1 x2 t1,
  x1 <> x2 ->
  spec_fun2 x1 x2 t1 (val_fun2 x1 x2 t1).
Proof using. introv. intros X1 X2 H Q M. applys* rule_app_fun2. Qed.

*)



(* ---------------------------------------------------------------------- *)
(** Combination of [rule_let] and [rule_fun] or [rule_fix] *)


Lemma rule_let_fun : forall f x t1 t2 H Q,
  (forall (F:val), spec_fun x t1 F -> triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_fun x t1) t2) H Q.
Proof using.
  introv M. applys rule_let (fun F => \[spec_fun x t1 F] \* H).
  { applys rule_fun. introv HF. hsimpl~. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val), spec_fix f x t1 F -> triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M. applys rule_let (fun F => \[spec_fix f x t1 F] \* H).
  { applys rule_fix. introv HF. hsimpl~. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.

Lemma rule_let_fun2 : forall f x1 x2 t1 t2 H Q,
  (forall (F:val), spec_fun2 x1 x2 t1 F -> triple (subst f F t2) H Q) ->
  x1 <> x2 ->
  triple (trm_let f (trm_fun x1 (trm_fun x2 t1)) t2) H Q.
Proof using.
  introv M N. applys rule_let (fun F => \[spec_fun2 x1 x2 t1 F] \* H).
  { applys rule_func_val. hsimpl. applys~ spec_fun2_val_fun2. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.


================
LIFTED




(* ********************************************************************** *)
(* * Bonus *)

(* DEPRECATED?

(* ---------------------------------------------------------------------- *)
(** Reformulation of rule for N-ary functions *)

Definition Spec_funs (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:dyns), length xs = length Xs ->
    Triple (Substn xs Xs t1) ===> Triple (trm_apps F (encs Xs)).

Lemma spec_funs_val_funs : forall xs t1,
  var_distinct xs ->
  xs <> nil ->
  Spec_funs xs t1 (val_funs xs t1).
Proof using. introv D N E M. applys* Triple_apps_funs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Reformulation of rule for N-ary recursive functions *)

Definition Spec_fixs (f:var) (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:dyns), length xs = length Xs ->
    Triple (subst1 f F (Substn xs Xs t1)) ===> Triple (trm_apps F (encs Xs)).

Lemma Spec_fixs_val_fixs : forall f xs t1,
  var_distinct (f::xs) ->
  xs <> nil ->
  Spec_fixs f xs t1 (val_fixs f xs t1).
Proof using. introv D N L M. applys* Triple_apps_fixs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of one argument *)

(* TODO: upper case arguments that are encoded *)

Lemma Triple_app_fun : forall x F V t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fun x t1) ->
  Triple (subst x V t1) H Q ->
  Triple (trm_app F V) H Q.
Proof using. introv EF M. applys* triple_app_fun. Qed.

Definition Spec_fun (x:var) (t1:trm) (F:val) :=
  forall X, Triple (subst x X t1) ===> Triple (trm_app F X).

Lemma Spec_fun_val_fun : forall x t1,
  Spec_fun x t1 (val_fun x t1).
Proof using. introv. intros X H Q M. applys* Triple_app_fun. Qed.

Lemma Triple_fun_spec : forall x t1 H (Q:func->hprop),
  (forall (F:val), Spec_fun x t1 F -> H ==> Q F) ->
  Triple (trm_fun x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fun x t1).
  { applys Spec_fun_val_fun. }
  { applys~ Triple_fun. }
Qed.

Lemma Triple_let_fun : forall f x t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  (forall (F:val), Spec_fun x t1 F -> Triple (subst f F t2) H Q) ->
  Triple (trm_let f (trm_fun x t1) t2) H Q.
Proof using.
  introv M. applys Triple_let (fun F => \[Spec_fun x t1 F] \* H).
  { applys Triple_fun_spec. introv HF. hsimpl~. }
  { intros F. applys Triple_extract_hprop. applys M. }
Qed.

(* ---------------------------------------------------------------------- *)
(** Recursive functions of one argument *)

Lemma Triple_app_fix : forall f x F V t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fix f x t1) ->
  Triple (subst f F (subst x V t1)) H Q ->
  Triple (trm_app F V) H Q.
Proof using. introv EF M. applys* triple_app_fix. Qed.

Definition Spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X, Triple (subst f F (subst x X t1)) ===> Triple (trm_app F X).

Lemma Spec_fix_val_fix : forall f x t1,
  Spec_fix f x t1 (val_fix f x t1).
Proof using. introv. intros X H Q M. applys* Triple_app_fix. Qed.

Lemma Triple_fix_spec : forall f x t1 H (Q:func->hprop),
  (forall (F:val), Spec_fix f x t1 F -> H ==> Q F) ->
  Triple (trm_fix f x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fix f x t1).
  { applys Spec_fix_val_fix. }
  { applys~ Triple_fix. }
Qed.

Lemma Triple_let_fix : forall f x t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  (forall (F:val), Spec_fix f x t1 F -> Triple (subst f F t2) H Q) ->
  Triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M. applys Triple_let (fun F => \[Spec_fix f x t1 F] \* H).
  { applys Triple_fix_spec. introv HF. hsimpl~. }
  { intros F. applys Triple_extract_hprop. applys M. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Derived rules *)

Lemma Triple_if' : forall t0 t1 t2 H (Q1:bool->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  Triple t1 (Q1 true) Q ->
  Triple t2 (Q1 false) Q ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M0 M1 M2. applys* Triple_if. { intros b. case_if*. }
Qed.

Lemma Triple_let_val : forall A1 `{Enc A1} (V1:A1) x v1 t2 H A `{EA: Enc A} (Q:A->hprop),
  v1 = enc V1 ->
  (forall X, X = V1 -> Triple (Subst x (Dyn X) t2) H Q) ->
  Triple (trm_let x (trm_val v1) t2) H Q.
Proof using.
  introv E M. applys triple_let_val. intros X EX. subst. applys~ M.
Qed.

*)

(* ---------------------------------------------------------------------- *)
(** Other rules for loops *)

(*
Lemma Triple_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.

Lemma Triple_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2 H,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* \Top) ->
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q) ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) H Q.

Lemma Triple_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  (fun r => \* H) ===> (Q \*+ \Top) ->
  triple (trm_for x n1 n2 t3) H Q.

Lemma Triple_for_le : forall Q1 x n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst x n1 t3) H Q1 ->
  triple (trm_for x (n1+1) n2 t3) (Q1 val_unit) Q ->
  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]) ->
  triple (trm_for x n1 n2 t3) H Q.

Lemma Triple_for_inv : forall (I:int->hprop) H' x n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 ->
     triple (subst x i t3) (I i) (fun r => I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
*)
