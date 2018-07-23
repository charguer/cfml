

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

