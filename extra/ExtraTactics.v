



(*

(* ********************************************************************** *)
(* * Database for registering a specification for each program. *)

(* ---------------------------------------------------------------------- *)
(* ** Database of specifications used by [xapp], through tactic [xspec] *)

(** A name for the database *)

Definition database_spec := True.

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : charac.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xapp_basic_prepare tt :=
  fail "not instantiated".

Ltac xspec_context G := (* refined only in LambdaCFLifted *)
  fail "not instantiated".

Ltac xspec_registered G :=
  ltac_database_get database_spec G.

Ltac xspec_database G :=
   first [ xspec_registered G | xspec_context G ].

Ltac xspec_base tt :=
  match goal with
  | |- ?G => xspec_database G
  end.

Ltac xspec_core tt :=
  xapp_basic_prepare tt;
  xspec_base tt.

Tactic Notation "xspec" :=
  xspec_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Registering specifications for lifted triple *)

Notation "'Register_Spec' f" := (Register_goal (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : charac.


(* ---------------------------------------------------------------------- *)
(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Triple_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide Triple_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.




(* ********************************************************************** *)
(* * Auxiliary tactics *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] *)

Ltac xlocal' :=
  try solve [ apply is_local_local ].
  (*   | apply is_local_wp_triple ]. *)


(*--------------------------------------------------------*)
(* ** [xdecode_args] : used internally *)

Ltac xdecode_arg v :=
  let W := constr:(decode v) in
  let W' := (eval simpl decode in W) in
  match W' with Dyn ?V' =>
    change (trm_val v) with (trm_val (enc V'))
  end.

Ltac xdecode_args_from_trms ts :=
  match ts with
  | (trm_val (enc ?V))::?ts' => xdecode_args_from_trms ts'
  | (trm_val ?v)::?ts' => xdecode_arg v; xdecode_args_from_trms ts'
  | nil => idtac
  end.

Ltac xdecode_args tt :=
  match goal with |- Triple (trm_apps ?f ?ts) ?H ?Q =>
    xdecode_args_from_trms ts end.


(*--------------------------------------------------------*)
(* ** [xeq_encs] : used internally *)

(** [xeq_encs] solves goal of the form [ [`V1; ..; `VN] = encs ?VS ]. *)

Lemma encs_nil :
  encs nil = @nil val.
Proof using. auto. Qed.

Lemma encs_cons : forall `{EA:Enc A} (V:A) (VS:dyns),
  encs ((Dyn V)::VS) = (enc V)::(encs VS).
Proof using. auto. Qed.

Hint Rewrite <- @encs_nil @encs_cons : rew_encs.

Tactic Notation "rew_encs" :=
  autorewrite with rew_encs.

Ltac xeq_encs_core tt :=
  rew_encs; reflexivity.

(* DEPRECATED
match goal with |- ?vs = encs ?Vs => applys (refl_equal (encs (decodes vs))) end.*)

Tactic Notation "xeq_encs" :=
  xeq_encs_core tt.


(*--------------------------------------------------------*)
(* ** [rew_dyn] *)

Hint Rewrite dyn_to_val_dyn_make @enc_decode enc_dyn_make : rew_dyn.
 (* DEPRECATEd: was enc_dyn_eq *)

(** The encoding of a dynamic value [V] is the same as the encoding of V *)

Tactic Notation "rew_dyn" :=
  autorewrite with rew_dyn; simpl dyn_value.
Tactic Notation "rew_dyn" "in" hyp(H) :=
  autorewrite with rew_dyn in H; simpl dyn_value in H.
Tactic Notation "rew_dyn" "in" "*" :=
  autorewrite with rew_dyn in *; simpl dyn_value in *.



(* ********************************************************************** *)
(* * Tactics for computing characteristic formulae *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_remove_encs f :=
  constr:(f).

Ltac xcf_get_fun_from_goal tt :=
  match goal with |- @Triple (trm_apps (trm_val ?f) _) _ _ _ _ => constr:(f) end.

Ltac xcf_get_fun tt :=
  xcf_get_fun_from_goal tt.

Ltac xcf_reveal_fun tt :=
  try (let f := xcf_get_fun tt in
       first [ unfold f
             | match goal with H: f = _ |- _ => rewrite H end ]).

Ltac xcf_trm n :=
 (*  applys triple_trm_of_wp_iter n; [ xcf_post tt ]. *) fail.

Ltac xcf_post tt :=
  simpl; rew_enc_dyn.

Ltac xcf_basic_fun n f':=
  let f := xcf_get_fun tt in
  match f with
  | val_fixs _ _ _ =>
      applys Triple_apps_fixs_of_Wp f';
      [ try unfold f'; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | try xeq_encs
      | reflexivity
      | xcf_post tt ]
  end.

Ltac xcf_fun n :=
  let f' := xcf_get_fun tt in
  xcf_reveal_fun tt;
  (*rew_trms_vals;*)
  xcf_basic_fun n f'.

Ltac xcf_prepare_args tt :=
  try xdecode_args tt.

Ltac xcf_core n :=
  intros; first [ xcf_fun n | xcf_trm n ].

Tactic Notation "xcf" :=
  xcf_core 100%nat.

Tactic Notation "xcf_depth" constr(depth) :=
  xcf_core depth.





(* ********************************************************************** *)
(* * Tactics for manipulating characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt :=
  fail "not instantiated".

Tactic Notation "xseq" :=
  xseq_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Lemma xlet_lemma : forall Q1 (F1:formula) (F2:val->formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> wp_let F1 F2 Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.

Ltac xlet_core tt :=
  applys xlet_lemma; [ xlocal' | | ].

Tactic Notation "xlet" :=
  xlet_core tt.

Ltac xlet_as_core X :=
  xlet_core tt; [ | intros X ].

Tactic Notation "xlet" "as" simple_intropattern(X) :=
  xlet_as_core X.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xif] *)

Ltac xif_post tt :=
  rew_bool_eq.

Ltac xif_core tt :=
  fail "not instantiated".

Tactic Notation "xif" :=
  xif_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt :=
  fail "not instantiated".

Tactic Notation "xfail" :=
  xfail_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Ltac hpull_cont tt :=
  fail "not instantiated".
Ltac hsimpl_cont tt :=
  fail "not instantiated".
Ltac xapp_let_cont tt :=
  fail "not instantiated".
Ltac xapp_as_let_cont tt :=
  fail "not instantiated".
Ltac xapps_let_cont tt :=
  fail "not instantiated".
Ltac xapp_template xlet_tactic xapp_tactic xlet_cont :=
  fail "not instantiated".
Ltac xapp_with_args E cont_xapply :=
  fail "not instantiated".
Ltac xapp_basic E cont_post tt :=
  fail "not instantiated".

Ltac xapp_debug tt :=
  xapp_basic_prepare tt;
  xapp_with_args __ ltac:(fun H => generalize H).

Ltac xapp_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ idcont) ltac:(xapp_let_cont).

Ltac xapp_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E idcont) ltac:(xapp_let_cont).

Ltac xapp_as_core X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic __ idcont) ltac:(xapp_as_let_cont).

Ltac xapp_arg_as_core E X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic E idcont) ltac:(xapp_as_let_cont).

Ltac xapps_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ hpull_cont) ltac:(xapps_let_cont).

Ltac xapps_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E hpull_cont) ltac:(xapps_let_cont).

Tactic Notation "xapp" :=
  xapp_core tt.
Tactic Notation "xapp" "~" :=
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  :=
  xapp; auto_star.

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

Tactic Notation "xapps" :=
  xapps_core tt.
Tactic Notation "xapps" "~" :=
  xapps; auto_tilde.
Tactic Notation "xapps" "*" :=
  xapps; auto_star.

Tactic Notation "xapps" constr(E) :=
  xapps_arg_core E.
Tactic Notation "xapps" "~" constr(E) :=
  xapps E; auto_tilde.
Tactic Notation "xapps" "*" constr(E) :=
  xapps E; auto_star.

Tactic Notation "xapp" "as" simple_intropattern(X) :=
  xapp_as_core X.
Tactic Notation "xapp" "~" "as" simple_intropattern(X) :=
  xapp as X; auto_tilde.
Tactic Notation "xapp" "*" "as" simple_intropattern(X) :=
  xapp as X; auto_star.

Tactic Notation "xapp" constr(E) "as" simple_intropattern(X) :=
  xapp_arg_as_core E X.
Tactic Notation "xapp" "~" constr(E) "as" simple_intropattern(X) :=
  xapp E as X; auto_tilde.
Tactic Notation "xapp" "*" constr(E) "as" simple_intropattern(X) :=
  xapp E as X; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xval] and [xvals] *)

Ltac xval_core tt :=
  fail "not instantiated".
Ltac xval_as_core X :=
  fail "not instantiated".
Ltac xvals_core tt :=
  fail "not instantiated".

Tactic Notation "xval" :=
  xval_core tt.
Tactic Notation "xval" "~" :=
  xval; auto_tilde.
Tactic Notation "xval" "*"  :=
  xval; auto_star.

Tactic Notation "xvals" :=
  xvals_core tt.
Tactic Notation "xvals" "~" :=
  xvals; auto_tilde.
Tactic Notation "xvals" "*" :=
  xvals; auto_star.

Tactic Notation "xval" "as" simple_intropattern(X) :=
  xval_as_core X.
Tactic Notation "xval" "~" "as" simple_intropattern(X) :=
  xval as X; auto_tilde.
Tactic Notation "xval" "*" "as" simple_intropattern(X) :=
  xval as X; auto_star.




(* ********************************************************************** *)
(* * Tactics for loops *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwhile] *)

Ltac xwhile_intros_all R LR HR :=
  fail "not instantiated".
Ltac xwhile_intros R :=
  fail "not instantiated".
Ltac xwhile_basic xwhile_intros_tactic :=
  fail "not instantiated".
Ltac xwhile_core xwhile_tactic :=
  fail "not instantiated".

Tactic Notation "xwhile" "as" ident(R) :=
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros R)).

Tactic Notation "xwhile" "as" ident(R) ident(LR) ident(HR) :=
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros_all R LR HR)).





(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] demo

Lemma xapp_lemma : forall t H `{EA:Enc A} (Q:A->hprop),
  Triple t H Q ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M. applys local_erase'. rewrite~ <- Triple_eq_himpl_Wp_triple.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.

 *)







*)


(* [xapp_lemma'] is only used for calling [xspec] directly on a goal
   that is not well_suited TODO: use [xapp_spec] instead. *)
Lemma xapp_lemma' : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M1 M2. applys Local_erase.
  hchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp_Triple.
  applys* Triple_ramified_frame. hsimpl.
Qed.

Ltac xspec_pre tt :=
  first
    [ match goal with |- Triple _ _ _ => idtac end
    | match xgoal_code_without_iswp tt with (Wp_app _) => eapply xapp_lemma' end ].
