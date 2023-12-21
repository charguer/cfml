(**




!!!DEPRECATED!!!














This file defines tactic notations useful for characteristic formulae

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export Semantics.


(* ---------------------------------------------------------------------- *)
(* ** Database of specifications used by [xapp], through tactic  [xspec] *)

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
(* ** Tactic [xcf] *)

Ltac xcf_trm n :=
  fail "not instantiated".

Ltac xcf_basic_fun n f' :=
  fail "not instantiated".

Ltac xcf_get_fun_remove_encs f :=
  constr:(f).

Ltac xcf_get_fun_from_trm t :=
  match t with
  | trm_apps (trm_val ?f) _ => xcf_get_fun_remove_encs f
  | trm_app ?t1 ?t2 =>
      match t1 with
      | trm_app ?t11 ?t12 => xcf_get_fun_from_trm t1
      | ?f => xcf_get_fun_remove_encs f
      end
  end.

Ltac xcf_get_fun_from_goal tt :=
  fail "not instantiated".

Ltac xcf_get_fun tt :=
  xcf_get_fun_from_goal tt.

Ltac xcf_reveal_fun tt :=
  try (let f := xcf_get_fun tt in
       first [ unfold f
             | match goal with H: f = _ |- _ => rewrite H end ]).

Ltac xcf_prepare_args tt :=
  rew_nary.

Ltac xcf_fun n :=
  xcf_prepare_args tt;
  let f' := xcf_get_fun tt in
  xcf_reveal_fun tt;
  rew_nary;
  rew_trms_vals;
  xcf_basic_fun n f'.

Ltac xcf_core n :=
  intros; first [ xcf_fun n | xcf_trm n ].

Tactic Notation "xcf" :=
  xcf_core 100%nat.

Tactic Notation "xcf_depth" constr(depth) :=
  xcf_core depth.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt :=
  fail "not instantiated".

Tactic Notation "xseq" :=
  xseq_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Ltac xlet_core tt :=
  fail "not instantiated".

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
