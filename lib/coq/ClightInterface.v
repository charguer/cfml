Set Implicit Arguments.


From compcert Require Coqlib Maps Integers Floats.
From compcert Require Import Maps Errors SimplExpr Values Memory AST Globalenvs Events Ctypes Clight ClightBigstep.


Section Bigstep_interface.


  Definition config : Type :=
    Clight.env
    * Clight.temp_env
    * Memory.Mem.mem
    * Clight.statement.

  Definition final_config : Type :=
    Clight.temp_env
    * Memory.mem
    * ClightBigstep.outcome.

  Definition pc : Type := final_config -> Prop.
  Implicit Type Q : pc.


  Variable ge : genv.

  (* [exec_stmt] uncurrified, and with empty trace *)
  Definition exec_stmt' : config -> final_config -> Prop :=
    fun '(e, te, m, s) '(te', m', out) =>
      exec_stmt ge e te m s E0 te' m' out.

  Definition terminates (c : config) : Prop :=
    exists (fc : final_config), exec_stmt' c fc.

  Import Cop Coqlib.

  Inductive omni_exec_stmt: config -> pc -> Prop :=
  | omni_exec_Sskip: forall e le m Q,
      Q (le, m, Out_normal) ->
      omni_exec_stmt (e, le, m, Sskip) Q
  | omni_exec_Sassign:   forall e le m a1 a2 loc ofs bf v2 v m' Q,
      eval_lvalue ge e le m a1 loc ofs bf ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      Q (le, m', Out_normal) ->
      omni_exec_stmt (e, le, m, (Sassign a1 a2)) Q
  | omni_exec_Sset:  forall e le m id a v Q,
      eval_expr ge e le m a v ->
      Q ((PTree.set id v le), m, Out_normal) ->
      omni_exec_stmt (e, le, m, (Sset id a)) Q
  (* | exec_Scall:   forall e le m optid a al tyargs tyres cconv vf vargs f t m' vres, *)
  (*     classify_fun (typeof a) = fun_case_f tyargs tyres cconv -> *)
  (*     eval_expr ge e le m a vf -> *)
  (*     eval_exprlist ge e le m al tyargs vargs -> *)
  (*     Genv.find_funct ge vf = Some f -> *)
  (*     type_of_fundef f = Tfunction tyargs tyres cconv -> *)
  (*     eval_funcall m f vargs t m' vres -> *)
  (*     exec_stmt e le m (Scall optid a al) *)
  (*               t (set_opttemp optid vres le) m' Out_normal *)
  (* | exec_Sbuiltin:   forall e le m optid ef al tyargs vargs t m' vres, *)
  (*     eval_exprlist ge e le m al tyargs vargs -> *)
  (*     external_call ef ge vargs m t vres m' -> *)
  (*     exec_stmt e le m (Sbuiltin optid ef tyargs al) *)
  (*               t (set_opttemp optid vres le) m' Out_normal *)
  | omni_exec_Sseq_1:   forall e le m s1 s2 Q1 Q,
      omni_exec_stmt (e, le, m, s1) Q1 ->
      (forall le1 m1 out, Q1 (le1, m1, out) ->
                 omni_exec_stmt (e, le1, m1, s2) Q) ->
      omni_exec_stmt (e, le, m, (Ssequence s1 s2)) Q
  (* | exec_Sifthenelse: forall e le m a s1 s2 v1 b t le' m' out, *)
  (*     eval_expr ge e le m a v1 -> *)
  (*     bool_val v1 (typeof a) m = Some b -> *)
  (*     exec_stmt e le m (if b then s1 else s2) t le' m' out -> *)
  (*     exec_stmt e le m (Sifthenelse a s1 s2) *)
  (*               t le' m' out *)
  (* | exec_Sreturn_none:   forall e le m, *)
  (*     exec_stmt e le m (Sreturn None) *)
  (*              E0 le m (Out_return None) *)
  (* | exec_Sreturn_some: forall e le m a v, *)
  (*     eval_expr ge e le m a v -> *)
  (*     exec_stmt e le m (Sreturn (Some a)) *)
  (*               E0 le m (Out_return (Some (v, typeof a))) *)
  (* | exec_Sbreak:   forall e le m, *)
  (*     exec_stmt e le m Sbreak *)
  (*              E0 le m Out_break *)
  (* | exec_Sloop_stop1: forall e le m s1 s2 t le' m' out' out, *)
  (*     exec_stmt e le m s1 t le' m' out' -> *)
  (*     out_break_or_return out' out -> *)
  (*     exec_stmt e le m (Sloop s1 s2) *)
  (*               t le' m' out *)
  (* | exec_Sloop_stop2: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out, *)
  (*     exec_stmt e le m s1 t1 le1 m1 out1 -> *)
  (*     out_normal_or_continue out1 -> *)
  (*     exec_stmt e le1 m1 s2 t2 le2 m2 out2 -> *)
  (*     out_break_or_return out2 out -> *)
  (*     exec_stmt e le m (Sloop s1 s2) *)
  (*               (t1**t2) le2 m2 out *)
  (* | exec_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out, *)
  (*     exec_stmt e le m s1 t1 le1 m1 out1 -> *)
  (*     out_normal_or_continue out1 -> *)
  (*     exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal -> *)
  (*     exec_stmt e le2 m2 (Sloop s1 s2) t3 le3 m3 out -> *)
  (*     exec_stmt e le m (Sloop s1 s2) *)
  (*               (t1**t2**t3) le3 m3 out *)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> mem -> val -> Prop :=
  | eval_funcall_internal: forall m f vargs e m1 m2 vres m4 Q,
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      omni_exec_stmt (e, (create_undef_temps f.(fn_temps)), m2, f.(fn_body)) Q ->
        (forall le m3 out, Q (le, m3, out) ->
      outcome_result_value out f.(fn_return) vres m3 ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4) ->
      eval_funcall m (Internal f) vargs m4 vres
  | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall m (External ef targs tres cconv) vargs m' vres.

End Bigstep_interface.


(* We define an omni-small-step semantics for CLight *)

(*** WIP, unusable for now *)

(** * Non-CPS omnismall step for Clight *)
Section Clight_OMNI.

  Definition state : Type := statement * env * temp_env * mem.

  Definition small_pc : Type := state -> Prop.

  Implicit Type P : small_pc.


  Inductive clight_evalctx : (statement -> statement) -> Prop :=
  | clight_evalctx_seq : forall s',
      clight_evalctx (fun s => Ssequence s s')
  | clight_evalctx_loop1 : forall s',
      clight_evalctx (fun s => Sloop s s')
  | clight_evalctx_loop2 : clight_evalctx (fun s => Sloop Sskip s).

  Variable ge: genv.

  Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

  Inductive step : state -> small_pc -> Prop :=
  | step_evalctx : forall C st e le m P' P,
      clight_evalctx C ->
      step (st, e, le, m) P' ->
      (forall '(st', e', le', m'), P' (st', e', le', m') ->
                              P ((C st'), e', le', m')) ->
      step ((C st), e, le, m) P

  | step_assign: forall a1 a2 e le m loc ofs bf v2 v m' P,
      eval_lvalue ge e le m a1 loc ofs bf ->
      eval_expr ge e le m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      P (Sskip, e, le, m') ->
      step ((Sassign a1 a2), e, le, m) P

  | step_set:   forall id a e le m v P,
      eval_expr ge e le m a v ->
      P (Sskip, e, (PTree.set id v le), m) ->
      step ((Sset id a), e, le, m) P

  | step_call_internal:   forall optid a al e le m tyargs tyres cconv vf vargs fd P
                            e' le' m1 P',
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Globalenvs.Genv.find_funct ge vf = Some (Internal fd) ->
      type_of_fundef (Internal fd) = Tfunction tyargs tyres cconv ->
      function_entry fd vargs m e' le' m1 ->
      step (fd.(fn_body), e', le', m1) P' ->
      (forall st', P' st' -> P st') ->
      step ((Scall optid a al), e, le, m) P

  | step_builtin: forall optid ef tyargs al e le m vargs t vres m' P,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      P (Sskip, e, (set_opttemp optid vres le), m') ->
      step ((Sbuiltin optid ef tyargs al), e, le, m) P

  (* | step_seq: forall s1 s2 e le m P' P, *)
  (*     step (s1, e, le, m) P' -> *)
  (*     (forall st, P' st -> *)
  (*            let '(s1', e', le', m') := st in *)
  (*            P ((Ssequence s1' s2), e', le', m')) -> *)
  (*     step ((Ssequence s1 s2), e, le, m) P *)

  | step_skip_seq: forall s e le m P,
      P (s, e, le, m) ->
      step ((Ssequence Sskip s), e, le, m) P

  | step_ifthenelse: forall a s1 s2 e le m v1 b P,
      eval_expr ge e le m a v1 ->
      Cop.bool_val v1 (typeof a) m = Some b ->
      P ((if b then s1 else s2), e, le, m) ->
      step ((Sifthenelse a s1 s2), e, le, m) P

  | step_loop: forall e le m a s P,
      P ((Sifthenelse a (Ssequence s (Swhile a s)) Sskip), e, le, m) ->
      step (Swhile a s, e, le, m) P.

  (* Swhile e s := Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.
     -->
     Sifthenelse e (Ssequence s (Swhile e s)) Sskip (le + proche de cfml)
   *)

(*

  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k e le m v v' m',
      eval_expr e le m a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m')
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

  | step_switch: forall f a sl k e le m v n,
      eval_expr e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      step (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
  | step_continue_switch: forall f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)

  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

  | step_internal_function: forall f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1)

  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')

  | step_returnstate: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m).
 *)


End Clight_OMNI.

Section Clight_eventually.

  Import Clight.
  Definition postcond := state -> Prop.

  Implicit Type st : state.
  Implicit Type tr : trace.
  Implicit Type P : postcond.


  Variable ge: genv.

  (* See CompilationTest.v: the choice was made to follow the semantics of
     [function_entry2] where function parameters are passed as temporaries *)
  Let step := step2 ge.

  (** [eventually' st P] denotes that all executions from state [st],
      eventually reache a state [st'] such that [st'] ∈ [P], with
      empty trace *)
  Inductive eventually' : state -> postcond -> Prop :=
  | eventually'_here : forall st P,
      P st ->
      eventually' st P
  | eventually'_step : forall st P,
      (exists st' , step st E0 st') ->
      (forall st' , step st E0 st' -> eventually' st' P) ->
      eventually' st P.

End Clight_eventually.
