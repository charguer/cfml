Set Implicit Arguments.


From compcert Require Coqlib Maps Integers Floats.
From compcert Require Import Maps Errors SimplExpr Values Memory AST Globalenvs Events Ctypes Clight.




(* We define an omni-small-step semantics for CLight *)

(* TODO *)

(** * Non-CPS omnismall step for Clight *)
Section Clight_OMNI.

  Variant state : Type :=
    State
      (s : statement)
      (e : env)
      (le : temp_env)
      (m : mem) : state.

  Definition pc : Type := state -> Prop.

  Implicit Type P : pc.

  Variable ge: genv.

  Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

  Inductive step : state -> pc -> Prop :=
  | step_assign: forall a1 a2 e le m loc ofs bf v2 v m' P,
      eval_lvalue ge e le m a1 loc ofs bf ->
      eval_expr ge e le m a2 v2 ->
      Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      P (State Sskip e le m') ->
      step (State (Sassign a1 a2) e le m) P

  | step_set:   forall id a e le m v P,
      eval_expr ge e le m a v ->
      P (State Sskip e (PTree.set id v le) m) ->
      step (State (Sset id a) e le m) P

  | step_call_internal:   forall optid a al e le m tyargs tyres cconv vf vargs fd P
                            e' le' m1 P',
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Globalenvs.Genv.find_funct ge vf = Some (Internal fd) ->
      type_of_fundef (Internal fd) = Tfunction tyargs tyres cconv ->
      function_entry fd vargs m e' le' m1 ->
      step (State fd.(fn_body) e' le' m1) P' ->
      (forall st', P' st' -> step st' P) ->
      step (State (Scall optid a al) e le m) P

  | step_builtin: forall optid ef tyargs al e le m vargs t vres m' P,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      P (State Sskip e (set_opttemp optid vres le) m') ->
      step (State (Sbuiltin optid ef tyargs al) e le m) P.

(*


  | step_seq:  forall f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_continue_seq: forall f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
  | step_break_seq: forall f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)

  | step_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if b then s1 else s2) k e le m)

  | step_loop: forall f s1 s2 k e le m,
      step (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
  | step_break_loop1:  forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_loop2: forall f s1 s2 k e le m,
      step (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
  | step_break_loop2: forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)

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
