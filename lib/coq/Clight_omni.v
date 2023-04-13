Set Implicit Arguments.


From compcert Require Coqlib Maps Integers Floats.
From compcert Require Import Maps Errors SimplExpr Values Memory AST Events Ctypes Clight.




(* We define an omni-small-step semantics for CLight *)

(* TODO *)

Section Clight_OMNI.

  Definition postcond := state -> trace -> Prop.

  Implicit Type st : state.
  Implicit Type tr : trace.
  Implicit Type P : postcond.


  Variable ge: genv.

  (* See CompilationTest.v: the choice was made to follow the semantics of
     [function_entry2] where function parameters are passed as temporaries *)
  Let step := step2 ge.

  (** [eventually' st tr P] denotes that all executions from state
      [st], with starting trace [tr], eventually reache a state [st']
      with trace [tr'] such that [(st',tr')] ∈ [P] *)
  Inductive eventually' : state -> trace -> postcond -> Prop :=
  | eventually'_here : forall st tr P,
      P st tr ->
      eventually' st tr P
  | eventually'_step : forall st tr P,
      (exists st' tr', step st tr' st') ->
      (forall st' tr', step st tr' st' -> eventually' st' (tr ** tr') P) ->
      eventually' st tr P.

End Clight_OMNI.
