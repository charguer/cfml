Set Implicit Arguments.


From compcert Require Coqlib Maps Integers Floats.
From compcert Require Import Maps Errors SimplExpr Values Memory AST Events Ctypes Clight.




(* We define an omni-small-step semantics for CLight *)

(* TODO *)

Section Clight_OMNI.

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

End Clight_OMNI.
