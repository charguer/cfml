Add Rec LoadPath "../../../CompCert" as compcert.
Add Rec LoadPath "../../../CompCert/flocq" as Flocq.
From compcert Require Coqlib Maps Integers Floats Values AST Ctypes Clight.
From compcert Require Import Maps Errors SimplExpr.

(* We define an omni-small-step semantics for CLight *)

(* TOOD *)
