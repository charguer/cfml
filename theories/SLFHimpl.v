(**

Separation Logic Foundations

Chapter: "Himpl".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import Semantics. 
(* TODO move *)
  Module CoercionsFromStrings.
  Coercion string_to_var (x:string) : var := x.
  End CoercionsFromStrings.
  Arguments fmap_single {A} {B}.
  Arguments fmap_union {A} {B}.
  Arguments fmap_disjoint {A} {B}.

  Import NotationForVariables NotationForTerms CoercionsFromStrings.

Close Scope fmap_scope.
