(**

This file contains common declarations for examples in
lifted Separation Logic, using lifted characteristic formulae.

Author: Arthur Charguéraud.
License: MIT.

*)

From Sep Require Export LambdaSepLifted LambdaCFLifted.
From Sep Require Export LambdaStructLifted.
From TLC Require Export LibList LibListZ.
Open Scope liblist_scope.
Open Scope Z_scope.

(* Open Scope charac. TODO: not needed? *)

Ltac auto_star ::= jauto.


(** Common preambule to be copied:

Set Implicit Arguments.
Generalizable Variables A B.

*)

(** Optional type declarations, e.g.:

Implicit Types p : loc.
Implicit Types n : int.

*)
