Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
Generalizable Variables A.

Implicit Types r : loc.

Require Import Sek_ml.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stack L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)

(*

Definition Stack A `{EA:Enc A} (L:list A) r :=
  \exists n,
      r ~~~> `{ items' := L; size' := n }
   \* \[ n = length L ].


Lemma Stack_eq : forall r A `{EA:Enc A} (L:list A),
  (r ~> Stack L) =
  (\exists n, r ~~~> `{ items' := L; size' := n } \* \[ n = length L ]).
Proof using. auto. Qed.

Arguments Stack_eq : clear implicits.

*)