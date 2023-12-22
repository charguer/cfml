Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibList.

Require Import ListIterator_ml.

(**************************************)
(** ListIterator *)

Definition ListIterator A {EA:Enc A} (L:list A) it := it ~~> L.

Lemma of_list_spec : forall A (EA:Enc A) (IA:Inhab A) (L:list A),
  SPEC (of_list L)
    PRE (\$1)
    POST (fun lit => lit ~> ListIterator L).
Proof. xcf_go. Qed.

Hint Extern 1 (RegisterSpec of_list) => Provide of_list_spec.

Lemma finished_spec : forall A (EA:Enc A) (IA:Inhab A) (L:list A) (lit:t_ A),
  SPEC (finished lit)
    PRE (\$1)
    INV (lit ~> ListIterator L)
    POST \[= isTrue (L = nil)].
Proof. xunfold ListIterator. xcf_go*. Qed.

Hint Extern 1 (RegisterSpec finished) => Provide finished_spec.

Lemma get_spec : forall A (EA:Enc A) (IA:Inhab A) (L:list A) (lit:t_ A),
  L <> nil ->
  SPEC (get lit)
    PRE (\$1)
    INV (lit ~> ListIterator L)
    POST (fun x => \exists LS, \[L = x::LS]).
Proof. xunfold ListIterator. xcf_go*. Qed.

Hint Extern 1 (RegisterSpec get) => Provide get_spec.

Lemma get_and_move_spec : forall A (EA:Enc A) (IA:Inhab A) (L:list A) (lit:t_ A),
  L <> nil ->
  SPEC (get_and_move lit)
    PRE (\$1 \* lit ~> ListIterator L)
    POST (fun x => \exists L', lit ~> ListIterator L' \* \[L = x::L'] ).
Proof. xunfold ListIterator. xcf_go*. Qed.

Hint Extern 1 (RegisterSpec get_and_move) => Provide get_and_move_spec.

Lemma move_spec : forall A (EA:Enc A) (IA:Inhab A) (L:list A) (lit:t_ A),
  L <> nil ->
  SPEC (move lit)
    PRE(\$2 \* lit ~> ListIterator L)
    POSTUNIT (\exists x L', lit ~> ListIterator L' \* \[L = x::L'] ).
Proof.
  xcf_go*.
  (*
  xapp (>> get_and_move_spec A EA IA L lit H).
  xgo*.*)
Qed.

Hint Extern 1 (RegisterSpec move) => Provide move_spec.
