(** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.
Implicit Types n m : int.

Require Import PureStackSized_ml.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** Definition of [r ~> Stack L], which is a notation for [Stack L r], of type
    [hprop] *)

Definition Stack A `{EA:Enc A} (L:list A) (r:t_ A) :=
   r = {| items' := L; size' := length L |}.

Lemma Stack_intro : forall A `{EA:Enc A} (L:list A) (r:t_ A) n,
  r = {| items' := L; size' := n |} ->
  n = length L ->
  Stack L r.
Proof using. intros. unfolds. subst*. Qed.

Lemma Stack_inv : forall A `{EA:Enc A} (L:list A) (r:t_ A),
  Stack L r ->
  items' r = L /\ size' r = length L.
Proof using. introv Hr. unfolds in Hr. subst*. Qed.


(* ********************************************************************** *)
(** ** Verification *)

(** Verification of the code *)

Lemma empty_spec : forall A `{EA:Enc A},
  Stack (@nil A) (@empty A).
Proof using. xcf*. Qed.

Lemma size_spec : forall A `{EA:Enc A} (L:list A) s,
  Stack L s ->
  SPEC_PURE (size s)
    POST (\[= length L]).
Proof using.
  introv Hs. xcf*. lets (_&->):Stack_inv Hs. xvals*.
Qed.

Lemma is_empty_spec : forall A `{EA:Enc A} (L:list A) s,
  Stack L s ->
  SPEC_PURE (is_empty s)
    POST (fun b => \[b = isTrue (L = nil)]).
Proof using.
  introv Hs. xcf*. lets (_&->):Stack_inv Hs. xlets. xvals.
  rewrite* length_zero_eq_eq_nil.
Qed.

Lemma push_spec : forall A `{EA:Enc A} (L:list A) s (x:A),
  Stack L s ->
  SPEC_PURE (push x s)
    POST (fun s' => \[Stack (x::L) s']).
Proof using.
  introv Hs. xcf*. lets (->&->):Stack_inv Hs. 
  (* xgo; subst. *) 
  xlets. xlets. xvals.
  applys* Stack_intro. rew_list; math.
Qed.

Lemma pop_spec : forall A `{EA:Enc A} (L:list A) s,
  Stack L s ->
  L <> nil ->
  SPEC_PURE (pop s)
    POST (fun '(x,s') => \exists L', \[L = x::L'] \* \[Stack L' s']).
Proof using.
  introv Hs HL. xcf. lets (->&->):Stack_inv Hs.
  (* xgo. { subst*. } *)
  xlets. xmatch. xlets. xlets. xvals*. 
  { applys* Stack_intro. rew_list; math. }
Qed.

