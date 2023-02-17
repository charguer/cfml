Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import MList_ml.
From TLC Require Import LibListZ.



(*

Implicit Types p : loc.
Implicit Types n : int.

(* TODO: TLC *)
Lemma list_same_length_inv_nil : forall A1 A2 (l1:list A1) (l2:list A2),
  length l1 = length l2 ->
  l1 = nil <-> l2 = nil.
Proof using. intros. destruct l1; destruct l2; auto_false*. Qed.


*)


(* ---------------------------------------------------------------------- *)
(** ** Representation predicate for [MListOf] *)


Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Definition MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  \exists (l:list A), \[length l = length L] \* p ~> MList l
                      \* hfold_list2 (fun X x => x ~> R X) L l.

(* ---------------------------------------------------------------------- *)
(** ** Derived specifications for stack operations *)


Section Ops.

Context A {EA:Enc A} TA (R:TA->A->hprop).
Implicit Types L : list TA.
Implicit Types x : A.
Implicit Types X : TA.


Lemma Triple_create :
  SPEC (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).
Proof using.
Admitted.

Lemma Triple_is_empty : forall L p,
  SPEC (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).
Proof using.
Admitted.

Lemma Triple_push : forall L p x X,
  SPEC (push p x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).
Proof using.
Admitted.


Lemma Triple_pop : forall L p,
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').
Proof using.
Admitted.





(*============proofs

Lemma Triple_create :
  SPEC (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).
Proof using.
  xtriple. xapp (>> Triple_create EA) ;=> p. xunfold MListOf. xsimpl*.
  { rew_heapx. xsimpl. }
Qed.

Lemma Triple_is_empty : forall L p,
  SPEC (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp. xsimpl*.
  { applys* list_same_length_inv_nil. }
Qed.

Lemma Triple_push : forall L p x X,
  SPEC (push p ``x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  xsimpl (x::l). { rew_list~. } { rew_heapx. xsimpl. }
Qed.

Lemma Triple_pop : forall L p,
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  { rewrites~ (>> list_same_length_inv_nil L). }
  intros x l' ->. destruct L as [|X L']; rew_listx in *; tryfalse.
  rew_heapx. xsimpl*.
Qed.

*)

End Ops.

Hint Extern 1 (RegisterSpec create) => Provide Triple_create.
Hint Extern 1 (RegisterSpec is_empty) => Provide Triple_is_empty.
Hint Extern 1 (RegisterSpec push) => Provide Triple_push.
Hint Extern 1 (RegisterSpec pop) => Provide Triple_pop.

Global Opaque MListOf.
