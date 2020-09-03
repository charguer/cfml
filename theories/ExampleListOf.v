(**

This file formalizes mutable list examples in CFML 2.0.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example ExampleList.
Generalizable Variables A B.
Import MList.

Implicit Types p : loc.
Implicit Types n : int.

(* TODO: TLC *)
Lemma list_same_length_inv_nil : forall A1 A2 (l1:list A1) (l2:list A2),
  length l1 = length l2 ->
  l1 = nil <-> l2 = nil.
Proof using. intros. destruct l1; destruct l2; auto_false*. Qed.


(* ********************************************************************** *)
(* * Lists with recursive ownership *)

(* ---------------------------------------------------------------------- *)
(** ** Recursive representation predicate: works, but not modular *)

(**
[[
  Definition MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
    match L with
    | nil => \[p = null]
    | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'}
                     \* (x ~> R X) \* (p' ~> MListOf R L')
    end.
]]
*)

(* ---------------------------------------------------------------------- *)
(** ** Representation predicate for [MListOf] *)

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
  TRIPLE (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).
Proof using.
  xtriple. xapp (>> Triple_create EA) ;=> p. xunfold MListOf. xsimpl*.
  { rew_heapx. xsimpl. }
Qed.

Lemma Triple_is_empty : forall L p,
  TRIPLE (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp. xsimpl*.
  { applys* list_same_length_inv_nil. }
Qed.

Lemma Triple_push : forall L p x X,
  TRIPLE (push p ``x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  xsimpl (x::l). { rew_list~. } { rew_heapx. xsimpl. }
Qed.

Lemma Triple_pop : forall L p,
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  { rewrites~ (>> list_same_length_inv_nil L). }
  intros x l' ->. destruct L as [|X L']; rew_listx in *; tryfalse.
  rew_heapx. xsimpl*.
Qed.

End Ops.

Hint Extern 1 (Register_Spec (create)) => Provide Triple_create.
Hint Extern 1 (Register_Spec (is_empty)) => Provide Triple_is_empty.
Hint Extern 1 (Register_Spec (push)) => Provide Triple_push.
Hint Extern 1 (Register_Spec (pop)) => Provide Triple_pop.

Global Opaque MListOf.
