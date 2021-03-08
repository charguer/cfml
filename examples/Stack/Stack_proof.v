(** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import CFLib.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.

Import Stack_ml.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stack L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)

Definition Stack A `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


(* ********************************************************************** *)
(** ** Verification *)

Lemma Triple_create : forall A `{Enc A},
  TRIPLE (create '())
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xval. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.

Lemma Triple_is_empty : forall A `{Enc A} (p:loc) (L:list A),
  TRIPLE (is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xwp. xunfold Stack. xapp. xval. xapp~. xsimpl*.
Qed.

Hint Extern 1 (Register_Spec is_empty) => Provide Triple_is_empty.

Lemma Triple_push : forall A `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xapp. xval. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec push) => Provide Triple_push.

Lemma Triple_pop : forall A `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xapp. xval. xsimpl~. }
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.

Lemma Triple_clear : forall A `{Enc A} (p:loc) (L:list A),
  TRIPLE (clear p)
    PRE (p ~> Stack L)
    POSTUNIT (p ~> Stack (@nil A)).
Proof using.
  xwp. xunfold Stack. xval. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec clear) => Provide Triple_clear.

Lemma Triple_concat : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (concat p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack (L1 ++ L2) \* p2 ~> Stack (@nil A)).
Proof using.
  xwp. xunfold Stack. xapp. xapp. xapp. xapp. xapp. xapp. xapp.
  xapp. { rew_listx. auto. } xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec concat) => Provide @riple_concat.

Opaque Stack.

Lemma Triple_rev_append : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POSTUNIT (p1 ~> Stack (@nil A) \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xapp. xapp. xif ;=> C.
  { (* case cons *)
    xapp~ ;=> x L1' E. xapp. xapp. { subst*. } xsimpl. subst. rew_list~. }
  { (* case nil *)
    xval. xsimpl~. subst. rew_list~. }
Qed.

Hint Extern 1 (Register_Spec rev_append) => Provide Triple_rev_append.

