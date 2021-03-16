  (** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.

Require Import Stack_ml.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stack L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)

Definition Stack A `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.

Lemma Stack_eq : forall (p:loc) A `{Enc A} (L:list A),
  p ~> Stack L  =  p ~~> L.
Proof using. auto. Qed.


(* ********************************************************************** *)
(** ** Verification *)

(* TODO: not working
Ltac xcf_top_fun tt ::=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  eapply Sf;
  clear Sf;
  instantiate;
  try solve_type.
*)

Lemma create_spec : forall A `{Enc A},
  SPEC (create tt)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xcf. xapp. xsimpl.
  Unshelve. solve_type. typeclass.
Qed.

Hint Extern 1 (RegisterSpec create) => Provide create_spec.

Lemma is_empty_spec : forall A `{Enc A} (p:loc) (L:list A),
  SPEC (is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xcf. xunfold Stack. xapp. (* TODO xapp_types. infix_eq_spec. xapp~. xsimpl*. *)
  skip.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Ltac xtypes_triple E ::=
  let aux Vs T ET :=
    xtypes_dyn_list Vs; xtypes_type false T ET in
  match E with
  | (Wptag ?F) => xtypes_triple F
  | (@Wpgen_App_typed ?T ?ET ?f ?Vs) => aux Vs T ET
  | (@Triple (Trm_apps ?f ?Vs) ?T ?ET ?H ?Q) => aux Vs T ET
  | ?H ==> ?F _ _ ?Q => xtypes_triple F
  end.
  (* TODO: document -- xlet. xtypes_goal tt. *)

Lemma push_spec : forall A `{Enc A} (p:loc) (x:A) (L:list A),
  SPEC (push p x)
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xcf. xunfold Stack. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec push) => Provide push_spec.

Lemma pop_spec : forall A `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xcf. xunfold Stack. xapp. (* xmatch.*)  xmatch_no_intros.
  { intros. false. }
  {  intros X L' HL. xapp. xval. xsimpl~. }
  (* TODO: xmatch should regeneralize *)
Qed.

Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.

Lemma clear_spec : forall A `{Enc A} (p:loc) (L:list A),
  SPEC (clear p)
    PRE (p ~> Stack L)
    POSTUNIT (p ~> Stack (@nil A)).
Proof using.
  xcf. xunfold Stack. xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec clear) => Provide clear_spec.

Lemma concat_spec : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  SPEC (concat p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack (L1 ++ L2) \* p2 ~> Stack (@nil A)).
Proof using.
  xcf. xunfold Stack. xapp. xapp. xapp.
  rewrite <- (Stack_eq p2). xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec concat) => Provide concat_spec.

Opaque Stack.

Lemma rev_append_spec : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  SPEC (rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POSTUNIT (p1 ~> Stack (@nil A) \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xcf. xapp. xif ;=> C.
  { (* case cons *)
    xapp~ ;=> x L1' E. xapp. xapp. { subst*. } xsimpl. subst. rew_list~. }
  { (* case nil *)
    xval. xsimpl~. subst. rew_list~. }
Qed.

Hint Extern 1 (RegisterSpec rev_append) => Provide rev_append_spec.

