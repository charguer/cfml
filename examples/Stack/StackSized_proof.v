(** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import CFLib.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.

Import StackSized_ml.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** Definition of [r ~> Stack L], which is a notation for [Stack L r], of type
    [hprop] *)

Definition Stack A (L:list A) r :=
  \exists n,
      r ~> `{ items' := L; size' := n }
   \* \[ n = length L ].


Lemma Stack_eq : forall r A (L:list A),
  (r ~> Stack L) =
  (\exists n, r ~> `{ items' := L; size' := n } \* \[ n = length L ]).
Proof using. auto. Qed.

Arguments Stack_eq : clear implicits.

Tactic Notation "xopen" constr(r) :=
  rewrite (Stack_eq r); xpull.

Tactic Notation "xclose" constr(r) :=
  rewrite <- (Stack_eq r).


(* ********************************************************************** *)
(** ** TEMPORARY *)

(* TODO: generalize tactics using:

  (** Unfolding and folding lemmas paraphrasing the definition of [Stack] *)

  Lemma Stack_open : forall r A (L:list A),
    r ~> Stack L ==>
    \exists n, r ~> `{ items' := L; size' := n } \* \[ n = length L ].
  Proof using. dup 2.
    { intros. xunfold Stack. hpull. intros. hcancel. auto.
      (* Try [hcancel 3] to see how it works *) }
    { intros. xunfolds~ Stack. }
  Qed.

  Lemma Stack_close : forall r A (L:list A) (n:int),
    n = length L ->
    r ~> `{ items' := L; size' := n } ==>
    r ~> Stack L.
  Proof using. intros. xunfolds~ Stack. Qed.

  Arguments Stack_close : clear implicits.

  (** Customization of [xopen] and [xclose] tactics for [Stack].
      These tactics avoid the need to call [hchange] or [xchange]
      by providing explicitly the lemmas [Stack_open] and [Stack_close].
      Note that the number of underscores avec [Stack] after the [RegisterOpen]
      needs to match the number of arguments of the representation predicate
      [Stack], excluding the pointer. (Here, we have one underscore for [L].) *)

  Hint Extern 1 (RegisterOpen (Stack _)) =>
    Provide Stack_open.
  Hint Extern 1 (RegisterClose (record_repr _)) =>
    Provide Stack_close.

*)


(* ********************************************************************** *)
(** ** Verification *)

(** Verification of the code *)

Lemma create_spec : forall (A:Type),
  TRIPLE (create tt)
    PRE \[]
    POST (fun r => r ~> Stack (@nil A)).
Proof using.
  xwp. dup 2.
  { xapp. intros r.  (* or just [xapp. => r] *)
    xclose r. auto. xsimpl. }
  { xapp ;=> r. xclose~ r. }
Qed.

Lemma size_spec : forall (A:Type) (L:list A) (s:loc),
  TRIPLE (size s)
    INV (s ~> Stack L)
    POST (fun n => \[n = length L]).
(* Remark: the above is a notation for:
  app size [s]
    PRE (s ~> Stack L)
    POST (fun n => \[n = length L] \* s ~> Stack L).
*)
Proof using.
  xwp. (* TODO: add xopens to do xpull *)
  xopen s. (* details: xchange (@Stack_open s). *)
  xpull ;=> n Hn.
  (* interesting: do [unfold tag] here, to unfold this identity
     function used to decorate the file. *)
  xapp. (* computes on-the-fly the record_get specification *)
  intros m.
  xpull ;=> ->. (* details: [xpull. intros E. subst E.] *)
  xclose s. (* details: xchange (@Stack_close s). *)
  auto. xsimpl. math.
  (* Here we have an issue because Coq is a bit limited.
     Workaround to discharge the remaining type: *)
  Unshelve. solve_type. (* TODO: support [xwp A] in the beginning *)
Qed.

Lemma length_zero_iff_nil : forall A (L:list A),
  length L = 0 <-> L = nil.
Proof using.
  intros. destruct L; rew_list. (* [rew_list] normalizes list expressions *)
  { autos*. (* [intuition eauto] *) }
  { iff M; false; math. (* [iff M] is [split; intros M] *) }
Qed.

Lemma is_empty_spec : forall (A:Type) (L:list A) (s:loc),
  (* <EXO> *)
  TRIPLE (is_empty s)
    INV (s ~> Stack L)
    POST (fun b => \[b = isTrue (L = nil)]).
  (* </EXO> *)
Proof using.
  (* Hint: use [xopen] then [xclose] like in [size_spec].
     Also use [xwp], [xpull], [xapps], [xrets],
     and lemma [length_zero_iff_nil] from above. *)
  (* <EXO> *)
  xwp.
  (* Note that the boolean expression [n = 0] from Caml
     was automatically translated into [isTrue (x0__ = 0)];
     Indeed, [Ret_ P] is notation for [Ret (isTrue P)]. *)
  xopen s. xpull ;=> n Hn. xapps. xclose~ s.
  dup 2.
  { xret_no_clean.
    reflect_clean tt. (* automatically called by [hsimpl] *)
    hsimpl.
    subst. apply length_zero_iff_nil. }
  { xrets. subst. apply length_zero_iff_nil. }
  (* </EXO> *)
  Unshelve. solve_type.
Qed.

Lemma push_spec : forall (A:Type) (L:list A) (s:loc) (x:A),
  TRIPLE (push x s)
    PRE (s ~> Stack L)
    POST (# s ~> Stack (x::L)).
Proof using.
  (* Hint: use [xwp], [xapp], [xapps], [xpull], [xsimpl],
     [xopen], [xclose] and [rew_list] *)
  (* <EXO> *)
  xwp.
  xopen s. (* details: xchange (@Stack_open s) *)
  xpull ;=> n Hn.
  xapps. xapp.
  xapps. xapp.
  xclose s. (* details: xchange (@Stack_close s) *)
  rew_list. (* normalizes expression on lists *)
  math.
  xsimpl.
  (* </EXO> *)
Qed.

Hint Extern 1 (RegisterSpec push) => Provide push_spec.

(* [xapp] on a call to push.
   Otherwise, need to do [xapp_spec push_spec]. *)

Lemma pop_spec : forall (A:Type) (L:list A) (s:loc),
  L <> nil ->
  TRIPLE (pop s)
    PRE (s ~> Stack L)
    POST (fun x => \exists L', \[L = x::L'] \* s ~> Stack L').
Proof using.
  (* Hint: also use [rew_list in H] *)
  (* <EXO> *)
  introv HL. xwp. xopen s. xpull ;=> n Hn. xapps. xmatch.
  xapps. xapps. xapps. xret. xclose~ s. rew_list in Hn. math.
  (* </EXO> *)
Qed.
