(** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.

Require Import StackSized_ml.




(* ********************************************************************** *)
(** ** Representation predicate *)

(** Definition of [r ~> Stack L], which is a notation for [Stack L r], of type
    [hprop] *)

Definition Stack A `{EA:Enc A} (L:list A) (r:loc) : hprop :=
  \exists n,
      r ~~~> `{ items' := L; size' := n }
   \* \[ n = length L ].


Lemma Stack_eq : forall r A `{EA:Enc A} (L:list A),
  (r ~> Stack L) =
  (\exists n, r ~~~> `{ items' := L; size' := n } \* \[ n = length L ]).
Proof using. auto. Qed.

Arguments Stack_eq : clear implicits.

(* TODO: use the generic xopen and close *)

Tactic Notation "xopen" constr(r) :=
  xchange (Stack_eq r); xpull.

Tactic Notation "xclose" constr(r) :=
  xchange <- (Stack_eq r).

Tactic Notation "xclose" "*" constr(r) :=
  xclose r; auto_star.


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

Lemma create_spec : forall A `{EA:Enc A},
  SPEC (create tt)
    PRE \[]
    POST (fun s => s ~> Stack (@nil A)).
Proof using.
  xcf. xapp ;=> s. xclose* s. xsimpl.
Qed.

Lemma size_spec : forall A `{EA:Enc A} (L:list A) (s:loc),
  SPEC (size s)
    INV (s ~> Stack L)
    POST (fun n => \[n = length L]).
Proof using.
  xcf. xopen s. xpull ;=> n Hn.
  xapp. xclose* s. xsimpl*.
Qed.

Lemma is_empty_spec : forall A `{EA:Enc A} (L:list A) (s:loc),
  (* <EXO> *)
  SPEC (is_empty s)
    INV (s ~> Stack L)
    POST (fun b => \[b = isTrue (L = nil)]).
  (* </EXO> *)
Proof using.
  (* Hint: use [xopen] then [xclose] like in [size_spec].
     Also use [xcf], [xpull], [xapps], [xrets],
     and lemma [length_zero_iff_nil] from above. *)
  (* <EXO> *)
  xcf. xopen s. intros n Hn. xapp. xclose* s.
  xvals. subst. rewrite* length_zero_eq_eq_nil.
  (* </EXO> *)
Qed.

Lemma push_spec : forall A `{EA:Enc A} (L:list A) (s:loc) (x:A),
  SPEC (push x s)
    PRE (s ~> Stack L)
    POSTUNIT (s ~> Stack (x::L)).
Proof using.
  (* Hint: use [xcf], [xapp], [xapps], [xpull], [xsimpl],
     [xopen], [xclose] and [rew_list] *)
  (* <EXO> *)
  xcf.
  xopen s. (* details: xchange (@Stack_open s) *)
  intros n Hn.
  xapp. xapp. xapp. xapp.
  xclose s. rew_list. math.
  xsimpl.
  (* </EXO> *)
Qed.

Lemma pop_spec : forall A `{EA:Enc A} (L:list A) (s:loc),
  L <> nil ->
  SPEC (pop s)
    PRE (s ~> Stack L)
    POST (fun x => \exists L', \[L = x::L'] \* s ~> Stack L').
Proof using.
  (* Hint: also use [rew_list in H] *)
  (* <EXO> *)
  introv HL. xcf. xopen s. intros n Hn. xapp. xmatch.
  xapp. xapp. xapp. xval.
  xclose* s. { rew_list in *. math. } xsimpl*.
  (* </EXO> *)
Qed.

Lemma clear_spec : forall A `{EA:Enc A} (L:list A) (s:loc),
  SPEC (clear s)
    PRE (s ~> Stack L)
    POSTUNIT (s ~> Stack (@nil A)).
Proof using.
  xcf. xopen s. intros n Hn. xapp. xapp. xclose* s. xsimpl*.
Qed.

(* Can add hints for exploiting the lemmas, e.g.:
   [Hint Extern 1 (RegisterSpec push) => Provide push_spec.] *)
