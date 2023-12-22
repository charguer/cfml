Set Implicit Arguments.
From CFML Require Import WPLib Stdlib LibSepGroup.

Definition OptionOf A (R:(A -> hprop)) (x:option A) : hprop :=
  match x with
  | None => \[]
  | Some s => s ~> R  end.

Tactic Notation "xunfold_optionof" :=
  xunfold OptionOf.

Lemma haffine_OptionOf : forall A (R:(A -> hprop)) (x:option A),
  (forall x, haffine (x ~> R)) ->
  haffine (x ~> OptionOf R).
Proof.
  intros ? ? [] ?; xunfold OptionOf; xaffine.
Qed.

Hint Resolve haffine_OptionOf : haffine.
