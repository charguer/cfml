Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLib Stdlib.

From TLC Require Import LibMap.

Require Import Mono.

Require Import Id_ml.

Module Id := Id_ml.

(*************************************************)
(** Identifiers *)

Notation Idents := (map (ref_ unit) unit).

Definition RefGroup : Idents -> hprop :=
  Group Ref.

Lemma haffine_RefGroup : forall I,
  haffine (RefGroup I).
Proof.
  intros.
  apply haffine_Group.
  typeclass. xaffine.
Qed.

Hint Resolve haffine_RefGroup : haffine.

Global Instance MonType_Idents : MonType Idents :=
  make_MonType RefGroup (fun x y => dom x \c dom y).

Lemma RefGroup_empty :
  \[] ==> RefGroup \{}.
Proof. xchange Group_create. Qed.

Definition Id (id:Id.t_) :=
  id ~~> tt.

Lemma RefGroup_single : forall x,
  Id x ==> RefGroup (x \:= tt).
Proof. xchange Group_singleton. Qed.

(*************************************************)
(** Specifications *)

Lemma create_spec : forall (I:Idents),
  SPEC (Id.create tt)
    PRE (\$1)
    INV (RefGroup I)
    POST (fun (id:Id.t_) =>
            \[id \notindom I] \* id ~~> tt).
Proof.
  intros. xcf. xpay. xapp. intros.
  xchange* Group_heapdata_single.
  1,2:typeclass. intros.
  xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec Id.create) => Provide create_spec.

Lemma eq_spec : forall (x y:Id.t_),
  SPEC (Id.eq x y)
    PRE (\$1)
    POST \[= isTrue (x=y)].
Proof.
  xcf_go*.
Qed.

Hint Extern 1 (RegisterSpec Id.eq) => Provide eq_spec.

Lemma eq_opt_spec : forall (x:option Id.t_) (y:Id.t_),
  SPEC (Id.eq_opt x y)
    PRE (\$1)
    POST \[= isTrue (x = Some y)].
Proof.
  xcf_go*.
  { auto_false. }
  { split; intros Z; try injects Z; auto_star. }
Qed.

Hint Extern 1 (RegisterSpec Id.eq_opt) => Provide eq_opt_spec.
