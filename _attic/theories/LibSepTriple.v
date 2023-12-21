

(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)

Module Type TripleArgs.

Module  SH : SepCore.

Definition hprop := heap -> Prop.

hstar
hexists
hpure

Parameter isframe : hprop -> hprop -> Prop.

isframe_haffine : isframe \GC \[]

Parameter isframe_isframe : forall HI1 HO1 HI2 HO2,
  isframe HI1 HO1 ->
  isframe HI2 HO2 ->
  isframe (HI1 \* HI2) (HO1 \* HO2).

Parameter trm : Type.

Parameter val : Type.

Parameter hoare : trm -> hprop -> (val->hprop) -> Prop.

hoare_conseq

hoare_hexists

xsimpl! => xsimplargs...
End TripleArgs.


(* ---------------------------------------------------------------------- *)

Module Triple (SH : SepCore)(TA : TripleArgs).

Module M := SepSetup (TA.SH).

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall HI HO, isframe HI HO ->
    hoare t (H \* HI) (Q \*+ HO \*+ \GC).


(** SL rules structural *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HI HO FR. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. use triple_hexists
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HI HO FR. applys* hoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Lemma triple_isframe : forall HI HO t H1 Q1,
  triple t H1 Q1 ->
  isframe HI HO ->
  triple t (H1 \* HI) (Q1 \*+ HO).
Proof using.
  introv M F. intros HI' HO' F'.
  lets F'': isframe_isframe F F'.
  applys hoare_conseq. { applys M F''. } { xsimpl. } { xsimpl. }
Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HI HO HF. applys* hoare_conseq M. { xsimpl. }
Qed.

Lemma triple_haffine_post : forall H' t H Q,
  triple t H (Q \*+ H') ->
  haffine H' ->
  triple t H Q.
Proof using.
  introv M F. applys triple_hgc_post. applys triple_conseq M; xsimpl.
Qed.

(*
Lemma triple_haffine_pre : forall t H H' Q,
  triple t H Q ->
  haffine H' ->
  triple t (H \* H') Q.
Proof using.
  introv M F. applys~ triple_haffine_post H'.
  applys* triple_frame_onlyrw M.
  applys* onlyrw_of_haffine.
Qed.
*)  

End Triple.

