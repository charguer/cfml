
(* ---------------------------------------------------------------------- *)
(* ** Injectivity of encoders *)

(* ** Injectivity of encoders for entire types *)

Definition Enc_injective A (EA:Enc A) :=
  injective (enc (A:=A)).

Lemma Enc_injective_inv : forall A (EA:Enc A) (V1 V2:A),
  Enc_injective EA ->
  (enc V1 = enc V2) = (V1 = V2).
Proof using. introv E. extens. iff M. { applys~ E. } { subst~. } Qed.

Lemma Enc_injective_inv_neq : forall A (EA:Enc A) (V1 V2:A),
  Enc_injective EA ->
  (enc V1 <> enc V2) ->
  (V1 <> V2).
Proof using.
  introv HEA HN. intros E. rewrites <- (>> Enc_injective_inv HEA) in E. false.
Qed.

Lemma Enc_injective_loc : Enc_injective Enc_loc.
Proof using.
  intros n1 n2 E. rewrite (enc_loc_eq n1), (enc_loc_eq n2) in E. congruence.
Qed.

Lemma Enc_injective_unit : Enc_injective Enc_unit.
Proof using.
  intros n1 n2 E. destruct n1; destruct n2; auto.
Qed.

Lemma Enc_injective_bool : Enc_injective Enc_bool.
Proof using.
  intros n1 n2 E. rewrite (enc_bool_eq n1), (enc_bool_eq n2) in E. congruence.
Qed.

Lemma Enc_injective_int : Enc_injective Enc_int.
Proof using.
  intros n1 n2 E. rewrite (enc_int_eq n1), (enc_int_eq n2) in E.
  (* todo, why [do 2 rewrite enc_int_eq] and [rew_enc in E] fail *)
  congruence.
Qed.

Lemma Enc_injective_pairs : forall A1 A2 (EA1:Enc A1) (EA2:Enc A2),
  Enc_injective EA1 ->
  Enc_injective EA2 ->
  Enc_injective (@Enc_pair A1 EA1 A2 EA2).
Proof using.
  introv HEA1 HEA2. intros p1 p2 E.
  destruct p1; destruct p2; simpls; tryfalse.
  { rew_enc in E. inverts E. fequals*. }
Qed.

Lemma Enc_injective_option : forall A (EA:Enc A),
  Enc_injective EA ->
  Enc_injective (@Enc_option A EA).
Proof using.
  introv HEA. intros o1 o2 E.
  induction o1; destruct o2; simpls; tryfalse.
  { rew_enc in E. inverts E. fequals*. }
  { auto. }
Qed.

Lemma Enc_injective_list : forall A (EA:Enc A),
  Enc_injective EA ->
  Enc_injective (@Enc_list A EA).
Proof using.
  introv HEA. intros l1 l2 E. gen l2.
  induction l1; intros; destruct l2; simpls; tryfalse.
  { auto. }
  { rew_enc in E. inverts E. fequals*. }
Qed.

Hint Resolve Enc_injective_loc Enc_injective_unit Enc_injective_bool
             Enc_injective_int Enc_injective_pairs Enc_injective_option
             Enc_injective_list
             : Enc_injective.

(* ** Injectivity of encoders for specific values
      (useful in many cases to avoid the need for an hypothesis
      of the form [Enc_injective EA] *)

Definition Enc_injective_value A {EA:Enc A} (V1:A) :=
  forall V2, (enc V1 = enc V2) -> (V1 = V2).

Lemma Enc_injective_value_eq_l : forall A (EA:Enc A) (V1:A),
  Enc_injective_value V1 ->
  forall V2, (enc V1 = enc V2) = (V1 = V2).
Proof using. introv E. extens. iff M. { applys~ E. } { subst~. } Qed.

Lemma Enc_injective_value_eq_r : forall A (EA:Enc A) (V1:A),
  Enc_injective_value V1 ->
  forall V2, (enc V2 = enc V1) = (V2 = V1).
Proof using. introv E. extens. iff M. { symmetry. applys~ E. } { subst~. } Qed.

Lemma Enc_injective_nil : forall A (EA:Enc A),
  Enc_injective_value (@nil A).
Proof using.
  intros A EA l E. destruct l; intros; simpls; tryfalse. { auto. }
Qed.

Lemma Enc_injective_none : forall A (EA:Enc A),
  Enc_injective_value (@None A).
Proof using.
  intros A EA o E. destruct o; intros; simpls; tryfalse. { auto. }
Qed.

Hint Resolve Enc_injective_nil Enc_injective_none : Enc_injective.

(** [Enc_comparable V1 V2] asserts that at least one of [V1]
    or [V2] satisfies [Enc_injective_value]. In such case,
    [``V1 = ``V2  <->  V1 = V2] holds. *)

Definition Enc_comparable A {EA:Enc A} (V1 V2:A) : Prop :=
     Enc_injective EA
  \/ Enc_injective_value V1
  \/ Enc_injective_value V2.

Lemma Enc_comparable_inv : forall A `(EA:Enc A) (V1 V2:A),
  Enc_comparable V1 V2 ->
  (``V1 = ``V2) = (V1 = V2).
Proof using.
  introv [M|[M|M]].
  { applys (>> Enc_injective_inv V1 V2 M). }
  { applys (>> Enc_injective_value_eq_l V1 M). }
  { applys (>> Enc_injective_value_eq_r V2 M). }
Qed.

Lemma Enc_comparable_inv_neg : forall A `(EA:Enc A) (V1 V2:A),
  Enc_comparable V1 V2 ->
  (``V1 <> ``V2) = (V1 <> V2).
Proof using.
  introv M. unfold not. rewrite* (Enc_comparable_inv M).
Qed.
