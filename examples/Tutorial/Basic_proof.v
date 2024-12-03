(** Same examples as in the first chapter of the course
    Separation Logic Foundations
    https://softwarefoundations.cis.upenn.edu/slf-current/Basic.html *)


Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibOrder LibInt.
Generalizable Variables A.

Implicit Types n m : int.

From EXAMPLES Require Import Basic_ml.


(* ####################################################### *)
(** * Proofs *)

Lemma incr_spec : forall p n,
  SPEC (incr p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+1)).
Proof. xcf. xapp. xapp. xsimpl. Qed.

#[global] Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.

Lemma example_let_spec : forall n,
  SPEC (example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using. xcf. xlet. xlet. xval. xsimpl. math. Qed.

Lemma quadruple_spec : forall n,
  SPEC (quadruple n)
    PRE \[]
    POST (fun r => \[r = 4 * n]).
Proof. xcf. xlet. xval. xsimpl. math. Qed.

Lemma inplace_double_spec : forall p n,
  SPEC (inplace_double p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (2*n)).
Proof. xcf. xapp. xlet. xapp. xsimpl. math. Qed.

Lemma incr_two_spec : forall (p q:loc) (n m:int),
  SPEC (incr_two p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n+1) \* q ~~> (m+1)).
Proof using. xcf. xapp. xapp. xsimpl. Qed.

#[global] Hint Extern 1 (RegisterSpec incr_two) => Provide incr_two_spec.

Lemma incr_two_aliased_spec : forall p n,
  SPEC (incr_two p p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+2)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.

Lemma aliased_call_spec : forall p n,
  SPEC (aliased_call p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+2)).
Proof using. xcf. xapp incr_two_aliased_spec. xsimpl. Qed.

Lemma incr_first_spec : forall p q n m,
  SPEC (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n+1) \* q ~~> m).
Proof using. xcf. xapp. xsimpl. Qed.

Lemma incr_first_spec' : forall p (q:loc) n,
  SPEC (incr_first p q)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+1)).
Proof using. xcf. xapp. xsimpl. Qed.

Lemma incr_first_derived_spec : forall p q n m,
  SPEC (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n+1) \* q ~~> m).
Proof using. intros. xapp incr_first_spec'. xsimpl. Qed.

Lemma transfer_spec : forall p q n m,
  SPEC (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n + m) \* q ~~> 0).
Proof using. xcf. xapp. xapp. xlet. xapp. xapp. xsimpl. math. Qed.

Lemma transfer_aliased_spec : forall p n,
  SPEC (transfer p p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> 0).
Proof using. xcf. xapp. xapp. xlet. xapp. xapp. xsimpl. Qed.

Lemma ref_greater_spec : forall p n,
  SPEC (ref_greater p)
    PRE (p ~~> n)
    POST (fun q => p ~~> n \* q ~~> (n+1)).
Proof using. xcf. xapp. xlet. xapp. intros q. xsimpl. math. Qed.

Lemma ref_greater_abstract_spec : forall p n,
  SPEC (ref_greater p)
    PRE (p ~~> n)
    POST (fun q => \exists m, \[m > n] \* q ~~> m \* p ~~> n).
Proof using. intros. xapp ref_greater_spec. xsimpl. { math. } Qed.

Lemma succ_using_incr_spec : forall n,
  SPEC (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using. xcf. xapp. intros p. xapp. xapp. xsimpl. auto. Qed.

Ltac xapp_postpone_type_evars tt :=
  match goal with |- ?A => match type of A with Type =>
    let X := fresh in evar (X:Type); exact X end end.

Ltac xapp_exploit_spec_lemma L cont ::=
  let HS := fresh "Spec" in
  intros HS;
  eapply L;
  [ applys HS; try clear HS; xapp_side_post tt
  | try clear HS; cont tt ].

(**
Lemma instantiate_type_vars : forall (A:Type), A ->
  A.
Proof using. auto. Qed.

 applys instantiate_type_vars.
*)


Lemma get_and_free_spec : forall p `{Enc A} (v:A),
  SPEC (get_and_free p)
    PRE (p ~~> v)
    POST (fun r => \[r = v]).
Proof using. xcf. xapp. xval. xsimpl. auto. Qed.


Module Import Facto.

Parameter facto : int -> int.

Parameter facto_init : forall n,
  0 <= n <= 1 ->
  facto n = 1.

Parameter facto_step : forall n,
  n > 1 ->
  facto n = n * (facto (n-1)).

End Facto.

Lemma factorec_spec : forall n,
  n >= 0 ->
  SPEC (factorec n)
    PRE \[]
    POST (fun r => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 0) n.
  intros Hn. xcf. xif.
  { intros C. xval. xsimpl.
    rewrite facto_init. math. math. }
  { intros C. xapp. { hnf. math. } { math. }
    xval. xsimpl. rewrite (@facto_step n). math. math. }
Qed.


Lemma repeat_incr_spec : forall (m n:int) p,
  m >= 0 ->
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + m)).
Proof using.
  intros m. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros n p Hm. xcf. xif; intros C.
  { xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. math. }
Qed.

Lemma step_transfer_spec : forall p q n m,
  m >= 0 ->
  SPEC (step_transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n + m) \* q ~~> 0).
Proof using.
  intros q p n m Hm.
  revert n Hm. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xcf. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. { math. } { math. } }
Qed.