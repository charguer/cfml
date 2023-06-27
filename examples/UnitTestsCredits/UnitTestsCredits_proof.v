Set Implicit Arguments.
From CFML Require Import WPLibCredits.
From CFML Require Import Stdlib.
From CFML Require Import Stdlib.Array_proof.
From EXAMPLES Require Import UnitTestsCredits_ml.



Lemma f_spec : forall n,
  SPEC (f n)
    PRE (\$ 1)
    POST \[= 2*n].
Proof using.
  xcf. xpay. xvals*. math.
Qed.

Lemma g_spec : forall n,
  n >= 0 ->
  SPEC (g n)
    PRE (\$ (n+1))
    POSTUNIT \[].
Proof using.
  intros n. induction_wf IH: (downto 0) n. introv Hn.
  xcf. xpay. xsimpl. xif; intros C.
  { xapp. auto with maths. math. xsimpl. }
  { xvals. }
Qed.


Lemma g_spec' : forall n,
  n >= 0 ->
  SPEC (g n)
    PRE \[]
    POSTUNIT (\$ (-n-1)).
Proof using.
  intros n. induction_wf IH: (downto 0) n. introv Hn.
  xcf. xpay. xif; intros C.
  { xapp. auto with maths. math. xsimpl. }
  { xvals. }
Qed.



(*

Lemma dup_spec : forall n,
  n >= 0 ->
  SPEC (dup n)
    PRE (\$ n)
    POST \[= 2 * n].
Proof using.
  xcf.
Qed.


let for_loop n =
  for i = 0 to n-1 do
    ()
  done

let while_loop n =
  while !n > 0 do
    decr n
  done

*)