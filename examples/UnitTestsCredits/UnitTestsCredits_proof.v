Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From CFML Require Import Stdlib.Array_proof.
From EXAMPLES Require Import UnitTestsCredits_ml.


(*

let f x =
  x + x

let rec g n =
  if n > 0 then g (n-1)

let rec dup n =
  if n > 0 then 2 + g (n-1) else 0

*)

(*

Lemma xpay_lemma_post : forall H F1 A (EA:Enc A) (Q1 Q:A->hprop),
  H ==> F1 (Q \*+ \$1) ->
  H ==> Wpgen_pay' F1 Q.
Proof using. Admitted.

Lemma xpay_lemma_pre : forall H1 H F1 A (EA:Enc A) (Q:A->hprop),
  H ==> \$1 \* H1 ->
  H1 ==> F1 Q ->
  H ==> Wpgen_pay' F1 Q.
Proof using. Admitted.

*)

Ltac xpay_core tt :=
  apply xpay_lemma_post.

Tactic Notation "xpay" :=
  xpay_core tt.

Ltac xpay_pre_core tt :=
  eapply xpay_lemma_pre.

Tactic Notation "xpay_pre" :=
  xpay_pre_core tt.


Notation "'Pay' F" :=
 ((*Wptag*) (Wpgen_pay F))
 (in custom wp at level 69, F at level 0) : wp_scope.

Parameter hcredits_gc : forall n,
  n >= 0 ->
  \$ n ==> \GC.


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
  xcf.
  rewrite (hcredits_sub_eq (n+1) 1). xpay_pre. xsimpl.
  math_rewrite (n+1-1 = (n-1)+1).
  xif; intros C.
  { xapp. auto with maths. math. xsimpl. }
  { xval. xchange hcredits_gc. math. xsimpl. }
Qed.

Lemma hcredits_sub_eq' : forall (n m : int),
  \$(n-m) = \$ n \* \$ (-m).
Admitted.

Lemma hcredits_appear : forall (n: int),
  \[] ==> \$ n \* \$ (-n).
Admitted.

Hint Rewrite hcredits_sub_eq' : xcredits_split_rew.


Lemma g_spec' : forall n,
  n >= 0 ->
  SPEC (g n)
    PRE \[]
    POSTUNIT (\$ (-n-1)).
Proof using.
  intros n. induction_wf IH: (downto 0) n. introv Hn.
  xcf. xpay. xif; intros C.
  { xapp. auto with maths. math.
    xchange (hcredits_appear 1). xchange (hcredits_appear (-n-1)).
    xcredits_split. xsimpl. (* TODO: xgc dollars not affine *) }
  { xval.
    xchange (hcredits_appear 1). xchange (hcredits_appear (-n-1)).
    xcredits_split. (* rewrite hcredits_sub_eq'. *)
    xsimpl. }
 (* TODO: xsimpl: move credits to left and regroup them *)
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