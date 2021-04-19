Set Implicit Arguments.
From CFML Require Import WPLib.
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
  xcf. xpay_pre. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. 

              match xsimpl_use_credits tt with
              | false => apply xsimpl_lr_exit_nogc_nocredits
              | _ => apply xsimpl_lr_exit_nogc

xsimpl1. applys himpl_refl.
  xif; intros C.
  { pattern n at 1. math_rewrite (n = (n-1)+1). 
    xapp. auto with maths. math. xsimpl. }
  { xval. xchanges* hcredits_gc. }
Qed.


(* TODO: might no longer be needed *)
Lemma neg_sub : forall n m,
  - (n - m) = (-n) + m.
Proof using. math. Qed.

Hint Rewrite neg_sub : rew_int.

Lemma g_spec' : forall n,
  n >= 0 ->
  SPEC (g n)
    PRE \[]
    POSTUNIT (\$ (-n-1)).
Proof using.
  intros n. induction_wf IH: (downto 0) n. introv Hn.
  xcf. xpay. xif; intros C.
  { xapp. auto with maths. math. rew_int; xcredits_split. xsimpl. }
  { xval. rew_int; xcredits_split. 
    xchange <- (hcredits_cancel 1). xchange <- (hcredits_cancel (-n)). xsimpl. }
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