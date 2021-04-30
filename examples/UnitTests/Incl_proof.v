Set Implicit Arguments.
From CFML Require Import WPLib.
Require UnitTests_proof.
Require Import Incl_ml.


(********************************************************************)
(********************************************************************)

Lemma myincr2_spec :
  myincr2 = UnitTests_ml.myincr.
Proof using.
  xcf.
Qed.

Lemma myincr2_spec' : forall n,
  SPEC (myincr2 n)
    PRE \[]
    POST \[= n + 1].
Proof using. rewrite myincr2_spec. applys UnitTests_proof.myincr_spec. Qed.

Lemma myincr3_spec :
  myincr3 = UnitTests_ml.myincr.
Proof using.
  xcf.
Qed.