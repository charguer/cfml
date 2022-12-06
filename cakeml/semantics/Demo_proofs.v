Require Import Prelude.

Set Implicit Arguments.

Require Import ZArith Lia.

Require Import Demo_obligations.

Module Proofs : Obligations.

Lemma f_obligation_proof : f_obligation.
Proof. hnf. intros. unfold f, OLD1.f. lia. Qed.

End Proofs.

