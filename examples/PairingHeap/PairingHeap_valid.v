(** This file contains a few examples illustrating how lifted characteristic
    formulae can be formally verified wrt the axiomatic semantics.
    In the future, the contents of this file will be automatically generated.
    Its contents is fully directed by the structure of the source code. *)


Set Implicit Arguments.
From CFML Require Import WPLib WPValid.
From CFML Require Import Stdlib.
From EXAMPLES Require Import PairingHeap_ml.

(** Manual validation of the CF generated *)

Lemma create_cf_valid__ : create_cf_def__.
Proof using.
  cf_main.
  cf_inlined.
  cf_app.
Qed.

Lemma is_empty_cf_valid__ : is_empty_cf_def__.
Proof using.
  cf_main.
  cf_app.
  cf_inlined.
  cf_app.
Qed.

Lemma merge_cf_valid__ : merge_cf_def__.
Proof using.
  cf_main.
  cf_app.
  cf_app.
  cf_if.
  { cf_app.
    cf_seq.
    { cf_app. }
    { cf_val. } }
  { cf_app.
    cf_seq.
    { cf_app. }
    { cf_val. } }
Qed.

Lemma insert_cf_valid__ : insert_cf_def__.
Proof using.
  cf_main.
  cf_app.
  cf_let. { cf_new. } intros ?.
  cf_app.
  cf_match. cf_case.
  { cf_inlined. cf_app. }
  { cf_case.
    { cf_app. cf_inlined. cf_app. }
    { cf_match_fail. } }
Qed.

Lemma merge_pairs_cf_valid__ : merge_pairs_cf_def__.
Proof using.
  cf_main.
  cf_app.
  cf_app.
  cf_if.
  { cf_val. }
  { cf_app.
    cf_app.
    cf_app.
    cf_if.
    { cf_val. }
    { cf_app.
      cf_app. } }
Qed.

Lemma pop_min_cf_valid__ : pop_min_cf_def__.
Proof using.
  cf_main.
  cf_app.
  cf_match. cf_case.
  { cf_fail. }
  { cf_case.
    { cf_app. cf_app. cf_app. cf_seq.
      { cf_if.
        { cf_inlined. cf_app. }
        { cf_app. cf_app. cf_inlined. cf_app. } }
      { cf_val. } }
    { cf_match_fail. } }
Qed.


