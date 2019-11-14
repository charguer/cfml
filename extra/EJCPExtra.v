
Lemma xpull_demo_hpure_false : forall H1 H2,
  H1 \* \[False] ==> H2.
Proof using.
  intros. xpull.
Abort.

(*
(** Use the placeholder value [__] to instantiate an existential with an evar. *)

Lemma xsimpl_demo_rhs_hints_evar : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl __ 4.
Abort.
*)


(** In some cases, it may desirable to provide an explicit instantiation,
    using the syntax [xsimpl v1 .. vn] or [xsimpl (>> v1 .. vn)]. *)

Lemma xsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl 3 4.
Abort.


(** [xsimpl] collapses the multiple occurences of [\GC].
    If the RHS consists of exactly [\GC] and nothing else, 
    then the goal is discharged. *)

Lemma xsimpl_demo_rhs_hgc : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \GC \* H2 \* \GC.
Proof using.
  intros. xsimpl.
Abort.


(** The instantiation of the evar (e.g., [n]) can be observed if there
    is another occurence of the same variable in the entailment. For example: *)

Lemma xsimpl_demo_rhs_hexists_unify_view : forall H1 H2 H3 (p:loc),
  H1 \* (p ~~~> 3) ==> H2 \* \exists (n:int), (p ~~~> n \* \[n > 0]) \* H3.
Proof using.
  intros. xsimpl. (* [p ~~~> n] unifies with [p ~~~> 3], then [3 > 0] remains. *)
Abort.


(** The tactic [xsimpl] also work on [===>]. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. xsimpl. intros r. Abort.



(** The tactic [xchange] is also able to instantiate lemmas if needed. *)

Lemma xchange_demo_inst : forall H1 (J J':int->hprop) H3 H4,
  (forall n, J n = J' (n+1)) ->
  H1 \* J 3 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  (* Note that freshly produced items appear to the front *)
Abort.
----------


Lemma xgc_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \Top) ->
  H ==> mkstruct F Q.
Proof using.
  introv M. xchange M.
  lets N: mkstruct_ramified (Q \*+ \Top) Q F. xchanges N.
Qed.


Tactic Notation "xgc" :=
  applys xgc_lemma.




(** Once again, let us check that we have not lost expressive power.
    We prove [triple_if_case] only from [wp_if] and structural properties
    of [wp]. Observe the transitivity step. *)

Lemma triple_if_case_from_wp_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  introv M. rewrite wp_equiv in *. xchange M.
  applys himpl_trans wp_if. auto.
Qed.



Lemma wp_characterization_wp_low :
  wp_characterization wp_low.
Proof using. apply wp_equiv_wp_low. Qed.

Lemma wp_characterization_wp_high :
  wp_characterization wp_high.
Proof using. apply wp_equiv_wp_high. Qed.


    To that end, we introduce a predicate [wp_characterization]
    such that [wp_characterization wpX] holds of a predicate [wpX]
    iff the equivalence [(triple t H Q) <-> (H ==> wpX t Q)] holds
    for all [t], [H] and [Q]. *)

Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
  forall t H Q, (triple t H Q) <-> (H ==> wp t Q).

(** Observe that the two definitions for [wp] (the "high level" and
    the "low level") both satisfy the predicate [wp_characterization]. *)


(** Our goal is to show that if any two predicates [wp1] and [wp2]
    both satisfy [wp_characterizations], then they are equal, 
    in the sense [wp1 = wp2]. By extensionality, and by exploiting
    the symmetry in [wp1] and [wp2], this amounts to showing that
    the entailment [wp1 t Q ==> wp2 t Q] holds for any [t] and [Q]. 
    We formalize this result throught the following lemma. *)

Lemma wp_characterization_unique : forall wp1 wp2,
  wp_characterization wp1 ->
  wp_characterization wp2 ->
  wp1 = wp2.
Proof using.
  (* Observe how the assertion is used to exploit the symmetry. *)
  asserts L: (forall t Q wp1 wp2,
    wp_characterization wp1 ->
    wp_characterization wp2 ->
    wp1 t Q ==> wp2 t Q).
  { introv M1 M2. unfolds wp_characterization.
    rewrite <- M2. rewrite M1. applys himpl_refl. }
  (* Observe how extensionality is exploited to prove the equality. *)
  introv M1 M2. applys fun_ext_2. intros t Q.
  applys himpl_antisym; applys L; auto.
Qed.

(** In conclusion, it really does not matter which concrete definition 
    of [wp] is considered, because all definitions are equivalent. *)
