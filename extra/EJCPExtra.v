
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

