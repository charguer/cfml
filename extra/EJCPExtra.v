
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





(* ------------------------------------------------------- *)
(** *** Realisation of [mkstruct] *)


(** Rather than pulling out the definition of [mkstruct] from a hat,
    let us explain how to converge towards a sensible definition. 
    
    The rule [mkstruct_frame] provides an introduction rule for
    [mkstruct F Q'] when [Q'] is of the form [Q \*+ H].

[[
    (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H)
]]

    Our goal is to define [mkstruct F Q'] for an arbitrary [Q'].
    So, let us rewrite [mkstruct_frame] rule

[[
    (mkstruct F Q) \* H ==> mkstruct F Q'
]]




(2) Cela indique une propriété de "mkstruct F (Q1 * H)".
On a besoin de définir "mkstruct F Q" pour un "Q" arbitraire.
Ajoutons donc une prémisse pour dire contraindre "Q" à être de la forme "Q1 * H" :

      Q1 * H ===> Q
-------------------------------------
(mkstruct F Q1) * H ==> mkstruct F Q


(2) En déplaçant l'hypothèse comme un fait pur dans la précondition
et en quantifiant H et Q1 existentiellement dans la précondition,
on obtient la règle équivalente suivante :

    \exists H Q1, (mkstruct F Q1) * H * \[Q1 * H ===> Q]
==> mkstruct F Q


(3) Cela suggère la définition de "mkstruct" :

  Definition mkstruct F Q :=
\exists H Q1, F Q1 * H * \[Q1 * H ===> Q]


Réciproquement, on prouve en Coq que cette définition satisfait bien
les deux propriétés annoncées au début, et on peut montrer aussi
"mkstruct F = mkstruct (mkstruct F)".










    which establishes the entailment [wpgen t Q ==> wp t Q].





    In particular, [wpgen] has the same type as [wp].
    Recall that [wp t Q] denotes a heap predicate of type [hprop], where [t]
    is a term of type [trm] and [Q] is a postcondition of type [val->hprop].
    Thus, [wpgen] has type [trm->(val->hprop)->hprop]. *)

, which we name
    [formula] for brevity.


Definition formula := (val->hprop) -> hprop.


Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

*)


(** [wpgen t] is defined by recursion on [t], as a function
    that expects a postcondition [Q] and returns a [hprop].
    We call "formula" the result type of [wgpen t]: *)


(** The function [wpgen] is defined as shown below.

    The definition makes use of a predicate [mkstruct] to support
    structural rules of Separation Logic. For the moment, just ignore it.

    The details of the definition will be explained in detail
    throughout the chapter. What matters for the moment is to
    get a high-level picture of the shape of the definition.

[[
    Fixpoint wpgen (t:trm) : formula :=
      mkstruct (fun Q =>
        match t with
        | trm_val v => Q v
        | trm_var x => \[False]
        | trm_fun x t1 => Q (val_fun x t1)
        | trm_fix f x t1 => Q (val_fix f x t1)
        | trm_if v0 t1 t2 =>
             \exists (b:bool), \[v0 = val_bool b]
               \* (if b then (wpgen t1) Q else (wpgen t2) Q)
        | trm_seq t1 t2 =>
             (wpgen t1) (fun v => (wpgen t2) Q)
        | trm_let x t1 t2 =>
             (wpgen t1) (fun v => (wpgen (subst x v t2)) Q)
        | trm_app t1 t2 => wp t Q
        end).
]]

    The reason we present this definition as comment is that the above
    definition is not structurally recursive (the let-binding case
    involves a substitution), hence not accepted as such by Coq.

    In the course of this chapter, we'll present two approaches to remedy the
    situation. The first approach relies on a general fixed point combinator.
    The second approach tweaks the definition to pass as extra argument a list
    of bindings and avoid the need for substitutions during the recursion
    process. For now, let us assume the [wpgen] defined and explain how we
    plan to exploit this function. *)