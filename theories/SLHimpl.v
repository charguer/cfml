(*

(** * Heap entailment *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Require Import LambdaSemantics LambdaSep.


(** * Heap entailment *)

CHANGE

Notation "P ==> Q" := (pred_incl P Q)
  (at level 55, right associativity) : heap_scope.

(* [rel_incl'] is like TLC's [rel_incl] but defined in terms of [pred_incl]
   so that after [intros r] we get an entailment. *)

Definition rel_incl' A B (P Q:A->B->Prop) :=
  forall r, pred_incl (P r) (Q r).

Notation "P ===> Q" := (rel_incl' P Q)
  (at level 55, right associativity) : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Examples of entailment *)


r -> 6 * s -> 3 ==> s -> 3 * r -> 6

FALSE : r -> 3 ==> s -> 4 * r -> 3

negation: H1 h /\ ~ H2 h
  ~ (s -> 4 * r -> 3)
  forall h1 h2, ~ .. \/ ~ .. \/ ~ ...

  ~ A \/ ~ B \/ ~ C
  equiv to A -> B -> C -> False.

  r -> 3 means h1 has domain r
  s -> 4 means h2 has domain s

  if r = s, then disjoint entails false
  if r <> s, then h = h1 \u h2 = {r} \u {s}
    dom h = {r}



\[False] ==> r -> 6

FALSE:   r -> 3 \* s -> 4 ==> \[False]

r -> 3 \* r -> 4 ==> \[False]
r -> 3 \* r -> 3 ==> \[False]






(* ---------------------------------------------------------------------- *)
(* ** Properties of entailment *)


Section HimplProp.
Variable A : Type.
Implicit Types H : A -> Prop.

Hint Unfold pred_incl.

(** Entailment is reflexive, symmetric, transitive *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

(** Paragraphe of the definition, used by tactics *)

Lemma himpl_inv : forall H1 H2 (h:A),
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.


Lemma refl_rel_incl' : forall A B (Q:A->B->Prop),
  Q ===> Q.
Proof using. apply refl_rel_incl. Qed.



(* ---------------------------------------------------------------------- *)
(* ** A detour : extensionality *)

(* SLIDE: extensionality *)






(* ---------------------------------------------------------------------- *)
(* ** Fundamental properties of hprop *)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  intros H1 H2. unfold hprop, hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ heap_union_comm in U; exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys hprop_extens. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
Qed.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys hprop_extens. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ heap_union_empty_l. }
  { exists~ heap_empty h. }
Qed.


Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys hprop_extens. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.



lemma transitive + frame
  h1 ==> h2
  x ==> h1 * r
  h2 \* x => y
  x==> y

(* SLIDE: heap-entailment-properties *)


(* ---------------------------------------------------------------------- *)
(* ** example with instantiation and extrusion *)


check out the "derived" states from previous chapter,
and insert them here as exercises

unfolding/folding of lists/trees give exercises

split rule on segments


r -> 6 ==> hexists n, r -> n \* even n

hexists n, r -> n  ==> r --> 3   [FALSE]




illustration for tactics:

exists n , r -> n \* n > 0  ==>  exists n, n > 1 \* r -> (n-1)

r -> 3 * s -> r ==> hexists n, r -> n * s -> n





illustration for hchange

lemma : r -> a \* r -> b = false.

exists n, n > 0 \* n < 0 \* r -> n ==> r -> n * r -> n





(* SLIDE: structural-rules *)


(*--cover all structural rules*)
(*--cover splitting rules for segments *)

(* SLIDE: splitting-rule-for-list-segments *)





(** * Separation algebra *)

(** ** Entailment between heap predicates *)


(** ** Equality between heap predicates *)



(** ** [rew_heap] tactic *)

(** ** Algebra of heap predicates *)

(** ** Frame for heap predicates *)

(* + simplification rule *)


(** ** Extraction rules *)

(** ** Examples of heap entailment *)

(* + quiz *)


(** ** Simplification tactic [himpl] *)

(** ** Rewriting tactic [hchange] *)




(* ---------------------------------------------------------------------- *)
(* ** Frame and consequence *)

Lemma rule_conseq : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl. hchanges (MQ v). }
Qed.

Lemma rule_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.


check out the "derived" triples from previous chapter,
and insert them here as exercises




(* ---------------------------------------------------------------------- *)
(* ** Extraction rules *)

Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  intros t. applys (rule_extract_hprop_from_extract_hexists (triple t)).
  applys rule_extract_hexists.
Qed.

independent proofs

as exercise, proof via the equivalence.


(* ---------------------------------------------------------------------- *)
(* ** Combined structural rule *)

exercise

(* ---------------------------------------------------------------------- *)
(* ** Garbage collection *)

support in hsimpl for \Top

Lemma rule_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma rule_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys rule_htop_post. applys~ rule_frame.
Qed.






*)