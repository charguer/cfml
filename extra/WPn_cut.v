
(* ########################################################### *)
(** ** Weakest-Precondition Style Presentation. *)

(** In chapter \CHAP{WPsem}, we discussed several possible definitions of the
    weakest-precondition operator, namely [wp], in Separation Logic. In this
    chapter, we present yet another possible definition, based on the judgment
    [evaln].

    Consider the judgment [evaln s t Q]. Assume the arguments were reordered,
    yielding the judgment [evaln t Q s]. Consider now the partial application
    [evaln t Q]. This partial application has type [state->Prop], that is,
    [hprop]. This predicate [evaln t Q] denotes a predicate that characterizes
    the set of input states [s] in which the evaluation (or, rather, any
    possible evaluation) of the term [t] produces an output satisfying [Q].
    It thus corresponds exactly to the notion of weakest precondition for Hoare
    Logic.

    The judgment [hoarewpn t Q], defined below, simply reorder the arguments
    of [evaln] so as to produce this weakest-precondition operator. Note that
    this is a Hoare Logic style predicate, which talks about the full state. *)

Definition hoarewpn (t:trm) (Q:val->hprop) : hprop :=
  fun s => evaln s t Q.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).


(** On top of [hoarewpn], we can define the Separation Logic version of weakest
    precondition, written [wpn t Q]. At a high level, [wpn] extends [hoarewpn]
    with a description of "the rest of the world". More precisely, [wpn t Q]
    describes a heap predicate, that, if extended with a heap predicate [H]
    describing the rest of the world, yields the weakest precondition with
    respect to the postcondition [Q \*+ H], that is, [Q] extended with [H]. *)

Definition wpn (t:trm) (Q:val->hprop) : hprop :=
  \forall H, H \-* (hoarewpn t (Q \*+ H)).

(** This definition is associated with the following introduction rule,
    which reads as follows: to prove [H ==> wpn t Q], which asserts that
    [t] admits [H] as precondition and [Q] as postcondition, it suffices
    to prove that, for any [H'] describing the rest of the world, the
    entailment [H \* H'==> hoarewpn t (Q \*+ H')] holds, asserting that
    the term [t] admits, in Hoare logic, the precondition [H \* H'] and
    the postcondition [Q \*+ H']. *)

Lemma wpn_of_hoarewpn : forall H t Q,
  (forall H', H \* H' ==> hoarewpn t (Q \*+ H')) ->
  H ==> wpn t Q.
Proof using.
  introv M. unfolds wpn. applys himpl_hforall_r. intros H'.
  applys himpl_hwand_r. rewrite hstar_comm. applys M.
Qed.

(* EX4! (wpn_equiv) *)
(** Prove the standard equivalence [(H ==> wp t Q) <-> (triple t H Q)]
    to relate the predicates [wpn] and [triplen].
    Hint: using lemma [wpn_of_hoarewpn] can be helpful. *)

Lemma wpn_equiv : forall H t Q,
  (H ==> wpn t Q) <-> (triplen t H Q).
Proof using. (* ADMITTED *)
  unfolds triplen. iff M.
  { unfolds hoarewpn, wpn. introv K.
    cuts R: (H \* H' ==> hoarewpn t (Q \*+ H')).
    { unfolds hoarewpn. applys* R K. }
    xchange M. xchange (hforall_specialize H'). }
  { applys wpn_of_hoarewpn. intros s K. unfolds hoarewpn. applys* M. }
Qed. (* /ADMITTED *)

(** [] *)

(** Remark: as mentioned in the chapter \CHAP{WPsem}, it is possible to define
    the predicate [triplen t H Q] as [H ==> wpn t Q], that is, to define
    [triplen] as a notion derived from [hoarewpn] and [wpn]. *)


(* ########################################################### *)
(** ** Hoare Logic WP-Style Rules for a Non-Deterministic Semantics. *)

(** Given that the semantics expressed by the predicate [evaln] has a weakest-
    precondition flavor, there are good chances that deriving weakest-
    precondition style reasoning rules from [evaln] could be even easier than
    deriving the rules for [triplen]. Thus, let us investigate whether this is
    indeed the case, by stating and proving reasoning rules for the judgments
    [hoarewpn] and [wpn]. We begin with rules for [hoarewpn]. *)

(** Structural rules *)

Lemma hoarewpn_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  (hoarewpn t Q1) ==> (hoarewpn t Q2).
Proof using.
  introv W. unfold hoarewpn. intros h K. applys evaln_conseq K W.
Qed.

(** Rules for term constructs *)

Lemma hoarewpn_val : forall v Q,
  Q v ==> hoarewpn (trm_val v) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_val.
Qed.

Lemma hoarewpn_fix : forall f x t Q,
  Q (val_fix f x t) ==> hoarewpn (trm_fix f x t) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_fix.
Qed.

Lemma hoarewpn_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  hoarewpn (subst x v2 (subst f v1 t1)) Q ==> hoarewpn (trm_app v1 v2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_app_fix.
Qed.

Lemma hoarewpn_let : forall x t1 t2 Q,
      hoarewpn t1 (fun v => hoarewpn (subst x v t2) Q)
  ==> hoarewpn (trm_let x t1 t2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_let.
Qed.

Lemma hoarewpn_if : forall b t1 t2 Q,
  hoarewpn (if b then t1 else t2) Q ==> hoarewpn (trm_if b t1 t2) Q.
Proof using.
  unfold hoarewpn. intros. intros h K. applys* evaln_if.
Qed.

(** Rules for primitives. We state their specifications following the
    presentation described near the end of chapter \CHAP{Wand}. *)

Lemma hoarewpn_add : forall Q n1 n2,
  (Q (val_int (n1 + n2))) ==> hoarewpn (val_add (val_int n1) (val_int n2)) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K. applys* evaln_add.
Qed.

Lemma hoarewpn_rand : forall Q n,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> hoarewpn (val_rand (val_int n)) Q.
Proof using.
  unfolds hoarewpn. introv N. xsimpl. intros h K.
  applys* evaln_rand. intros n1 H1. lets K': hforall_inv K n1.
  rewrite* hwand_hpure_l in K'.
Qed.

Lemma hoarewpn_ref : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> hoarewpn (val_ref v) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K. applys* evaln_ref. intros p D.
  lets K': hforall_inv (rm K) p.
  applys hwand_inv (single p v) K'.
  { applys hsingle_intro. }
  { applys* disjoint_single_of_not_indom. }
Qed.

Lemma hoarewpn_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> hoarewpn (val_get p) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  forwards*: hwand_inv h1 P2.
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys evaln_get.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { subst h1. rewrite* Fmap.read_union_l. rewrite* Fmap.read_single. }
Qed.
(* LATER: simplify *)

Lemma hoarewpn_set : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> hoarewpn (val_set p w) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  forwards: hwand_inv (single p w) P2.
  { applys hsingle_intro. }
  { subst h1. applys Fmap.disjoint_single_set D. }
    { applys evaln_set.
    { applys* Fmap.indom_union_l. subst. applys indom_single. }
    { subst h1. rewrite* Fmap.update_union_l. rewrite* update_single. } }
Qed.
(* LATER: simplify *)

Lemma hoarewpn_free : forall v p Q,
  (p ~~> v) \* (Q val_unit) ==> hoarewpn (val_free p) Q.
Proof using.
  unfolds hoarewpn. intros. intros h K.
  lets (h1&h2&P1&P2&D&->): hstar_inv (rm K).
  lets E1: hsingle_inv P1. lets I1: indom_single p v.
  applys_eq evaln_free.
  { applys* Fmap.indom_union_l. subst. applys indom_single. }
  { subst h1. rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys* Fmap.disjoint_inv_not_indom_both D Dl. }
Qed.
(* LATER: simplify *)


(* ########################################################### *)
(** ** Separation Logic WP-Style Rules for a Non-Deterministic Semantics. *)

(** In the previous section, we established reasoning rules for [hoarewpn].
    Based on these rules, we are ready to derive reasoning rules for [wpn]. *)

(** Structural rules *)

Lemma wpn_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wpn t Q1) \* H ==> (wpn t Q2).
Proof using.
  introv M. unfold wpn. xsimpl.
  intros H'. xchange (hforall_specialize (H \* H')).
  applys hoarewpn_conseq. xchange M.
Qed.

Lemma wpn_ramified_trans : forall t H Q1 Q2,
  H ==> (wpn t Q1) \* (Q1 \--* Q2) ->
  H ==> (wpn t Q2).
Proof using.
  introv M. xchange M. applys wpn_conseq_frame. applys qwand_cancel.
Qed.

(** Rules for term constructs *)

Lemma wpn_val : forall v Q,
  Q v ==> wpn (trm_val v) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_val (Q \*+ H')).
Qed.

Lemma wpn_fix : forall f x t Q,
  Q (val_fix f x t) ==> wpn (trm_fix f x t) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_fix (Q \*+ H')).
Qed.

Lemma wpn_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wpn (subst x v2 (subst f v1 t1)) Q ==> wpn (trm_app v1 v2) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (hforall_specialize H').
  applys* hoarewpn_app_fix.
Qed.

(* EX4! (wpn_let) *)
(** Derive the reasoning rule [wpn_let] from [hoarewpn_let]. *)

Lemma wpn_let : forall x t1 t2 Q,
  wpn t1 (fun v => wpn (subst x v t2) Q) ==> wpn (trm_let x t1 t2) Q.
Proof using. (* ADMITTED *)
  intros. unfold wpn. xsimpl. intros H'.
  xchange (hforall_specialize H').
  applys himpl_trans; [| applys* hoarewpn_let ].
  applys hoarewpn_conseq. intros v.
  xchange (hforall_specialize H').
Qed. (* /ADMITTED *)

(** [] *)

Lemma wpn_if : forall b t1 t2 Q,
  wpn (if b then t1 else t2) Q ==> wpn (trm_if b t1 t2) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (hforall_specialize H').
  applys hoarewpn_if.
Qed.

(** Rules for primitives. *)

Lemma wpn_add : forall Q n1 n2,
  (Q (val_int (n1 + n2))) ==> wpn (val_add (val_int n1) (val_int n2)) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  xchange (>> hoarewpn_add (Q \*+ H')).
Qed.

Lemma wpn_rand : forall Q n,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> wpn (val_rand (val_int n)) Q.
Proof using.
  introv N. unfold wpn. xsimpl. intros H'.
  applys himpl_trans; [| applys* hoarewpn_rand ].
  xsimpl. intros n1. xchange (hforall_specialize n1).
  intros H1. rewrite* hwand_hpure_l.
Qed.

Lemma wpn_ref : forall Q v,
  (\forall p, (p ~~> v) \-* Q (val_loc p)) ==> wpn (val_ref v) Q.
Proof using.
  intros. unfold wpn. xsimpl. intros H'.
  applys himpl_trans; [| applys hoarewpn_ref ].
  xsimpl. intros p. xchange (hforall_specialize p).
Qed.

Lemma wpn_get : forall v p Q,
  (p ~~> v) \* (p ~~> v \-* Q v) ==> wpn (val_get p) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  rewrite hstar_comm.
  applys himpl_trans; [| applys hoarewpn_get v ]. simpl.
  rewrite hstar_assoc. applys himpl_frame_r.
  xsimpl.
Qed.

(* LATER: in proof above, cannot use xsimpl because it simplifies too much *)
(* LATER: simplify. Last xsimpl could be an explicit
  [applys hstar_hwand (p ~~> v) (Q v) H'] *)

Lemma wpn_set : forall v w p Q,
  (p ~~> v) \* (p ~~> w \-* Q val_unit) ==> wpn (val_set p w) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  rewrite hstar_comm.
  applys himpl_trans; [| applys hoarewpn_set v ]. simpl.
  rewrite hstar_assoc. applys himpl_frame_r.
  xsimpl.
Qed.
(* LATER: same comments as for wpn_get; same below for free *)

Lemma wpn_free : forall v p Q,
  (p ~~> v) \* (Q val_unit) ==> wpn (val_free p) Q.
Proof using.
  intros. unfold wpn.
  applys himpl_hforall_r. intros H'. applys himpl_hwand_r.
  applys himpl_trans; [| applys hoarewpn_free v ]. xsimpl.
Qed.

(** Rules for primitives, alternative presentation using triples. *)

Lemma triplen_add : forall n1 n2,
  triplen (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_add ]. xsimpl*.
Qed.

Lemma triplen_rand : forall n,
  n > 0 ->
  triplen (val_rand n)
    \[]
    (fun r => \exists n1, \[0 <= n1 < n] \* \[r = val_int n1]).
Proof using.
  introv N. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys* wpn_rand ]. xsimpl*.
Qed.

Lemma triplen_ref : forall v,
  triplen (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_ref ]. xsimpl*.
Qed.

Lemma triplen_get : forall v p,
  triplen (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_get ]. xsimpl*.
Qed.

Lemma triplen_set : forall w p v,
  triplen (val_set (val_loc p) v)
    (p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_set ]. xsimpl*.
Qed.

Lemma triplen_free : forall p v,
  triplen (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using.
  intros. rewrite <- wpn_equiv.
  applys himpl_trans; [| applys wpn_free ]. xsimpl*.
Qed.

(* EX4? (wpn_rand_of_triplen_rand) *)
(** The proof of lemma [triplen_rand] shows that a triple-based specification
    of [val_rand] is derivable from a wp-style specification. In this
    exercise, we aim to prove the reciprocal. Concretely, prove the following
    specification by exploiting [triplen_rand].
    Hint: make use of [wpn_equiv]. *)

Lemma wpn_rand_of_triplen_rand : forall n Q,
  n > 0 ->
      (\forall n1, \[0 <= n1 < n] \-* Q (val_int n1))
  ==> wpn (val_rand (val_int n)) Q.
Proof using. (* ADMITTED *)
  introv N. forwards* E: triplen_rand N. rewrite <- wpn_equiv in E.
  xchange (rm E). applys wpn_ramified_trans. xsimpl.
  intros ? n1 H1 ->. xchange (hforall_specialize n1). rewrite* hwand_hpure_l.
Qed. (* /ADMITTED *)

(** [] *)

