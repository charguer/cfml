(**

Separation Logic Foundations

Chapter: "Direct".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFHprop.
From Sep Require Var Fmap Hsimpl.

(** Implicit Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * Imports *)

(* ******************************************************* *)
(** ** Extensionality axioms *)

Module Assumptions.

(** The file [LibAxioms] from the TLC library includes the axioms of
    functional extensionality and propositional extensionality.
    These axioms are essential to proving equalities between
    heap predicates, and between postconditions. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

End Assumptions.


(* ******************************************************* *)
(** ** Variables *)

(** The file [Var.v] defines the type [var] as an alias for [string].

    It provides the boolean function [var_eq x y] to compare two variables.

    It provides the tactic [case_var] to perform case analysis on 
    expressions of the form [if var_eq x y then .. else ..] 
    that appear in the goal. *)


(* ******************************************************* *)
(** ** Finite maps *)

(** The file [Fmap.v] provides a formalization of finite maps, which
    are then used to represent heaps in the semantics.

    The implementation details need not be revealed. 
  
    Finiteness of maps is essential because to justify that allocation
    yields a fresh reference, one must be able to argue for the 
    existence of a location fresh from existing heaps. From the 
    finiteness of heaps and the infinite number of variables, we
    can conclude that fresh locations always exist. 
    
    The library [Fmap.v] provides the basic operations of finite maps,
    and in particular the definition of disjointness.

    It provides a tactic [fmap_disjoint] to automate the disjointness proofs,
    and a tactic [fmap_eq] to prove equalities between heaps modulo
    associativity and commutativity. Without these two tactics, the 
    proofs would be extremely tedious and fragile. *)



(* ####################################################### *)
(** * Source language *)

(* ******************************************************* *)
(** ** Syntax *)

Definition loc : Type := nat.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_add : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.


(* ******************************************************* *)
(** ** Implicit Types *)

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types s : state.


(* ******************************************************* *)
(** ** Substitution *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.


(* ******************************************************* *)
(** ** Coercions *)

Coercion trm_val : val >-> trm.
Coercion trm_app : trm >-> Funclass.

Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ******************************************************* *)
(** ** Semantics *)

Inductive eval : state -> trm -> state -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r, 
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if_case : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_ref : forall s v l,
      ~ Fmap.indom s l ->
      eval s (val_ref v) (Fmap.update s l v) (val_loc l)
  | eval_get : forall s l,
      Fmap.indom s l ->
      eval s (val_get (val_loc l)) s (Fmap.read s l)
  | eval_set : forall s l v,
      Fmap.indom s l ->
      eval s (val_set (val_loc l) v) (Fmap.update s l v) val_unit.


(* ####################################################### *)
(** * Heap predicates *)

(** For technical reasons, to enable sharing the code implementing 
    the tactic [hsimpl], we need the definitions that follow to be
    wrapped in a module. *)

Module HsimplArgs. 


(* ******************************************************* *)
(** ** Hprop and entailement *)

(** Type of heap predicates *)

Definition hprop := heap -> Prop.

(** Entailment for heap predicates *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

Open Scope heap_scope.

(** Entailment between postconditions *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).


(* ******************************************************* *)
(** ** Definition of heap predicates *)

(** Core heap predicates *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single l v).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "\[]" := (hempty)
  (at level 0).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity).

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'").

(** Derived heap predicates.

    The following operators are defined in terms of the ones
    above, rather than as functions over heaps, to reduce the
    proof effort. (See the summary in [SLFWand.v] for details.) *)

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Definition htop : hprop :=
  \exists (H:hprop), H.

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* \[ (H0 \* H1) ==> H2].

Definition qwand A (Q1 Q2:A->hprop) :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]").

Notation "\Top" := (htop).

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40).

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43).


(* ******************************************************* *)
(** ** Basic properties of Separation Logic operators *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [himpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

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

Lemma himpl_forall_trans : forall H1 H2,
  (forall H, H ==> H1 -> H ==> H2) ->
  H1 ==> H2.
Proof using. introv M. applys~ M. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l.
  applys~ hstar_comm.
  applys~ hstar_hempty_l.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1. 
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1. 
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hpure] *)

Lemma hstar_hpure : forall P H h, 
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists.
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hstar_hpure. Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. intros h K. rewrite* hstar_hpure.
Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure.
  rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]).
  rewrite hstar_comm. rewrite~ hstar_hpure.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys pred_ext_1. intros h. iff M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys pred_ext_1. intros h. rewrite hstar_hpure. iff M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hexists *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

(* not needed *)
Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hforall *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

(* not needed *)
Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hwand (others are found further in the file) *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).
Proof using.
  unfold hwand. iff M.
  { applys himpl_trans. applys himpl_frame_l M.
    (* applys himpl_hstar_trans_l (rm M). *)
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0. 
    rewrite hstar_comm. rewrite <- (hstar_hempty_l H0) at 1.
    applys himpl_frame_l. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H1 \* H2 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite hstar_comm. rewrite~ <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. rewrite hwand_equiv. rewrite~ hstar_hempty_l. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- (hstar_hempty_l (\[] \-* H)). applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_r. }
Qed.

Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using. 
  introv HP. rewrite <- (hstar_hempty_l (\[P] \-* H)).
  forwards~ K: himpl_hempty_hpure P.
  applys* himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. do 2 rewrite hwand_equiv.
  rewrite hstar_assoc. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite <- (hstar_comm (H1 \* H2)). 
  rewrite (@hstar_comm H1). rewrite hstar_assoc.
  applys himpl_trans. applys himpl_frame_r. applys hwand_cancel.
  applys hwand_cancel.
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_trans.
    applys himpl_frame_l M. applys himpl_trans. applys hstar_hforall.
    applys himpl_hforall_l x. rewrite <- hwand_equiv. applys himpl_refl. }
  { applys himpl_hforall_r. intros x.
    rewrite hwand_equiv. rewrite* hstar_comm. }
Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using.
  intros. applys himpl_forall_trans. intros H M.
  rewrite qwand_equiv in M. specializes M x.
  rewrite hwand_equiv. rewrite~ hstar_comm.
Qed.

Arguments qwand_specialize [ A ].


(* ---------------------------------------------------------------------- *)
(** Properties of htop *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { applys himpl_forall_trans. intros H M. applys himpl_trans M.
    rewrite <- (hstar_hempty_r \Top) at 1. applys himpl_frame_r.
    applys himpl_htop_r. }
Qed.


(* ******************************************************* *)
(** ** Hsimpl tactic *)

(** The definitions and properties above enable us to instantiate
    the [hsimpl] tactic, which implements powerful simplifications
    for Separation Logic entailments. 
    
    For technical reasons, we need to provide a definition for [hgc],
    a restriction of [htop] to affine heap predicates. For our purpose,
    it suffices to define [hgc] as an alias for [htop]. *)

(* ---------------------------------------------------------------------- *)
(** Definition and properties of hgc *)

Definition hgc := htop.

Definition haffine := fun H => True.

Lemma haffine_hempty :
  haffine \[].
Proof using. hnfs*. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.


(* ---------------------------------------------------------------------- *)
(** Functor instantiation to obtain [hsimpl] *)

End HsimplArgs. 

(** We are now ready to instantiate the functor. *)

Module Export HS := HsimplSetup(HsimplArgs).

(** At this point, the tactic [hsimpl] is available.
    See the file [SLFHimpl.v] for demos of its usage. *)  

(** And we open the module [HsimplArgs], essentially pretending
    that it was never created. *)

Export HsimplArgs.


(* ####################################################### *)
(** * Reasoning rules *)


(* ******************************************************* *)
(** ** Evaluation rules for primitives in Separation style *)

(** It is not needed to follow through these proofs. *)

Lemma eval_get_sep : forall s s2 l v, 
  s = (Fmap.single l v) \u s2 ->
  eval s (val_get (val_loc l)) s v.
Proof using.
  introv ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_get 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 l v1 v2,
  s1 = Fmap.union (Fmap.single l v1) h2 ->
  s2 = Fmap.union (Fmap.single l v2) h2 ->
  Fmap.disjoint (Fmap.single l v1) h2 ->
  eval s1 (val_set (val_loc l) v2) s2 val_unit.
Proof using.
  introv -> -> D. forwards Dv: Fmap.indom_single l v1.
  applys_eq eval_set 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

Lemma eval_ref_sep : forall s1 s2 v l,
  s2 = Fmap.single l v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc l).
Proof using.
  (** It is not needed to follow through this proof. *)
  introv -> D. forwards Dv: Fmap.indom_single l v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed.


(* ******************************************************* *)
(** ** Hoare reasoning rules *)

(** * Definition of Hoare triples *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.

(** The tactic [himpl_fold] applies to a goal of the form [H1 h].
    It searches the context for an assumption of the from [H2 h],
    then replaces the goal with [H1 ==> H2].
    It also deletes the assumption [H2 h]. *)

Ltac himpl_fold_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    applys himpl_inv N; clear N end.

Tactic Notation "himpl_fold" := himpl_fold_core tt.
Tactic Notation "himpl_fold" "~" := himpl_fold; auto_tilde.
Tactic Notation "himpl_fold" "*" := himpl_fold; auto_star.

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h.
  { himpl_fold~. }
  exists h' v. splits~. { himpl_fold. auto. }
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys eval_val. }
  { himpl_fold~. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using.
  introv N M. intros h Hh. exists___. splits.
  { applys~ eval_fun. }
  { himpl_fold~. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using.
  introv N M. intros h Hh. exists___. splits.
  { applys~ eval_fix. }
  { himpl_fold~. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_seq R2. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if_case : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite hstar_hpure_iff. split.
    { auto. }
    { applys K0. } }
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We claim the disjointness relation 
       [Fmap.disjoint (Fmap.single l v) s1]. *)
  forwards~ (l&D): (single_fresh s1 v).
  (* 3. We provide the witnesses for the reduction,
        as dictated by [red_ref_sep]. *)
  exists ((Fmap.single l v) \u s1) (val_loc l). split.
  { (* 4. We exploit [red_ref_sep], which has exactly the desired shape! *)
    applys eval_ref_sep D. auto. }
  { (* 5. We establish the postcondition 
       [(\exists l, \[r = val_loc l] \* l ~~~> v) \* H]
       by providing [p] and the relevant pieces of heap. *)
    applys hstar_intro.
    { exists l. rewrite hstar_hpure.
      split. { auto. } { applys hsingle_intro. } }
    { applys K0. }
    { applys D. } }
Qed.

Lemma hoare_get : forall H v l,
  hoare (val_get l)
    ((l ~~~> v) \* H)
    (fun r => \[r = v] \* (l ~~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s K0. 
  (* 2. We provide the witnesses for the reduction,
        as dictated by [red_get_sep]. *)
  exists s v. split.
  { (* 3. To justify the reduction using [red_get_sep], we need to
          argue that the state [s] decomposes as a singleton heap
          [Fmap.single l v] and the rest of the state [s2]. This is
          obtained by eliminating the star in hypothesis [K0]. *)
    destruct K0 as (s1&s2&P1&P2&D&U).
    (*    and subsequently inverting [(l ~~~> v) h1]. *)
    lets E1: hsingle_inv P1. subst s1.
    (* 4. At this point, the goal matches exactly [red_get_sep]. *)
    applys eval_get_sep U. }
  { (* 5. To establish the postcondition, we reuse justify the
          pure fact \[v = v], and check that the state, which
          has not changed, satisfy the same heap predicate as
          in the precondition. *)
    rewrite hstar_hpure. auto. }
Qed.


Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using. 
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We decompose the star from the precondition. *)
  destruct K0 as (h1&h2&P1&P2&D&U).
  (* 3. We also decompose the singleton heap predicate from it. *)
  lets E1: hsingle_inv P1.
  (* 4. We provide the witnesses as guided by [red_set_sep]. *)
  exists ((Fmap.single l w) \u h2) val_unit. split.
  { (* 5. The evaluation subgoal matches the statement of [red_set_sep]. *)
    subst h1. applys eval_set_sep U D. auto. }
  { (* 6. To establish the postcondition, we first isolate the pure fact. *)
    rewrite hstar_hpure. split.
    { auto. }
    { (* 7. Then establish the star. *)
      applys hstar_intro.
      { (* 8. We establish the heap predicate [l ~~~> w] *) 
        applys hsingle_intro. }
      { applys P2. }
      { (* 9. Finally, we justify disjointness using the lemma 
              [Fmap.disjoint_single_set] introduced earlier. *)
        subst h1. applys Fmap.disjoint_single_set D. } } }
Qed.


(* ******************************************************* *)
(** ** Definition of [wp] and reasoning rules *)


(* ---------------------------------------------------------------------- *)
(** Definition of [wp] w.r.t. [hoare]  *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[forall H', hoare t (H \* H') (Q \*+ H' \*+ \Top)].


(* ---------------------------------------------------------------------- *)
(** Structural rule for [wp]. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).
Proof using.
  intros. do 2 rewrite wp_def. hpull ;=> H M.
  hsimpl (H \* (Q1 \--* Q2 \*+ \Top)). intros H'.
  applys hoare_conseq M; hsimpl.
Qed.

(* ---------------------------------------------------------------------- *)
(** Reasoning rules for terms. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. intros. rewrite wp_def. hsimpl; intros H'. applys hoare_val. hsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. rewrite wp_def. hsimpl; intros H'. applys hoare_fun. hsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. rewrite wp_def. hsimpl; intros H'. applys hoare_fix. hsimpl. Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. repeat rewrite wp_def. hsimpl; intros H M H'.
  applys hoare_if_case. applys M.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans wp_if_case. case_if~. Qed.

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. rewrite wp_def. hsimpl. intros H' M1.
  rewrite wp_def. hsimpl. intros H''.
  applys hoare_seq. applys (rm M1). rewrite wp_def.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; hsimpl.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. rewrite wp_def. hsimpl. intros H' M1.
  rewrite wp_def. hsimpl. intros H''.
  applys hoare_let. applys (rm M1). intros v. simpl.
  rewrite wp_def.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; hsimpl.
Qed.


(* ---------------------------------------------------------------------- *)
(** Rules for primitives. *)

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using. 
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We decompose the star from the precondition. *)
  destruct K0 as (h1&h2&P1&P2&D&U).
  (* 3. We also decompose the singleton heap predicate from it. *)
  lets E1: hsingle_inv P1.
  (* 4. We provide the witnesses as guided by [red_set_sep]. *)
  exists ((Fmap.single l w) \u h2) val_unit. split.
  { (* 5. The evaluation subgoal matches the statement of [red_set_sep]. *)
    subst h1. applys eval_set_sep U D. auto. }
  { (* 6. To establish the postcondition, we first isolate the pure fact. *)
    rewrite hstar_hpure. split.
    { auto. }
    { (* 7. Then establish the star. *)
      applys hstar_intro.
      { (* 8. We establish the heap predicate [l ~~~> w] *) 
        applys hsingle_intro. }
      { applys P2. }
      { (* 9. Finally, we justify disjointness using the lemma 
              [Fmap.disjoint_single_set] introduced earlier. *)
        subst h1. applys Fmap.disjoint_single_set D. } } }
Qed.



(* ******************************************************* *)
(** ** Definition of triple and equivalence *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \Top).

Lemma wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).
Proof using.
  iff M.
  { hsimpl H. apply M. }
  { applys triple_conseq Q M.
    { applys triple_hexists. intros H'.
      rewrite hstar_comm. applys triple_hpure. 
      intros N. applys N. }
    { applys qimpl_refl. } }
Qed.


(* ******************************************************* *)
(** ** Specification for primitive functions *)

Lemma triple_add' : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  rewrite wp_equiv.
  intros. applys triple_of_hoare. intros H'. esplit. split.
  applys hoare_add. hsimpl. auto.
(* /SOLUTION *)
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_ref. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get l)
    (l ~~~> v)
    (fun r => \[r = v] \* (l ~~~> v)).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_get. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_set. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.



(* ####################################################### *)
(** * WP generator *)

(* ******************************************************* *)
(** ** Definition *)

(* ******************************************************* *)
(** ** Soundness *)

(* ******************************************************* *)
(** ** Notations *)

(* ******************************************************* *)
(** ** Tactics *)


(* ####################################################### *)
(** * Practical proofs *)

(* ******************************************************* *)
(** ** Notation for terms *)

(* ******************************************************* *)
(** ** Example proof *)
