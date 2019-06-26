(**

EJCP Course: implementation of CFML

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFDirect.
Generalizable Variables A.


(* ####################################################### *)
(** * Source language (extract from [SLFHprop] and [SLFRules]) *)

Module Language.

(* ******************************************************* *)
(** ** Syntax *)

Definition var := string.

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

Definition state : Type := fmap loc val.

Definition heap : Type := state.

(*
[[
    Check Fmap.empty : heap.

    Check Fmap.single : loc -> val -> heap.

    Check Fmap.union : heap -> heap -> heap.

    Check Fmap.disjoint : heap -> heap -> Prop.
]]
*)

(** [Fmap] operations require [val] to be inhabited. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** Example term *)

Definition example_trm : trm :=
  trm_fun "x" (trm_if (trm_var "x") (trm_val (val_int 0)) (trm_val (val_int 1))).

(** Coercions, e.g. *)

Coercion trm_val : val >-> trm.
Coercion val_int : Z >-> val.
Coercion trm_app : trm >-> Funclass.

(** With notation, can write:
[[
  Definition example_trm' : trm :=
    Fun "x" :=
      If_ "x" Then 0 Else 1.
]]
*)

(* ******************************************************* *)
(** ** Semantics *)

Implicit Types v : val.

(** Substitution function *)

Parameter subst : forall (y:var) (w:val) (t:trm), trm.

(** Big-step semantics *)

Inductive eval : state -> trm -> state -> val -> Prop :=

  (* [eval] for values and function definitions *)

  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)

  (* [eval] for function applications *)

  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v

  (* [eval] for structural constructs *)

  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if_case : forall s1 s2 b v t1 t2,
      eval s1 (if (b:bool) then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v

  (* [eval] for primitive operations *)

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

End Language.


(* ####################################################### *)
(** * Heap predicates (extract from [SLFHprop]) *)

Module Hprop.

(* ******************************************************* *)
(** ** Core heap predicates *)

Definition hprop := heap -> Prop.

Implicit Type H : hprop.


Definition hempty : hprop :=
  fun (h:heap) => (h = Fmap.empty).

Notation "\[]" := (hempty) (at level 0).


Definition hpure (P:Prop) : hprop :=
  fun (h:heap) => (h = Fmap.empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").


Definition hsingle (l:loc) (v:val) : hprop :=
  fun (h:heap) => (h = Fmap.single l v).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).


Definition hstar (H1 H2 : hprop) : hprop :=
  fun (h:heap) => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).


Definition hexists A (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").


Definition htop : hprop :=
  fun (h:heap) => True.

Notation "\Top" := (htop).


(* ******************************************************* *)
(** ** Extensionality *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

Lemma predicate_extensionality : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.
Proof using.
  introv M. applys functional_extensionality. 
  intros. applys* propositional_extensionality. 
Qed.

Lemma hprop_eq : forall H1 H2,
  (forall h, H1 h <-> H2 h) ->
  H1 = H2.
Proof using. applys predicate_extensionality. Qed.

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

End Hprop.


(* ####################################################### *)
(** * Entailment (extract from [SLFHimpl]) *)


Module Himpl.

(* ******************************************************* *)
(** ** Definition of entailment *)

(** Definition of [H1 ==> H2] *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** Entailment is an order relation *)

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using.
  introv M1 M2. applys Hprop.hprop_eq.
  intros h. iff N.
  { applys M1. auto. }
  { applys M2. auto. }
Qed.

(** Definition of [Q1 ==> Q2] *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).


(* ******************************************************* *)
(** ** Fundamental properties *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral for the star. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:
      [(\exists x, H1) \* H2  =  \exists x, (H1 \* H2)].
      when [x] does not occur in [H2]. *)
 
Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (J \*+ H).

(** (5) Star is "regular" with respect to entailment. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** (+) Only one cell can be allocated at a given address *)

Parameter hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].

(* ******************************************************* *)
(** ** The tactics for entailment *)

(** Recall the demos from the tutorial. *)

End Himpl.


(* ####################################################### *)
(** * Definition of triples (extract from [SLFHprop]) *)


Module Triple.

(* ******************************************************* *)
(** ** Triples *)

(** [hoare t H Q] features pre- and post-conditions describing
    the full state. *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s ->
  exists (s':state) (v:val), eval s t s' v /\ Q v s'.

(** [triple1 t H Q] features pre- and post-conditions describing
    only a piece of state. *)

Definition triple1 (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

(** [triple t H Q] adds a [\Top] to make the logic affine as 
    opposed to linear: resources can be freely thrown away. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \Top).

(** An alternative, equivalent definition of triples *)

Definition fmap_disjoint_3 (h1 h2 h3:heap) :=
     Fmap.disjoint h1 h2
  /\ Fmap.disjoint h2 h3
  /\ Fmap.disjoint h1 h3.

Definition triple_lowlevel t H Q :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists v h1' h3',
       fmap_disjoint_3 h1' h2 h3'
    /\ eval (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ (Q v) h1'.

Parameter triple_iff_triple_lowlevel : forall t H Q,
  triple t H Q <-> triple_lowlevel t H Q.


(* ******************************************************* *)
(** ** Frame *)

(** The frame rule *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** Example application of the frame *)

Parameter incr : val.

Parameter triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).

Parameter triple_incr_2 : forall (p q:loc) (n m:int),
  triple (incr p)
    ((p ~~~> n) \* (q ~~~> m))
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* (q ~~~> m)).

Parameter triple_incr_3 : forall (p:loc) (n:int) (H:hprop),
  triple (incr p)
    ((p ~~~> n) \* H)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* H).


End Triple.


(* ####################################################### *)
(** * Reasoning rules (extract from [SLFRules]) *)


Module Rules.

(* ******************************************************* *)
(** ** Structural rules *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.

Parameter triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.

Parameter triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.

(** Factorized into the combined rule *)

Parameter triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.


(* ******************************************************* *)
(** ** Term rules *)

(** Hoare logic rule for sequence:
[[
      {H} t1 {fun r => H1}     {H1} t2 {Q}
      ------------------------------------
              {H} (t1;t2) {Q}
]]

In SL:
*)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** Informal Hoare logic rule for let-binding:
[[
      {H} t1 {Q1}     (forall x, {Q1 x} t2 {Q})
      -----------------------------------------
            {H} (let x = t1 in t2) {Q}
]]


  Formal Hoare logic rule for let-binding:
[[
      {H} t1 {Q1}     (forall v, {Q1 v} (subst x v t2) {Q})
      -----------------------------------------------------
                {H} (let x = t1 in t2) {Q}
]]

  In SL:
*)

Parameter triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** Plus one rule for each term construct, 
    plus one rule for each primitive operation. *)

End Rules.


(* ####################################################### *)
(** * Magic wand (extract from [SLFWand]) *)

Module Wand.

(* ******************************************************* *)
(** ** Definition of magic wand *)

(** The following equivalence can be proved to characterizes a unique 
    heap predicate [hwand]. *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> hwand H1 H2) <-> (H0 \* H1 ==> H2).

(** Corrolaries *)

Parameter hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.

(** For postconditions *)

Definition qwand A (Q1 Q2:A->hprop) :=
  \forall x, (Q1 x) \-* (Q2 x).

(* ******************************************************* *)
(** ** Ramified frame rule *)

(** Recall combined rule *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** New formulation using the magic wand to eliminate [H2] *)

Parameter triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.

(** Generalization with \Top *)

Parameter triple_ramified_frame_top : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \Top)) ->
  triple t H Q.

End Wand.


(* ####################################################### *)
(** * Weakest precondition (extract from [SLFWPsem]) *)

Module Wpsem.

(* ******************************************************* *)
(** ** Definition of [wp] *)

(** The following equivalence can be proved to characterizes a unique 
    function [wp]. *)

Parameter wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).

(** Corrolary *)

Parameter wp_pre : forall t Q,
  triple t (wp t Q) Q.


(* ******************************************************* *)
(** ** Benefits *)

(** Extraction rules are no longer needed: *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(** Reformulation of the combined structural rule *)

Parameter wp_conseq_frame_htop : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 \*+ \Top ->
  (wp t Q1) \* H ==> (wp t Q2).

(** Reformulation of the reasoning rules for terms *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

End Wpsem.


(* ####################################################### *)
(** * Characteristic formula (extract from [SLFWPgen]) *)

Module Wpgen.

(* ******************************************************* *)
(** ** High-level picture *)

Definition formula := (val->hprop) -> hprop.

(** Definition of the characteristic formula generator *)
(* 
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

    Parameter triple_of_wpgen : forall H t Q,
      H ==> wpgen t Q ->
      triple t H Q.

]]
*)
Module Wpgen1.

Parameter wpgen : forall (t:trm), formula.

(** Role of [mkstruct] is to ensure that the ramified frame rule
    can be applied to any formula produced by [wpgen], that is: *)

Parameter wpgen_ramified : forall t Q1 Q2,
  (wpgen t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wpgen t Q2).

End Wpgen1.

(** [mkstruct] is a formula transformer *)

Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
  \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).

(** [mkstruct] can be exploited to apply frame/consequence/garbage rules *)

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

(** [mkstruct] can be dropped *)

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. xsimpl. Qed.


(* ******************************************************* *)
(** ** Naive implementation *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition Wpgen wpgen (t:trm) : formula :=
  mkstruct
  match t with
  | trm_val v =>
       wpgen_val v
  | trm_var x =>
       wpgen_fail
  | trm_fun x t1 =>
       wpgen_val (val_fun x t1)
  | trm_fix f x t1 =>
       wpgen_val (val_fix f x t1)
  | trm_app t1 t2 =>
       wp t
  | trm_seq t1 t2 =>
       wpgen_seq (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 =>
       wpgen_let (wpgen t1) (fun v => wpgen (subst x v t2))
  | trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen t1) (wpgen t2)
  |  _ => wpgen_fail (* term not in normal form *)
  end.


(* ******************************************************* *)
(** ** Real implementation *)

Definition ctx : Type := list (var*val).

(** On contexts, we'll need two basic operations: lookup and removal. *)

(** [lookup x E] returns [Some v] if [x] maps to [v] in [E],
    and [None] if no value is bound to [x]. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** [rem x E] removes from [E] all the bindings on [x]. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** [isubst E t] substitutes all bindings from [E] in [t] *)

Parameter isubst : forall (E:ctx) (t:trm), trm.

(** Function [wpgen E t] computes a [wp (isubst E t)] *)

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v =>
       wpgen_val v
  | trm_var x =>
       wpgen_var E x
  | trm_fun x t1 =>
       wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 =>
       wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 =>
       wp (isubst E t)
  | trm_seq t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 =>
       wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 =>
      match isubst E t0 with
      | trm_val v0 => wpgen_if v0 (wpgen E t1) (wpgen E t2)
      | _ => wpgen_fail
      end
  end.

(* ******************************************************* *)
(** ** Soundness proof *)

(** Statement of the soundness result:
    [formula_sound_for (isubst E t) (wpgen E t)] *)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

(** Example soundness lemma, for [wpgen_seq] *)

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys himpl_trans wp_seq.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

(** Soundness of [mkstruct] *)

Lemma mkstruct_sound : forall t F,
  formula_sound_for t F ->
  formula_sound_for t (mkstruct F).
Proof using.
  introv M. intros Q. unfold mkstruct. xsimpl ;=> Q'.
  lets N: M Q'. xchange N. applys wp_ramified.
Qed.

(** Inductive proof of soundness *)

Parameter wpgen_sound : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
(**
Proof using.
  intros. gen E. induction t; intros; simpl;
   applys mkstruct_sound.
  { applys wpgen_val_sound. }
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_val_sound. }
  { applys wpgen_fix_val_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { rename v into x. applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite <- isubst_rem. applys IHt2. } }
  { case_eq (isubst E t1); intros; try applys wpgen_fail_sound.
    { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } } }
Qed.
*)

Parameter triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.


(* ******************************************************* *)
(** ** Notation and tactics *)

(** Notation for [wpgen_seq] *)

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ;  '/'  '[' F2 ']' ']'") : wp_scope.

(** The tactic [xseq] applies to goal of the form [(Seq F1 ; F2) Q] *)

Parameter xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> mkstruct (wpgen_seq F1 F2) Q.

Tactic Notation "xseq" :=
   applys xseq_lemma.

(** The tactic [xapp] leverages the following lemma. 
    Assume the current state [H] decomposes as [H1 \* H2]. 
    Then, the premise becomes [H1 \* H2 ==> H1 \* (Q1 \--* Q)]
    which simplifies to [H2 ==> Q1 \--* Q], which in turns 
    is equivalent to [Q1 \*+ H2 ==> Q]. In other words,
    [Q] is equal to [Q1] augmented with "[H] minus [H1]",
    which corresponds to the framed part. *)

Parameter xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> wp t Q.

(** The tag trick (displayed as [`F] in CFML) *)

Definition wptag (F:formula) : formula := F.

(** Integration:
[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    wptag (mkstruct (match t with ... end))
]]
*)

(** Notation for goals involving tagged formulae in the form
[[
    PRE H
    CODE F
    POST Q
]]
*)

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (wptag F) Q)
  (at level 8, H, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

End Wpgen.



(* ####################################################### *)
(** * Lifting (will be later in [SLFLift] *)

Module Lift.

(* ******************************************************* *)
(** ** The encoder typeclass *)

Class Enc (A:Type) :=
  make_Enc { enc : A -> val }.

(** Notation [``V] for [enc V] *)

Notation "`` V" := (enc V) (at level 8, format "`` V").

(** Example instances *)

Instance Enc_int : Enc int.
Proof using. constructor. applys val_int. Defined.

Instance Enc_unit : Enc unit.
Proof using. constructor. intros. applys val_unit. Defined.



(* ******************************************************* *)
(** ** Lifted singleton heap predicate *)

(** Singleton: [l ~~> V] describes a singleton heap at location [l]
    whose contents is the encoding of [V]. *)

Definition Hsingle `{EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '~~>' V" := (l ~> Hsingle V)
  (at level 32, no associativity) : heap_scope.


(* ******************************************************* *)
(** ** Lifted triples *)

(** [Triple t H Q] describes a triple where the postcondition [Q] has
    type [A->hprop] for some encodable type [A] *)

Definition Triple (t:trm) `{EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (fun v => \exists V, \[v = enc V] \* Q V).

(** Lifted rule for sequence: [Q1] has type [unit->hprop] *)

Parameter Triple_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.

(** Lifted rule for let bindings: [Q1] has type [A1->hprop]
    for some encodable type [A1] *)

Parameter Triple_let : forall z t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (subst z (enc X) t2) (Q1 X) Q) ->
  Triple (trm_let z t1 t2) H Q.


(* ******************************************************* *)
(** ** Lifted characteristic formulae *)

(** Type of a lifted formula *)

Definition Formula := forall A (EA:Enc A), (A -> hprop) -> hprop.

(** Notation [^F Q] as a shorthand for [F _ _ Q], which is same as  
    [F A EA Q] where [Q] has type [A->hprop] and [EA:Enc A]. *)

Notation "^ F Q" := ((F:Formula) _ _ Q)
  (at level 45, F at level 0, Q at level 0, format "^ F  Q") : wp_scope.

Open Scope wp_scope.

(** The [MkStruct] predicate lifts [mkstruct]. *)

Definition MkStruct (F:Formula) : Formula :=
  fun A `{EA:Enc A} Q => \exists Q', ^F Q' \* (Q' \--* (Q \*+ \GC)).

(** Lifted characteristic formula generator *)

Definition Wpgen_seq (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wpgen_let (F1:Formula) (F2of:forall `{EA1:Enc A1} ,A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1), ^F1 (fun (X:A1) => ^(F2of X) Q)).

(*
[[
Fixpoint Wpgen (E:ctx) (t:trm) : Formula :=
  MkStruct 
  match t with 
  ..
  | trm_seq t1 t2 => Wpgen_seq (Wpgen E t1) (Wpgen E t2)
  | trm_let x t1 t2 => Wpgen_let (Wpgen E t1) (fun A (EA:Enc A) (X:A) =>
                         Wpgen ((x, enc X)::E) t2)
  ...
  end
]]
*)

Parameter Wpgen : forall (E:ctx) (t:trm), Formula.

(** Soundness theorem *)

Parameter Triple_of_Wpgen : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen nil t) Q ->
  Triple t H Q.

End Lift.

