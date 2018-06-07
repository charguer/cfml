(**

This file extends [LambdaSep.v] by "lifting" heap predicates
and triples so as to express specifications using logical values,
as opposed to deeply-embedded values.

The relationship between the two kind of values is implemented
using encoding functions, called encoders, realized using
typeclasses. Decoders implement the inverse functions to encoders.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import LambdaSep.
Import LibList.
Generalizable Variables A B.

Open Scope trm_scope.
Open Scope heap_scope.

Implicit Types l : loc.
Implicit Types u : unit.


(* ********************************************************************** *)
(* * Types *)

(* ---------------------------------------------------------------------- *)
(* ** Func type *)

Definition func := val.


(* ********************************************************************** *)
(* * Encoders *)

(* ---------------------------------------------------------------------- *)
(* ** Encoders *)

Class Enc (A:Type) :=
  make_Enc { enc : A -> val }.

Notation "`` V" := (enc V) (at level 8, format "`` V").


(* TEMPORARY: this is patch of a TLC tactic to prevent undesired
   eager instantiation of the typeclasses [Enc]. *)
Ltac app_evar t A cont ::=
  let x := fresh "TEMP" in
  let T :=
    match A with Enc ?X => constr:(id Enc X) | _ => constr:(A) end in
  evar (x:T);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

(** Notation for lists of encoded values *)

Notation "``[ ]" :=
  (@nil val) (format "``[ ]") : enc_scope.
Notation "``[ x ]" :=
  (cons (enc x) nil) : enc_scope.
Notation "``[ x , y , .. , z ]" :=
  (cons (enc x) (cons (enc y) .. (cons (enc z) nil) ..)) : enc_scope.

Open Scope enc_scope.
Delimit Scope enc_scope with enc.


(* ---------------------------------------------------------------------- *)
(* ** Representation of values packed with their type and encoder *)

(** Representation of dependent pairs *)

Record dyn := dyn_make {
  dyn_type : Type;
  dyn_enc : Enc dyn_type;
  dyn_value : dyn_type }.

Arguments dyn_make [dyn_type] {dyn_enc}.

(*Unset Printing Records.*)
Notation "'Dyn' V" := (dyn_make V)
  (at level 69) : heap_scope.

Lemma dyn_inj : forall A `{EA:Enc A} (x y : A),
  Dyn x = Dyn y -> x = y.
Proof using. introv H. inverts~ H. Qed.

Lemma dyn_inj_type : forall A1 `{EA1:Enc A1} A2 `{EA2:Enc A2} (x1:A1) (x2:A2),
  Dyn x1 = Dyn x2 -> A1 = A2.
Proof using. introv H. inverts~ H. Qed.

Lemma dyn_def : forall (d:dyn),
  d = @dyn_make _ (dyn_enc d) (dyn_value d).
Proof using. intros. destruct~ d. Qed.

(** Conversion from dyn to val *)

Definition dyn_to_val (d:dyn) : val :=
  @enc _ (dyn_enc d) (dyn_value d).

Lemma dyn_to_val_dyn_make : forall A `{EA:Enc A} V,
  dyn_to_val (dyn_make V) = enc V.
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Encoder instances *)

Global Instance Enc_dyn : Enc dyn.
Proof using. constructor. applys dyn_to_val. Defined.

Instance Enc_loc : Enc loc.
Proof using. constructor. applys val_loc. Defined.

Instance Enc_unit : Enc unit.
Proof using. constructor. applys (fun (x:unit) => val_unit). Defined.

Instance Enc_bool : Enc bool.
Proof using. constructor. applys val_bool. Defined.

Instance Enc_int : Enc int.
Proof using. constructor. applys val_int. Defined.

Instance Enc_func : Enc func.
Proof using. constructor. applys (fun (x:func) => x). Defined.

Instance Enc_val : Enc val.
Proof using. constructor. applys (fun (x:val) => x). Defined.

Instance Enc_prim : Enc prim.
Proof using. constructor. applys (fun (p:prim) => val_prim p). Defined.

Global Opaque Enc_dyn Enc_loc Enc_unit Enc_bool Enc_int
              Enc_func Enc_val Enc_prim.


(* ---------------------------------------------------------------------- *)
(* ** Specification of encoders for dyns *)

(* TODO: not needed? *)
Lemma enc_dyn_eq' : forall (d:dyn),
  enc d = dyn_to_val d.
Proof using. auto. Qed.

(* TODO: not needed? *)
Lemma enc_dyn_eq : forall (d:dyn),
  enc d = @enc _ (dyn_enc d) (dyn_value d).
Proof using. auto. Qed.

Lemma enc_dyn_make : forall `{EA:Enc A} (V:A),
  enc (dyn_make V) = enc V.
Proof using. auto. Qed.

Hint Rewrite @enc_dyn_make : rew_enc_dyn.

Tactic Notation "rew_enc_dyn" :=
  autorewrite with rew_enc_dyn.


(* ---------------------------------------------------------------------- *)
(* ** Specification of other encoders *)

Lemma enc_loc_eq : forall (l:loc),
  enc l = val_loc l.
Proof using. auto. Qed.

Lemma enc_unit_eq : forall (u:unit),
  enc u = val_unit.
Proof using. auto. Qed.

Lemma enc_bool_eq : forall (b:bool),
  enc b = val_bool b.
Proof using. auto. Qed.

Lemma enc_int_eq : forall (n:int),
  enc n = val_int n.
Proof using. auto. Qed.

Lemma enc_func_eq : forall (f:func),
  enc f = f.
Proof using. auto. Qed.

Lemma enc_val_eq : forall (v:val),
  enc v = v.
Proof using. auto. Qed.

Lemma enc_prim_eq : forall (p:prim),
  enc p = p.
Proof using. auto. Qed.

Hint Rewrite enc_dyn_make enc_loc_eq enc_unit_eq enc_bool_eq enc_int_eq
             enc_func_eq enc_val_eq enc_prim_eq : rew_enc.

Tactic Notation "rew_enc" :=
  autorewrite with rew_enc.
Tactic Notation "rew_enc" "in" hyp(H) :=
  autorewrite with rew_enc in H.
Tactic Notation "rew_enc" "in" "*" :=
  autorewrite with rew_enc in *.


(* ---------------------------------------------------------------------- *)
(* ** Injectivity of encoders *)

Definition Enc_injective A (EA:Enc A) :=
  injective enc.

Lemma Enc_injective_eq : forall `{EA:Enc A} (V1 V2:A),
  Enc_injective EA ->
  (enc V1 = enc V2) = (V1 = V2).
Proof using. introv E. extens. iff M. { applys~ E. } { subst~. } Qed.


Lemma Enc_injective_loc : Enc_injective Enc_loc.
Proof using.
  intros n1 n2 E. rewrite (enc_loc_eq n1), (enc_loc_eq n2) in E. congruence.
Qed.

Lemma Enc_injective_unit : Enc_injective Enc_unit.
Proof using.
  intros n1 n2 E. destruct n1; destruct n2; auto.
Qed.

Lemma Enc_injective_bool : Enc_injective Enc_bool.
Proof using.
  intros n1 n2 E. rewrite (enc_bool_eq n1), (enc_bool_eq n2) in E. congruence.
Qed.

Lemma Enc_injective_int : Enc_injective Enc_int.
Proof using.
  intros n1 n2 E. rewrite (enc_int_eq n1), (enc_int_eq n2) in E.
  (* todo, why [do 2 rewrite enc_int_eq] and [rew_enc in E] fail *)
  congruence.
Qed.

Hint Resolve Enc_injective_loc Enc_injective_unit Enc_injective_bool
             Enc_injective_int. (* TODO: put in a base? *)


(* ---------------------------------------------------------------------- *)
(* ** List of dynamic values *)

(** List of dyns *)

Definition dyns := list dyn.
(** Notation for lists of dynamic values *)

Notation "``[ ]" :=
  (@nil dyn) (format "``[ ]") : dyns_scope.
Notation "``[ x ]" :=
  (cons (Dyn x) nil) : dyns_scope.
Notation "``[ x , y , .. , z ]" :=
  (cons (Dyn x) (cons (Dyn y) .. (cons (Dyn z) nil) ..)) : dyns_scope.

Open Scope dyns_scope.
Delimit Scope dyns_scope with dyn.
Bind Scope dyns_scope with dyns.


(* ---------------------------------------------------------------------- *)
(* ** Encoder for list of values *)

(** Encoder for lists *)

Definition encs (ds:dyns) : vals :=
  List.map enc ds.

(** Preserves length *)

Lemma length_encs : forall (ds:dyns),
  length (encs ds) = length ds.
Proof using. intros. induction ds; simpl; rew_list; math. Qed.



(* ********************************************************************** *)
(* * Decoders *)

(* ---------------------------------------------------------------------- *)
(* ** Decoder *)

Fixpoint decode (v:val) : dyn :=
  match v with
  | val_unit => Dyn tt
  | val_bool b => Dyn b
  | val_int n => Dyn n
  | val_loc l => Dyn l
  | val_prim p => Dyn p
  | val_fix f x t => Dyn (v:func)
  end.

Lemma enc_decode' : forall (v:val),
  let d := decode v in
  @enc _ (dyn_enc d) (dyn_value d) = v.
Proof using.
  intros. destruct v; auto.
Qed.

Lemma enc_decode : forall (v:val),
  enc (decode v) = v.
Proof using. applys enc_decode'. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Decoder for lists *)

(** Decoders for lists *)

Definition decodes (vs:vals) : dyns :=
  List.map decode vs.

(** Inverse functions *)

Definition encodes_decodes : forall (vs:vals),
  encs (decodes vs) = vs.
Proof using.
  intros. induction vs.
  { auto. }
  { simpl. fequals. applys enc_decode. }
Qed.


(* ********************************************************************** *)
(* * Lifting of arguments and return values *)

(* ---------------------------------------------------------------------- *)
(* ** Lifting of postconditions *)

Definition Post A `{Enc A} (Q:A->hprop) : val->hprop :=
  fun v => Hexists V, \[v = enc V] \* Q V.

Lemma Post_himpl : forall `{Enc A} Q Q',
  Q ===> Q' ->
  Post Q ===> Post Q'.
Proof using.
  introv M. unfold Post. intros v.
  hpull. intros x E. subst v. hsimpl*.
Qed.

Lemma Post_star : forall `{Enc A} Q H,
  Post (Q \*+ H) = (Post Q) \*+ H.
Proof using.
  intros. unfold Post. applys fun_ext_1.
  intros v. applys himpl_antisym; hsimpl~.
Qed.

Local Hint Resolve Post_himpl.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of heap predicates *)

(** Singleton *)

Definition Hsingle `{EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '~~>' v" := (l ~> Hsingle v)
  (at level 32, no associativity) : heap_scope.

Lemma Hsingle_to_hsingle : forall `{EA:Enc A} (l:loc) (V:A),
  (l ~~> V) = hsingle l (enc V).
Proof using. auto. Qed.

Lemma Hsingle_not_null : forall l `{EA:Enc A} (V:A),
  (l ~~> V) ==+> \[l <> null].
Proof using. intros. xunfold Hsingle. applys hsingle_not_null. Qed.

Arguments Hsingle_not_null : clear implicits.

(** Field *)

Definition Hfield `{EA:Enc A} (V:A) (l_f:loc*field) : hprop :=
  let '(l,f) := l_f in
  hfield l f (enc V).

Notation "l `.` f '~~>' v" := ((l,f) ~> Hfield v)
  (at level 32, f at level 0, no associativity,
   format "l `.` f  '~~>'  v") : heap_scope.

Lemma Hfield_eq_fun_Hsingle :
  @Hfield = (fun `{EA:Enc A} (V:A) l_f => let '(l,f) := l_f in ((l+f)%nat ~~> V) \* \[l <> null]).
Proof using. intros. auto. Qed.

Lemma Hfield_to_hfield : forall `{EA:Enc A} (l:loc) (f:field) (V:A),
  (l`.`f ~~> V) = hfield l f (enc V).
Proof using. auto. Qed.

Lemma Hfield_to_Hsingle : forall l f v,
  (l`.`f ~~> v) ==> ((l+f)%nat ~~> v) \* \[l <> null].
Proof using. intros. xunfold Hfield. hchanges~ hfield_to_hsingle. Qed.

Lemma Hfield_not_null : forall l f `{EA:Enc A} (V:A),
  (l`.`f ~~> V) ==+> \[l <> null].
Proof using. intros. xunfold Hfield. applys~ hfield_not_null. Qed.

Arguments Hfield_not_null : clear implicits.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of substitution *)

Definition Subst1 (y:var) (d:dyn) (t:trm) : trm :=
  subst1 y (enc d) t.

Definition Substn (ys:vars) (ds:dyns) (t:trm) : trm :=
  substn ys (encs ds) t.


(* ********************************************************************** *)
(* * Lifting of triples *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of lifted triples *)

Definition Triple (t:trm) `{EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (Post Q).

Lemma is_local_Triple : forall t A `{EA:Enc A},
  is_local (@Triple t A EA).
Proof using.
  unfold is_local, Triple. intros.
  applys pred_ext_2. intros H Q. iff M.
  { unfold local. hsimpl. split*. hsimpl. }
  { rewrite is_local_triple. unfold local. hchange M. hsimpl ;=> H1 H2 Q1 [P1 P2].
    split*. apply Post_himpl in P2. rewrite !Post_star in P2. auto. }
Qed.

(** Extension of [xlocal] tactic *)

Ltac xlocal_base tt ::=
  try first [ applys is_local_local
            | applys is_local_triple
            | applys is_local_Triple ].


(* ---------------------------------------------------------------------- *)
(* ** Lemma for changing the encoder in a triple *)

Definition PostChange `{Enc A1} (Q1:A1->hprop) `{Enc A2} (Q2:A2->hprop) :=
  forall (X:A1), Q1 X ==> Hexists (Y:A2), \[enc X = enc Y] \* Q2 Y.

Lemma PostChange_refl : forall `{EA:Enc A} (Q:A->hprop),
  PostChange Q Q.
Proof using. intros. unfolds. intros X. hsimpl*. Qed.

Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  PostChange Q1 Q2 ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ rule_consequence (rm M).
  unfold Post. intros v. hpull ;=> V EV. subst. applys N.
Qed.

(** Specializations for converting from and to the raw values *)

Lemma Triple_enc_val_inv :
  forall (t:trm) (H:hprop) (Q1:val->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  (forall (X:val), Q1 X ==> Hexists (Y:A2), \[X = enc Y] \* Q2 Y) ->
  Triple t H Q2.
Proof using.
  introv M N. applys* (@Triple_enc_change val).
Qed.

Lemma Triple_enc_val :
  forall A1 `{EA1:Enc A1} (t:trm) (H:hprop) (Q1:A1->hprop) (Q2:val->hprop),
  Triple t H Q1 ->
  (forall (X:A1), Q1 X ==> Q2 (enc X)) ->
  Triple t H Q2.
Proof using.
  introv M N. applys* Triple_enc_change.
  intros X. hchange (N X). hsimpl~.
Qed.


(* ********************************************************************** *)
(* * Lifting of rules *)

(* ---------------------------------------------------------------------- *)
(* ** Lifting of structural rules *)

Lemma Rule_extract_hexists : forall t `{Enc A} B (J:B->hprop) (Q:A->hprop),
  (forall x, Triple t (J x) Q) ->
  Triple t (hexists J) Q.
Proof using. intros. applys~ rule_extract_hexists. Qed.

Lemma Rule_extract_hprop : forall t (P:Prop) `{Enc A} H (Q:A->hprop),
  (P -> Triple t H Q) ->
  Triple t (\[P] \* H) Q.
Proof using. intros. applys~ rule_extract_hprop. Qed.

Lemma Rule_consequence : forall t H' `{Enc A} (Q':A->hprop) H (Q:A->hprop),
  H ==> H' ->
  Triple t H' Q' ->
  Q' ===> Q ->
  Triple t H Q.
Proof using. introv MH M MQ. applys* rule_consequence MH. Qed.

Lemma Rule_frame : forall t `{Enc A} H (Q:A->hprop) H',
  Triple t H Q ->
  Triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold Triple. rewrite Post_star. applys* rule_frame.
Qed.

Lemma Rule_htop_post : forall t H Q,
  Triple t H (Q \*+ \Top) ->
  Triple t H Q.
Proof using.
  introv M. unfolds Triple. rewrite Post_star in M. applys* rule_htop_post.
Qed.

Lemma Rule_htop_pre : forall t H Q,
  Triple t H Q ->
  Triple t (H \* \Top) Q.
Proof using. introv M. applys* rule_htop_pre. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of term rules *)

Lemma Rule_val : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = enc V ->
  H ==> Q V ->
  Triple (trm_val v) H Q.
Proof using.
  introv E M. applys rule_val. subst.
  unfold Post. hsimpl*.
Qed.

(* DEPRECATEd
Lemma Rule_fun : forall x t1 H (Q:func->hprop),
  H ==> Q (val_fun x t1) ->
  Triple (trm_fun x t1) H Q.
Proof using.
  introv M. applys rule_fun. unfold Post. hsimpl*.
Qed.
*)

Lemma Rule_fix : forall f x t1 H (Q:func->hprop),
  H ==> Q (val_fix f x t1) ->
  Triple (trm_fix f x t1) H Q.
Proof using.
  introv M. applys rule_fix. unfold Post. hsimpl*.
Qed.

Lemma Rule_if : forall t0 t1 t2 H (Q1:bool->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  (forall (b:bool), Triple (if b then t1 else t2) (Q1 b) Q) ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* rule_if.
  { intros b. unfold Post. xpull ;=> V E.
    asserts E': (V = b). { destruct* V. } clears E. subst V. applys M2. }
  { intros v N. unfold Post. hpull ;=> V E. subst. false N.
    rewrite enc_bool_eq. hnfs*. } (* todo : simplify ?*)
Qed.

Lemma Rule_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_seq.
  { applys M1. }
  { intros X. unfold Post. xpull ;=> V E.
    destruct V. applys M2. }
Qed.

Lemma Rule_let : forall x t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (Subst1 x (Dyn X) t2) (Q1 X) Q) ->
  Triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_let M1. intros v. unfold Post at 1.
  xpull. intros V E. subst. applys M2.
Qed.

(* TODO: investigate definition of (Subst A EA x (X:A) t2) *)

Lemma Rule_apps_funs : forall xs F (Vs:dyns) t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  Triple (Substn xs Vs t1) H Q ->
  Triple (trm_apps F (encs Vs)) H Q.
Proof using.
  introv E N M. unfold Triple. applys* rule_apps_funs. rewrite~ length_encs.
Qed.

Lemma Rule_apps_fixs : forall xs (f:var) F (Vs:dyns) t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  Triple (Substn (f::xs) ((Dyn F)::Vs) t1) H Q ->
  Triple (trm_apps F (encs Vs)) H Q.
Proof using.
  introv E N M. unfold Triple. applys* rule_apps_fixs. rewrite~ length_encs.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Rules for loops *)

Lemma Rule_while_raw : forall t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  Triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  Triple (trm_while t1 t2) H Q.
Proof using. introv M. applys rule_while_raw. applys M. Qed.

Lemma Rule_for_raw : forall (x:var) (n1 n2:int) t3 H A `{EA: Enc A} (Q:A->hprop),
  Triple (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  Triple (trm_for x n1 n2 t3) H Q.
Proof using. introv M. applys rule_for_raw. applys M. Qed.
(* TODO: Should it be Subst1 above? *)


(* ---------------------------------------------------------------------- *)
(** Primitive functions *)

Implicit Types v : val.
Implicit Types n : int.
Implicit Types b : bool.

Section RulesStateOps.
Transparent Hsingle.

Lemma Rule_ref : forall A `{EA:Enc A} (V:A),
  Triple (val_ref ``V)
    \[]
    (fun l => l ~~> V).
Proof using. intros. applys_eq rule_ref 1. subst~. Qed.

Lemma Rule_get : forall A `{EA:Enc A} (V:A) l,
  Triple (val_get ``l)
    (l ~~> V)
    (fun x => \[x = V] \* (l ~~> V)).
Proof using.
  introv. unfold Triple, Post. rewrite Hsingle_to_hsingle. xapplys* rule_get.
Qed.

Lemma Rule_set' : forall v1 A2 `{EA2:Enc A2} (V2:A2) l,
  Triple (val_set ``l ``V2)
    (l ~~> v1)
    (fun u => l ~~> V2).
Proof using.
  intros. unfold Triple. rewrite Hsingle_to_hsingle. xapplys rule_set.
  intros. subst. unfold Post. hsimpl~ tt.
Qed.

Lemma Rule_set : forall A1 A2 `{EA1:Enc A1} (V1:A1) `{EA2:Enc A2} (V2:A2) l,
  Triple (val_set l ``V2)
    (l ~~> V1)
    (fun u => l ~~> V2).
Proof using. intros. applys~ Rule_set'. Qed.

End RulesStateOps.

Lemma Rule_alloc : forall n,
  n >= 0 ->
  Triple (val_alloc n)
    \[]
    (fun l => \[l <> null] \* Alloc (abs n) l).
Proof using.
  introv N. unfold Triple, Post. xapplys* rule_alloc.
Qed.

Lemma Rule_alloc_nat : forall (n:nat),
  Triple (val_alloc (n:int))
    \[]
    (fun l => \[l <> null] \* Alloc n l).
Proof using.
  intros. xapplys~ Rule_alloc. { math. }
  { intros. rewrite abs_nat. hsimpl. }
Qed.

Lemma Rule_eq_val : forall v1 v2,
  Triple (val_eq v1 v2)
    \[]
    (fun b => \[ b = isTrue (v1 = v2) ]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_eq. Qed.

Lemma Rule_eq : forall `{EA:Enc A},
  Enc_injective EA ->
  forall (v1 v2 : A),
  Triple (val_eq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { sapply Rule_eq_val. } (* todo: why sapply ? *)
  unfolds. hpulls. hsimpl*. unfolds Enc_injective. unfolds injective.
  rewrite~ Enc_injective_eq.
Qed.

Lemma Rule_add : forall n1 n2,
  Triple (val_add n1 n2)
    \[]
    (fun n => \[n = n1 + n2]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_add. Qed.

Lemma Rule_sub : forall n1 n2,
  Triple (val_sub n1 n2)
    \[]
    (fun n => \[n = n1 - n2]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_sub. Qed.

(* TODO: add other arithmetic primitives *)

Lemma Rule_ptr_add : forall (l:loc) (n:int),
  (l:nat) + n >= 0 ->
  Triple (val_ptr_add l n)
    \[]
    (fun l' => \[(l':nat) = abs ((l:nat) + n)]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_ptr_add. Qed.

Lemma Rule_ptr_add_nat : forall (l:loc) (f:nat),
  Triple (val_ptr_add l f)
    \[]
    (fun l' => \[(l':nat) = (l+f)%nat]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_ptr_add_nat. Qed.



(* ********************************************************************** *)
(* * Bonus *)

(* DEPRECATED?

(* ---------------------------------------------------------------------- *)
(** Reformulation of rule for N-ary functions *)

Definition Spec_funs (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:dyns), length xs = length Xs ->
    Triple (Substn xs Xs t1) ===> Triple (trm_apps F (encs Xs)).

Lemma spec_funs_val_funs : forall xs t1,
  var_distinct xs ->
  xs <> nil ->
  Spec_funs xs t1 (val_funs xs t1).
Proof using. introv D N E M. applys* Rule_apps_funs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Reformulation of rule for N-ary recursive functions *)

Definition Spec_fixs (f:var) (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:dyns), length xs = length Xs ->
    Triple (subst1 f F (Substn xs Xs t1)) ===> Triple (trm_apps F (encs Xs)).

Lemma Spec_fixs_val_fixs : forall f xs t1,
  var_distinct (f::xs) ->
  xs <> nil ->
  Spec_fixs f xs t1 (val_fixs f xs t1).
Proof using. introv D N L M. applys* Rule_apps_fixs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of one argument *)

(* TODO: upper case arguments that are encoded *)

Lemma Rule_app_fun : forall x F V t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fun x t1) ->
  Triple (subst x V t1) H Q ->
  Triple (trm_app F V) H Q.
Proof using. introv EF M. applys* rule_app_fun. Qed.

Definition Spec_fun (x:var) (t1:trm) (F:val) :=
  forall X, Triple (subst x X t1) ===> Triple (trm_app F X).

Lemma Spec_fun_val_fun : forall x t1,
  Spec_fun x t1 (val_fun x t1).
Proof using. introv. intros X H Q M. applys* Rule_app_fun. Qed.

Lemma Rule_fun_spec : forall x t1 H (Q:func->hprop),
  (forall (F:val), Spec_fun x t1 F -> H ==> Q F) ->
  Triple (trm_fun x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fun x t1).
  { applys Spec_fun_val_fun. }
  { applys~ Rule_fun. }
Qed.

Lemma Rule_let_fun : forall f x t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  (forall (F:val), Spec_fun x t1 F -> Triple (subst f F t2) H Q) ->
  Triple (trm_let f (trm_fun x t1) t2) H Q.
Proof using.
  introv M. applys Rule_let (fun F => \[Spec_fun x t1 F] \* H).
  { applys Rule_fun_spec. introv HF. hsimpl~. }
  { intros F. applys Rule_extract_hprop. applys M. }
Qed.

(* ---------------------------------------------------------------------- *)
(** Recursive functions of one argument *)

Lemma Rule_app_fix : forall f x F V t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fix f x t1) ->
  Triple (subst f F (subst x V t1)) H Q ->
  Triple (trm_app F V) H Q.
Proof using. introv EF M. applys* rule_app_fix. Qed.

Definition Spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X, Triple (subst f F (subst x X t1)) ===> Triple (trm_app F X).

Lemma Spec_fix_val_fix : forall f x t1,
  Spec_fix f x t1 (val_fix f x t1).
Proof using. introv. intros X H Q M. applys* Rule_app_fix. Qed.

Lemma Rule_fix_spec : forall f x t1 H (Q:func->hprop),
  (forall (F:val), Spec_fix f x t1 F -> H ==> Q F) ->
  Triple (trm_fix f x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fix f x t1).
  { applys Spec_fix_val_fix. }
  { applys~ Rule_fix. }
Qed.

Lemma Rule_let_fix : forall f x t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  (forall (F:val), Spec_fix f x t1 F -> Triple (subst f F t2) H Q) ->
  Triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M. applys Rule_let (fun F => \[Spec_fix f x t1 F] \* H).
  { applys Rule_fix_spec. introv HF. hsimpl~. }
  { intros F. applys Rule_extract_hprop. applys M. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Derived rules *)

Lemma Rule_if' : forall t0 t1 t2 H (Q1:bool->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  Triple t1 (Q1 true) Q ->
  Triple t2 (Q1 false) Q ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M0 M1 M2. applys* Rule_if. { intros b. case_if*. }
Qed.

Lemma Rule_let_val : forall A1 `{Enc A1} (V1:A1) x v1 t2 H A `{EA: Enc A} (Q:A->hprop),
  v1 = enc V1 ->
  (forall X, X = V1 -> Triple (Subst x (Dyn X) t2) H Q) ->
  Triple (trm_let x (trm_val v1) t2) H Q.
Proof using.
  introv E M. applys rule_let_val. intros X EX. subst. applys~ M.
Qed.

*)

(* ---------------------------------------------------------------------- *)
(** Other rules for loops *)

(*
Lemma Rule_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.

Lemma Rule_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2 H,
  let Q := (fun r => Hexists Y, I false Y) in
  wf R ->
  (H ==> (Hexists b X, I b X) \* \Top) ->
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q) ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) H Q.

Lemma Rule_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  (fun r => \* H) ===> (Q \*+ \Top) ->
  triple (trm_for x n1 n2 t3) H Q.

Lemma Rule_for_le : forall Q1 x n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst x n1 t3) H Q1 ->
  triple (trm_for x (n1+1) n2 t3) (Q1 val_unit) Q ->
  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]) ->
  triple (trm_for x n1 n2 t3) H Q.

Lemma Rule_for_inv : forall (I:int->hprop) H' x n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 ->
     triple (subst x i t3) (I i) (fun r => I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
*)
