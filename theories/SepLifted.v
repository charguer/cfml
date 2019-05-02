(**

This file extends [SepBase.v] by "lifting" heap predicates
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
From Sep Require Import SepBase.
Import LibList.
Generalizable Variables A B.

Open Scope trm_scope.
Open Scope heap_scope.

Implicit Types l : loc.
Implicit Types u : unit.
Implicit Types z : bind.
Implicit Types v : val.
Implicit Types vs : vals.
Implicit Types n : int.
Implicit Types b : bool.


(* ********************************************************************** *)
(* * Encoders *)

(* ---------------------------------------------------------------------- *)
(* ** Encoders *)

Class Enc (A:Type) :=
  make_Enc { enc : A -> val }.

Notation "`` V" := (enc V) (at level 8, format "`` V").

(** Notation for lists of encoded values *)

Notation "``[ ]" :=
  (@nil val) (format "``[ ]", only parsing) : enc_scope.
Notation "``[ x ]" :=
  (cons (enc x) nil) : enc_scope.
Notation "``[ x , y , .. , z ]" :=
  (cons (enc x) (cons (enc y) .. (cons (enc z) nil) ..)) : enc_scope.

Open Scope enc_scope.
Delimit Scope enc_scope with enc.


(** TEMPORARY: below is a patch for TLC tactics to prevent undesired
   eager instantiation of the typeclasses [Enc]. *)

Ltac app_evar t A cont ::=
  let x := fresh "TEMP" in
  let T :=
    match A with Enc ?X => constr:(id Enc X) | _ => constr:(A) end in
  evar (x:T);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.


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
(* ** Func type *)

(** Let [func] be an alias for [val], used to describing functions. 
    This type name helps deriving instances of encoders. *)

Definition func := val.

(* ---------------------------------------------------------------------- *)
(* ** ConstrType type *)

(** Let [constrtype] be a type to represent data constructors. *)

Inductive tyconstr : Type :=
  | constr : idconstr -> vals -> tyconstr.


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

Instance Enc_tyconstr : Enc tyconstr.
Proof using. constructor. applys (fun (cstr:tyconstr) => 
  match cstr with constr id vs => val_constr id vs end). Defined.

Instance Enc_option : forall `{Enc A}, Enc (option A).
Proof using. constructor. applys (fun o => match o with
  | None => val_constr "none" nil
  | Some x => val_constr "some" ((``x)::nil)
  end). Defined.

Instance Enc_list : forall `{Enc A}, Enc (list A).
Proof using. constructor. applys (fix f (l:list A) :=
  match l with
  | nil => val_constr "nil" nil
  | x::l' => val_constr "cons" ((``x)::(f l')::nil)
  end). Defined.

Global Opaque Enc_dyn Enc_loc Enc_unit Enc_bool Enc_int
              Enc_func Enc_val Enc_prim Enc_tyconstr
              Enc_list Enc_option.


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

Lemma enc_constr_eq : forall id vs,
  enc (constr id vs) = val_constr id vs.
Proof using. auto. Qed.

Lemma enc_list_none : forall `{Enc A},
  enc (@None A) = val_constr "none" nil.
Proof using. auto. Qed.

Lemma enc_list_some : forall `{Enc A} x,
  enc (Some x) = val_constr "some" (``x :: nil).
Proof using. auto. Qed.

Lemma enc_list_nil : forall `{Enc A},
  enc (@nil A) = val_constr "nil" nil.
Proof using. auto. Qed.

Lemma enc_list_cons : forall `{Enc A} x (l:list A),
  enc (x::l) = val_constr "cons" (``x :: ``l :: nil).
Proof using. auto. Qed.

(** Specification of encoders for values of type [dyn] *)

Lemma enc_dyn_eq_dyn_to_val : forall (d:dyn),
  enc d = dyn_to_val d.
Proof using. auto. Qed.

(** The encoding of a dynamic value [V] is the same as the encoding of V *)

Lemma enc_dyn_make : forall `{EA:Enc A} (V:A),
  enc (dyn_make V) = enc V.
Proof using. auto. Qed.

(** [rew_enc] normalizes all encoders. *)

Hint Rewrite enc_dyn_make enc_loc_eq enc_unit_eq enc_bool_eq enc_int_eq
             enc_func_eq enc_val_eq enc_prim_eq enc_constr_eq
             @enc_list_none @enc_list_some @enc_list_nil @enc_list_cons : rew_enc.

Tactic Notation "rew_enc" :=
  autorewrite with rew_enc.
Tactic Notation "rew_enc" "in" hyp(H) :=
  autorewrite with rew_enc in H.
Tactic Notation "rew_enc" "in" "*" :=
  autorewrite with rew_enc in *.

(** [rew_enc] normalizes only the [dyn] encoder. *)

Hint Rewrite @enc_dyn_make : rew_enc_dyn.

Tactic Notation "rew_enc_dyn" :=
  autorewrite with rew_enc_dyn.
Tactic Notation "rew_enc_dyn" "in" hyp(H) :=
  autorewrite with rew_enc_dyn in H.
Tactic Notation "rew_enc_dyn" "in" "*" :=
  autorewrite with rew_enc_dyn in *.


(* ---------------------------------------------------------------------- *)
(* ** Injectivity of encoders *)

(* ** Injectivity of encoders for entire types *)

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

Lemma Enc_injective_option : forall A (EA:Enc A), 
  Enc_injective EA ->
  Enc_injective (@Enc_option A EA).
Proof using.
  introv HEA. intros o1 o2 E.
  induction o1; destruct o2; simpls; tryfalse.
  { rew_enc in E. inverts E. fequals*. }
  { auto. }
Qed.

Lemma Enc_injective_list : forall A (EA:Enc A), 
  Enc_injective EA ->
  Enc_injective (@Enc_list A EA).
Proof using.
  introv HEA. intros l1 l2 E. gen l2.
  induction l1; intros; destruct l2; simpls; tryfalse.
  { auto. }
  { rew_enc in E. inverts E. fequals*. }
Qed.

Hint Resolve Enc_injective_loc Enc_injective_unit Enc_injective_bool
             Enc_injective_int @Enc_injective_option @Enc_injective_list.
             (* TODO: put in a base? *)

(* ** Injectivity of encoders for specific values
      (useful in many cases to avoid the need for an hypothesis
      of the form [Enc_injective EA] *)

Definition Enc_injective_value A `{EA:Enc A} (V1:A) :=
  forall V2, (enc V1 = enc V2) -> (V1 = V2).

Lemma Enc_injective_value_eq_l : forall `{EA:Enc A} (V1:A),
  Enc_injective_value V1 ->
  forall V2, (enc V1 = enc V2) = (V1 = V2).
Proof using. introv E. extens. iff M. { applys~ E. } { subst~. } Qed.

Lemma Enc_injective_value_eq_r : forall `{EA:Enc A} (V1:A),
  Enc_injective_value V1 ->
  forall V2, (enc V2 = enc V1) = (V2 = V1).
Proof using. introv E. extens. iff M. { symmetry. applys~ E. } { subst~. } Qed.

Lemma Enc_injective_nil : forall `{EA:Enc A},
  Enc_injective_value (@nil A).
Proof using.
  intros A EA l E. destruct l; intros; simpls; tryfalse. { auto. }
Qed.

Lemma Enc_injective_none : forall `{EA:Enc A},
  Enc_injective_value (@None A).
Proof using.
  intros A EA o E. destruct o; intros; simpls; tryfalse. { auto. }
Qed.

Hint Resolve @Enc_injective_nil @Enc_injective_none.


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

(* DEPRECATED ?*)


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
  | val_fixs f xs t => Dyn (v:func)
  | val_constr id vs => Dyn (constr id vs)
     (* Note: universe constraints prevent decoding to 
        [Dyn (Constr id (List.map decode vs))] *)
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

(** [LiftPost Q] converts a postcondition of type [A->hprop] into a
    postcondition of type [val->hprop], where [A] is encodable. *)

Definition LiftPost A `{Enc A} (Q:A->hprop) : val->hprop :=
  fun v => \exists V, \[v = enc V] \* Q V.

(** [LiftPost] is covariant *)

Lemma LiftPost_himpl : forall `{Enc A} Q Q',
  Q ===> Q' ->
  LiftPost Q ===> LiftPost Q'.
Proof using.
  introv M. unfold LiftPost. intros v.
  hpull. intros x E. subst v. hsimpl*.
Qed.

Local Hint Resolve LiftPost_himpl.

(** [LiftPost] distributes over the star *)

Lemma LiftPost_star : forall `{Enc A} Q H,
  LiftPost (Q \*+ H) = (LiftPost Q) \*+ H.
Proof using.
  intros. unfold LiftPost. applys fun_ext_1.
  intros v. applys himpl_antisym; hsimpl~.
Qed.

(** [LiftPost] preserves [is_local] *)

Lemma is_local_LiftPost : forall A `{Enc A} (F:~~val),
  is_local F ->
  is_local (fun H (Q:A->hprop) => F H (LiftPost Q)).
Proof using.
  introv L. rename H into EQ. applys is_local_intro.
  intros H Q M. applys~ is_local_elim.
  hchange M. hpull ;=> H1 H2 Q1 (N1&N2).
  hsimpl H1 H2 (LiftPost Q1). splits~. 
  do 2 rewrite <- LiftPost_star. applys~ LiftPost_himpl.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of heap predicates *)

(** Singleton: [l ~~> V] describes a singleton heap at location [l]
    with contents [V], where the value [V] has some encodable type [A]. *)

Definition Hsingle `{EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '~~>' V" := (l ~> Hsingle V)
  (at level 32, no associativity) : heap_scope.

Lemma Hsingle_to_hsingle : forall `{EA:Enc A} (l:loc) (V:A),
  (l ~~> V) = hsingle l (enc V).
Proof using. auto. Qed.

Lemma Hsingle_not_null : forall l `{EA:Enc A} (V:A),
  (l ~~> V) ==+> \[l <> null].
Proof using. intros. xunfold Hsingle. applys hsingle_not_null. Qed.

Arguments Hsingle_not_null : clear implicits.

(** Field: [ l `.` f ~~> V ] describes the ownership of a record field
    storing one encodable value [V]. *)

Definition Hfield `{EA:Enc A} (V:A) (l_f:loc*field) : hprop :=
  let '(l,f) := l_f in
  hfield l f (enc V).

Notation "l `.` f '~~>' V" := ((l,f) ~> Hfield V)
  (at level 32, f at level 0, no associativity,
   format "l `.` f  '~~>'  V") : heap_scope.

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

(** [Subst1 y d t] substitues variable [y] with the encoding of [V] in [t]. *)

Definition Subst1 A `{EA:Enc A} (z:bind) (V:A) (t:trm) : trm :=
  subst1 z (enc V) t.

(** [Substn ys ds t] substitues the list of variables [ys] with the
    encodings of the list of dynamic values [ds] in [t]. *)

Definition Substn (ys:vars) (ds:dyns) (t:trm) : trm :=
  substn ys (encs ds) t.


(* ********************************************************************** *)
(* * Lifting of triples *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of lifted triples *)

(** [Triple t H Q] describes a triple where the postcondition [Q] has
    type [A->hprop] for some encodable type [A] *)

Definition Triple (t:trm) `{EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (LiftPost Q).

(** [Triple] satisfies [is_local], like [triple] does. *)

Lemma is_local_Triple : forall t A `{EA:Enc A},
  is_local (@Triple t A EA).
Proof using. intros. applys is_local_LiftPost. applys is_local_triple. Qed.

Hint Resolve @is_local_Triple.


(* ---------------------------------------------------------------------- *)
(* ** Lemma for changing the encoder in a triple *)

(** [RetypePost Q1 Q2] asserts that [Q1] of type [A1->hprop] entails
    [Q2] of type [A2->hprop]. This predicate is used in the lemmas
    that enable changing the type of the postcondition in a triple. *)

Definition RetypePost `{Enc A1} (Q1:A1->hprop) `{Enc A2} (Q2:A2->hprop) :=
  forall (X:A1), Q1 X ==> \exists (Y:A2), \[enc X = enc Y] \* Q2 Y.

Lemma RetypePost_refl : forall `{EA:Enc A} (Q:A->hprop),
  RetypePost Q Q.
Proof using. intros. unfolds. intros X. hsimpl*. Qed.

(* NEEDED TODO RENAME ?*)
Lemma RetypePost_same : forall `{EA:Enc A} (Q1 Q2:A->hprop),
  Q1 ===> Q2 ->
  RetypePost Q1 Q2.
Proof using. introv M. unfolds. intros X. hchanges* M. Qed.

(* NEEDED ?*)
Lemma RetypePost_same_subst : forall H `{EA:Enc A} (V:A) (Q:A->hprop),
  H ==> Q V ->
  RetypePost (fun x => \[x = V] \* H) Q.
Proof using. introv M. applys RetypePost_same. hpull ;=> ? ->. auto. Qed.


Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  RetypePost Q1 Q2 ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ triple_conseq (rm M).
  unfold LiftPost. intros v. hpull ;=> V EV. subst. applys N.
Qed.

(** Specialization of [Triple_enc_change] for converting from a postcondition
    of type [val->hprop]  *)

Lemma Triple_enc_val_inv :
  forall (t:trm) (H:hprop) (Q1:val->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  (forall (X:val), Q1 X ==> \exists (Y:A2), \[X = enc Y] \* Q2 Y) ->
  Triple t H Q2.
Proof using.
  introv M N. applys* (@Triple_enc_change val).
Qed.

(** Specialization of [Triple_enc_change] for converting to a postcondition
    of type [val->hprop]  *)

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

Lemma Triple_conseq : forall t H' `{Enc A} (Q':A->hprop) H (Q:A->hprop),
  H ==> H' ->
  Triple t H' Q' ->
  Q' ===> Q ->
  Triple t H Q.
Proof using. intros. applys* is_local_conseq. Qed.

Lemma Triple_frame : forall t `{Enc A} H (Q:A->hprop) H',
  Triple t H Q ->
  Triple t (H \* H') (Q \*+ H').
Proof using. intros. applys* is_local_frame. Qed.

Lemma Triple_ramified_frame_hgc : forall t `{Enc A} H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q \*+ \GC) ->
  Triple t H Q.
Proof using. intros. applys* is_local_ramified_frame_hgc. Qed.

Lemma Triple_ramified_frame : forall t `{Enc A} H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  Triple t H Q.
Proof using. intros. applys* is_local_ramified_frame. Qed.

Lemma Triple_hgc_pre : forall t `{Enc A} H (Q:A->hprop),
  Triple t H Q ->
  Triple t (H \* \GC) Q.
Proof using. intros. applys* is_local_hgc_pre. Qed.

Lemma Triple_hgc_post : forall t `{Enc A} H (Q:A->hprop),
  Triple t H (Q \*+ \GC) ->
  Triple t H Q.
Proof using. intros. applys~ is_local_hgc_post. Qed.

Lemma Triple_hexists : forall t `{Enc A} B (J:B->hprop) (Q:A->hprop),
  (forall x, Triple t (J x) Q) ->
  Triple t (hexists J) Q.
Proof using. intros. applys~ is_local_hexists. Qed.

Lemma Triple_hforall : forall B (x:B) t (J:B->hprop) `{EA:Enc A} (Q:A->hprop),
  Triple t (J x) Q ->
  Triple t (hforall J) Q.
Proof using. intros. applys* is_local_hforall. Qed.

Lemma Triple_hforall_exists : forall t B (J:B->hprop) `{EA:Enc A} (Q:A->hprop),  (* TODO: needed? *)
  (exists x, Triple t (J x) Q) ->
  Triple t (hforall J) Q.
Proof using. intros. applys~ is_local_hforall_exists. Qed.

Lemma Triple_hprop : forall t (P:Prop) `{Enc A} H (Q:A->hprop),
  (P -> Triple t H Q) ->
  Triple t (\[P] \* H) Q.
Proof using. intros. applys~ is_local_hprop. Qed.

Lemma Triple_hwand_hpure_l : forall t (P:Prop) H `{EA:Enc A} (Q:A->hprop),
  P ->
  Triple t H Q ->
  Triple t (\[P] \-* H) Q.
Proof using. intros. applys~ is_local_hwand_hpure_l. Qed.

Lemma Triple_hor : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H1 Q ->
  Triple t H2 Q ->
  Triple t (hor H1 H2) Q.
Proof using. intros. applys~ is_local_hor. Qed.

Lemma Triple_hand_l : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H1 Q ->
  Triple t (hand H1 H2) Q.
Proof using. intros. applys~ is_local_hand_l. Qed.

Lemma Triple_hand_r : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H2 Q ->
  Triple t (hand H1 H2) Q.
Proof using. intros. applys~ is_local_hand_r. Qed.

Lemma Triple_conseq_frame_hgc : forall t H1 H2 `{Enc A} (Q1 Q:A->hprop) H,
  Triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  Triple t H Q.
Proof using. intros. applys* is_local_conseq_frame_hgc. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of evaluation context rules *)

(** Not needed? *)
Lemma Triple_evalctx : forall C t1 H,
 forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  evalctx C ->
  Triple t1 H Q1 ->
  (forall (V:A1), Triple (C ``V) (Q1 V) Q) ->
  Triple (C t1) H Q.
Proof using.
  introv EC M1 M2. applys* triple_evalctx. 
  { intros v. unfold LiftPost. xpull ;=> V ->. applys M2. }
Qed.

(** Substitution commutes with evaluation contexts, for triples *)

Lemma Triple_isubst_evalctx : forall E C t1 H,
 forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  evalctx C ->
  Triple (isubst E t1) H Q1 ->
  (forall V, Triple (isubst E (C ``V)) (Q1 V) Q) ->
  Triple (isubst E (C t1)) H Q.
Proof using.
  introv EC M1 M2. applys* triple_isubst_evalctx. 
  { intros v. unfold LiftPost. xpull ;=> V ->. applys M2. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of term rules *)

Lemma Triple_val : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = enc V ->
  H ==> Q V ->
  Triple (trm_val v) H Q.
Proof using.
  introv E M. applys triple_val. subst.
  unfold LiftPost. hsimpl*.
Qed.

Lemma Triple_fixs : forall f xs t1 H (Q:func->hprop),
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  Triple (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. applys* triple_fixs. unfold LiftPost. hchanges* M.
Qed.

Lemma Triple_constr : forall id vs H (Q:tyconstr->hprop),
  H ==> Q (constr id vs) ->
  Triple (trm_constr id (LibList.map trm_val vs)) H Q.
Proof using. introv M. applys triple_constr. unfold LiftPost. hchanges* M. Qed.

Lemma Triple_constr_trm : forall id ts t1 vs H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 -> 
  (forall (X:A1), Triple (trm_constr id ((trms_vals vs)++(trm_val ``X)::ts)) (Q1 X) Q) ->
  Triple (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. applys* triple_constr_trm M1.
  intros v. unfold LiftPost at 1. xpull ;=> V ->. subst. applys M2.
Qed.

Lemma Triple_let : forall z t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (Subst1 z X t2) (Q1 X) Q) ->
  Triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_let M1. 
  intros v. unfold LiftPost at 1. xpull ;=> V ->. subst. applys M2.
Qed.

Lemma Triple_seq : forall t1 t2 H,
  forall A `{EA:Enc A} (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_seq.
  { applys M1. }
  { intros X. unfold LiftPost. xpull ;=> V E.
    destruct V. applys M2. }
Qed.

Lemma Triple_if : forall t0 t1 t2 H (Q1:bool->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  (forall (b:bool), Triple (if b then t1 else t2) (Q1 b) Q) ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* triple_if.
  { intros b. unfold LiftPost. xpull ;=> V E.
    asserts E': (V = b). { destruct* V. } clears E. subst V. applys M2. }
  { intros v N. unfold LiftPost. hpull ;=> V ->. false N.
    rewrite enc_bool_eq. hnfs*. } (* LATER : simplify? *)
Qed.

Lemma Triple_if_bool : forall (b:bool) t1 t2 H A `{EA:Enc A} (Q:A->hprop),
  Triple (if b then t1 else t2) H Q ->
  Triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. applys triple_if_bool. { applys M1. }
Qed.

Lemma Triple_apps_funs : forall xs F vs t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_funs xs t1) ->
  var_funs (length vs) xs ->
  Triple (substn xs vs t1) H Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv E N M. unfold Triple. applys* triple_apps_funs.
Qed.

Lemma Triple_apps_fixs : forall xs (f:var) F vs t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fixs f xs t1) ->
  var_fixs f (length vs) xs ->
  Triple (substn (f::xs) (F::vs) t1) H Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv E N M. unfold Triple. applys* triple_apps_fixs.
Qed.

Lemma Triple_while_raw : forall t1 t2 H A `{EA: Enc A} (Q:A->hprop),
  Triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  Triple (trm_while t1 t2) H Q.
Proof using. introv M. applys triple_while_raw. applys M. Qed.

Lemma Triple_for_raw : forall (x:var) (n1 n2:int) t3 H A `{EA: Enc A} (Q:A->hprop),
  Triple (
    If (n1 <= n2)
      then (trm_seq (Subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  Triple (trm_for x n1 n2 t3) H Q.
Proof using. introv M. applys triple_for_raw. applys M. Qed.

Lemma Triple_match_trm : forall t1 pts H,
  forall A `{EA:Enc A} (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 -> 
  (forall (X:A1), Triple (trm_match (``X) pts) (Q1 X) Q) ->
  Triple (trm_match t1 pts) H Q.
Proof using.
  introv M1 M2. applys* triple_match_trm.
  intros v. unfold LiftPost at 1. xpull ;=> V ->. applys M2.
Qed.

Lemma Triple_match : forall v p t1 pts H `{EA:Enc A} (Q:A->hprop),
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> Triple (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> Triple (trm_match v pts) H Q) ->
  Triple (trm_match v ((p,t1)::pts)) H Q.
Proof using. 
  introv M1 M2. applys* triple_match.
  { introv HG Hv. applys* M1. }
  { introv HG Hv. applys* M2. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Lifting of specitification of primitive functions *)

Section RulesStateOps.
Transparent Hsingle.

Lemma Triple_ref : forall A `{EA:Enc A} (V:A),
  Triple (val_ref ``V)
    \[]
    (fun l => l ~~> V).
Proof using. intros. applys_eq triple_ref 1. subst~. Qed.

Lemma Triple_get : forall A `{EA:Enc A} (V:A) l,
  Triple (val_get ``l)
    (l ~~> V)
    (fun x => \[x = V] \* (l ~~> V)).
Proof using.
  introv. unfold Triple, LiftPost. rewrite Hsingle_to_hsingle. xapplys* triple_get.
Qed.

(** Specification of [set] allowing for change in type (i.e. strong update). *)

Lemma Triple_set_strong : forall A1 A2 `{EA1:Enc A1} (V1:A1) `{EA2:Enc A2} (V2:A2) l,
  Triple (val_set l ``V2)
    (l ~~> V1)
    (fun u => l ~~> V2).
Proof using.
  intros. unfold Triple. rewrite Hsingle_to_hsingle. xapplys triple_set.
  intros. subst. unfold LiftPost. hsimpl~ tt.
Qed.

Lemma Triple_set_strong_val : forall v1 A2 `{EA2:Enc A2} (V2:A2) l,
  Triple (val_set ``l ``V2)
    (l ~~> v1)
    (fun u => l ~~> V2).
Proof using.
  intros. applys Triple_set_strong.
Qed.

(** Specification of [set] for writes preserving the type. *)

Lemma Triple_set : forall A1 `{EA1:Enc A1} (V1 V2:A1) l,
  Triple (val_set ``l ``V2)
    (l ~~> V1)
    (fun u => l ~~> V2).
Proof using.
  intros. applys Triple_set_strong.
Qed.

Lemma Triple_alloc : forall n,
  n >= 0 ->
  Triple (val_alloc n)
    \[]
    (fun l => \[l <> null] \* Alloc (abs n) l).
Proof using.
  introv N. unfold Triple, LiftPost. xapplys* triple_alloc.
Qed.

Lemma Triple_alloc_nat : forall (k:nat),
  Triple (val_alloc (k:int))
    \[]
    (fun l => \[l <> null] \* Alloc k l).
Proof using.
  intros. xapplys~ Triple_alloc. { math. }
  { intros. rewrite abs_nat. hsimpl. }
Qed.

End RulesStateOps.

Lemma Triple_ptr_add : forall (l:loc) (n:int),
  (l:nat) + n >= 0 ->
  Triple (val_ptr_add l n)
    \[]
    (fun l' => \[(l':nat) = abs ((l:nat) + n)]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_ptr_add. Qed.

Lemma Triple_ptr_add_nat : forall (l:loc) (f:nat),
  Triple (val_ptr_add l f)
    \[]
    (fun l' => \[(l':nat) = (l+f)%nat]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_ptr_add_nat. Qed.

Lemma Triple_neg : forall b1,
  Triple (val_neg b1)
    \[]
    (fun b => \[b = neg b1]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_neg. Qed.

Lemma Triple_opp : forall n1,
  Triple (val_opp n1)
    \[]
    (fun n => \[n = - n1]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_opp. Qed.

Lemma Triple_eq_val : forall v1 v2,
  Triple (val_eq v1 v2)
    \[]
    (fun b => \[ b = isTrue (v1 = v2) ]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_eq. Qed.

Lemma Triple_eq : forall `{EA:Enc A},
  Enc_injective EA ->
  forall (v1 v2 : A),
  Triple (val_eq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { sapply Triple_eq_val. } (* todo: why sapply ? *)
  unfolds. hpull ;=> ? ->. hsimpl*. rewrite~ Enc_injective_eq.
Qed.

Lemma Triple_neq_val : forall v1 v2,
  Triple (val_neq v1 v2)
    \[]
    (fun b => \[ b = isTrue (v1 <> v2) ]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_neq. Qed.

Lemma Triple_neq : forall `{EA:Enc A},
  Enc_injective EA ->
  forall (v1 v2 : A),
  Triple (val_neq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { sapply Triple_neq_val. } 
  unfolds. hpull ;=> ? ->. hsimpl*. rewrite* Enc_injective_eq.
Qed.

Lemma Triple_add : forall n1 n2,
  Triple (val_add n1 n2)
    \[]
    (fun n => \[n = n1 + n2]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_add. Qed.

Lemma Triple_sub : forall n1 n2,
  Triple (val_sub n1 n2)
    \[]
    (fun n => \[n = n1 - n2]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_sub. Qed.

Lemma Triple_mul : forall n1 n2,
  Triple (val_mul n1 n2)
    \[]
    (fun n => \[n = n1 * n2]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_mul. Qed.

Lemma Triple_div : forall n1 n2,
  n2 <> 0 ->
  Triple (val_div n1 n2)
    \[]
    (fun n => \[n = Z.quot n1 n2]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_div. Qed.

Lemma Triple_mod : forall n1 n2,
  n2 <> 0 ->
  Triple (val_mod n1 n2)
    \[]
    (fun n => \[n = Z.rem n1 n2]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_mod. Qed.

Lemma Triple_le : forall n1 n2,
  Triple (val_le n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 <= n2)]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_le. Qed.

Lemma Triple_lt : forall n1 n2,
  Triple (val_lt n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 < n2)]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_lt. Qed.

Lemma Triple_ge : forall n1 n2,
  Triple (val_ge n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 >= n2)]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_ge. Qed.

Lemma Triple_gt : forall n1 n2,
  Triple (val_gt n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 > n2)]).
Proof using. intros. unfold Triple, LiftPost. xapplys* triple_gt. Qed.




(* ********************************************************************** *)
(* * Extra -- not needed? *)

Lemma Triple_apps_funs' : forall xs F (Vs:dyns) t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  Triple (Substn xs Vs t1) H Q ->
  Triple (trm_apps F (encs Vs)) H Q.
Proof using.
  introv E N M. unfold Triple. applys* triple_apps_funs. rewrite~ length_encs.
Qed.

Lemma Triple_apps_fixs' : forall xs (f:var) F (Vs:dyns) t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  Triple (Substn (f::xs) ((Dyn F)::Vs) t1) H Q ->
  Triple (trm_apps F (encs Vs)) H Q.
Proof using.
  introv E N M. unfold Triple. applys* triple_apps_fixs. rewrite~ length_encs.
Qed.