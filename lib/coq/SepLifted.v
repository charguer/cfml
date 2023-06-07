(**

This file extends [SepBase.v] by "lifting" heap predicates
and triples so as to express specifications using logical values,
as opposed to deeply-embedded values.

The relationship between the two kind of values is implemented
using encoding functions, called encoders, realized using
typeclasses.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From CFML Require Import SepBase.
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

Class Enc (A:Type) : Type := make_Enc
  { enc : A -> val;
    enc_inj : injective enc }.

Hint Mode Enc + : typeclass_instances.

Notation "`` V" := (enc V) (at level 8, format "`` V").

(** Notation for lists of encoded values *)

Declare Scope enc_scope.
Open Scope enc_scope.
Delimit Scope enc_scope with enc.

Notation "``[ ]" :=
  (@nil val) (only parsing) : enc_scope.
Notation "``[ x ]" :=
  (cons (enc x) nil) : enc_scope.
Notation "``[ x , y , .. , z ]" :=
  (cons (enc x) (cons (enc y) .. (cons (enc z) nil) ..)) : enc_scope.

(* LATER: Below is a patch for TLC tactics to prevent undesired
   eager instantiation of the typeclasses [Enc].
   This patch could be presumably removed in v8.12. *)

Ltac app_evar t A cont ::=
  let x := fresh "TEMP" in
  let T :=
    match A with Enc ?X => constr:(id Enc X) | _ => constr:(A) end in
  evar (x:T);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas to exploit injectivity *)

Lemma Enc_eq_eq : forall A (EA:Enc A) (V1 V2:A),
  (enc V1 = enc V2) = (V1 = V2).
Proof using.
  intros. lets E: (@enc_inj A EA). extens. iff M. { applys~ E. } { subst~. }
Qed.

Lemma Enc_eq_inv : forall A (EA:Enc A) (V1 V2:A),
  (enc V1 = enc V2) ->
  (V1 = V2).
Proof using. introv M. rewrite* Enc_eq_eq in M. Qed.

Lemma Enc_neq : forall A (EA:Enc A) (V1 V2:A),
  (V1 <> V2) ->
  (enc V1 <> enc V2).
Proof using. introv M E. applys M. applys Enc_eq_inv E. Qed.

Lemma Enc_neq_inv : forall A (EA:Enc A) (V1 V2:A),
  (enc V1 <> enc V2) ->
  (V1 <> V2).
Proof using. introv M E. subst*. Qed.

Lemma Enc_neq_eq : forall A (EA:Enc A) (V1 V2:A),
  (enc V1 <> enc V2) = (V1 <> V2).
Proof using.
  intros. extens. iff M. { applys Enc_neq_inv M. } { applys Enc_neq M. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Tactic to prove injectivity *)

Ltac injective_enc_core tt :=
  let x := fresh "x" in
  let y := fresh "y" in
  let E := fresh "E" in
  intros; intros x y E; gen y; induction x; intros; destruct y; simpls; tryfalse;
   try solve [ inverts E; fequals; eauto using Enc_eq_inv ].

Tactic Notation "injective_enc_prove" :=
  injective_enc_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Representation of values packed with their type and encoder *)

(** Representation of dependent pairs *)

Record dyn := dyn_make {
  dyn_type : Type;
  dyn_enc : Enc dyn_type;
  dyn_value : dyn_type }.

Arguments dyn_make [dyn_type] {dyn_enc}.

Notation "'Dyn' V" := (dyn_make V)
  (at level 69) : heap_scope.

Lemma dyn_inj : forall A (EA:Enc A) (x y : A),
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

Lemma dyn_to_val_dyn_make : forall A (EA:Enc A) (V:A),
  dyn_to_val (dyn_make V) = enc V.
Proof using. auto. Qed.

(** List of [dyns] *)

Definition dyns := list dyn.


(* ---------------------------------------------------------------------- *)
(* ** Func type *)

(** Let [func] be an alias for [val], used to describing functions.
    This type name helps deriving instances of encoders. *)

Definition func := val.

(* TODO: use or deprecate ... *)


(* ---------------------------------------------------------------------- *)
(* ** ConstrType type *)

(* DEPRECATED
(** Let [constrtype] be a type to represent data constructors. *)

Inductive tyconstr : Type :=
  | constr : idconstr -> vals -> tyconstr.

*)

(* ---------------------------------------------------------------------- *)
(* ** Encoder instances *)

(* DEPRECATED
Global Instance Enc_dyn : Enc dyn.
Proof using. applys make_Enc dyn_to_val.
  { intros [AX EAX X] [AY EAY Y]. do 2 rewrite dyn_to_val_dyn_make.
    intros. fequals. auto. simpl. hnf. simpl. Defined.
*)


Definition enc_val_impl := (fun (x:val) => x).

Lemma injective_enc_val_impl : injective enc_val_impl.
Proof using. introv E. auto. Qed.

Global Instance Enc_val : Enc val := make_Enc injective_enc_val_impl.

Lemma enc_val : forall (v:val),
  enc v = v.
Proof using. auto. Qed.

Lemma enc_func : forall (f:func),
  enc f = f.
Proof using. auto. Qed.


Definition enc_loc_impl := val_loc.

Lemma injective_enc_loc_impl : injective enc_loc_impl.
Proof using. injective_enc_prove. Qed.

Global Instance Enc_loc : Enc loc := make_Enc injective_enc_loc_impl.

Lemma enc_loc : forall (l:loc),
  enc l = val_loc l.
Proof using. auto. Qed.


Definition enc_unit_impl := fun (_:unit) => val_unit.

Lemma injective_enc_unit_impl : injective enc_unit_impl.
Proof using. injective_enc_prove. Qed.

Global Instance Enc_unit : Enc unit := make_Enc injective_enc_unit_impl.

Lemma enc_unit : forall (u:unit),
  enc u = val_unit.
Proof using. auto. Qed.


Definition enc_bool_impl := val_bool.

Lemma injective_enc_bool_impl : injective enc_bool_impl.
Proof using. injective_enc_prove. Qed.

Global Instance Enc_bool : Enc bool := make_Enc injective_enc_bool_impl.

Lemma enc_bool : forall (b:bool),
  enc b = val_bool b.
Proof using. auto. Qed.


Definition enc_int_impl := val_int.

Lemma injective_enc_int_impl : injective enc_int_impl.
Proof using. introv E. inverts* E. Qed.

Global Instance Enc_int : Enc int := make_Enc injective_enc_int_impl.

Lemma enc_int : forall (n:int),
  enc n = val_int n.
Proof using. auto. Qed.

(* DEPRECATED

Instance Enc_func : Enc func.
Proof using. constructor. applys (fun (x:func) => x). Defined.

Instance Enc_prim : Enc prim.
Proof using. constructor. applys (fun (p:prim) => val_prim p). Defined.

Instance Enc_tyconstr : Enc tyconstr.
Proof using. constructor. applys (fun (cstr:tyconstr) =>
  match cstr with constr id vs => val_constr id vs end). Defined.

*)


Section EncPair.
Context A1 `{EA1:Enc A1} A2 `{EA2:Enc A2}.

Definition enc_pair_impl := (fun p : A1*A2 =>
  let '(x1,x2) := p in val_constr "tuple" (``x1 :: ``x2 :: nil)).

Lemma injective_enc_pair_impl : injective enc_pair_impl.
Proof using. intros [x1 x2] [y1 y2] E. inverts E. fequals; applys* Enc_eq_inv. Qed.

Global Instance Enc_pair : Enc (prod A1 A2) := make_Enc injective_enc_pair_impl.

Lemma enc_pair : forall (x1:A1) (x2:A2),
  enc (x1,x2) = val_constr "tuple" (``x1 :: ``x2 :: nil).
Proof using. auto. Qed.

End EncPair.


Section EncOption.
Context A1 `{EA1:Enc A1}.

Definition enc_option_impl :=
  fun (o:option A1) => match o with
  | None => val_constr "none" nil
  | Some x => val_constr "some" ((``x)::nil)
  end.

Lemma injective_enc_option_impl : injective enc_option_impl.
Proof using. injective_enc_prove. Qed.

Global Instance Enc_option : Enc (option A1) := make_Enc injective_enc_option_impl.

Lemma enc_option_none :
  enc (@None A1) = val_constr "none" nil.
Proof using. auto. Qed.

Lemma enc_option_some : forall (x:A1),
  enc (Some x) = val_constr "some" (``x :: nil).
Proof using. auto. Qed.

End EncOption.


Section EncList.

Definition enc_list_impl := fix f A1 (EA1:Enc A1) (l:list A1) : val :=
  match l with
  | nil => val_constr "nil" nil
  | x::l' => val_constr "cons" ((``x)::(f A1 EA1 l')::nil)
  end.

Lemma injective_enc_list_impl : forall A1 (EA1:Enc A1),
  injective (@enc_list_impl A1 EA1).
Proof using. injective_enc_prove. Qed.

Global Instance Enc_list : forall A1 (EA1:Enc A1), Enc (list A1) :=
  fun A1 (EA1:Enc A1) =>
  make_Enc (@injective_enc_list_impl A1 EA1).

Lemma enc_list_nil : forall A1 (EA1:Enc A1),
  enc (@nil A1) = val_constr "nil" nil.
Proof using. auto. Qed.

Lemma enc_list_cons : forall A1 (EA1:Enc A1) (x:A1) (l:list A1),
  enc (x::l) = val_constr "cons" (``x :: ``l :: nil).
Proof using. auto. Qed.

End EncList.

(* ALTERNATIVE

Section EncList.
Context A1 `{EA1:Enc A1}.

Definition enc_list_impl := fix f (l:list A1) : val :=
  match l with
  | nil => val_constr "nil" nil
  | x::l' => val_constr "cons" ((``x)::(f l')::nil)
  end.

Lemma injective_enc_list_impl : injective enc_list_impl.
Proof using. injective_enc_prove. Qed.

Global Instance Enc_list : Enc (list A1) := make_Enc injective_enc_list_impl.

Lemma enc_list_nil :
  enc (@nil A1) = val_constr "nil" nil.
Proof using. auto. Qed.

Lemma enc_list_cons : forall (x:A1) (l:list A1),
  enc (x::l) = val_constr "cons" (``x :: ``l :: nil).
Proof using. auto. Qed.

End EncList.
*)

(* ALTERNATIVE

Fixpoint enc_list_impl' (l:list A1) : val := (* details *)
  match l with
  | nil => val_constr "nil" nil
  | x::l' => val_constr "cons" ((``x)::(enc_list_impl' l')::nil)
  end.

Lemma injective_enc_list_impl' : injective enc_list_impl. (* details *)
Proof using.
  intros l1 l2 E. gen l2.
  induction l1; intros; destruct l2; simpls; tryfalse.
  { auto. }
  { inverts E. fequals. { applys* Enc_eq_inv. } { applys* IHl1. } }
Qed.

*)


Global Opaque Enc_loc Enc_unit Enc_bool Enc_int Enc_val
              Enc_pair Enc_option Enc_list.


(** [rew_enc] normalizes all encoders. *)

Hint Rewrite enc_loc enc_unit enc_bool enc_int
             enc_func enc_val (* enc_prim_eq enc_constr *)
             @enc_pair @enc_option_none @enc_option_some @enc_list_nil @enc_list_cons : rew_enc.

Tactic Notation "rew_enc" :=
  autorewrite with rew_enc.
Tactic Notation "rew_enc" "in" hyp(H) :=
  autorewrite with rew_enc in H.
Tactic Notation "rew_enc" "in" "*" :=
  autorewrite with rew_enc in *.


(* TODO: generalize *)

Section EncTuple3.
Context A1 `{EA1:Enc A1} A2 `{EA2:Enc A2} A3 `{EA3:Enc A3}.

Definition enc_tuple3_impl := (fun p : A1*A2*A3 =>
  let '(x1,x2,x3) := p in val_constr "tuple" (``x1 :: ``x2 :: ``x3 :: nil)).

Lemma injective_enc_tuple3_impl : injective enc_tuple3_impl.
Proof using. intros [[x1 x2] x3] [[y1 y2] y3] E. inverts E. fequals; applys* Enc_eq_inv. Qed.

Global Instance Enc_tuple3 : Enc (A1*A2*A3)%type := make_Enc injective_enc_tuple3_impl.

Lemma enc_tuple3 : forall (x1:A1) (x2:A2) (x3:A3),
  enc (x1,x2,x3) = val_constr "tuple" (``x1 :: ``x2 :: ``x3 :: nil).
Proof using. auto. Qed.

End EncTuple3.

Global Opaque Enc_tuple3.
Hint Rewrite enc_tuple3 : rew_enc.


Section EncTuple4.
Context A1 `{EA1:Enc A1} A2 `{EA2:Enc A2} A3 `{EA3:Enc A3} A4 `{EA4:Enc A4}.

Definition enc_tuple4_impl := (fun p : A1*A2*A3*A4 =>
  let '(x1,x2,x3,x4) := p in val_constr "tuple" (``x1 :: ``x2 :: ``x3 :: ``x4 :: nil)).

Lemma injective_enc_tuple4_impl : injective enc_tuple4_impl.
Proof using. intros [[[x1 x2] x3] x4] [[[y1 y2] y3] y4] E. inverts E. fequals; applys* Enc_eq_inv. Qed.

Global Instance Enc_tuple4 : Enc (A1*A2*A3*A4)%type := make_Enc injective_enc_tuple4_impl.

Lemma enc_tuple4 : forall (x1:A1) (x2:A2) (x3:A3) (x4:A4),
  enc (x1,x2,x3,x4) = val_constr "tuple" (``x1 :: ``x2 :: ``x3 :: ``x4 :: nil).
Proof using. auto. Qed.

End EncTuple4.

Global Opaque Enc_tuple4.
Hint Rewrite enc_tuple4 : rew_enc.


(* Demo: dealing with type aliases

Definition t := list int.

Global Instance Enc_t : Enc t.
Proof using.
 typeclasses eauto.
Defined.

Typeclasses Opaque t.

Lemma enc_t : forall (x:t),
  enc x = enc (x:list int).
Proof using. auto. Qed.

*)


(* ---------------------------------------------------------------------- *)
(* ** DEPRECATED *)

(*
Lemma enc_prim_eq : forall (p:prim),
  enc p = p.
Proof using. auto. Qed.

Lemma enc_constr_eq : forall id vs,
  enc (constr id vs) = val_constr id vs.
Proof using. auto. Qed.

*)

              (* Enc_dyn Enc_func  Enc_prim Enc_tyconstr DEPRECATED *)

(*DEPRECATED
(** Specification of encoders for values of type [dyn] *)

Lemma enc_dyn_eq_dyn_to_val : forall (d:dyn),
  enc d = dyn_to_val d.
Proof using. auto. Qed.

(** The encoding of a dynamic value [V] is the same as the encoding of V.
    This goal displays as [``(Dyn V) = ``V] *)

Lemma enc_dyn_make : forall A (EA:Enc A) (V:A),
  enc (dyn_make V) = enc V.
Proof using. auto. Qed.

Hint Rewrite @enc_dyn_make  : rew_enc.

(** [rew_enc] normalizes only the [dyn] encoder. *)

Hint Rewrite @enc_dyn_make : rew_enc_dyn.

Tactic Notation "rew_enc_dyn" :=
  autorewrite with rew_enc_dyn.
Tactic Notation "rew_enc_dyn" "in" hyp(H) :=
  autorewrite with rew_enc_dyn in H.
Tactic Notation "rew_enc_dyn" "in" "*" :=
  autorewrite with rew_enc_dyn in *.

*)

(* DEPRECATED
(** Encoder for lists *)

Definition encs (ds:dyns) : vals :=
  List.map enc ds.

(** Preserves length *)

Lemma length_encs : forall (ds:dyns),
  length (encs ds) = length ds.
Proof using. intros. induction ds; simpl; rew_list; math. Qed.
*)


(* ********************************************************************** *)
(* * Lifting of arguments and return values *)

(* ---------------------------------------------------------------------- *)
(* ** Lifting of postconditions *)

(** [Post Q] converts a postcondition of type [A->hprop] into a
    postcondition of type [val->hprop], where [A] is encodable. *)

Definition Post A {EA:Enc A} (Q:A->hprop) : val->hprop :=
  fun v => \exists V, \[v = enc V] \* Q V.

(** [Post] is covariant *)

Lemma Post_himpl : forall A (EA:Enc A) (Q Q':A->hprop),
  Q ===> Q' ->
  Post Q ===> Post Q'.
Proof using.
  introv M. unfold Post. intros v.
  xpull. intros x E. subst v. xsimpl*.
Qed.

Local Hint Resolve Post_himpl.

(** [Post] distributes over the star *)

Lemma Post_star : forall A (EA:Enc A) (Q:A->hprop) H,
  Post (Q \*+ H) = (Post Q) \*+ H.
Proof using.
  intros. unfold Post. applys fun_ext_1.
  intros v. applys himpl_antisym; xsimpl~.
Qed.

(** [Post] preserves [local] *)

Lemma local_Post : forall A (EA:Enc A) (F:~~val),
  local F ->
  local (fun H (Q:A->hprop) => F H (Post Q)).
Proof using.
  introv L. applys local_intro.
  intros H Q M. applys~ local_elim.
  xchange M. xpull ;=> H1 H2 Q1 (N1&N2).
  xsimpl H1 H2 (Post Q1). splits~.
  do 2 rewrite <- Post_star. applys~ Post_himpl.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of heap predicates *)

(** Singleton: [l ~~> V] describes a singleton heap at location [l]
    with contents [V], where the value [V] has some encodable type [A]. *)

Definition Hsingle A {EA:Enc A} (V:A) (l:loc) : hprop :=
  hsingle l (enc V).

Notation "l '~~>' V" := (l ~> Hsingle V)
  (at level 32, no associativity) : heap_scope.

Lemma Hsingle_to_hsingle : forall A (EA:Enc A) (l:loc) (V:A),
  (l ~~> V) = hsingle l (enc V).
Proof using. auto. Qed.

Lemma Hsingle_not_null : forall l A (EA:Enc A) (V:A),
  (l ~~> V) ==> (l ~~> V) \* \[l <> null].
Proof using. intros. xunfold Hsingle. applys hsingle_not_null. Qed.

Arguments Hsingle_not_null : clear implicits.

Lemma haffine_Hsingle : forall l A (EA:Enc A) (V:A),
  haffine (l ~~> V).
Proof using. intros. rewrite Hsingle_to_hsingle. applys haffine_hsingle. Qed.

Hint Resolve haffine_Hsingle : haffine.

(** Field: [ l `. f ~~> V ] describes the ownership of a record field
    storing one encodable value [V]. *)

Definition Hfield A {EA:Enc A} (V:A) (l_f:loc*field) : hprop :=
  let '(l,f) := l_f in
  hfield l f (enc V).

Notation "l `. f '~~>' V" := ((l,f) ~> Hfield V)
  (at level 32, f at level 0, no associativity,
   format "l `. f  '~~>'  V") : heap_scope.

Lemma Hfield_eq_fun_Hsingle :
  @Hfield = (fun A (EA:Enc A) (V:A) l_f => let '(l,f) := l_f in ((S l+f)%nat ~~> V) \* \[l <> null]).
Proof using. intros. auto. Qed.

Lemma Hfield_to_hfield : forall A (EA:Enc A) (l:loc) (f:field) (V:A),
  (l`.f ~~> V) = hfield l f (enc V).
Proof using. auto. Qed.

Lemma Hfield_to_Hsingle : forall l f v,
  (l`.f ~~> v) ==> ((S l+f)%nat ~~> v) \* \[l <> null].
Proof using. intros. xunfold Hfield. xchanges~ hfield_to_hsingle. Qed.

Lemma Hfield_not_null : forall l f A (EA:Enc A) (V:A),
  (l`.f ~~> V) ==> (l`.f ~~> V) \* \[l <> null].
Proof using. intros. xunfold Hfield. applys~ hfield_not_null. Qed.

Arguments Hfield_not_null : clear implicits.

Lemma haffine_Hfield : forall l f A (EA:Enc A) (V:A),
  haffine (l`.f ~~> V).
Proof using. intros. rewrite Hfield_to_hfield. applys haffine_hfield. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of substitution *)

(** [Subst1 y d t] substitues variable [y] with the encoding of [V] in [t]. *)

Definition Subst1 A {EA:Enc A} (z:bind) (V:A) (t:trm) : trm :=
  subst1 z (enc V) t.

(* DEPRECATED
(** [Substn ys ds t] substitues the list of variables [ys] with the
    encodings of the list of dynamic values [ds] in [t]. *)

Definition Substn (ys:vars) (ds:dyns) (t:trm) : trm :=
  substn ys (encs ds) t.
*)


(* ********************************************************************** *)
(* * Lifting of triples *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of lifted triples *)

(** [Triple t H Q] describes a triple where the postcondition [Q] has
    type [A->hprop] for some encodable type [A] *)

Definition Triple (t:trm) A {EA:Enc A} (H:hprop) (Q:A->hprop) : Prop :=
  triple t H (Post Q).

(** [Triple] satisfies [local], like [triple] does. *)

Lemma local_Triple : forall t A (EA:Enc A),
  local (@Triple t A EA).
Proof using. intros. applys local_Post. applys local_triple. Qed.

Hint Resolve local_Triple.


(* ********************************************************************** *)
(* * Lifting of arguments in applications *)

(* ---------------------------------------------------------------------- *)
(* ** Predicate [Trm_apps] *)

(*
Fixpoint Trm_apps_aux (f:trm) (Vs:dyns) : trm :=
  match Vs with
  | nil => f
  | (Dyn V)::Vs' => Trm_apps_aux (f (enc V)) Vs'
  end.

Definition Trm_apps (f:val) (Vs:dyns) : trm :=
  Trm_apps_aux (trm_val f) Vs.
*)

Definition Trm_apps (f:val) (Vs:dyns) : trm :=
  trm_apps (trm_val f) (LibList.map (fun V => trm_val (dyn_to_val V)) Vs).


(* ---------------------------------------------------------------------- *)
(* ** Notation for [Trm_apps] *)

(** This set up allows writing [f V1 .. VN] as short for
    [Trm_apps f ((Dyn V1):: .. ::(Dyn Vn)::nil)]. *)

Declare Scope Trm_apps_scope.

Declare Custom Entry Trm_apps.

Notation "f x" := (Trm_apps f ((Dyn x)::nil))
  (in custom Trm_apps at level 1,
   f constr at level 0,
   x constr at level 0)
  : Trm_apps_scope.

Notation "f x1 x2 .. xn" := (Trm_apps f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..)))
  (in custom Trm_apps at level 1,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0)
  : Trm_apps_scope.

Notation "( x )" :=
  x
  (in custom Trm_apps,
   x at level 99) : Trm_apps_scope.

Open Scope Trm_apps_scope.


(* ---------------------------------------------------------------------- *)
(* ** Notation for triples *)

Declare Scope triple_scope.
Open Scope triple_scope.

Notation "'SPEC' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of structural rules *)


(* ********************************************************************** *)
(* * Lifting of rules *)

(* ---------------------------------------------------------------------- *)
(* ** Lifting of structural rules *)

Lemma Triple_conseq : forall t H' A (EA:Enc A) (Q':A->hprop) H (Q:A->hprop),
  H ==> H' ->
  Triple t H' Q' ->
  Q' ===> Q ->
  Triple t H Q.
Proof using. intros. applys* local_conseq. Qed.

Lemma Triple_frame : forall t A (EA:Enc A) H (Q:A->hprop) H',
  Triple t H Q ->
  Triple t (H \* H') (Q \*+ H').
Proof using. intros. applys* local_frame. Qed.

Lemma Triple_ramified_frame_hgc : forall t A (EA:Enc A) H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q \*+ \GC) ->
  Triple t H Q.
Proof using. intros. applys* local_ramified_frame_hgc. Qed.

Lemma Triple_ramified_frame : forall t A (EA:Enc A) H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  Triple t H Q.
Proof using. intros. applys* local_ramified_frame. Qed.

Lemma Triple_hgc_pre : forall t A (EA:Enc A) H (Q:A->hprop),
  Triple t H Q ->
  Triple t (H \* \GC) Q.
Proof using. intros. applys* local_hgc_pre. Qed.

Lemma Triple_hgc_post : forall t A (EA:Enc A) H (Q:A->hprop),
  Triple t H (Q \*+ \GC) ->
  Triple t H Q.
Proof using. intros. applys~ local_hgc_post. Qed.

Lemma Triple_hexists : forall t A (EA:Enc A) B (J:B->hprop) (Q:A->hprop),
  (forall x, Triple t (J x) Q) ->
  Triple t (hexists J) Q.
Proof using. intros. applys~ local_hexists. Qed.

Lemma Triple_hforall : forall B (x:B) t (J:B->hprop) A (EA:Enc A) (Q:A->hprop),
  Triple t (J x) Q ->
  Triple t (hforall J) Q.
Proof using. intros. applys* local_hforall. Qed.

Lemma Triple_hpure : forall t (P:Prop) A (EA:Enc A) H (Q:A->hprop),
  (P -> Triple t H Q) ->
  Triple t (\[P] \* H) Q.
Proof using. intros. applys~ local_hpure. Qed.

Lemma Triple_hwand_hpure_l : forall t (P:Prop) H A (EA:Enc A) (Q:A->hprop),
  P ->
  Triple t H Q ->
  Triple t (\[P] \-* H) Q.
Proof using. intros. applys~ local_hwand_hpure_l. Qed.

Lemma Triple_hor : forall t H1 H2 A (EA:Enc A) (Q:A->hprop),
  Triple t H1 Q ->
  Triple t H2 Q ->
  Triple t (hor H1 H2) Q.
Proof using. intros. applys~ local_hor. Qed.

Lemma Triple_hand_l : forall t H1 H2 A (EA:Enc A) (Q:A->hprop),
  Triple t H1 Q ->
  Triple t (hand H1 H2) Q.
Proof using. intros. applys~ local_hand_l. Qed.

Lemma Triple_hand_r : forall t H1 H2 A (EA:Enc A) (Q:A->hprop),
  Triple t H2 Q ->
  Triple t (hand H1 H2) Q.
Proof using. intros. applys~ local_hand_r. Qed.

Lemma Triple_conseq_frame_hgc : forall t H1 H2 A (EA:Enc A) (Q1 Q:A->hprop) H,
  Triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  Triple t H Q.
Proof using. intros. applys* local_conseq_frame_hgc. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of evaluation context rules *)

(** Currently not used *)

Lemma Triple_evalctx : forall C t1 H,
 forall A (EA:Enc A) (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  evalctx C ->
  Triple t1 H Q1 ->
  (forall (V:A1), Triple (C ``V) (Q1 V) Q) ->
  Triple (C t1) H Q.
Proof using.
  introv EC M1 M2. applys* triple_evalctx.
  { intros v. unfold Post. xtpull ;=> V ->. applys M2. }
Qed.

(** Substitution commutes with evaluation contexts, for triples *)

Lemma Triple_isubst_evalctx : forall E C t1 H,
 forall A (EA:Enc A) (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  evalctx C ->
  Triple (isubst E t1) H Q1 ->
  (forall V, Triple (isubst E (C ``V)) (Q1 V) Q) ->
  Triple (isubst E (C t1)) H Q.
Proof using.
  introv EC M1 M2. applys* triple_isubst_evalctx.
  { intros v. unfold Post. xtpull ;=> V ->. applys M2. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lifting of term rules *)

Lemma Triple_val : forall A (EA:Enc A) (V:A) v H (Q:A->hprop),
  v = enc V ->
  H ==> Q V ->
  Triple (trm_val v) H Q.
Proof using.
  introv E M. applys triple_val. subst.
  unfold Post. xsimpl*.
Qed.

Lemma Triple_fixs : forall f xs t1 H (Q:func->hprop),
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  Triple (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. applys* triple_fixs. unfold Post. xchanges* M.
Qed.

(* DEPRECATED
Lemma Triple_constr : forall id vs H (Q:tyconstr->hprop),
  H ==> Q (constr id vs) ->
  Triple (trm_constr id (trms_vals vs)) H Q.
Proof using. introv M. applys triple_constr. unfold Post. xchanges* M. Qed.
*)

Lemma Triple_constr : forall id vs H A (EA:Enc A) (V:A) (Q:A->hprop),
  val_constr id vs = enc V ->
  H ==> Q V ->
  Triple (trm_constr id (trms_vals vs)) H Q.
Proof using. introv E M. applys triple_constr. unfold Post. xchanges* M. Qed.

Lemma Triple_constr_trm : forall id ts t1 vs H,
  forall A (EA:Enc A) (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (trm_constr id ((trms_vals vs)++(trm_val ``X)::ts)) (Q1 X) Q) ->
  Triple (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. applys* triple_constr_trm M1.
  intros v. unfold Post at 1. xtpull ;=> V ->. subst. applys M2.
Qed.

Lemma Triple_let : forall z t1 t2 H,
  forall A (EA:Enc A) (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (Subst1 z X t2) (Q1 X) Q) ->
  Triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_let M1.
  intros v. unfold Post at 1. xtpull ;=> V ->. subst. applys M2.
Qed.

Lemma Triple_seq : forall t1 t2 H,
  forall A (EA:Enc A) (Q:A->hprop) (Q1:unit->hprop),
  Triple t1 H Q1 ->
  Triple t2 (Q1 tt) Q ->
  Triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_seq.
  { applys M1. }
  { intros X. unfold Post. xtpull ;=> V E.
    destruct V. applys M2. }
Qed.

Lemma Triple_if_trm : forall t0 t1 t2 H (Q1:bool->hprop) A (EA:Enc A) (Q:A->hprop),
  Triple t0 H Q1 ->
  (forall (b:bool), Triple (if b then t1 else t2) (Q1 b) Q) ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* triple_if_trm'.
  { intros b. unfold Post. xtpull ;=> V E.
     rewrite (enc_bool V) in E. inverts E. applys* M2. }
  { intros v N. unfold Post. xpull ;=> V ->. false N.
    rewrite enc_bool. hnfs*. }
Qed.

Lemma Triple_if : forall (b:bool) t1 t2 H A (EA:Enc A) (Q:A->hprop),
  Triple (if b then t1 else t2) H Q ->
  Triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. applys triple_if. { applys M1. }
Qed.

Lemma Triple_apps_funs : forall xs F vs t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_funs xs t1) ->
  var_funs xs (length vs) ->
  Triple (substn xs vs t1) H Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv E N M. unfold Triple. applys* triple_apps_funs.
Qed.

Lemma Triple_apps_fixs : forall xs (f:var) F vs t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fixs f xs t1) ->
  var_fixs f xs (length vs) ->
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
  forall A (EA:Enc A) (Q:A->hprop) A1 `{EA1:Enc A1} (Q1:A1->hprop),
  Triple t1 H Q1 ->
  (forall (X:A1), Triple (trm_match (``X) pts) (Q1 X) Q) ->
  Triple (trm_match t1 pts) H Q.
Proof using.
  introv M1 M2. applys* triple_match_trm.
  intros v. unfold Post at 1. xtpull ;=> V ->. applys M2.
Qed.

Lemma Triple_match : forall v p t1 pts H A (EA:Enc A) (Q:A->hprop),
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> Triple (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> Triple (trm_match v pts) H Q) ->
  Triple (trm_match v ((p,t1)::pts)) H Q.
Proof using.
  introv M1 M2. applys triple_match.
  { introv HG Hv. applys* M1. }
  { introv HG Hv. applys* M2. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Lifting of specitification of primitive functions *)

(* TODO: rewrite using notation? or at least Trm_apps? *)

Section RulesStateOps.
Transparent Hsingle.

Lemma Triple_ref : forall A (EA:Enc A) (V:A),
  Triple (val_ref ``V)
    \[]
    (fun l => l ~~> V).
Proof using. intros. applys_eq~ triple_ref. Qed.

Lemma Triple_get : forall A (EA:Enc A) (V:A) l,
  Triple (val_get ``l)
    (l ~~> V)
    (fun x => \[x = V] \* (l ~~> V)).
Proof using.
  introv. unfold Triple, Post. rewrite Hsingle_to_hsingle. xapplys* triple_get.
Qed.

(** Specification of [set] allowing for change in type (i.e. strong update). *)

Lemma Triple_set_strong : forall A1 A2 `{EA1:Enc A1} (V1:A1) `{EA2:Enc A2} (V2:A2) l,
  Triple (val_set l ``V2)
    (l ~~> V1)
    (fun u => l ~~> V2).
Proof using.
  intros. unfold Triple. rewrite Hsingle_to_hsingle. xapplys triple_set.
  intros. subst. unfold Post. xsimpl~ tt.
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


Lemma Triple_free : forall l v,
  Triple (val_free (val_loc l))
    (l ~~> v)
    (fun u => \[]).
Proof using.
  introv. unfold Triple, Post.
  xapply (>> triple_free v). { xsimpl. } { xsimpl* tt. }
Qed.

(* TODO: later
Lemma Triple_alloc : forall n,
  n >= 0 ->
  Triple (val_alloc n)
    \[]
    (fun l => \[l <> null] \* Alloc (abs n) l).
Proof using.
  introv N. unfold Triple, Post. xapplys* triple_alloc.
Qed.

Lemma Triple_alloc_nat : forall (k:nat),
  Triple (val_alloc (k:int))
    \[]
    (fun l => \[l <> null] \* Alloc k l).
Proof using.
  intros. xapplys~ Triple_alloc. { math. }
  { intros. rewrite abs_nat. xsimpl. }
Qed.

Lemma Triple_dealloc : forall n l,
  n >= 0 ->
  Triple (val_dealloc n l)
    (Dealloc (abs n) l)
    (fun u => \[]).
Proof using.
  introv M. unfold Triple, Post. xapply~ triple_dealloc. xsimpl. xsimpl* tt.
Qed.
*)

End RulesStateOps.

Lemma Triple_ptr_add : forall (l:loc) (n:int),
  (l:nat) + n >= 0 ->
  Triple (val_ptr_add l n)
    \[]
    (fun l' => \[(l':nat) = abs ((l:nat) + n)]).
Proof using. intros. unfold Triple, Post. xapplys* triple_ptr_add. Qed.

Lemma Triple_ptr_add_nat : forall (l:loc) (f:nat),
  Triple (val_ptr_add l f)
    \[]
    (fun l' => \[(l':nat) = (l+f)%nat]).
Proof using. intros. unfold Triple, Post. xapplys* triple_ptr_add_nat. Qed.

Lemma Triple_neg : forall b1,
  Triple (val_neg b1)
    \[]
    (fun b => \[b = neg b1]).
Proof using. intros. unfold Triple, Post. xapplys* triple_neg. Qed.

Lemma Triple_opp : forall n1,
  Triple (val_opp n1)
    \[]
    (fun n => \[n = - n1]).
Proof using. intros. unfold Triple, Post. xapplys* triple_opp. Qed.

Lemma Triple_eq_val : forall v1 v2,
  Triple (val_eq v1 v2)
    \[]
    (fun b => \[ b = isTrue (v1 = v2) ]).
Proof using. intros. unfold Triple, Post. xapplys* triple_eq. Qed.

Lemma Triple_eq : forall A (EA:Enc A) (V1 V2 : A),
  Triple (val_eq ``V1 ``V2)
    \[]
    (fun (b:bool) => \[b = isTrue (V1 = V2)]).
Proof using.
  intros. applys_eq Triple_eq_val.
  applys fun_ext_1. intros b. rewrite* Enc_eq_eq.
Qed.

Lemma Triple_neq_val : forall v1 v2,
  Triple (val_neq v1 v2)
    \[]
    (fun b => \[ b = isTrue (v1 <> v2) ]).
Proof using. intros. unfold Triple, Post. xapplys* triple_neq. Qed.

Lemma Triple_neq : forall A (EA:Enc A) (V1 V2 : A),
  Triple (val_neq ``V1 ``V2)
    \[]
    (fun (b:bool) => \[b = isTrue (V1 <> V2)]).
Proof using.
  intros. applys_eq Triple_neq_val.
  applys fun_ext_1. intros b. rewrite* Enc_eq_eq.
Qed.

Lemma Triple_add : forall n1 n2,
  Triple (val_add n1 n2)
    \[]
    (fun n => \[n = n1 + n2]).
Proof using. intros. unfold Triple, Post. xapplys* triple_add. Qed.

Lemma Triple_sub : forall n1 n2,
  Triple (val_sub n1 n2)
    \[]
    (fun n => \[n = n1 - n2]).
Proof using. intros. unfold Triple, Post. xapplys* triple_sub. Qed.

Lemma Triple_mul : forall n1 n2,
  Triple (val_mul n1 n2)
    \[]
    (fun n => \[n = n1 * n2]).
Proof using. intros. unfold Triple, Post. xapplys* triple_mul. Qed.

Lemma Triple_div : forall n1 n2,
  n2 <> 0 ->
  Triple (val_div n1 n2)
    \[]
    (fun n => \[n = Z.quot n1 n2]).
Proof using. intros. unfold Triple, Post. xapplys* triple_div. Qed.

Lemma Triple_mod : forall n1 n2,
  n2 <> 0 ->
  Triple (val_mod n1 n2)
    \[]
    (fun n => \[n = Z.rem n1 n2]).
Proof using. intros. unfold Triple, Post. xapplys* triple_mod. Qed.

Lemma Triple_le : forall n1 n2,
  Triple (val_le n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 <= n2)]).
Proof using. intros. unfold Triple, Post. xapplys* triple_le. Qed.

Lemma Triple_lt : forall n1 n2,
  Triple (val_lt n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 < n2)]).
Proof using. intros. unfold Triple, Post. xapplys* triple_lt. Qed.

Lemma Triple_ge : forall n1 n2,
  Triple (val_ge n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 >= n2)]).
Proof using. intros. unfold Triple, Post. xapplys* triple_ge. Qed.

Lemma Triple_gt : forall n1 n2,
  Triple (val_gt n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 > n2)]).
Proof using. intros. unfold Triple, Post. xapplys* triple_gt. Qed.
