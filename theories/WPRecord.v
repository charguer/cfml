(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export WPTactics.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* ********************************************************************** *)
(* * Records *)

Implicit Types l : loc.

(* ---------------------------------------------------------------------- *)
(* ** Record get/set functions *)

Definition val_get_field (k:field) : val :=
  VFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  VFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 66, f at level 0, format "t1 ''.' f" ) : trm_scope.

Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2") : trm_scope.


(* ---------------------------------------------------------------------- *)
(* ** Record representation *)

(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r `.` f ~~> V) \* (r ~> Record L')
  end.

(* TODO: currently restricted due to [r `.` f ~> V] not ensuring [r<>null] *)
Lemma hRecord_not_null : forall (r:loc) (L:Record_fields),
  (* L <> nil -> *)
  mem (0%nat:field) (List.map fst L) ->
  (r ~> Record L) ==> (r ~> Record L) \* \[r <> null].
Proof using.
  introv M. induction L as [|(f,[A EA v]) L'].
  { inverts M. }
  { xunfold Record. inverts M.
    { hchange~ (Hfield_not_null r). hsimpl~. }
    { hchange~ IHL'. hsimpl~. } }
Qed.

(** Lemmas for unfolding the definition *)

Lemma Record_nil : forall p,
  p ~> Record nil = \[].
Proof using. auto. Qed.

Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.`x ~~> ``V \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,v) L']. { false. }
  rewrite Record_cons. hchanges~ Hfield_not_null.
Qed.


(** Notation for record contents (only supported up to arity 5) *)

Notation "`{ f1 := x1 }" :=
  ((f1, Dyn x1)::nil)
  (at level 0, f1 at level 0)
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::nil)
  (at level 0, f1 at level 0, f2 at level 0)
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0)
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::(f4, Dyn x4)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0)
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 ; f5 := x5 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::(f4, Dyn x4)::(f5, Dyn x5)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0)
  : fields_scope.

Open Scope fields_scope.
Bind Scope fields_scope with Record_fields.
Delimit Scope fields_scope with fields.


(* ---------------------------------------------------------------------- *)
(* ** Small-footprint lifted specifications for records *)

Section Triple_fields.
Transparent loc field Hfield.

(* TODO move *)
Lemma Hfield_eq_fun_Hsingle_ext : forall `{EA:Enc A} (V:A) (l:loc) (f:field),
  (l`.`f ~~> V) = (((l+f)%nat ~~> V) \* \[l <> null]).
Proof using. intros. rewrite Hfield_eq_fun_Hsingle. rewrite~ repr_eq. Qed.

Lemma Hfield_to_Hsingle : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  (l`.`f ~~> V) ==> ((l+f)%nat ~~> V) \* \[l <> null].
Proof using. intros. rewrite~ Hfield_eq_fun_Hsingle_ext. Qed.

Lemma Hsingle_to_Hfield : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  l <> null ->
  ((l+f)%nat ~~> V) ==> (l`.`f ~~> V).
Proof using. introv N. rewrite Hfield_eq_fun_Hsingle_ext. hsimpl~. Qed.



Lemma Triple_get_field : forall (l:loc) f `{EA:Enc A} (V:A),
  TRIPLE ((val_get_field f) l)
    PRE (l `.` f ~~> V)
    POST (fun r => \[r = V] \* (l `.` f ~~> V)).
Proof using.
  dup. 
  { intros. 
    rewrite Hfield_eq_fun_Hsingle, repr_eq. xpull ;=> N.
    xwp. xapp @Triple_ptr_add_nat. xapp. hsimpl~. }
  { (* details TEMPORARY *)
    intros.
    (* unfold field *)
    rewrite Hfield_eq_fun_Hsingle, repr_eq. xpull ;=> N.
    (* xwp *)
    applys xwp_lemma_funs; try reflexivity; simpl.
    (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_ptr_add_nat. } xapp_post tt ;=> r ->.
    (* xapp *)
    applys @xapps_lemma. { applys @Triple_get. } xapp_post tt.
    (* done *)
    hsimpl~. }
Qed.

Lemma Triple_set_field_strong : forall `{EA1:Enc A1} (V1:A1) (l:loc) f `{EA2:Enc A2} (V2:A2),
  TRIPLE ((val_set_field f) l ``V2)
    PRE (l `.` f ~~> V1)
    POST (fun (r:unit) => l `.` f ~~> V2).
Proof using.
  dup. 
  { intros. 
    rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
    xpull ;=> N. xwp. xapp @Triple_ptr_add_nat. xapp (>> (@Triple_set_strong) A1 A2). 
    hsimpl~. }
  { intros.
    (* unfold field *)
    rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
    xpull ;=> N.
    (* xwp *)
    applys xwp_lemma_funs; try reflexivity; simpl.
    (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_ptr_add_nat. } hsimpl ;=> r ->.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_set_strong A1 A2. } hsimpl. xapp_post tt.
    (* done *)
    hsimpl~. }
Qed.

Lemma Triple_set_field : forall `{EA:Enc A} (V1:A) (l:loc) f (V2:A),
  TRIPLE ((val_set_field f) l ``V2)
    PRE (l `.` f ~~> V1)
    POST (fun (r:unit) => l `.` f ~~> V2).
Proof using. intros. applys Triple_set_field_strong. Qed.

End Triple_fields.

(* Arguments Triple_get_field Triple_set_field : clear implicits. *)



(* ---------------------------------------------------------------------- *)
(* ** Derived large-footprint lifted specifications for records *)

Definition field_eq_dec := Nat.eq_dec.

Fixpoint record_get_compute_dyn (f:field) (L:Record_fields) : option dyn :=
  match L with
  | nil => None
  | (f',d')::T' =>
     if field_eq_dec f f'
       then Some d'
       else record_get_compute_dyn f T'
  end.

Definition record_get_compute_spec (f:field) (L:Record_fields) : option Prop :=
  match record_get_compute_dyn f L with
  | None => None
  | Some (Dyn V) => Some (forall r,
     Triple (val_get_field f ``r) (r ~> Record L) (fun x => \[x = V] \* r ~> Record L))
  end.

Lemma record_get_compute_spec_correct : forall (f:field) L (P:Prop),
  record_get_compute_spec f L = Some P ->
  P.
Proof using.
  introv M. unfolds record_get_compute_spec.
  sets_eq <- vo E: (record_get_compute_dyn f L).
  destruct vo as [[T ET v]|]; inverts M. intros r.
  induction L as [|[F D] L']; [false|].
  destruct D as [A EA V]. simpl in E.
  xunfold Record at 1. xunfold Record at 2. case_if. (*--todo fix subst *)
  { subst. inverts E. xapplys~ Triple_get_field. }
  { specializes IHL' (rm E). xapplys~ IHL'. }
Qed.

Fixpoint record_set_compute_dyn (f:nat) (d:dyn) (L:Record_fields) : option Record_fields :=
  match L with
  | nil => None
  | (f',d')::T' =>
     if field_eq_dec f f'
       then Some ((f,d)::T')
       else match record_set_compute_dyn f d T' with
            | None => None
            | Some L' => Some ((f',d')::L')
            end
  end.

Definition record_set_compute_spec (f:field) `{EA:Enc A} (W:A) (L:Record_fields) : option Prop :=
  match record_set_compute_dyn f (Dyn W) L with
  | None => None
  | Some L' => Some (forall r,
     Triple (val_set_field f ``r ``W) (r ~> Record L) (fun (_:unit) => r ~> Record L'))
  end.

Lemma record_set_compute_spec_correct : forall (f:field) `{EA:Enc A} (W:A) L (P:Prop),
  record_set_compute_spec f W L = Some P ->
  P.
Proof using.
  introv M. unfolds record_set_compute_spec.
  sets_eq <- do E: (record_set_compute_dyn f (Dyn W) L).
  destruct do as [L'|]; inverts M.
  gen L'. induction L as [|[f' D] T]; intros; [false|].
  destruct D as [A' EA' V]. simpl in E.
  xunfold Record at 1. simpl. case_if. (*--todo fix subst *)
  { subst. inverts E. xapply~ Triple_set_field_strong. 
    intros _. xunfold Record at 2. simpl. hsimpl. }
  { cases (record_set_compute_dyn f (Dyn W) T) as C'; [|false].
    inverts E. specializes~ IHT r. xapply IHT. hsimpl.
    intros. xunfold Record at 2. hsimpl~. }
Qed.

Global Opaque Record.


(* ---------------------------------------------------------------------- *)
(* ** Tactics for generating specifications for get and set on records *)

(** Auxiliary tactic to read the record state from the precondition *)

Ltac xspec_record_repr_compute r H :=
  match H with context [ r ~> Record ?L ] => constr:(L) end.

(** Tactic [xget] derives a record [get] specification *)

Ltac xspec_record_get_compute_for f L :=
  let G := fresh in
  forwards G: (record_get_compute_spec_correct f L);
  [ reflexivity | revert G ].

Ltac xspec_record_get_loc v :=
  match v with
  | val_loc ?r => constr:(r)
  | @enc loc Enc_loc ?r => constr:(r)
  end.

Ltac xspec_record_get_compute tt :=
(* TODO   match goal with |- Triple (trm_apps (trm_val (val_get_field ?f)) ((trm_val ?v)::nil)) ?H _ => *)
  match goal with |- Triple (trm_apps (trm_val (val_get_field ?f)) (trms_vals (?v::nil))) ?H _ =>
    let r := xspec_record_get_loc v in
    let L := xspec_record_repr_compute r H in
    xspec_record_get_compute_for f L end.

(** Tactic [sget] derives a record [set] specification *)

Ltac xspec_record_get_arg w :=
  match w with
  | @enc _ _ ?W => constr:(W)
  | _ => constr:(w)
  end.

Ltac xspec_record_set_compute_for f W L :=
  let G := fresh in
  forwards G: (record_set_compute_spec_correct f W L);
  [ reflexivity | revert G ].

Ltac xspec_record_set_compute tt :=
(*  match goal with |- Triple (trm_apps (trm_val (val_set_field ?f)) ((trm_val ?v)::(trm_val ?w)::nil)) ?H _ =>*)
  match goal with |- Triple (trm_apps (trm_val (val_set_field ?f)) (trms_vals (?v::?w::nil))) ?H _ =>
    let r := xspec_record_get_loc v in
    let W := xspec_record_get_arg w in
    let L := xspec_record_repr_compute r H in
    xspec_record_set_compute_for f W L end.

(** [xspec_record] adds to the goal the relevant specification *)

Ltac xspec_record tt :=
  match goal with
  | |- Triple (trm_apps (trm_val (val_get_field ?f)) _) _ _ =>
     xspec_record_get_compute tt
  | |- Triple (trm_apps (trm_val (val_set_field ?f)) _) _ _ =>
     xspec_record_set_compute tt
  end.


(* ---------------------------------------------------------------------- *)


Lemma xapp_record_get : forall A `{EA:Enc A} (Q:A->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* (match record_get_compute_dyn f L with
    | None => \[False]
    | Some (Dyn V) => (p ~> Record L) \-* ^(is_Wp (Wp_cast V)) (protect Q) end) ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q.
Proof using.
  introv M1. hchanges (rm M1).
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec.
  destruct (record_get_compute_dyn f L) as [[T ET V]|]; try solve [hpull].  
  set (H' := (p ~> Record L \-* ^(`Wp_cast V) Q)).
  forwards R': R; eauto. clear R. specializes R' p.
  applys himpl_wp_app_of_Triple.
  applys Triple_enc_change. xapplys (rm R'). simpl.
  unfold PostChange, is_Wp. hpull ;=> ? ->. unfold H'. hpull.
  unfold Wp_cast, is_Wp. applys himpl_refl.
Qed. (* TODO: simplify proof *)

Lemma xapp_record_set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* ((
    match record_set_compute_dyn f (Dyn W) L with
    | None => \[False]
    | Some L' =>  
        (p ~> Record L' \-* protect (Q tt)) end)  ) ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_set_field f)) (trms_vals ((p:val)::(``W)::nil)))) Q.
Proof using.
  introv M1. hchanges (rm M1).
  lets R: record_set_compute_spec_correct f W L.
  unfolds record_set_compute_spec.
  destruct (record_set_compute_dyn f (Dyn W) L) as [L'|]; try solve [hpull].
  forwards R': R; eauto. clear R. specializes R' p. 
  applys himpl_wp_app_of_Triple.
  xapplys R'.
Qed. (* TODO: simplify proof *)


Global Opaque val_set_field val_get_field.

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record] *)

Ltac xapp_record_post tt :=
  hsimpl; simpl; hsimpl; unfold protect; try xcast.

Ltac xapp_record_get tt :=
  applys xapp_record_get; xapp_record_post tt.

Ltac xapp_record_set tt :=
  applys xapp_record_set; xapp_record_post tt.

Ltac xapp_record tt ::= (* dummy binding in WPTactics *)
  match xgoal_fun tt with
  | (val_get_field _) => xapp_record_get tt
  | (val_set_field _) => xapp_record_set tt
  end.


(* ---------------------------------------------------------------------- *)


(* TODO: 
   Set 'p '. X ':= ('p '.X '+ 1).
   won't parse 
*)



