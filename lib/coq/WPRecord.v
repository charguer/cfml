(**

This file defines notation, specification and tactics for manipulating
records.

Disclaimer: notation currently support records with up to 5 fields.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From CFML Require Export WPTactics.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Local Open Scope val_scope.
Local Open Scope pat_scope.
Local Open Scope trm_scope.


(* ********************************************************************** *)
(* * Records *)

Implicit Types l : loc.

(* ---------------------------------------------------------------------- *)
(* ** Record operations: get, set, alloc, init *)

Definition val_get_field (k:field) : val :=
  Fun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z (S k)) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  Fun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z (S k)) in
    val_set 'q 'v.

Definition val_record_alloc (ks:fields) : val :=
  Fun 'u :=
    val_alloc (1 + List.fold_right Nat.max 0%nat ks)%nat.

Definition val_record_init (ks:fields) : val :=
  let nb := List.length ks in
  let xs := var_seq 0 nb in
  let body := fix body (p:var) (kxs:list (field*var)) :=
    match kxs with
    | nil => trm_var p
    | (k,x)::kxs' => (val_set_field k) (trm_var p) x '; body p kxs'
    end in
  val_funs xs (
    Let 'p := (val_record_alloc ks) tt in
    body 'p (List.combine ks xs)).

(* Delete a list of record fields, given in the same order as allocation *)
Definition val_record_delete (ks:fields) : val :=
  Fun 'p :=
    val_dealloc (val_int (List.length ks)) 'p.

(** Notation for record operations *)

Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 56, f at level 0, format "t1 ''.' f" ) : trm_scope.

Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2") : trm_scope.

Notation "'New' `{ f1 := x1 }" :=
  ((val_record_init (f1::nil)) x1)
  (at level 0, f1 at level 0)
  : trm_scope.
Notation "'New' `{ f1 := x1 ; f2 := x2 }" :=
  ((val_record_init (f1::f2::nil)) x1 x2)
  (at level 0, f1 at level 0, f2 at level 0)
  : trm_scope.
Notation "'New' `{ f1 := x1 ; f2 := x2 ; f3 := x3 }" :=
  ((val_record_init (f1::f2::f3::nil)) x1 x2 x3)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0)
  : trm_scope.
Notation "'New' `{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 }" :=
  ((val_record_init (f1::f2::f3::f4::nil)) x1 x2 x3 x4)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0)
  : trm_scope.
Notation "'New' `{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 ; f5 := x5 }" :=
  ((val_record_init (f1::f2::f3::f4::f5::nil)) x1 x2 x3 x4 x5)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0)
  : trm_scope.
Notation "'New' `{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 ; f5 := x5 ; f6 := x6 }" :=
  ((val_record_init (f1::f2::f3::f4::f5::f6::nil)) x1 x2 x3 x4 x5 x6)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0, f6 at level 0)
  : trm_scope.

Notation "'Delete' `{ f1 }" :=
  (val_record_delete (f1::nil))
  (at level 0, f1 at level 0)
  : trm_scope.
Notation "'Delete' `{ f1 ; f2 }" :=
  (val_record_delete (f1::f2::nil))
  (at level 0, f1 at level 0, f2 at level 0)
  : trm_scope.
Notation "'Delete' `{ f1 ; f2 ; f3 }" :=
  (val_record_delete (f1::f2::f3::nil))
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0)
  : trm_scope.
Notation "'Delete' `{ f1 ; f2 ; f3 ; f4 }" :=
  (val_record_delete (f1::f2::f3::f4::nil))
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0)
  : trm_scope.
Notation "'Delete' `{ f1 ; f2 ; f3 ; f4 ; f5 }" :=
  (val_record_delete (f1::f2::f3::f4::f5::nil))
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0)
  : trm_scope.
Notation "'Delete' `{ f1 ; f2 ; f3 ; f4 ; f5 ; f6 }" :=
  (val_record_delete (f1::f2::f3::f4::f5::f6::nil))
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0, f6 at level 0)
  : trm_scope.

(** Notation for record contents (only supported up to arity 6) *)

Declare Scope fields_scope.
Open Scope fields_scope.
Delimit Scope fields_scope with fields.

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
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 ; f5 := x5 ; f6 := x6 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::(f4, Dyn x4)::(f5, Dyn x5)::(f6, Dyn x6)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0, f6 at level 0)
  : fields_scope.


(* ---------------------------------------------------------------------- *)
(* ** Record representation *)

(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Bind Scope fields_scope with Record_fields.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => hheader 0 r
  | (f, Dyn V)::L' => (r`.f ~~> V) \* (r ~> Record L')
  end.

Fixpoint RecordNoHeader (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r`.f ~~> V) \* (r ~> RecordNoHeader L')
  end.

Lemma Record_extract_header : forall (r:loc) (L:Record_fields),
  r ~> Record L = hheader 0 r \* r ~> RecordNoHeader L.
Proof.
  induction L as [|a L].
  { xsimpl*. }
  { destruct a; xunfold Record. xunfold RecordNoHeader.
    destruct d. rewrite IHL.
    xsimpl*. }
Qed.

Lemma Heapdata_record : forall (r:loc) (L1 L2:Record_fields),
  r ~> Record L1 \* r ~> Record L2 ==> \[False].
Proof.
  intros.
  do 2 xchange Record_extract_header.
  rewrite <- (repr_eq (hheader 0) r).
  xchange Heapdata_hheader.
Qed.

Lemma haffine_Record : forall (L:Record_fields) (r:loc),
    haffine (r ~> Record L).
Proof.
  induction L as [|([],[])]; intros; xunfold Record; xaffine.
  all:rewrite repr_eq;apply haffine_hfield.
Qed.

Hint Resolve haffine_Record : haffine.

(* --TODO: currently restricted due to [r `. f ~> V] not ensuring [r<>null] *)
(* --TODO: rename *)
Lemma hRecord_not_null : forall (r:loc) (L:Record_fields),
  (* L <> nil -> *)
  mem (0%nat:field) (List.map fst L) ->
  (r ~> Record L) ==> (r ~> Record L) \* \[r <> null].
Proof using.
  introv M. induction L as [|(f,[A EA v]) L'].
  { inverts M. }
  { xunfold Record. inverts M.
    { xchange~ (Hfield_not_null r). xsimpl~. }
    { xchange~ IHL'. xsimpl~. } }
Qed.

(** Lemmas for unfolding the definition *)

Lemma Record_nil : forall p,
  p ~> Record nil = hheader 0 p.
Proof using. auto. Qed.

Lemma Record_cons : forall p x A (EA:Enc A) (V:A) L,
  (p ~> Record ((x, dyn_make V)::L)) =
  (p`.x ~~> V \* p ~> Record L).
Proof using. auto. Qed.

(* DEPRECATED
Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.x ~~> V \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.
*)

Hint Rewrite Record_nil @Record_cons : Record_to_HField.
(* enc_dyn_make DEPRECATED *)


Local Open Scope heap_scope_ext.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,[A EA V]) L']. { false. }
  rewrite Record_cons. xchanges~ Hfield_not_null.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Tactic to prove record equality *)

Lemma eq_Record_fields : forall (L1 L2:Record_fields) (f:field) `{Enc A} (V1 V2:A),
  V1 = V2 ->
  L1 = L2 ->
  (f, Dyn V1)::L1 = (f,Dyn V2)::L2.
Proof using. intros. subst~. Qed.

Ltac xrecord_eq_core tt :=
  repeat (apply eq_Record_fields); try reflexivity.

Tactic Notation "xrecord_eq" :=
  xrecord_eq_core tt.

(* --LATER: xrecord_eq might need to take care of reordering *)

(** Updating the cancellation tactic. *)

Ltac xsimpl_lr_cancel_eq_repr_post tt ::=
  match goal with
  | |- Record ?L1 = Record ?L2 => fequal; xrecord_eq
  | _ => try fequal; try reflexivity
  end.


(* ---------------------------------------------------------------------- *)
(* ** Small-footprint lifted specifications for records *)

Section Triple_fields.
Transparent loc field Hfield.

(* --TODO move *)
Lemma Hfield_eq_fun_Hsingle_ext : forall A `{EA:Enc A} (V:A) (l:loc) (f:field),
  (l`.f ~~> V) = (((S l+f)%nat ~~> V) \* \[l <> null]).
Proof using. intros. rewrite Hfield_eq_fun_Hsingle. rewrite~ repr_eq. Qed.

Lemma Hfield_to_Hsingle : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  (l`.f ~~> V) ==> ((S l+f)%nat ~~> V) \* \[l <> null].
Proof using. intros. rewrite~ Hfield_eq_fun_Hsingle_ext. Qed.

Lemma Hsingle_to_Hfield : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  l <> null ->
  ((S l+f)%nat ~~> V) ==> (l`.f ~~> V).
Proof using. introv N. rewrite Hfield_eq_fun_Hsingle_ext. xsimpl~. Qed.

(* TODO: move *)
Lemma xlet_lemma : forall A1 (EA1:Enc A1) (Q1:A1->hprop) H A (EA:Enc A) (Q:A->hprop) ,
  forall (F1:Formula) (F2of:forall A1 (EA1:Enc A1), A1->Formula),
  Structural F1 ->
  H ==> F1 A1 EA1 Q1 ->
  (forall (X:A1), Q1 X ==> ^(@F2of A1 EA1 X) Q) ->
  H ==> ^(@Wpgen_let F1 F2of) Q.
Proof using.
  introv HF1 M1 M2. applys MkStruct_erase. applys himpl_hexists_r A1.
  applys himpl_hexists_r EA1. xchange M1. applys* Structural_conseq.
Qed.

Lemma xapp_untyped_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_app_untyped t) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp. applys* Triple_ramified_frame.
Qed.


Lemma Triple_get_field : forall (l:loc) f `{EA:Enc A} (V:A),
  Triple ((val_get_field f) l)
    (l`.f ~~> V)
    (fun r => \[r = V] \* (l`.f ~~> V)).
Proof using.
  intros.
  (* unfold field *)
  rewrite Hfield_eq_fun_Hsingle, repr_eq. xtpull ;=> N.
  (* xwp *)
  applys xwp_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  eapply (@xlet_lemma loc _ (fun r => \[r = S (l + f)%nat] \* r ~~> V)). xstructural.
    (* --   notypeclasses refine (xlet_lemma _ _ _ _ _). *)
  (* xapp *)
  applys xapp_untyped_lemma. { applys @Triple_ptr_add_nat. } xapp_simpl tt.
  intros ? ->. xsimpl*. math_rewrite (S (l + f) = l + S f)%nat. xsimpl.
  intros r. xpull ;=> ->.
  (* xapp *)
  applys xapp_untyped_lemma. { applys @Triple_get. } xapp_simpl tt.
  intros ? ->. xsimpl*.
  (* Alternative LATER: { intros.
    rewrite Hfield_eq_fun_Hsingle, repr_eq. xtpull ;=> N.
    xwp. xapp @Triple_ptr_add_nat. xapp Triple_get. xsimpl~. } *)
Qed.

Lemma Triple_set_field_strong : forall A1 `{EA1:Enc A1} (V1:A1) (l:loc) f A2 `{EA2:Enc A2} (V2:A2),
  Triple ((val_set_field f) l ``V2)
    (l`.f ~~> V1)
    (fun (r:unit) => l`.f ~~> V2).
Proof using.
  intros.
  (* unfold field *)
  rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
  xtpull ;=> N.
  (* xwp *)
  applys xwp_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  eapply (@xlet_lemma loc _ (fun r => \[r = S (l + f)%nat] \* r ~~> V1)). xstructural.
  (* xapp *)
  applys xapp_untyped_lemma. { applys @Triple_ptr_add_nat. } xapp_simpl tt.
  intros ? ->. xsimpl*.  math_rewrite (S (l + f) = l + S f)%nat. xsimpl.
  intros r. xpull ;=> ->.
  (* xapp *)
  applys xapp_untyped_lemma. { applys @Triple_set_strong A1 A2. } xapp_simpl tt.
  xsimpl~.
  (* LATER: alternative
  { intros.
    rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
    xtpull ;=> N. xwp. xapp @Triple_ptr_add_nat. xapp (>> (@Triple_set_strong) A1 A2).
    xsimpl~. } *)
Qed.

Lemma Triple_set_field : forall A `{EA:Enc A} (V1:A) (l:loc) f (V2:A),
  Triple ((val_set_field f) l ``V2)
    (l`.f ~~> V1)
    (fun (r:unit) => l`.f ~~> V2).
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
    intros _. xunfold Record at 2. simpl. xsimpl. }
  { cases (record_set_compute_dyn f (Dyn W) T) as C'; [|false].
    inverts E. specializes~ IHT r. xapply IHT. xsimpl.
    intros. xunfold Record at 2. xsimpl~. }
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
(* --TODO   match goal with |- Triple (trm_apps (trm_val (val_get_field ?f)) ((trm_val ?v)::nil)) ?H _ => *)
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
(* DEPRECATED? *)
Ltac xspec_record tt :=
  match goal with
  | |- Triple (trm_apps (trm_val (val_get_field ?f)) _) _ _ =>
     xspec_record_get_compute tt
  | |- Triple (trm_apps (trm_val (val_set_field ?f)) _) _ _ =>
     xspec_record_set_compute tt
  end.


(* ---------------------------------------------------------------------- *)

(* Wpgen_val without MkStruct *)
Definition Wpgen_val' B {EB:Enc B} (V:B) : Formula :=
  fun A (EA:Enc A) (Q:A->hprop) => PostCast B Q V.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xval'], used by WPrecord *)

Ltac xval'_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val' _) => idtac
  end.

Lemma xval'_lemma : forall (H:hprop) A {EA:Enc A} (Q:A->hprop) (V:A),
  H ==> Q V ->
  H ==> ^(Wpgen_val' V) Q.
Proof using. introv M. unfolds Wpgen_val'. xchange M. applys qimpl_PostCast_r. Qed.

Ltac xval'_core tt :=
  xval'_pre tt;
  applys xval'_lemma.

Tactic Notation "xval'" :=
  xval'_core tt.

Ltac xval'_types_core tt :=
  idtac "[xval'] fails to simplify due to type mismatch";
  match goal with |-
   ?H ==> (Wptag (@Wpgen_val' ?A1 ?EA1 ?X)) ?A2 ?EA2 ?Q =>
   xtypes_type false A1 EA1;
   xtypes_type false A2 EA2
 end.

Tactic Notation "xval'_types" :=
  xval'_types_core tt.


(* ---------------------------------------------------------------------- *)

Lemma xapp_record_get : forall A `{EA:Enc A} (Q:A->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* (match record_get_compute_dyn f L with
    | None => \[False]
    | Some (Dyn V) => (p ~> Record L) \-* ^(Wptag (Wpgen_val' V)) (protect Q) end) ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q.
Proof using.
  introv M1. xchanges (rm M1).
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec.
  destruct (record_get_compute_dyn f L) as [[T ET V]|]; try solve [xpull].
  set (H' := (p ~> Record L \-* ^(Wptag (Wpgen_val' V)) Q)).
  forwards R': R; eauto. clear R. specializes R' p.
  applys himpl_Wpgen_app_untyped_of_Triple.
  applys Triple_PostCast_conseq. xapplys (rm R'). simpl.
  unfold H'. xsimpl. intros ? ->. auto. (* unfold Wptag, Wpgen_val'. *)
Qed. (* --TODO: simplify proof *)


Lemma xapp_record_set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* ((
    match record_set_compute_dyn f (Dyn W) L with
    | None => \[False]
    | Some L' =>
        (p ~> Record L' \-* protect (Q tt)) end)  ) ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_set_field f)) (trms_vals ((p:val)::(``W)::nil)))) Q.
Proof using.
  introv M1. xchanges (rm M1).
  lets R: record_set_compute_spec_correct f EA1 W L.
  unfolds record_set_compute_spec.
  destruct (record_set_compute_dyn f (Dyn W) L) as [L'|]; try solve [xpull].
  forwards R': R; eauto. clear R. specializes R' p.
  applys himpl_Wpgen_app_untyped_of_Triple.
  xapplys R'.
Qed. (* --TODO: simplify proof *)


Global Opaque val_set_field val_get_field.


(* lifted versions, to prove *)

Lemma xapp_record_Get : forall A `{EA:Enc A} (Q:A->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* (match record_get_compute_dyn f L with
    | None => \[False]
    | Some (Dyn V) => (p ~> Record L) \-* ^(Wptag (Wpgen_val' V)) (protect Q) end) ->
  H ==> ^(Wpgen_app A (val_get_field f) ((Dyn p)::nil)) Q.
Proof using. introv M. xchanges (>> xapp_record_get M). Qed.

Lemma xapp_record_Set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* ((
    match record_set_compute_dyn f (Dyn W) L with
    | None => \[False]
    | Some L' =>
        (p ~> Record L' \-* protect (Q tt)) end)  ) ->
  H ==> ^(Wpgen_app unit (val_set_field f) ((Dyn p)::(Dyn W)::nil)) Q.
Proof using. introv M. xchange (>> xapp_record_set M). Qed.


(* ---------------------------------------------------------------------- *)
(* ** No duplicated fields checker *)

(* --LATER: use a more generic noduplicates_exec function *)

(* --TODO: move

Fixpoint field_fresh_exec (k:field) (ks:fields) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.

Fixpoint field_distinct_exec (ks:fields) : bool :=
  match ks with
  | nil => true
  | k::ks' => var_fresh k ks' && var_distinct_exec ks'
  end.

Lemma noduplicates_exec_eq : forall cmp xs,
  noduplicates_exec xs = isTrue (noduplicates xs).
Proof using.
  intros. induction xs as [|x xs']; simpl; rew_isTrue.
  { auto. } { rewrite~ IHxs'. }
Qed.

*)

Fixpoint fresh_field_exec (k:field) (ks:fields) : bool :=
  match ks with
  | nil => true
  | k'::ks' => if eq_nat_dec k k' then false else fresh_field_exec k ks'
  end.

Fixpoint noduplicates_fields_exec (ks:fields) : bool :=
  match ks with
  | nil => true
  | k::ks' => fresh_field_exec k ks' && noduplicates_fields_exec ks'
  end.

Fixpoint consecutive_fields_exec (koffset:nat) (ks:fields) : bool :=
  match ks with
  | nil => true
  | k::ks => if eq_nat_dec k koffset
               then consecutive_fields_exec (S koffset) ks
               else false
  end.

Fixpoint fields_check (ks:fields) (L:Record_fields) : bool :=
  match ks,L with
  | nil, nil => true
  | k::ks', (f,d)::L' => if eq_nat_dec k f
                           then fields_check ks' L'
                           else false
  | _, _ => false
  end.

(* --TODO: use boolean version of [eq_nat_dec] *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record_get] *)

(* Binding for use by [xapp] in case the precondition contains [ p`.f ~~> ?V ]
Hint Extern 1 (Register_Spec (val_get_field _)) => Provide @Triple_get_field.
 *)
(* Test to detect whether the precondition contains [ p`.f ~~> ?V ] *)
Ltac xapp_record_get_find_single_field tt :=
  match goal with
  |- ?H ==> @Wptag (Wpgen_app_untyped (trm_apps (trm_val (val_get_field ?f)) (trms_vals ((val_loc ?p)::nil)))) ?A ?EA ?Q =>
      match H with context [ p`.f ~~> ?V ] => idtac end
  end.

(* Common postprocessing to [xapp_record_get] and [xapp_record_set] *)

Ltac xapp_record_get_set_post tt :=
  xsimpl; simpl; xsimpl; unfold protect; try xval'.

Ltac xapp_record_get_grouped tt :=
  first [ applys xapp_record_Get
        | applys xapp_record_get ];
  xapp_record_get_set_post tt.

(* Tactic to handle [get_field] using lemma [xapp_record_get] which expects
   [p ~> Record ?L], unless the precondition contains [ p`.f ~~> ?V ] in which
   case there is support for the "exploded" mode. *)

Ltac xapp_record_get tt :=
  first [ xapp_record_get_find_single_field tt; fail 1 (* trigger call to [xapp] *)
        | xapp_record_get_grouped tt ].


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record_set] *)

(* Similar construction as for [xapp_record_get]

 *)
Ltac xapp_record_set_find_single_field tt :=
  match goal with
  |- ?H ==> @Wptag (Wpgen_app_untyped (trm_apps (trm_val (val_set_field ?f)) (trms_vals ((val_loc ?p)::?W::nil)))) ?A ?EA ?Q =>
      match H with context [ p`.f ~~> ?V ] => idtac end
  end.

Ltac xapp_record_set_grouped tt :=
  first [ applys xapp_record_Set
        | applys xapp_record_set ];
  xapp_record_get_set_post tt.

Ltac xapp_record_set tt :=
  first [ xapp_record_set_find_single_field tt; fail 1 (* trigger call to [xapp] *)
        | xapp_record_set_grouped tt ].


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record_new] *)

Ltac list_boxer_to_dyns E :=
  match E with
  | nil => constr:(@nil dyn)
  | (boxer ?V) :: ?E' =>
       let L := list_boxer_to_dyns E' in
       constr:( (Dyn V) :: L)
  end.

(* --TODO: port the proof from the previous CFML version to the new setting; it's nontrivial
Parameter xapp_record_new : forall (Vs:dyns) (Q:loc->hprop) (H:hprop) (ks:fields) (vs:vals),
  noduplicates_fields_exec ks = true ->
  LibListExec.is_nil ks = false ->
  List.length ks = List.length Vs ->
  vs = encs Vs ->
  (fun p => p ~> Record (List.combine ks Vs)) \*+ H ===> (protect Q) ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_record_init ks)) (trms_vals vs))) Q.
 *)
Lemma xapp_record_new : true. auto. Qed. (* stub *)

Ltac xnew_post tt :=
  idtac.

Ltac xnew_core E :=
  let Vs := list_boxer_to_dyns E in
  applys (@xapp_record_new Vs);
  [ try reflexivity
  | try reflexivity
  | try reflexivity
  | try reflexivity
  | xsimpl; simpl List.combine; simpl; xsimpl; unfold protect; xnew_post tt ].
(* --TODO:  simpl; xsimpl; might not be needed *)

Tactic Notation "xnew" constr(E) :=
  xnew_core E.


(* An implementation of [xnew_post] that can be used to expose fields one by one
   instead of generating [p ~> Record ?L]. To activate, use:
   [Ltac xnew_post ::= xnew_post_exploded]. *)

Ltac xnew_post_exploded tt :=
  let r := fresh "r" in intros r; autorewrite with Record_to_HField; gen r.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record_delete] *)

(*
Parameter xapp_record_delete : forall (L:Record_fields) (Q:unit->hprop) (H:hprop) (ks:fields) (p:loc),
  H ==> p ~> Record L \* (protect (Q tt)) ->
  fields_check ks L = true ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_record_delete ks)) (trms_vals ((val_loc p)::nil)))) Q.
*)

Ltac xapp_record_delete_grouped tt :=
  fail "not yet implemented: xapp_record_delete_grouped".


(* --TODO: define delete tactic for [p ~> Record L] *)

Fixpoint xapp_to_delete_fields (p:loc) (ks:fields) :=
  match ks with
  | nil => \[]
  | k::ks' => (\exists (A:Type) (EA:Enc A) (V:A), p`.k ~~> V) \* xapp_to_delete_fields p ks'
  end.

(** Exploded mode for delete *)

Lemma xapp_to_delete_fields_of_consecutive_fields_exec : forall ks koffset p,
  consecutive_fields_exec koffset ks = true ->
  xapp_to_delete_fields p ks ==> Dealloc (List.length ks) (S p+koffset)%nat.
Proof using.
  intros ks. induction ks as [|k ks']; simpl; introv M.
  { rewrite Dealloc_zero_eq. (* --TODO: rename *) xsimpl. }
  { case_if. subst k. rewrite Dealloc_succ_eq. xpull ;=> A EA V.
    rewrite Hfield_to_hfield. xchange hfield_to_hsingle ;=> N.
    xsimpl (``V). xchange (>> IHks' M).
    math_rewrite ((S p + S koffset)%nat = S (S (p + koffset))%nat). xsimpl. }
Qed.

(* LATER: requires dealloc
Lemma xapp_record_delete_exploded : forall (Q:unit->hprop) (H:hprop) (ks:fields) (p:loc),
  consecutive_fields_exec 0 ks = true ->
  H ==> xapp_to_delete_fields p ks \* (protect (Q tt)) ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_record_delete ks)) (trms_vals ((val_loc p)::nil)))) Q.
*)
(*
  introv Hks M. applys MkStruct_erase. xchange (rm M).
  xchange (>> xapp_to_delete_fields_of_consecutive_fields_exec Hks).
  math_rewrite ((p+0)%nat = p). rewrite <- Triple_eq_himpl_Wp.
  (* xwp *)
  applys xwp_lemma_funs; try reflexivity; simpl.
  (* xapp *)
  xapp Triple_dealloc. { math. }
  (* xsimpl *)
  rewrite abs_nat. unfold xapp_hidden, protect. xsimpl.  (* --TODO avoid *)
Qed.
*)
Lemma xapp_record_delete_exploded : True. auto. Qed. (* stub *)

Ltac xapp_record_delete_exploded tt :=
  applys xapp_record_delete_exploded;
  [ try reflexivity
  | unfold xapp_to_delete_fields; xsimpl; unfold protect ].

Ltac xapp_record_delete_find_single_field tt :=
  match goal with
  |- ?H ==> @Wptag (Wpgen_app_untyped (trm_apps (trm_val (val_record_delete ?ks)) (trms_vals ((val_loc ?p)::nil)))) ?A ?EA ?Q =>
      match H with context [ p`.?f ~~> ?V ] => idtac end
  end.

Ltac xapp_record_delete tt :=
  first [ xapp_record_delete_find_single_field tt; xapp_record_delete_exploded tt
        | xapp_record_delete_grouped tt ].




(* ********************************************************************** *)
(* * Direct WPgen for record allocation *)

Definition Wpgen_record_new (Lof:loc->Record_fields) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    (fun r => r ~> Record (Lof r)) \--* (PostCast loc Q)).

(* Note:   [Triple H (new L) (fun r => r ~> Record (Lof r) \* H)]
   H ==> wp (new L) (fun r => r ~> Record (Lof r) \* H)

   H \* ((fun r => r ~> Record (Lof r) \* H) \--* Q) ==> wp (new L) Q
   wp (new L) Q :=  ((fun r => r ~> Record (Lof r)) \--* Q)

  TODO: exercise in course. *)

Lemma xapp_lemma_record_new : forall (Lof:loc->Record_fields) H (Q:loc->hprop),
  (forall r, (r ~> Record (Lof r)) \* H ==> (Q r)) ->
  H ==> ^(Wpgen_record_new Lof) Q.
Proof using.
  introv M. applys MkStruct_erase. xsimpl. intros r.
  xchange M. applys qimpl_PostCast_r.
Qed.

(* TODO later check no redundant record fields? *)

Fixpoint record_with_compute_dyn (L:Record_fields) (Lup:Record_fields) : option Record_fields :=
  match Lup with
  | nil => Some L
  | (f,d)::Lup' => (* TODO: monadic notation? *)
      match record_set_compute_dyn f d L with
      | None => None
      | Some L' => record_with_compute_dyn L' Lup'
      end
  end.

(* [record_with_check_all_fields fs L] checks that every field from [fs] is bound in [L]
   --in practice due to typing the set of fields can only be equal. *)

Fixpoint record_with_check_all_fields (fs:fields) (L:Record_fields) : bool :=
  match fs with
  | nil => true
  | f::fs' =>
     match record_get_compute_dyn f L with
     | None => false
     | Some d => record_with_check_all_fields fs' L
     end
  end.

(* TODO: check header is present, if we want the record fields to not be considered affine *)

Definition Wpgen_record_with (r:loc) (Lup:Record_fields) (fs:fields) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \forall L,
    r ~> Record L \* (
      match record_with_check_all_fields fs L with
      | false => \[False]
      | true =>
        match record_with_compute_dyn L Lup with
        | None => \[False]
        | Some L' => (fun r' => r ~> Record L \* r' ~> Record L') \--* (PostCast loc Q)
        end
      end)).

(* LATER: prove
Parameter xapp_record_With_lemma : forall (Q:loc->hprop) (H:hprop) (p:loc) (L Lup:Record_fields) (fs:fields),
  H ==> p ~> Record L \* (
      match record_with_check_all_fields fs L with
      | false => \[False]
      | true =>
        match record_with_compute_dyn L Lup with
        | None => \[False]
        | Some L' => (*  (fun r' => r ~> Record L \* r' ~> Record L') \--* (Post_cast loc (protect Q)) *)
                 \forall p', (p ~> Record L \* p' ~> Record L') \-* protect (Q p')
        end
      end) ->
  H ==> ^(Wpgen_record_with p Lup fs) Q.
*)
Lemma xapp_record_With_lemma : true. auto. Qed. (* stub *)

Ltac xapp_record_with_post tt :=
  xsimpl; simpl; xsimpl; unfold protect.

Ltac xapp_record_with tt :=
  applys xapp_record_With_lemma;
  xapp_record_with_post tt.


(* ********************************************************************** *)
(* * Notation *)

(* TODO *)
Declare Scope record_scope.
Notation "p '~~~>' kvs" := (p ~> Record kvs)
  (at level 32) : record_scope.

(* ********************************************************************** *)
(* * Tactics *)

(* TODO *)

(* ---------------------------------------------------------------------- *)
(* ** Extending tactic [xapp] to support record operations *)

Ltac xapp_record tt ::= (* initial dummy binding located in WPTactics *)
  match xgoal_code_without_wptag tt with
  | Wpgen_record_new ?Lof => applys xapp_lemma_record_new
  | Wpgen_record_with ?v ?L ?fs => xapp_record_with tt
  | Wpgen_app ?T ?f ?Vs =>
      match f with
      | val_get_field _ => xapp_record_get tt
      | val_set_field _ => xapp_record_set tt
      (* DEPRECATED | val_record_init _ => xapp_record_new tt (* TODO redundant? *)*)
      | val_record_delete _ => xapp_record_delete tt
      end
  end.

Ltac xapp_pre_wp tt ::=
  xlet_xseq_cont_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app_untyped ?t) => idtac (* TODO: DEPRECATED *)
  | (Wpgen_app ?T ?f ?Vs) => idtac
  | (Wpgen_record_new ?Lof) => idtac
  | (Wpgen_record_with ?v ?L ?fs) => idtac
  end.

Ltac check_is_Wpgen_record_alloc F ::=
  match F with
  | (Wpgen_record_new _) => idtac
  | (Wpgen_record_with _ _) => idtac
  end.


(* ---------------------------------------------------------------------- *)
(* ** Notation *)


Notation "'New' Vs 'as' r" :=
  ((Wpgen_record_new (fun r => Vs)))
  (in custom cf at level 69,
   Vs constr at level 69)
  : cf_scope.

Notation "'New' Vs" :=
  ((Wpgen_record_new (fun _ => Vs)))
  (in custom cf at level 69,
   Vs constr at level 69)
  : cf_scope.

Notation "'New' v 'With' Vs" :=
  ((Wpgen_record_with v Vs _))
  (in custom cf at level 69,
   only printing,
   v constr at level 69,
   Vs constr at level 69)
  : cf_scope.


(*
Notation "'App' r '.' f" :=
  (Wpgen_app _ (val_get_field f) ((Dyn r)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   format "'App'  r '.' f") : cf_scope.

Notation "'App' r '.' f <- v" :=
  (Wpgen_app _ (val_set_field f) ((Dyn r)::(Dyn v)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   v constr at level 69,
   format "'App'  r '.' f  <-  v") : cf_scope.

*)

Notation "r '.' f" :=
  (Wpgen_app _ (val_get_field f) ((Dyn r)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   format "r '.' f") : cf_scope.

Notation "r '.' f <- v" :=
  (Wpgen_app _ (val_set_field f) ((Dyn r)::(Dyn v)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   v constr at level 69,
   format "r '.' f  <-  v") : cf_scope.

(** Same with tag 
DEPRECATED


Notation "'New' Vs 'as' r" :=
  (Wptag (Wpgen_record_new (fun r => Vs)))
  (in custom cf at level 69,
   only printing,
   Vs constr at level 69)
  : cf_scope.

Notation "'New' Vs" :=
  (Wptag (Wpgen_record_new (fun _ => Vs)))
  (in custom cf at level 69,
   only printing,
   Vs constr at level 69)
  : cf_scope.

Notation "r '.' f" :=
  (Wptag (Wpgen_app _ (val_get_field f) ((Dyn r)::nil)))
  (in custom cf at level 69,
   only printing,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   format "r '.' f") : cf_scope.

Notation "r '.' f <- v" :=
  (Wptag (Wpgen_app _ (val_set_field f) ((Dyn r)::(Dyn v)::nil)))
  (in custom cf at level 69,
   only printing,
   no associativity,
   r constr at level 0,
   f constr at level 0,
   v constr at level 69,
   format "r '.' f  <-  v") : cf_scope.
*)
