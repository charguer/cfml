(**

This file defines notation, specification and tactics for manipulating
records.

Disclaimer: notation currently support records with up to 5 fields.

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
(* ** Record operations: get, set, alloc, init *)

Definition val_get_field (k:field) : val :=
  VFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  VFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Definition val_record_alloc (ks:fields) : val :=
  VFun 'u :=
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
Delimit Scope fields_scope with fields.


(* ---------------------------------------------------------------------- *)
(* ** Record representation *)

(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Bind Scope fields_scope with Record_fields.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r`.f ~~> V) \* (r ~> Record L')
  end.

(* TODO: currently restricted due to [r `. f ~> V] not ensuring [r<>null] *)
(* TODO: rename *)
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
  p ~> Record nil = \[].
Proof using. auto. Qed.

Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.x ~~> ``V \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.

Hint Rewrite Record_nil Record_cons enc_dyn_make : Record_to_HField.


Local Open Scope heap_scope_ext.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,v) L']. { false. }
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

(* LATER: xrecord_eq might need to take care of reordering *)

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

(* TODO move *)
Lemma Hfield_eq_fun_Hsingle_ext : forall `{EA:Enc A} (V:A) (l:loc) (f:field),
  (l`.f ~~> V) = (((l+f)%nat ~~> V) \* \[l <> null]).
Proof using. intros. rewrite Hfield_eq_fun_Hsingle. rewrite~ repr_eq. Qed.

Lemma Hfield_to_Hsingle : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  (l`.f ~~> V) ==> ((l+f)%nat ~~> V) \* \[l <> null].
Proof using. intros. rewrite~ Hfield_eq_fun_Hsingle_ext. Qed.

Lemma Hsingle_to_Hfield : forall (l:loc) (f:field) `{EA:Enc A} (V:A),
  l <> null ->
  ((l+f)%nat ~~> V) ==> (l`.f ~~> V).
Proof using. introv N. rewrite Hfield_eq_fun_Hsingle_ext. xsimpl~. Qed.



Lemma Triple_get_field : forall (l:loc) f `{EA:Enc A} (V:A),
  TRIPLE ((val_get_field f) l)
    PRE (l`.f ~~> V)
    POST (fun r => \[r = V] \* (l`.f ~~> V)).
Proof using.
  dup.
  { intros.
    rewrite Hfield_eq_fun_Hsingle, repr_eq. xtpull ;=> N.
    xwp. xapp @Triple_ptr_add_nat. xapp Triple_get. xsimpl~. }
  { (* details TEMPORARY *)
    intros.
    (* unfold field *)
    rewrite Hfield_eq_fun_Hsingle, repr_eq. xtpull ;=> N.
    (* xwp *)
    applys xwp_lemma_funs; try reflexivity; simpl.
    (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_ptr_add_nat. } xapp_post tt ;=> r ->.
    (* xapp *)
    applys @xapps_lemma. { applys @Triple_get. } xapp_post tt.
    (* done *)
    xsimpl~. }
Qed.

Lemma Triple_set_field_strong : forall `{EA1:Enc A1} (V1:A1) (l:loc) f `{EA2:Enc A2} (V2:A2),
  TRIPLE ((val_set_field f) l ``V2)
    PRE (l`.f ~~> V1)
    POST (fun (r:unit) => l`.f ~~> V2).
Proof using.
  dup.
  { intros.
    rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
    xtpull ;=> N. xwp. xapp @Triple_ptr_add_nat. xapp (>> (@Triple_set_strong) A1 A2).
    xsimpl~. }
  { intros.
    (* unfold field *)
    rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
    xtpull ;=> N.
    (* xwp *)
    applys xwp_lemma_funs; try reflexivity; simpl.
    (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_ptr_add_nat. } xsimpl ;=> r ->.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_set_strong A1 A2. } xsimpl. xapp_post tt.
    (* done *)
    xsimpl~. }
Qed.

Lemma Triple_set_field : forall `{EA:Enc A} (V1:A) (l:loc) f (V2:A),
  TRIPLE ((val_set_field f) l ``V2)
    PRE (l`.f ~~> V1)
    POST (fun (r:unit) => l`.f ~~> V2).
Proof using. intros. applys Triple_set_field_strong. Qed.

Lemma Triple_set_field_Decode : forall (v2:val) A (EA:Enc A) (V1:A) (l:loc) f (V2:A),
  Decode v2 V2 ->
  TRIPLE ((val_set_field f) l v2)
    PRE (l`.f ~~> V1)
    POST (fun (r:unit) => l`.f ~~> V2).
Proof using. introv M. unfolds Decode. subst v2. applys Triple_set_field_strong. Qed.

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
    | Some (Dyn V) => (p ~> Record L) \-* ^(Wptag (Wpgen_cast V)) (protect Q) end) ->
  H ==> ^(Wpgen_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q.
Proof using.
  introv M1. xchanges (rm M1).
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec.
  destruct (record_get_compute_dyn f L) as [[T ET V]|]; try solve [xpull].
  set (H' := (p ~> Record L \-* ^(`Wpgen_cast V) Q)).
  forwards R': R; eauto. clear R. specializes R' p.
  applys himpl_Wpgen_app_of_Triple.
  applys Triple_enc_change. xapplys (rm R'). simpl.
  unfold RetypePost, Wptag. xpull ;=> ? ->. unfold H'. xpull.
  unfold Wpgen_cast, Wptag. applys himpl_refl.
Qed. (* TODO: simplify proof *)

Lemma xapp_record_set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* ((
    match record_set_compute_dyn f (Dyn W) L with
    | None => \[False]
    | Some L' =>
        (p ~> Record L' \-* protect (Q tt)) end)  ) ->
  H ==> ^(Wpgen_app (trm_apps (trm_val (val_set_field f)) (trms_vals ((p:val)::(``W)::nil)))) Q.
Proof using.
  introv M1. xchanges (rm M1).
  lets R: record_set_compute_spec_correct f W L.
  unfolds record_set_compute_spec.
  destruct (record_set_compute_dyn f (Dyn W) L) as [L'|]; try solve [xpull].
  forwards R': R; eauto. clear R. specializes R' p.
  applys himpl_Wpgen_app_of_Triple.
  xapplys R'.
Qed. (* TODO: simplify proof *)


Global Opaque val_set_field val_get_field.



(* ---------------------------------------------------------------------- *)
(* ** No duplicated fields checker *)

(* LATER: use a more generic noduplicates_exec function *)

(* TODO: move

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


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record] *)

Ltac xapp_record_get_set_post tt :=
  xsimpl; simpl; xsimpl; unfold protect; try xcast.

Ltac xapp_record_get tt :=
  applys xapp_record_get; xapp_record_get_set_post tt.

Ltac xapp_record_set tt :=
  applys xapp_record_set; xapp_record_get_set_post tt.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xnew] *)

Ltac list_boxer_to_dyns E :=
  match E with
  | nil => constr:(@nil dyn)
  | (boxer ?V)::?E' =>
       let L := list_boxer_to_dyns E' in
       constr:((Dyn V)::L)
  end.

(* TODO: port the proof from the previous CFML version to the new setting *)
Parameter xapp_record_new : forall (Vs:dyns) (Q:loc->hprop) (H:hprop) (ks:fields) (vs:vals),
  noduplicates_fields_exec ks = true ->
  ks <> nil ->
  List.length ks = List.length Vs ->
  vs = encs Vs ->
  (fun p => p ~> Record (List.combine ks Vs)) \*+ H ===> (protect Q) ->
  H ==> ^(Wpgen_app (trm_apps (trm_val (val_record_init ks)) (trms_vals vs))) Q.

Ltac xnew_post tt :=
  idtac.

Ltac xnew_core E :=
  let Vs := list_boxer_to_dyns E in
  applys (@xapp_record_new Vs);
  [ try reflexivity
  | intros ?; solve [ false ]
  | try reflexivity
  | try reflexivity
  | xsimpl; simpl List.combine; simpl; xsimpl; unfold protect; xnew_post tt ].
(* TODO:  simpl; xsimpl; might not be needed *)

Tactic Notation "xnew" constr(E) :=
  xnew_core E.

Lemma xapp_record_new' : forall (Vs:dyns) (Q:loc->hprop) (H:hprop) (ks:fields) (vs:vals),
  noduplicates_fields_exec ks = true ->
  ks <> nil ->
  Decodes vs Vs ->
  List.length ks = List.length Vs ->
  (fun p => p ~> Record (List.combine ks Vs)) \*+ H ===> (protect Q) ->
  H ==> ^(Wpgen_app (trm_apps (trm_val (val_record_init ks)) (trms_vals vs))) Q.
Proof using. introv HN HE HD EQ HI. unfolds Decodes. applys* xapp_record_new. Qed.

Ltac xnew_core_noarg tt :=
  applys xapp_record_new';
  [ try reflexivity
  | intros ?; solve [ false ]
  | xdecodes
  | try reflexivity
  | xsimpl; simpl List.combine; unfold protect; xnew_post tt ].

Tactic Notation "xnew" :=
  xnew_core_noarg tt.

Ltac xapp_record_new tt :=
  xnew_core_noarg tt.


(* ---------------------------------------------------------------------- *)
(* ** Extending tactic [xapp] to support record operations *)

Ltac xapp_record tt ::= (* initial dummy binding located in WPTactics *)
  match xgoal_fun tt with
  | (val_get_field _) => xapp_record_get tt
  | (val_set_field _) => xapp_record_set tt
  | (val_record_init _) => xapp_record_new tt
  end.

