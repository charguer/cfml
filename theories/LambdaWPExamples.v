(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [LambdaWPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWPTactics.
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
  ValFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  ValFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.


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
  intros.
  (* unfold field *)
  rewrite Hfield_eq_fun_Hsingle, repr_eq. xpull ;=> N.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapp *)
  applys @xapp_lemma. { applys @Triple_ptr_add_nat. } hsimpl ;=> r ->.
  (* xapp *)
  applys @xapps_lemma. { applys @Triple_get. } hsimpl.
  (* done *)
  hsimpl~.
Qed.

Lemma Triple_set_field_strong : forall `{EA1:Enc A1} (V1:A1) (l:loc) f `{EA2:Enc A2} (V2:A2),
  TRIPLE ((val_set_field f) l ``V2)
    PRE (l `.` f ~~> V1)
    POST (fun (r:unit) => l `.` f ~~> V2).
Proof using.
  intros.
  (* unfold field *)
  rewrite Hfield_eq_fun_Hsingle. rewrite repr_eq. rewrites (>> repr_eq (l,f)).
  xpull ;=> N.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapp *)
  applys @xapp_lemma. { applys @Triple_ptr_add_nat. } hsimpl ;=> r ->.
  (* xapp *)
  applys @xapp_lemma. { applys @Triple_set_strong A1 A2. } hsimpl.
  (* done *)
  hsimpl~.
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
    intros. xunfold Record at 2. simpl. hsimpl~. }
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


(* ********************************************************************** *)
(* * Demo *)




(* ********************************************************************** *)
(* * Point *)

(* TODO *)
Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 66, f at level 0, format "t1 ''.' f" ) : trm_scope.


Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2") : trm_scope.


Lemma himpl_wp_app_of_Triple : forall A `{EA:Enc A} (Q:A->hprop) t H,
  Triple t H Q ->
  H ==> ^(Wp_app t) Q.
Proof using. intros. applys Local_erase. rewrite~ <- Triple_eq_himpl_Wp_Triple. Qed.



Lemma xapp_record_set : forall A1 `{EA1:Enc A1} (W:A1)(Q:unit->hprop) H H1 (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* H1 ->
  match record_set_compute_dyn f (Dyn W) L with
  | None => False
  | Some L' =>  
      p ~> Record L' \* H1 ==> Q tt
  end ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_set_field f)) (trms_vals ((p:val)::(``W)::nil)))) Q.
Proof using.
  introv M1 M2.
  hchanges (rm M1).
  lets R: record_set_compute_spec_correct f W L.
  unfolds record_set_compute_spec.
  destruct (record_set_compute_dyn f (Dyn W) L); tryfalse.
  forwards R': R; eauto. clear R. specializes R' p. 
  applys himpl_wp_app_of_Triple.
  xapplys R'. hsimpl. hchanges M2. 
Qed. (* TODO: simplify proof *)



Lemma xapp_record_get : forall A `{EA:Enc A} (Q:A->hprop) H H1 (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* H1 ->
  match record_get_compute_dyn f L with
  | None => False
  | Some (Dyn V) =>  
      PostChange (fun x => \[x = V] \* p ~> Record L \* H1) Q
  end ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q.
Proof using.
  introv M1 M2.
  hchanges (rm M1).
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec.
  destruct (record_get_compute_dyn f L); tryfalse. destruct d as [T V].
  forwards R': R; eauto. clear R. specializes R' p. 
  applys himpl_wp_app_of_Triple. Search PostChange.
  applys Triple_enc_change M2.
  xapplys R'. auto.
Qed. (* TODO: simplify proof *)

Lemma PostChange_same : forall `{EA:Enc A} (Q1 Q2:A->hprop),
  Q1 ===> Q2 ->
  PostChange Q1 Q2.
Proof using. introv M. unfolds. intros X. hchanges* M. Qed.



Lemma PostChange_same_subst : forall H `{EA:Enc A} (V:A) (Q:A->hprop),
  H ==> Q V ->
  PostChange (fun x => \[x = V] \* H) Q.
Proof using. introv M. applys PostChange_same. hpull ;=> ? ->. auto. Qed.



Definition record_get_compute_spec' (f:field) (L:Record_fields) : option Prop :=
  match record_get_compute_dyn f L with
  | None => None
  | Some (Dyn V) => Some (forall p H H1 Q,
     H ==> p ~> Record L \* H1 ->
     p ~> Record L \* H1 ==> Q V -> (* nosubst: (fun x => \[x = v] \* H) ===> Q *)
     H ==> ^(Wp_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q)
  end.

Lemma record_get_compute_spec_correct' : forall (f:field) L (P:Prop),
  record_get_compute_spec' f L = Some P ->
  P.
Proof using.
  introv M. unfolds record_get_compute_spec'.
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec. 
  destruct (record_get_compute_dyn f L) as [[T ET V]|]; tryfalse.
  inverts M. introv M1 M2.
  forwards R': R. eauto. 
  hchange M1. apply himpl_wp_app_of_Triple. xapplys R'.
  intros. subst. hchanges M2.
Qed.





Module Point.
Implicit Type p : loc.
Implicit Type x y k : int.

Definition X : field := 0%nat.
Definition Y : field := 1%nat.
Definition K : field := 2%nat.

Definition Point (x y:int) (p:loc) : hprop :=
  \exists k, p ~> Record`{ X := x; Y := y; K := k } \* \[ k = x + y ].


Definition val_move_X : val :=
  ValFun 'p :=
   Set 'p'.X ':= ('p'.X '+ 1) ';
   Set 'p'.K ':= ('p'.K '+ 1).


(* TODO: 
   Set 'p '. X ':= ('p '.X '+ 1).
   won't parse 
*)


Lemma Triple_move_X : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  unfold Point. hpull ;=> k Hk.
  (* xseq *)
  applys xseq_lemma.
  (* xlet-poly *) (* TODO: check why double let *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  eapply Local_erase.
  (* xapps record, strategy 2 

  match goal with |- PRE ?H CODE (`App (trm_val (val_get_field ?f)) ?v) POST _ => 
    let r := xspec_record_get_loc v in
    let L := xspec_record_repr_compute r H in 
  let G := fresh in 
  forwards G: (record_get_compute_spec_correct' f L);
  [ reflexivity | applys G ]; try clear G end. 
   hsimpl. 
*)

  (* xapps record, strategy 1 *)

  applys xapp_record_get. hsimpl. simpl. applys @PostChange_same_subst. rew_heap.

    (* variante 
    applys @himpl_wp_app_of_Triple.
    xspec_record tt ;=> M1. (* xspec_record_get_compute tt *)
    applys Triple_ramified_frame. { applys M1. } hsimpl ;=> ? ->. (* todo: xapp lemma *)
    *)
  (* xreturn *)
  applys @xreturn_lemma_typed.
  (* xapps record *)
  applys xapp_record_set. hsimpl. simpl.
    (* variante
    applys himpl_wp_app_of_Triple.
    xspec_record tt ;=> M2. (* xspec_record_get_compute tt *)
    applys Triple_ramified_frame. { applys M2. } hsimpl.
    *)

  (* xlet-poly *) (* TODO: check why double let *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  eapply Local_erase.
  (* xapps record *)
  applys xapp_record_get. hsimpl. simpl. applys @PostChange_same_subst. rew_heap.
    (* variante:
    applys @himpl_wp_app_of_Triple.
    xspec_record tt ;=> M1'. (* xspec_record_get_compute tt *)
    applys Triple_ramified_frame. { applys M1'. } hsimpl ;=> ? ->. (* todo: xapp lemma *)
    *)
  (* xreturn *)
  applys @xreturn_lemma_typed.
  (* xapps record *)
    applys xapp_record_set. hsimpl. simpl.
    (* variante:
    applys himpl_wp_app_of_Triple.
    xspec_record tt ;=> M2'. (* xspec_record_get_compute tt *)
    applys Triple_ramified_frame. { applys M2'. } hsimpl.
    *)

  (* done *)
  hsimpl. math.
Qed.


End Point.


(* ********************************************************************** *)
(* * Mutable lists *)


Module MList.

Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).

Definition trm_Nil : trm := trm_constr "nil" nil.
Definition trm_Cons (t1 t2:trm) : trm := trm_constr "cons" (t1::t2::nil).

Definition pat_Nil : pat := pat_constr "nil" nil.
Definition pat_Cons (p1 p2:pat) : pat := pat_constr "cons" (p1::p2::nil).


(*
  course -> For recursive predicate: would be useful to recall the duality between
  `Fixpoint` and `Inductive` for defining predicates, taking the example of `In` and `Forall` on lists.
*)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (MList L' p')
  end.

Lemma MList_unfold : 
  MList = fun A `{EA:Enc A} (L:list A) (p:loc) =>
    \exists v, p ~~> v \*
    match L with
    | nil => \[v = Nil]
    | x::L' => \exists p', \[v = Cons x p'] \* (MList L' p')
    end.
Proof using. applys fun_ext_4; intros A EA L p. destruct L; auto. Qed.
 


(* ---------------------------------------------------------------------- *)
(** Length *)

(* TODO : move *)
Notation "'ValFix' f x1 ':=' t" :=
  (val_fixs f (x1::nil) t)
  (at level 69, f, x1 at level 0) : trm_scope.


Definition val_mlist_length : val :=
  ValFix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| pat_Nil '=> 0
    '| pat_Cons 'x 'q '=> 1 '+ 'f 'q
    End.

Lemma Triple_mlist_length_1 : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (MList L p)
    POST (fun (r:int) => \[r = length L] \* MList L p).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  (* xtriple *)
  intros. applys xtriple_lemma_fixs; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xunfold *)
  pattern MList at 1. rewrite MList_unfold. hpull ;=> v.
  (* xapps *)
  applys @xapps_lemma. { applys @Triple_get. } hsimpl.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; hpull.
    { intros ->. applys~ @xval_lemma 0. hsimpl. skip. (* TODO *) rew_list~. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; hpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        (* xlet *)
        eapply Local_erase. (* TODO: change to : applys xlet_lemma. *)
        (* xapp *)
        applys @xapp_lemma. { applys* IH. } hsimpl ;=> r ->.
        (* xreturn *)
        applys @xreturn_lemma_typed. (* TODO: rename*)
        (* done *)
        pattern MList at 2. rewrite MList_unfold. hsimpl*. rew_list; math. } }
    { intros N. destruct L as [|x L']; hpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.




(*

   length : using recursion + using loop
   copy : using recursion + using loop
   append (destructive, or non-destructive)
   mem
   count
   in-place reversal
   cps-append (bonus example)
   split 
   combine  
   basic sorting on list of integers, e.g. merge sort, insertion sort

*)

End MList.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.

(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  ValFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  ValFun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  intros.
  (* optional simplification step to reveal [trm_apps] *)
  simpl combiner_to_trm.
  (* xtriple *)
  applys xtriple_lemma_funs.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  eapply Local_erase.
  (* xapps *)
  applys @xapps_lemma. { applys Triple_get. } hsimpl.
  (* xreturn *)
  applys @xreturn_lemma_val.
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl.
  (* done *) 
  auto.
Qed.

Lemma Triple_incr_frame : forall (p1 p2:loc) (n1 n2:int),
  TRIPLE (val_incr p1)
    PRE (p1 ~~> n1 \* p2 ~~> n2)
    POST (fun (r:unit) => (p1 ~~> (n1+1) \* p2 ~~> n2)).
Proof using.
  skip.
Qed.

(* TODO SHOULD BE:

  xtriple.
  xlet. { xapp. xapplys triple_get. }
  hpull ;=> ? ->.
  xlet. { xapp. xapplys triple_add. }
  hpull ;=> ? ->.
  xapp. xapplys triple_set. auto.

then just:

  xtriple.
  xapp.
  xapp.
  xapp.

*)

(*

(* ---------------------------------------------------------------------- *)
(** Swap *)

Definition val_swap :=
  ValFun 'p 'q :=
    Let 'x := val_get 'p in
    Let 'y := val_get 'q in
    val_set 'p 'y ;;;
    val_set 'q 'x.

Lemma Triple_swap_neq : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (w:A2) p q,
  Triple (val_swap ``p ``q)
    PRE (p ~~> v \* q ~~> w)
    POST (fun (r:unit) => p ~~> w \* q ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. hsimpl~.
Qed.

Lemma Triple_swap_eq : forall A1 `{EA1:Enc A1} (v:A1) p,
  Triple (val_swap ``p ``p)
    PRE (p ~~> v)
    POST (fun (r:unit) => p ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Succ using incr *)

Definition val_succ_using_incr :=
  ValFun 'n :=
    Let 'p := val_ref 'n in
    val_incr 'p ;;;
    Let 'x := val_get 'p in
    'x.

Lemma triple_succ_using_incr : forall n,
  triple (val_succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xtriple. xapp as p. intros; subst. xapp~. intros _. xapps~.
  (* not possible: applys local_erase. unfold cf_val. hsimpl. *)
  xvals~.
Qed.



(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  ValFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma Triple_val_example_let : forall n,
  Triple (val_example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xtriple. xapps. xapps. xapp. hsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

(*
  let val_example_one_ref n =
    let i = ref 0 in
    incr i;
    !i
*)

Definition val_example_one_ref :=
  ValFun 'n :=
    Let 'k := 'n '+ 1 in
    Let 'i := 'ref 'k in
    val_incr 'i ;;;
    '!'i.

Lemma Triple_val_example_one_ref : forall n,
  Triple (val_example_one_ref n)
    PRE \[]
    POST (fun r => \[r = n+2]).
Proof using.
  xtriple. xapps. xapps ;=> r. xapp~. xapp~. hsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding two ref *)

(*
  let val_example_two_ref n =
    let i = ref 0 in
    let r = ref n in
    decr r;
    incr i;
    r := !i + !r;
    !i + !r
*)

Definition val_example_two_ref :=
  ValFun 'n :=
    Let 'i := 'ref 0 in
    Let 'r := 'ref 'n in
    val_decr 'r ;;;
    val_incr 'i ;;;
    Let 'i1 := '!'i in
    Let 'r1 := '!'r in
    Let 's := 'i1 '+ 'r1 in
    'r ':= 's ;;;
    Let 'i2 := '!'i in
    Let 'r2 := '!'r in
    'i2 '+ 'r2.

Lemma Triple_val_example_two_ref : forall n,
  Triple (val_example_two_ref n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xtriple. xapp ;=> i. xapp ;=> r.
  xapp~. xapp~. xapps. xapps. xapps. xapps~.
  xapps. xapps. xapps.
  hsimpl. math.
Qed.

*)

End Basic.


(* ********************************************************************** *)
(* * Test *)

Module Test.

(* ---------------------------------------------------------------------- *)
(* ** Case without variables *)

Definition val_test1 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else 'Fail.

Lemma Triple_test1 : forall (p:loc),
  TRIPLE (val_test1 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Case with 1 variable *)

Definition val_test2 : val :=
  ValFun 'p :=
    Case' 'p = 'x Then 'x Else 'Fail.

Lemma Triple_test2 : forall (p:loc),
  TRIPLE (val_test2 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Match without variables *)


Definition val_test0 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else
    Case' 'p = pat_unit Then 'p Else 
    'Fail.

Lemma triple_test0 : forall (p:loc),
  TRIPLE (val_test0 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


End Test.

(* ********************************************************************** *)
(* * Stack *)

Module Stack.

Definition val_is_empty : val :=
  ValFun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  ValFun 'u :=
   val_ref 'nil.

Definition val_push : val :=
  ValFun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition val_pop : val :=
  ValFun 'p :=
   (Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End).

Definition val_rev_append : val :=
  ValFix 'f 'p1 'p2 :=
    If_ val_is_empty 'p1 Then '() Else 
       Let 'x := val_pop 'p1 in
       val_push 'p2 'x ';
       'f 'p1 'p2.


Definition Stack `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


Lemma Triple_is_empty : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (val_is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma nil).
  (* xapps *)
  applys @xapps_lemma_pure. { applys @Triple_eq_val. } hsimpl.
  (* done *)
  rewrite* @Enc_injective_value_eq_r.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* Two ways of completing the proof *)
  dup.
  (* xcase with lemma for match list *)
  { applys xmatch_lemma_list.
    { intros HL. 
      (* xfail *)
      false. }
    { intros X L' HL. 
      (* xseq *)
      applys xseq_lemma.
      (* xapp *)
      applys @xapp_lemma. { applys @Triple_set. } hsimpl.
      (* xval *)
      applys~ xval_lemma.
      (* done *)
      hsimpl~. } }
  (* inlining the proof of xmatch_list *)
  { applys xcase_lemma0 ;=> E1.
    { destruct L; tryfalse. }
    { applys xcase_lemma2.
      2: { intros E. destruct L; rew_enc in *; tryfalse. }
      { intros x1 x2 E2. destruct L as [|x L']; rew_enc in *; tryfalse.
        inverts E2.
        (* xseq *)
        applys xseq_lemma.
        (* xapp *)
        applys @xapp_lemma. { applys @Triple_set. } hsimpl.
        (* xval *)
        applys~ xval_lemma.
        (* post *)
        hsimpl~. } } }
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma_val (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. } hsimpl.
  (* done *)
  auto.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* xval *)
  applys~ (xval_lemma_val (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl. 
  (* done *)
  auto.
Qed.

Opaque Stack.

Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  (* xtriple *)
  intros. applys xtriple_lemma_fixs; try reflexivity; simpl.
  (* xlet *)
  applys xlet_typed_lemma.
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_is_empty. } hsimpl.
  (* xif *)
  applys @xifval_lemma_isTrue ;=> C.
  (* case nil *)
  { (* xval *)
    applys~ (xval_lemma tt).
    (* done *)
    hsimpl. subst. rew_list~. }
  (* case cons *)
  { (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_pop. eauto. } hsimpl ;=> x L1' E.
    (* xseq *)
    applys xseq_lemma.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_push. } hsimpl.
    (* xapp *)
    applys @xapp_lemma. { applys IH L1'. subst*. } hsimpl.
    (* done *)
    hsimpl. subst. rew_list~. }
Qed.


End Stack.



(* ********************************************************************** *)
(* * Factorial *)

Module Factorial.

Parameter facto : int -> int.
Parameter facto_zero : facto 0 = 1.
Parameter facto_one : facto 1 = 1.
Parameter facto_succ : forall n, n >= 1 -> facto n = n * facto(n-1).

(*

  let rec facto_rec n =
    if n <= 1 then 1 else n * facto_rec (n-1)

  let facto_ref_rec_up n =
    let r = ref 1 in
    let rec f x =
      if x <= n
        then r := !r * x; f (x+1) in
    f 1;
    !r

  let facto_ref_rec_down n =
    let r = ref 1 in
    let rec f n =
      if n > 1
        then r := !r * n; f (n-1) in
    f n; 
    !r

  let facto_for n =
    let r = ref 1 in
    for x = 1 to n do
      r := !r * x;
    done;
    !r

  let facto_for_down n =
    let r = ref 1 in
    for x = 0 to n-1 do 
      r := !r * (n-x);
    done;
    !r

  let facto_for_downto n =
    let r = ref 1 in
    for x = n downto 1 do 
      r := !r * x;
    done;
    !r

  let facto_for_downto2 n =
    let r = ref 1 in
    for x = n downto 2 do 
      r := !r * x;
    done;
    !r

  let facto_while_up n =
    let r = ref 1 in
    let x = ref 1 in
    while get x <= n do
      r := !r * !x;
      incr x;
    done;
    !r

  let facto_while_down n =
    let r = ref 1 in
    let x = ref n in
    while get x > 1 do
      r := !r * !x;
      decr x;
    done;
    !r
*)

End Factorial.




















