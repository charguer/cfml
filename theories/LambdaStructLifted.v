(**

This file formalizes basic examples from standard Separation Logic,
as described in Arthur Charguéraud's lecture notes.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export LambdaStruct LambdaCFLifted.
From TLC Require Import LibList.
Open Scope trm_scope.
Open Scope charac.
Generalizable Variables A.

Ltac auto_star ::= jauto.




(* ********************************************************************** *)
(* * Derived basic functions, useful for metaprogramming *)

(* ---------------------------------------------------------------------- *)
(* ** Rewriting lemmas for [Substn] *)

Lemma Substn_cons : forall x xs V Vs t,
  Substn (x::xs) (V::Vs) t = Substn xs Vs (Subst1 x V t).
Proof using.
  intros. unfold Substn, Subst1, encs. simpl.
  rewrite~ substn_cons.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Rewriting lemmas for [Subst] and [Substn] *)

Lemma Subst_seq : forall x V t1 t2,
  Subst1 x V (trm_seq t1 t2) = trm_seq (Subst1 x V t1) (Subst1 x V t2).
Proof using. auto. Qed.

Lemma Substn_val : forall xs Vs (v:val),
  length Vs = length xs ->
  Substn xs Vs v = v.
Proof using.
  introv E. list2_ind E; [|=> x xs' V Vs' L IH].
  { auto. }
  { rewrite Substn_cons. unfold Subst1, subst1. simpl. rewrite~ IH. }
Qed.

Lemma Substn_var_neq : forall xs (Vs:dyns) x,
  var_fresh x xs ->
  length Vs = length xs ->
  Substn xs Vs (trm_var x) = trm_var x.
Proof using.
  introv N E. gen N. list2_ind E; [|=> y ys' V Vs' L IH]; intros N.
  { auto. }
  { rewrite Substn_cons. unfold Subst1, subst1. simpls.
    rewrite var_eq_spec in *. case_if in N. case_if. rewrite~ IH. }
Qed.

Lemma Substn_seq : forall xs Vs t1 t2,
  length xs = length Vs ->
  Substn xs Vs (trm_seq t1 t2) = trm_seq (Substn xs Vs t1) (Substn xs Vs t2).
Proof using.
  introv E. gen t1 t2. list2_ind E; [|=> y ys' V Vs' L IH]; intros.
  { auto. }
  { do 3 rewrite Substn_cons. unfold Subst1, subst1. simpl. rewrite~ IH. }
Qed.

Lemma Substn_let : forall xs (Vs:dyns) x t1 t2,
  var_fresh x xs ->
  length Vs = length xs ->
  Substn xs Vs (trm_let x t1 t2) = trm_let x (Substn xs Vs t1) (Substn xs Vs t2).
Proof using.
  introv N E. gen t1 t2 N. list2_ind E; [|=> y ys' V Vs' L IH]; intros.
  { auto. }
  { do 3 rewrite Substn_cons. unfold Subst1, subst1. simpls.
    rewrite var_eq_spec in *. case_if in N. case_if. rewrite~ IH. }
Qed.

Lemma Substn_app : forall xs (Vs:dyns) t1 t2,
  length Vs = length xs ->
  Substn xs Vs (trm_app t1 t2) = trm_app (Substn xs Vs t1) (Substn xs Vs t2).
Proof using.
  introv E. gen t1 t2. list2_ind E; [|=> y ys' V Vs' L IH]; intros.
  { auto. }
  { repeat rewrite Substn_cons. unfold Subst1, subst1. simpl. rewrite~ IH. }
Qed.

(* LATER: complete *)


(* ********************************************************************** *)
(* * Derived basic functions *)

(* ---------------------------------------------------------------------- *)
(* ** Increment *)

Lemma Triple_incr : forall (p:loc) (n:int),
  Triple (val_incr ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+1)).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_Spec val_incr) => Provide Triple_incr.


(* ---------------------------------------------------------------------- *)
(* ** Decrement *)

(** [val_decr] defined in [ExampleBasicNonLifted.v] *)

Lemma Triple_decr : forall (p:loc) (n:int),
  Triple (val_decr ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n-1)).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_Spec val_decr) => Provide Triple_decr.


(* ---------------------------------------------------------------------- *)
(* ** Negation *)

Lemma Triple_not : forall (b:bool),
  Triple (val_not b)
    PRE \[]
    POST (fun b' => \[b' = !b]).
Proof using.
  intros. unfold Triple, Post. xapply triple_not. (*todo: xapplys bug *)
  hsimpl. hpull. intros. subst. hsimpl~ (!b).
Qed.

Hint Extern 1 (Register_Spec val_not) => Provide Triple_not.


(* ---------------------------------------------------------------------- *)
(* ** Disequality *)

Lemma Triple_neq : forall `{EA:Enc A} (v1 v2:A),
  Enc_injective EA ->
  Triple (val_neq ``v1 ``v2)
    PRE \[]
    POST (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using.
  intros. xcf.
  xapps~. (* Details: xlet. xapp~.xpull ;=> X E. subst. *)
  xapps. intros ? ->. hsimpl. rew_isTrue~.
Qed.

Hint Extern 1 (Register_Spec val_neq) => Provide Triple_neq.


(* ********************************************************************** *)
(* * Lifted records *)

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
(* ** Derived small-footprint lifted specifications for records *)

Section Triple_fields.
Transparent Hfield.

Lemma Triple_get_field : forall (l:loc) f `{EA:Enc A} (V:A),
  Triple ((val_get_field f) l)
    PRE (l `.` f ~~> V)
    POST (fun r => \[r = V] \* (l `.` f ~~> V)).
Proof using.
  intros. unfold Triple, Post. rewrite Hfield_to_hfield. xapplys~ triple_get_field.
Qed.

Lemma Triple_set_field : forall `{EA1:Enc A1} (V1:A1) (l:loc) f `{EA2:Enc A2} (V2:A2),
  Triple ((val_set_field f) l ``V2)
    PRE (l `.` f ~~> V1)
    POST (fun (r:unit) => l `.` f ~~> V2).
Proof using.
  intros. unfold Triple, Post. rewrite Hfield_to_hfield. xapply~ triple_set_field.
  hsimpl. hsimpl~ tt.
Qed.

End Triple_fields.


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
  { subst. inverts E. xapply~ Triple_set_field. intros _. xunfold Record at 2. simpl. hsimpl. }
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
  match goal with |- Triple (trm_apps (trm_val (val_get_field ?f)) ((trm_val ?v)::nil)) ?H _ =>
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
  match goal with |- Triple (trm_apps (trm_val (val_set_field ?f)) ((trm_val ?v)::(trm_val ?w)::nil)) ?H _ =>
    let r := xspec_record_get_loc v in
    let W := xspec_record_get_arg w in
    let L := xspec_record_repr_compute r H in
    xspec_record_set_compute_for f W L end.


(*--------------------------------------------------------*)
(* ** [xspec] extended to get and set functions *)

Ltac xspec_base tt ::=
  match goal with
  | |- Triple (trm_apps (trm_val (val_get_field ?f)) _) _ _ =>
     xspec_record_get_compute tt
  | |- Triple (trm_apps (trm_val (val_set_field ?f)) _) _ _ =>
     xspec_record_set_compute tt
  | |- ?G => xspec_database G
  end.


(* ---------------------------------------------------------------------- *)
(* ** Conversion between allocated segments and record representation *)

Section Alloc_to_Record.
Transparent Record repr loc.

(** Special case of arity 2 *)

Lemma Alloc2_to_Record : forall p, p <> null ->
  Alloc (abs 2) p ==>
    \exists (v1:val) (v2:val),
    (p ~> Record `{ (0%nat) := v1; (1%nat) := v2}).
Proof using.
  introv Np. change (abs 2) with 2%nat. rew_Alloc.
  hpull ;=> v1 v2. xunfold Record. unfold repr.
  rewrite Hfield_eq_fun_Hsingle. xunfold Hsingle.
  replace (p+0)%nat with p; [ | unfolds loc; math ].
  replace (p+1)%nat with (S p); [ | unfolds loc; math ].
  hsimpl~.
Qed.

(** General case *)

Lemma Alloc_to_Record : forall (p:loc) (start:nat) (n:nat),
  p <> null ->
  let xs := nat_seq start n in
      Alloc n (p+start)%nat
  ==> \exists (Vs:dyns), \[length Vs = n] \* p ~> Record (combine xs Vs).
Proof using.
  introv Np. gen start. induction n; intros; rew_Alloc.
  { subst. hsimpl (@nil dyn). rew_list~. }
  { hpull ;=> v. forwards K: (rm IHn) (S start).
    math_rewrite ((p + S start)%nat = S (p+start)) in K.
    hchange K. hpull ;=> Vs LVs. applys (himpl_hexists_r ((Dyn v)::Vs)).
    simpl List.combine. xunfold Record.
    rewrite Hfield_to_hfield.
    rewrite hfield_eq_fun_hsingle. rew_enc.
    unfold repr. hsimpl~. rew_list; math. }
Qed.

End Alloc_to_Record.


(* ---------------------------------------------------------------------- *)
(* ** Specification for allocation of records of arity 2,
      See below for the generalization to arbitrary arities. *)

Definition val_new_record_2 :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2 in
    val_set_field 0%nat 'p 'x;;;
    val_set_field 1%nat 'p 'y;;;
    'p.

Lemma Triple_new_record_2 : forall `{EA1:Enc A1} `{EA2:Enc A2} (v1:A1) (v2:A2),
  Triple (val_new_record_2 ``v1 ``v2)
    PRE \[]
    POST (fun p => p ~> Record`{ 0%nat := v1 ; 1%nat := v2 }).
Proof using.
  xcf. xapp Triple_alloc as p. { math. } (* TODO: try Triple_alloc_nat *)
  intros Np. xchanges~ Alloc2_to_Record ;=> w1 w2.
  xapp. xapp. xval~. hsimpl.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Specification for allocation of records of arbitrary arity *)

Definition val_new_record (n:nat) :=
  let fs := nat_seq 0%nat n in
  let xs := var_seq 0%nat n in
  let P : var := nat_to_var n in
  val_funs xs (
    Let P := val_alloc n in
    LibList.fold_right (fun f t => val_set_field (f:field) P (nat_to_var f);;; t) (trm_var P) fs).

Lemma Subst_new_record_aux : forall (n':nat) fs xs Vs (i n:nat) (p:loc),
  n' = length Vs ->
  fs = nat_seq i n' ->
  xs = var_seq i n' ->
  (i + n' = n)%nat ->
  let N := nat_to_var n in
    (Subst1 N (Dyn p) (Substn xs Vs (fold_right (fun f t => trm_seq (val_set_field (f:field) (trm_var N) (nat_to_var f)) t) (trm_var N) fs)))
  =  fold_right (fun fV t => let '(f,V) := fV in trm_seq (val_set_field (f:field) p (enc V)) t) p (LibList.combine fs Vs).
Proof using.
  intros n'. induction n' as [|n'']; introv LVs Efs Exs Ein; intros N.
  { destruct xs; [|rew_list in *; false; math].
    destruct fs; [|rew_list in *; false; math].
    destruct Vs; [|rew_list in *; false; math].
    rew_listx. unfold Subst1, subst1. simpl. rewrite var_eq_spec. case_if~. }
  { hide IHn''. destruct xs as [|x xs']; [rew_list in *; false; math|].
    destruct fs as [|f fs']; [rew_list in *; false; math|].
    destruct Vs as [|V Vs']; [rew_list in *; false; math|].
    invert Efs. intros Ef Efs'. subst i. invert Exs. intros Ex Exs'.
    rew_list in *.
    asserts EL: (length xs' = length Vs').
    { subst. rewrite length_var_seq. math. }
    asserts Nxn: (x <> N).
    { intros E. subst x. lets: injective_nat_to_var E. math. }
    rewrite <- Ex. rewrite <-Exs'. rew_listx.
    rewrite Substn_cons. rewrite Subst_seq. rewrite <- Ex.
    asserts_rewrite (Subst1 x V (val_set_field f N (trm_var x))
                     = val_set_field f N (enc V)).
    { unfold Subst1, subst1. simpl. repeat rewrite var_eq_spec. case_if. case_if~. }
    rewrite~ Substn_seq.
    asserts_rewrite (Substn xs' Vs' (val_set_field f N ``V)
                    = (val_set_field f N ``V)).
    { do 2 rewrite~ Substn_app. do 2 rewrite~ Substn_val. rewrite~ Substn_var_neq.
      { rewrite Exs'. applys var_fresh_var_seq_ge. math. } }
    rewrite~ Subst_seq.
    asserts_rewrite (Subst1 N (Dyn p) (val_set_field f N ``V) = val_set_field f p ``V).
    { unfold Subst1, subst1; simpl. rewrite var_eq_spec. case_if~. } (* todo: lemma Subst_var *)
    fequals.
    match goal with |- context [Subst1 x V ?t'] => set (t:=t') end.
    asserts_rewrite (Subst1 x V t = t).
    { subst x. cuts K: (forall n' i,
       (f < i)%nat ->
        let t := @fold_right nat trm (fun f' t =>
           trm_seq (val_set_field f' N (nat_to_var f')) t) N (nat_seq i n') in
       Subst1 (nat_to_var f) V t = t).
     { applys K. math. }
     intros n'. gen Nxn. clears_all. induction n'; introv L; intros; subst t.
     { simpl. unfold Subst1, subst1. simpl. rewrite var_eq_spec. case_if~. } (*todo: Subst_var_neq.*)
     { simpl. rewrite Subst_seq. fequals.
       { unfold Subst1, subst1. simpl. repeat rewrite var_eq_spec. case_if as C. case_if as C'.
         { lets: injective_nat_to_var C'. false; math. } { auto. } }
       { rewrite~ IHn'. } } }
    applys~ IHn'' Exs'; try math. }
Qed.

Lemma Triple_new_record : forall (n:nat) (Vs:dyns),
  (n > 0)%nat ->
  n = length Vs ->
  let fs := nat_seq 0%nat n in
  Triple (trm_apps (val_new_record n) (encs Vs))
    PRE \[]
    POST (fun p => p ~> Record (combine fs Vs)).
Proof using.
  introv HP LVs. intros fs. applys Triple_apps_funs.
  { reflexivity. }
  { subst. applys~ var_funs_var_seq. }
  { set (xs := var_seq 0 n).
    asserts EL: (length Vs = length xs). { unfold xs. rewrite~ length_var_seq. }
    rewrite Substn_let; [| applys var_fresh_var_seq_ge; math | auto ].
    asserts_rewrite (Substn xs Vs (val_alloc n) = val_alloc n).
    { rewrite~ Substn_app. (* rewrite~ Substn_val. do 2 rewrite~ Substn_val. *) }
    eapply (@Triple_let _ _ _ _ _ _ _ loc). (* todo: cleanup *)
    { xapplys Triple_alloc_nat. }
    { intros p. xpull ;=> Np. xchange~ (@Alloc_to_Record p 0%nat).
      { math_rewrite ((p+0)%nat = p). hsimpl. } (* todo simplify *)
        xpull ;=> Ws LWs. fold xs. fold fs.
        rewrite (@Subst_new_record_aux n fs xs Vs 0%nat n); try first [ math | auto ].
        asserts Lxs: (length xs = n). { subst xs. rewrite~ length_var_seq. }
        (*clearbody xs.*) clear HP.
        applys local_weaken_post (fun p' => \[p' = p] \* p ~> Record (combine fs Vs));
        [ xlocal | | hsimpl; intros; subst~]. (* todo: weaken_post with swapped order *)
        gen n Vs Ws. set (start := O). intros n. gen start.
        induction n as [|n']; intros.
        { destruct xs; [|rew_list in *; false; math]. (* todo: lemma/tactic for this *)
          destruct Vs; [|rew_list in *; false; math].
          destruct Ws; [|rew_list in *; false; math].
          rew_list in *. subst. simpls.
          applys~ Triple_val p. hsimpl~. }
        { destruct xs as [|xs']; [rew_list in *; false; math|].
          destruct Vs as [|V Vs']; [rew_list in *; false; math|].
          destruct Ws as [|W Ws'] ; [rew_list in *; false; math|].
          rew_list in *. simpl in fs. subst fs.
          do 2 rewrite combine_cons. rew_listx.
            rewrite Record_cons. applys Triple_seq.
            { xapplys @Triple_set_field. }
            { simpl. lets M: (>> IHn' (S start) Vs' Ws' __);
              try rewrite length_var_seq; try math.
              xapply M. { hsimpl. }
              { intros p'. rewrite Record_cons. hsimpl~. } } } } }
Qed.

Lemma Triple_new_record' : forall (n:nat) (Vs:dyns) (vs:vals) (Q:loc->hprop),
  vs = (encs Vs) ->
  (n = List.length Vs)%nat ->
  (n > 0)%nat ->
  let fs := nat_seq 0%nat n in
  ((fun p => p ~> Record (List.combine fs Vs)) ===> Q) ->
  Triple (trm_apps (val_new_record n) (vals_to_trms vs)) \[] Q.
Proof using.
  introv E HL HP HQ. rewrite List_length_eq in HL.
  rewrite List_combine_eq in HQ; [| rewrite~ length_nat_seq].
  subst. xapply~ Triple_new_record. hsimpl. hchanges~ HQ.
Qed.

(** Tactic [xtriple_new_record] for proving the specification
    triple for the allocation of a specific record.
    For an example, check out in [ExampleTree.v],
    Definition [val_new_node] and Lemma [Triple_new_node]. *)

Ltac xtriple_new_record_core tt :=
  intros; rew_nary; rew_trms_vals; applys Triple_new_record';
  [ xeq_encs | auto | math | hsimpl ].

Tactic Notation "xtriple_new_record" :=
  xtriple_new_record_core tt.


(* ********************************************************************** *)
(* * Lifted access rules for arrays *)


(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint Array A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (Array L' (S p))
  end.

Section ArrayProp.
Context A `{EA:Enc A}.
Implicit Types L : list A.
Implicit Types x : A.

Lemma Array_eq_ArrayNonlifted : forall L p,
  Array L p = LambdaStruct.Array (LibList.map enc L) p.
Proof using.
  intros L. induction L; intros.
  { auto. }
  { simpl. rewrite IHL. rew_listx. rewrite Array_cons_eq. auto. }
Qed.

Lemma Array_unlift : forall L p,
  p ~> Array L = LambdaStruct.Array (LibList.map enc L) p.
Proof using. apply Array_eq_ArrayNonlifted. Qed.

Lemma Array_nil_eq : forall p,
  p ~> Array (@nil A)  = \[].
Proof using. auto. Qed.

Lemma Array_cons_eq : forall p x L,
  p ~> Array (x::L) = (p ~~> x) \* (S p) ~> Array L.
Proof using. auto. Qed.

Lemma Array_one_eq : forall p x,
  p ~> Array (x::nil) = (p ~~> x).
Proof using. intros. rewrite Array_cons_eq, Array_nil_eq. rew_heap~. Qed.

Lemma Array_concat_eq : forall p L1 L2,
   p ~> Array (L1++L2) = p ~> Array L1 \* (p + length L1)%nat ~> Array L2.
Proof using.
  intros. repeat rewrite Array_unlift. rew_listx. rewrite Array_concat_eq.
   rewrite length_map. auto. (* TODO: add to rew_listx. *)
Qed.

Lemma Array_last_eq : forall p x L,
  p ~> Array (L&x) = p ~> Array L \* ((p + length L)%nat ~~> x).
Proof using. intros. rewrite Array_concat_eq. rewrite~ Array_one_eq. Qed.

Transparent loc. (* TODO: avoid the need for this by
   using pointer arithmetic operator for p+n *)

Lemma Array_middle_eq : forall n p L,
  0 <= n < length L ->
  (p ~> Array L) = \exists L1 x L2, \[L = L1++x::L2] \* \[length L1 = n :> int] \*
    p ~> Array L1 \* (abs(p+n) ~~> x) \* (p + length L1 + 1)%nat ~> Array L2.
Proof using.
  intros. repeat rewrite Array_unlift.
  rewrites (>> Array_middle_eq n p (map enc L)).
  rewrite length_map. auto. (* TODO: add to rew_listx. *)
  apply himpl_antisym.
  { hpull ;=> L1 x L2 N1 N2.
    lets (L1'&X'&L2'&E1&E2&E3&E4): map_eq_middle_inv N1. subst.
    rewrite length_map. hsimpl~ L1' X' L2'.
    do 2 rewrite Array_unlift. hsimpl. }
  { hpull ;=> L1 x L2 N1 N2. hsimpl (map enc L1) (enc x) (map enc L2).
    repeat rewrite Array_unlift. rewrite length_map. (* todo rew_list *) hsimpl.
    rewrite~ length_map. subst L. rew_listx~. }
Qed.

End ArrayProp.

Global Opaque Array.

Lemma Triple_alloc_array : forall n,
  n >= 0 ->
  Triple (val_alloc ``n)
    PRE \[]
    POST (fun p => \exists (L:list val), \[length L = n :> int] \* p ~> Array L).
Proof using.
  intros. unfold Triple. xapplys~ triple_alloc_array.
  intros r x L. intros E N. subst. unfold Post. hsimpl~ L.
  rewrite Array_unlift. rewrite map_id_ext. hsimpl.
  { intros v. rewrite~ enc_val_eq. }
Qed.

Import LibListZ.
Implicit Types i ofs len : int.

Section ArrayRules.
Context A `{EA:Enc A} `{IA:Inhab A}.
Implicit Types L : list A.

Hint Resolve index_map.

Lemma Triple_array_get : forall p i L,
  index L i ->
  Triple (val_array_get ``p ``i)
    PRE (p ~> Array L)
    POST (fun (r:A) => \[r = L[i]] \* p ~> Array L).
Proof using.
  intros. unfold Triple. rewrite Array_unlift.
  xapplys~ triple_array_get. intros r E.
 lets M: (@read_map A _ val) L. rewrites~ (rm M) in E. (* todo: polish *)
  unfold Post. subst. hsimpl*.
Qed.

Hint Extern 1 (Register_Spec val_array_get) => Provide Triple_array_get.

Lemma Triple_array_set : forall p i v L,
  index L i ->
  Triple (val_array_set ``p ``i ``v)
    PRE (p ~> Array L)
    POST (fun (_:unit) => p ~> Array (L[i:=v])).
Proof using.
  intros. unfold Triple. rewrite Array_unlift.
  xapplys~ triple_array_set. intros r E.
  rewrite~ <- map_update.
  unfold Post. subst. rewrite Array_unlift. hsimpl~ tt.
Qed.

Hint Extern 1 (Register_Spec val_array_set) => Provide Triple_array_set.

Lemma Triple_array_make : forall n v,
  n >= 0 ->
  Triple (val_array_make ``n ``v)
    PRE \[]
    POST (fun p => \exists L, \[L = make n v] \* p ~> Array L).
Proof using.
  intros. unfold Triple. xapplys~ triple_array_make.
  intros r p L E N. unfold Post. hsimpl~ p (make n v).
  rewrite Array_unlift. subst L. rewrite map_make; [|math]. hsimpl.
Qed.

Hint Extern 1 (Register_Spec val_array_make) => Provide Triple_array_make.

End ArrayRules.
