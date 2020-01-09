(** Reformulation of the definition of [subst2] *)

Lemma subst2_eq_subst1_subst1 : forall x1 x2 v1 v2 t,
  subst2 x1 v1 x2 v2 t = subst1 x2 v2 (subst1 x1 v1 t).
Proof using. auto. Qed.

(** Reformulation of the definition of [isubst2] *)

Lemma isubst2_eq_isubst1_isubst1 : forall x1 x2 v1 v2 t,
  isubst2 x1 v1 x2 v2 t = isubst1 x2 v2 (isubst1 x1 v1 t).
Proof using.
  intros. unfold isubst2. rewrite~ isubst_add.
  rewrites (>> isubst1_eq_subst1 x1). auto.
Qed.

(** [isubst2] matches [subst2] *)

Lemma isubst2_eq_subst2 : forall z1 v1 z2 v2 t,
  isubst2 z1 v1 z2 v2 t = subst2 z1 v1 z2 v2 t.
Proof using.
  intros. rewrite isubst2_eq_isubst1_isubst1, subst2_eq_subst1_subst1.
  do 2 rewrite isubst1_eq_subst1. auto.
Qed.
(** [subst2] is a shorthand that iterates two calls to [subst1]. *)

Definition subst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   subst1 z2 v2 (subst1 z1 v1 t).

Lemma trm_size_isubst1 : forall t z v,
  trm_size (isubst1 z v t) = trm_size t.
Proof using. intros. applys trm_size_isubst. Qed.


(** [isubst2 z1 v1 z2 v2 t] is similar. *)

Definition isubst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   isubst (Ctx.add z1 v1 (Ctx.one z2 v2)) t.


(** [isubst1 z v t] replaces occurences of binder [z] with [v] in [t]. *)

Definition isubst1 (z:bind) (v:val) (t:trm) :=
  isubst (Ctx.one z v) t.

(** [isubst1] matches [subst1] *)

Lemma isubst1_eq_subst1 : forall z v t,
  isubst1 z v t = subst1 z v t.
Proof using.
  intros. unfold isubst1, Ctx.one.
  rewrite isubst_add, isubst_empty. auto.
Qed.

(** [isubst1 z v t] returns [t] unchanged when [z] is anonymous. *)

Lemma isubst1_anon : forall v t,
  isubst1 bind_anon v t = t.
Proof using.
  intros. unfold isubst1, Ctx.one, Ctx.add. rewrite~ isubst_empty.
Qed.

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_isubst1; math.

=================================





(** [mkstruct] can be erased, with transitivity *)
(* TODO DEPRECATED *)

Lemma mkstruct_erase' : forall H F Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using.
  introv M. xchanges M. applys mkstruct_erase.
Qed.




(* ---------------------------------------------------------------------- *)
(* ** List of dynamic values *)


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



(* Note: currently not used *)
Lemma RetypePost_instantiate : forall H A `{EA:Enc A} (V:A) (Q:A->hprop),
  H ==> Q V ->
  RetypePost (fun x => \[x = V] \* H) Q.
Proof using. introv M. applys RetypePost_qimpl. xpull ;=> ? ->. auto. Qed.



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



(* ---------------------------------------------------------------------- *)
(* ** Decoder function *)

Fixpoint decode (v:val) : dyn :=
  match v with
  | val_uninitialized => Dyn val_uninitialized
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



Lemma Triple_eq_l : forall A `{EA:Enc A} (v1:A),
  Enc_injective_value v1 ->
  forall (v2 : A),
  Triple (val_eq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { applys Triple_eq_val. }
  unfolds. xpull ;=> ? ->. xsimpl*. rew_bool_eq. iff. { applys* I. } { subst*. }
Qed.

Lemma Triple_eq_r : forall A `{EA:Enc A} (v2:A),
  Enc_injective_value v2 ->
  forall (v1 : A),
  Triple (val_eq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { applys Triple_eq_val. }
  unfolds. xpull ;=> ? ->. xsimpl*. rew_bool_eq. iff. { symmetry. applys* I. } { subst*. }
Qed.


Lemma Triple_neq_l : forall A `{EA:Enc A} (v1:A),
  Enc_injective_value v1 ->
  forall (v2 : A),
  Triple (val_neq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { applys Triple_neq_val. }
  unfolds. xpull ;=> ? ->. xsimpl*. rew_bool_eq. iff R.
  { intros N. applys R. subst*. } { intros N. applys R. applys* I. }
Qed.

Lemma Triple_neq_r : forall A `{EA:Enc A} (v2:A),
  Enc_injective_value v2 ->
  forall (v1 : A),
  Triple (val_neq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using.
  introv I. intros.
  applys (@Triple_enc_change bool). { applys Triple_neq_val. }
  unfolds. xpull ;=> ? ->. xsimpl*. rew_bool_eq. iff R.
  { intros N. applys R. subst*. } { intros N. applys R. symmetry. applys* I. }
Qed.


=============
(* DEPRECATED
Definition Wpgen_val_typed `{EA1:Enc A1} (V:A1) : Formula :=
  MkStruct (fun A (EA:Enc A) Q => Q V1).
*)



(** [Wpgen_cast X Q] applies a postcondition [Q] of type [A2->hprop] to a value
    [X] of type [A1], with [X] converted on-the-fly to a value of type [A2]. *)
(* --TODO: is Wpgen_cast not similar to (Wpgen_val `X) *)

Definition Wpgen_cast `{Enc A1} (X:A1) A2 (EA2:Enc A2) (Q:A2->hprop) : hprop :=
  \exists (Y:A2), \[enc X = enc Y] \* Q Y.




(** [RetypePost Q1 Q2] asserts that [Q1] of type [A1->hprop] entails
    [Q2] of type [A2->hprop]. This predicate is used in the lemmas
    that enable changing the type of the postcondition in a triple. *)

Definition RetypePost A1 `{Enc A1} (Q1:A1->hprop) `{Enc A2} (Q2:A2->hprop) :=
  forall (X:A1), Q1 X ==> \exists (Y:A2), \[enc X = enc Y] \* Q2 Y.

(* Note: [RetypePost_refl] is currently not used.
   It is a special case of [RetypePost_qimpl]. *)

Lemma RetypePost_refl : forall A `{EA:Enc A} (Q:A->hprop),
  RetypePost Q Q.
Proof using. intros. unfolds. intros X. xsimpl*. Qed.

(* Note: [RetypePost_qimpl] is currently not used. *)

Lemma RetypePost_qimpl : forall A `{EA:Enc A} (Q1 Q2:A->hprop),
  Q1 ===> Q2 ->
  RetypePost Q1 Q2.
Proof using. introv M. unfolds. intros X. xchanges* M. Qed.

Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  RetypePost Q1 Q2 ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ triple_conseq (rm M).
  unfold LiftPost. intros v. xpull ;=> V EV. subst. applys N.
Qed.



(* DEPRECATED
Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 ''=>' F2" :=
  (Case v = vp1%val Then F1 Else
   Wptag (Case v = vp2%val Then F2 Else
   Wptag (Fail))) (at level 69, v, vp1, vp2 at level 69,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 [ x21 ] ''=>' F2" :=
  (Case v = vp1%val Then F1 Else
   Wptag (Case v = vp2%val [ x21 ] Then F2 Else
   Wptag (Fail))) (at level 69, v, vp1, vp2 at level 69, x21 ident,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  [ x21 ]  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' ''|' vp1 ''=>' F1 ''|' vp2 [ x21 x22 ] ''=>' F2" :=
  (Case v = vp1%val Then F1 Else
   Wptag (Case v = vp2%val [ x21 x22 ] Then F2 Else
   Wptag (Fail))) (at level 69, v, vp1, vp2 at level 0, x21 ident, x22 ident,
   format "'[v' 'Match_'  v  'With'  '[' '/' ''|'  vp1  ''=>'  '/' F1 ']'  '[' '/' ''|'  vp2  [ x21  x22 ]  ''=>'  '/' F2 ']' ']'")
  : wp_scope.

Notation "'Match_' v 'With' Fof 'End'" :=
  ((Wpgen_match_val v Fof))
  (at level 69,
   format "'[v' 'Match_'  v  'With'  '/' '[' Fof ']' '/'  'End' ']'")
   : wp_scope.


*)


(* NEEDED?
Notation "'Apptrm' t " :=
  ((Wpgen_app t))
  (at level 68, t at level 0) : wp_scope.
*)



(*
Notation "'Letval' x ':=' v 'in' F2" :=
  ((Wpgen_letval_typed v (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Letval'  x  ':='  v  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.
*)

(*
Notation "'App' f t1 " :=
  (Wpgen_app (trm_apps f (t1::nil)))
  (at level 68, f, t1 at level 0) : wp_scope.

Notation "'App' f t1 t2 " :=
  (Wpgen_app (trm_apps f (t1::t2::nil)))
  (at level 68, f, t1, t2 at level 0) : wp_scope.

Notation "'App' f t1 t2 t3 " :=
  (Wpgen_app (trm_apps f (t1::t2::t3::nil)))
  (at level 68, f, t1, t2, t3 at level 0) : wp_scope.
*)

-----------------------------------

(*
Lemma Wpgen_sound_letval_typed : forall v E C `{EA:Enc A} (F2of:A->Formula),
  (forall V, F2of V ====> Wpsubst E (C ``V)) ->
  Wpgen_letval_typed v F2of ====> Wp (isubst E (C v)).
Proof using.
  introv M. intros A1 EA1. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. xtpull ;=> V ->. applys Triple_of_Wp. applys M.
Qed.
*)


(*
Definition Wpgen_letval_typed (v:val) `{EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (V:A1), \[v = enc V] \* ^(F2of V) Q).
*)

(*
Definition Wpaux_getval_typed Wpgen (E:ctx) (t1:trm) `{EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  match t1 with
  | trm_val v => `Wpgen_letval_typed v F2of
  | trm_var x => match Ctx.lookup x E with
                 | Some v => `Wpgen_letval_typed v F2of
                 | None => `Wpgen_fail
                 end
  | _ => `Wpgen_let_typed (Wpgen E t1) F2of
  end.
*)

-----------------------------------




   \exists H, H \* \[forall vf,
                     (forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q') ->
                      H ==> Q vf].


  Goal:   H0 ==> wpgen (trm_fun x t)
  unfolds to:
      H0 ==> \exists H, H \* \[forall vf,
                     (forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q') ->
                      H ==> Q vf].
  simplifies to:

      forall vf,
      (forall vx H' Q',
          H' ==> Fof vx Q' ->
          triple (trm_app vf vx) H' Q') ->
      H0 ==> Q vf

  xfun_lemma:
      S vf => specification for the functoin

      (forall vf, (forall H' Q', H' ==> Fof vx Q' -> triple (trm_app vf vx) H' Q') -> S vf) ->
      (fun r => H0 \* \[S r]) ===> Q ->
      H0 ==> wpgen (trm_fun x t) Q
-------------------


Definition hsingle' (v:val) (p:loc) := hsingle p v.

Lemma hsingle_as_repr : forall (p:loc) (v:val),
  hsingle p v = (p ~> hsingle' v).
Proof using. auto. Qed.

Hint Rewrite hsingle_as_repr : hsingle_as_repr.
Hint Rewrite <- hsingle_as_repr : hsingle_as_repr_back.

(*
Ltac xsimpl_core tt ::=
  autorewrite with hsingle_as_repr;
  xsimpl_start tt;
  repeat (xsimpl_step tt);
  xsimpl_post tt;
  autorewrite with hsingle_as_repr_back.
*)






è-----------------------