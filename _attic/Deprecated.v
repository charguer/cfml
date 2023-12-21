
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
Definition Wpgen_unlifted_val_typed `{EA1:Enc A1} (V:A1) : Formula :=
  MkStruct (fun A (EA:Enc A) Q => Q V1).
*)



(** [Wpgen_cast X Q] applies a postcondition [Q] of type [A2->hprop] to a value
    [X] of type [A1], with [X] converted on-the-fly to a value of type [A2]. *)
(* --TODO: is Wpgen_cast not similar to (Wpgen_unlifted_val `X) *)

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


(** The soundness lemma for this construct is as follows. *)

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) ->
  formula_sound (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l_intro.
  { introv N. rewrite <- wp_equiv. applys himpl_trans_r.
    { applys* wp_app_fun. } { xchanges N. applys* M. } }
  { applys wp_fun. }
Qed.

[[
    forall vx H' Q', (H' ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'
]]

*)



(** Remark: the following variant of [wpgen_fun] enables deriving instances
    of [wp (trm_app vf vx)] rather than instances of [triple (trm_app vf vx)]. *)

Definition wpgen_fun' (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** This variant is completely equivalent to the previous version, and has the
    benefits that it is slightly more concise. It requires however a bit more
    effort for the use to exploit it. That said, when the manipulations of the
    formulae produced by [wpgen] are performed by x-tactic, then it does not
    make a difference to the end-user which variant of the definition is used. *)




Tactic Notation "xfun" constr(S) :=
  let varf := match S with fun varf => _ => varf end in
  let f := fresh varf in
  let Hf := fresh "H" f in
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_lemma S; intros f Hf.


===========


Lemma xfun_spec_lemma
introv M1 M2. applys* xfun_nospec_lemma.
intros vf N. applys M2. applys M1. applys N. Qed.


Lemma xfun_nospec_lemma : forall H Q Fof,
  (forall vf,
     (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
     (H ==> Q vf)) ->
  H ==> wpgen_fun Fof Q.
Proof using.
  introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
  introv K. rewrite <- wp_equiv. xchange K. applys N.
Qed.

Tactic Notation "xfun" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.

========



Tactic Notation "xapp" constr(E) :=
  xapp_pre; applys xapp_lemma E; xsimpl; unfold protect.

Tactic Notation "xapps" constr(E) :=
  xapp_pre; first
  [ applys xapps_lemma0 E
  | applys xapps_lemma1 E ];
  xsimpl; unfold protect.

Lemma xapps_lemma0 : forall t v H1 H Q,
  triple t H1 (fun r => \[r = v]) ->
  H ==> H1 \* (protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. xchanges W. intros ? ->. auto. Qed.

Lemma xapps_lemma1 : forall t v H1 H2 H Q,
  triple t H1 (fun r => \[r = v] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. xchanges W. intros ? ->. auto. Qed.

=============


(* ################################################ *)
(** *** Definition and verification of [incr]. *)

(** Here is an implementation of the increment function,
    written in A-normal form.
[[
   let incr p =
       let n = !p in
       let m = n + 1 in
       p := m
]]
*)

Definition incr : val :=
  VFun 'p :=
    (Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
    'p ':= 'm).

(** Here is the Separation Logic triple specifying increment.
    And the proof follows. Note that the script contains explicit
    references to the specification lemmas of the functions being
    called (e.g. [triple_get] for the [get] operation). The actual
    CFML2 setup is able to automatically infer those names. *)

Lemma triple_incr : forall (p:loc) (n:int),
  TRIPLE (trm_app incr p)
    PRE (p ~~~> n)
    POST (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xwp.
  xapps triple_get.
  xapps triple_add.
  xapps triple_set.
  xsimpl~.
Qed.

(** We register this specification so that it may be automatically
    invoked in further examples. *)

Hint Resolve triple_incr : triple.


(* ################################################ *)
(** *** Definition and verification of [mysucc]. *)

(** Here is another example, the function:
[[
   let mysucc n =
      let r = ref n in
      incr r;
      let x = !r in
      free r;
      x
]]

  Note that this function has the same behavior as [succ],
  but its implementation makes use of the [incr] function
  from above. *)

Definition mysucc : val :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    Let 'x := '! 'r in
    val_free 'r ';
    'x.

Lemma triple_mysucc : forall n,
  TRIPLE (trm_app mysucc n)
    PRE \[]
    POST (fun v => \[v = n+1]).
Proof using.
  xwp.
  xapp triple_ref. intros ? r ->.
  xapps triple_incr.
  xapps triple_get.
  xapps triple_free.
  xval. xsimpl~.
Qed.


(* ################################################ *)
(** *** Definition and verification of [myfun]. *)

(** Here is an example of a function involving a local function definition.

[[
   let myfun p =
      let f = (fun () => incr p) in
      f();
      f()
]]

*)

Definition myfun : val :=
  VFun 'p :=
    Let 'f := (Fun 'u := incr 'p) in
    'f '() ';
    'f '().

Lemma triple_myfun : forall (p:loc) (n:int),
  TRIPLE (trm_app myfun p)
    PRE (p ~~~> n)
    POST (fun _ => p ~~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    TRIPLE (f '())
      PRE (p ~~~> m)
      POST (fun _ => p ~~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp triple_incr. xsimpl. }
  xapp Hf. intros _.
  xapp Hf. intros _.
  math_rewrite (n+1+1=n+2). xsimpl.
Qed.

End Demo.

==============


  Definition qwand (Q1 Q2:val->hprop) : hprop :=
    fun h => forall v h', Fmap.disjoint h h' -> Q1 v h' -> Q2 v (h \u h').

  Definition qwand A (Q1 Q2:A->hprop) : hprop :=
    \forall v, (Q1 v) \-* (Q2 v).

    ============



(** For a further comparison between the consequence-frame rule
    and the ramified frame rule, consider the following example.

    Assume we want to frame the specification [triple_ref] with [l' ~~~> v'],
    that is, add this predicate to both the precondition and the postcondition.
    First, let's do it with the consequence-frame rule. *)

Lemma triple_ref_with_consequence_frame : forall (l':loc) (v':val) (v:val),
  triple (val_ref v)
    (l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \* l' ~~~> v').
Proof using.
  intros. applys triple_conseq_frame.
  (* observe the evar [?H2] in second and third goals *)
  { applys triple_ref. }
  { xsimpl. (* instantiates the evar [H2] *) }
  { xsimpl. auto. }
Qed.

(** Now, let's carry out the same proof using the ramified frame rule. *)

Lemma triple_ref_with_ramified_frame : forall (l':loc) (v':val) (v:val),
  triple (val_ref v)
    (l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \* l' ~~~> v').
Proof using.
  intros. applys triple_ramified_frame.
  { applys triple_ref. }
  { rewrite hstar_hempty_l. rewrite qwand_equiv.
    (* Remark: the first two steps above will be automatically
       carried out by [xsimpl], in subsequent chapters. *)
    (* Here, we read the same state as in the previous proof. *)
    xsimpl. auto. }
Qed.

(** Again, observe how we have been able to complete the same proof
    without involving any evar. *)

===========


    The tactic [xsimpl] provides dedicated support for
    simplifying expressions involving magic wand. So,
    in most proofs, it is not required to manually manipulate
    the lemmas capturing properties of the magic wand.
    Nevertheless, there are a few situations where [xsimpl]
    won't automatically perform the desired manipulation.
    In such cases, the tactic [xchange] proves very useful.=
 ======




(* EX3! (Triple_mappend_aux') *)
(** The specification of [mappend_aux] can be equivalently stated
    using the premise [L1 <> nil] instead of [p1 <> null].
    Complete the proof below to reflect this change. *)

Lemma Triple_mappend_aux' : forall (p1 p2:loc) (L1 L2:list int),
  L1 <> nil ->
  TRIPLE (mappend_aux p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using. (* ADMITTED *)
  introv N. gen N p1. induction_wf IH: list_sub L1.
  xwp. destruct L1 as [|x L1']; tryfalse.
  rewrite MList_cons. xpull. intros q.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xchange (MList_null_iff_nil q). intros HQ.
    xapp. xapp. { auto. }
    rew_list. xchange <- MList_cons. }
Qed. (* /ADMITTED *)




===========


(** Remark: in the proof above, the right-to-left direction was
    somewhat "too easy" to prove, because [xsimpl] is doing all
    the work for us. Here is a detailed proof not using [xsimpl]. *)
...
Lemma hwand_satisfies_hwand_characterization :
  hwand_characterization hwand.
Proof using.
  intros H0 H1 H2. unfold hwand. iff M.
  { applys himpl_trans. applys himpl_frame_l M.
    rewrite hstar_hexists. applys himpl_hexists_l. intros H3.
    rewrite (hstar_comm H3). rewrite hstar_assoc.
    applys himpl_hstar_hpure_l. intros N. applys N. }
  { applys himpl_hexists_r H0. rewrite hstar_comm.
    applys himpl_hstar_hpure_r. applys M. applys himpl_refl. }
Qed.

===================




(** The introduction and elimination lemmas for [qwand] correspond
    to the right-to-left and left-to-right directions of the equivalence
    rule [qwand_equiv]. *)

(*
TODO : without them ? ..
*)

Lemma himpl_qwand_r : forall H Q1 Q2,
  (Q1 \*+ H) ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite* qwand_equiv. Qed.

Lemma himpl_qwand_r_inv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. introv M. rewrite* <- qwand_equiv. Qed.




==========

(** Finally, let us restate the ramified frame rule for [wp] and
    [wp_ramified] and its corollary [wp_ramified_trans] using the
    new definition of [qwand]. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame. applys qwand_cancel. Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.


6----------------------


(* ******************************************************* *)
(** ** Texan triples *)

Module TexanTriples.
Import NewQwand.

Implicit Types v : val.

(* ------------------------------------------------------- *)
(** *** 1. Example of Texan triples *)

(** In this section, we show that specification triples can be presented
    in a different style using weakest preconditions. *)

(** Consider for example the specification triple for allocation. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v).

(** This specification can be equivalently reformulated in the following
    form. *)

Parameter wp_ref : forall Q v,
  \[] \* (\forall l, l ~~~> v \-* Q (val_loc l)) ==> wp (val_ref v) Q.

(** Above, we purposely left the empty heap predicate to the front to
    indicate where the precondition, if it were not empty, would go in
    the reformulation. *)

(** In what follows, we describe the chain of transformation that can take us
    from the triple form to the wp form, and establish the reciprocal.
    We then formalize the general pattern for translating a triple
    into a "texan triple" (i.e., the wp-based specification). *)

(** By replacing [triple t H Q] with [H ==> wp t Q], the specification
    [triple_ref] can be reformulated as follows. *)

Lemma wp_ref_0 : forall v,
  \[] ==> wp (val_ref v) (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using. intros. rewrite wp_equiv. applys triple_ref. Qed.

(** We wish to cast the RHS in the form [wp (val_ref v) Q] for an abstract
    variable [Q]. To that end, we reformulate the above statement by including
    a magic wand relating the current postcondition, which is
    [(fun r => \exists l, \[r = val_loc l] \* l ~~~> v)], and [Q]. *)

Lemma wp_ref_1 : forall Q v,
  ((fun r => \exists l, \[r = val_loc l] \* l ~~~> v) \--* Q) ==> wp (val_ref v) Q.
Proof using. intros. xchange (wp_ref_0 v). applys wp_ramified. Qed.

(** This statement can be made slightly more readable by unfolding the
    definition of [\--*], as shown next. *)

Lemma wp_ref_2 : forall Q v,
  (\forall r, (\exists l, \[r = val_loc l] \* l ~~~> v) \-* Q r) ==> wp (val_ref v) Q.
Proof using. intros. applys himpl_trans wp_ref_1. xsimpl. Qed.

(** Interestingly, the variable [r], which is equal to [val_loc l],
    can now be substituted away, further increasing readability.
    We obtain the specificaiton of [val_ref] in "Texan triple style". *)

Lemma wp_ref_3 : forall Q v,
  (\forall l, (l ~~~> v) \-* Q (val_loc l)) ==> wp (val_ref v) Q.
Proof using.
  intros. applys himpl_trans wp_ref_2.
  applys himpl_hforall_r. intros v'.
  rewrite hwand_equiv. xsimpl. intros l ->.
  xchange (hforall_specialize l).
  xchange (hwand_cancel (l ~~~> v)).
Qed.


(* ------------------------------------------------------- *)
(** *** 2. The general pattern *)

(** In practice, specification triples can (pretty much) all be casted
    in the form: [triple t H (fun r => exists x1 x2, \[r = v] \* H'].

    Above, the value [v] may depend on the [xi].
    The heap predicate [H'] may depend on [r] and the [xi].
    The number of existentials [xi] may vary, possibly be zero.
    The equality \[r = v] may be removed if no pure fact is needed about [r].

    A specification triple of the form
    [triple t H (fun r => exists x1 x2, \[r = v] \* H']
    can be be reformulated as the Texan triple:
    [(\forall x1 x2, H \-* Q v) ==> wp t Q].

    We next formalize the equivalence between the two presentations, for
    the specific case where the specification involves a single auxiliary
    variable, called [x1]. The statement below makes it explicit that
    [H] and [v] may depend on [x1]. *)

Lemma texan_triple_equiv : forall t H A (Hof:val->A->hprop) (vof:A->val),
      (triple t H (fun r => \exists x, \[r = vof x] \* Hof r x))
  <-> (forall Q, H \* (\forall x, Hof (vof x) x \-* Q (vof x)) ==> wp t Q).
Proof using.
  intros. rewrite <- wp_equiv. iff M.
  { intros Q. xchange M. applys wp_ramified_trans.
    xsimpl. rewrite qwand_equiv. xsimpl. intros r x ->.
    xchange (hforall_specialize x).
    xchange (hwand_cancel (Hof (vof x) x)). }
  { applys himpl_trans M. xsimpl~. }
Qed.


==========


hwand_hpure_l_intro
   (* Note: here is an alterantive proof w.r.t. [hwand]:
    introv HP. unfold hwand. intros h K.
    forwards M: K (Fmap.empty:heap).
    { apply Fmap.disjoint_empty_r. }
    { applys hpure_intro HP. }
    { rewrite Fmap.union_empty_r in M. applys M. } *)



==========


Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

The statement, shown below, asserts that:

    1. [wp t Q1] can absorb any heap predicate [H] with which it
      is starred, changing it to [wp t (Q1 \*+ H)].

    2. [wp t Q1] can be weakened to [wp t Q2] when [Q1 ===> Q2].

    3. [wp t (Q1 \*+ H)] can be simplified to [wp t Q1] if one
      wants to discard [H] from the postcondition.


=========

    More precisely, the tactic invokes the following variant of the rule
    [triple_haffine_pre], which allows to leverage [xsimpl] for computing
    the heap predicate [H2] that remains after a predicate [H1] is removed
    from a precondition [H], through the entailment [H ==> H1 \* H2]. *)

Lemma triple_haffine_pre_trans : forall H1 H2 t H Q,
  haffine H1 ->
  H ==> H1 \* H2 ->
  triple t H1 Q ->
  triple t H Q.
Proof using.
  introv K WH M. applys triple_conseq (H1 \* H2) Q.
  { applys WH. }
  { applys triple_hany_pre. auto. }
  { applys qimpl_refl. }
Qed.

=========



(** Second, the heap predicate [\GC] it itself affine. Indeed, recall
    that [\GC] denotes some heap [H] such that [haffine H] holds.
    Thus, by essence, it corresponds to a affine heap predicate. *)

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H h Hh. rewrite hstar_hpure in Hh.
  destruct Hh as [M N]. applys* M.
Qed.

=========

Tactic Notation "xaffine" :=
  repeat match goal with
  | |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  | |- forall _, haffine _ => intro; solve [ .. ]
  end.

==========


Lemma mkstruct_hgc_post : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.
Proof using.
  intros. unfolds mkstruct. xpull. intros Q'.
  set (X := hgc) at 3. replace X with (\GC \* \GC).
  { xsimpl. } { subst X. apply hstar_hgc_hgc. }
Qed.

Lemma mkstruct_haffine_pre : forall H Q F,
  haffine H -> (* here, [True] *)
  (mkstruct F Q) \* H ==> mkstruct F Q.
Proof using.
  introv K. applys himpl_trans. 2:{ applys mkstruct_hgc_post. }
  applys himpl_trans. { applys mkstruct_frame. }
  applys mkstruct_conseq. xsimpl.
Qed.


======



    One could simply reproduce the definition above and replace the last
    conclusion, stated on the last line, with:

[[
        (Q \*+ \GC) v h1'
]]

    as this would match the fact that our definition of triples evolved from
    [forall (H':hprop), hoare (H \* H') t (Q \*+ H')] to
    [forall (H':hprop), hoare (H \* H') t (Q \*+ H' \*+ \GC)].

    However, this would be somewhat cheating, because the entire point of a
    direct definition in terms of heap is to not depend on the definition of
    [hstar] nor of other Separation Logic operators such as [\GC].

    =========

    the same Hoare triples and

Lemma hoare_trm_equiv : forall t1 t2 H Q,
  trm_equiv t1 t2 ->
  hoare t1 H Q <-> hoare t2 H Q.
Proof using.
  introv E. unfolds trm_equiv. iff M.
  { applys hoare_same_eval M. applys E. }
  { applys hoare_same_eval M. applys E. }
Qed.





Lemma trm_equiv_hoare : forall (t1 t2:trm) H Q,
  trm_equiv t1 t2 ->
  hoare t1 H Q <-> hoare t2 H Q.
Proof using.
  introv E. unfolds hoare, trm_equiv. iff M.
  { intros h K. forwards* (h'&v&R&K'): M h. exists h' v. rewrite* <- E. }
  { intros h K. forwards* (h'&v&R&K'): M h. exists h' v. rewrite* E. }
Qed.

(** Two terms that are equivalent satisfy the same Separation Logic triples.
    Indeed, the definition of a Separation Logic triple directly depends on
    the notion of Hoare triple. *)

Lemma trm_equiv_triple : forall (t1 t2:trm) H Q,
  trm_equiv t1 t2 ->
  triple t1 H Q <-> triple t2 H Q.
Proof using.
  introv E. unfolds triple. iff M.
  { intros H'. rewrite* <- trm_equiv_hoare. }
  { intros H'. rewrite* trm_equiv_hoare. }
Qed.

Another example is
    if [t1] is a while loop, it enables applying reasoning rules that handles
    in a specific way the post-treatment described by [t2].


    =========


(** The tactic [xsimpl] can be extended with specific support for the
    predicate [\GC]. In particular, [xsimpl] can simplify goals of the
    form [H ==> \GC] by turning them into [haffine H], using the lemma
    above. How to discharge the side-condition [haffine H] then depends
    on the exact instantiation of this predicate [haffine]. *)

=======



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties of [haffine] *)

Lemma haffine_hempty :
  haffine \[].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar_hpure : forall (P:Prop) H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using. intros. applys haffine_hany. Qed.




(** Another feature of [xsimpl] is that it is able to collapse several
    occurences of [\GC] into one. *)

Lemma xsimpl_demo_hgc_collapse : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 ==> H4 \* \GC \* H5 \* \GC.
Proof using. intros. xsimpl. (* leaves only one [\GC] *) Abort.


)================


(** Remark: in the course of the proof of [MList_if] in chapter [SLFList],
    we have exploited the property that no data can be allocated at the
    [null] location. This invariant can be enforced in either of two manners:

    - The first possibility is to bake this invariant directly into the
      definition of [hsingle l v], as follows:
      [fun (h:heap) => (h = Fmap.single l v) /\ (l <> null)].
    - The second possibility is to enforce this invariant at a deeper level,
      in the type of [heap], a.k.a. [state], to ensure that a value of that
      type can never bind the [null] location.

    For simplicity, we will ignore throughout the rest of this course
    the requirement that allocated locations are not null. *)

(* LATER: check how much more complicated it would be to handle this formally. *)
============


(** Remark: what is tricky in the above proof is that we do not exploit
    the fact that [let x = t in x] small-step reduces to [t], but we
    exploit the fact that the evaluation rules used to prove a behavior
    for [let x = t in x] can be used to establish the same behavior for [t]. *)


============


(* ####################################################### *)
(** ** Safe deallocation of allocated blocks *)

block n p

abstract

state = fmap loc val + list of ranges

alloc => block n p * cells n p

free => block n p * cells n p





(* --------------------------------------------------------------------- *)
(** Valid domains *)

(** A domain is valid if it is finite and does not include the null location. *)

Definition map_valid (V:Type) (f:map V) : Prop :=
  map_finite f /\ f null = None.

Lemma map_union_valid : forall f1 f2,
  map_valid f1 ->
  map_valid f2 ->
  map_valid (map_union f1 f2).
Proof using.
  introv [F1 N1] [F2 N2]. split.
  { applys* map_union_finite. }
  { unfold map_union. rewrite* N1. }
Qed.

Definition map_remove_valid : forall x f,
  map_valid f ->
  map_valid (map_remove f x).
Proof using.
  introv [F N]. split.
  { applys* map_remove_finite. }
  { unfold map_remove. case_if*. }
Qed.
Inductive memory (V:Type) : Type := make {
  memory_data :> map V;
  memory_valid : map_valid memory_data; }.





    In what follows, we present the key ideas involved in the definition of
    the type [state]. Details are outside of the scope of this course; they
    may be found in the file [State.v]. *)

Module State.

(** A state is represented as a finite map from locations to values. *)

(** The underlying map is represented as a Coq function from [loc] to
    [val]. *)

  Definition map : Type :=
    loc -> option val.

(** A map [f] has a valid domain if its domain is finite, in the sense that
    there exists a list [L] that contains all the locations from the domain,
    i.e., all the locations [l] such that [f l <> None]. *)

  Definition map_finite (f:map) : Prop :=
    exists (L:list loc), forall (l:loc), f l <> None -> mem l L.

(** A [state] is a dependent pair made of a [map] and a proof that this
    map is valid, i.e., that it satisfies the predicate [map_valid]. *)

  Inductive state : Type := {
    state_data : map;
    state_finite : map_finite state_data; }.

(** A more complete, more generic presentation of the construction can be
    found in the file [State.v], but it is not required to understand the
    details to follow this course on Separation Logic. *)

End State.




(* ########################################################### *)
(** ** Iterated star operation *)


(** The definition above can be recognized as an instance of an
    "indexed fold" operation, applied to the "Separation Logic
    commutative monoid" made of the star operator [\*] and its
    neutral element [\[]], and applied to the list [L].

    On paper, we would write the "big star" operator, with subscript
    "[x] at index [i] in [L]", applied to the expression [(p+i) ~~> x].

    In Coq, we can formalize this using a recursive function as follows. *)

Fixpoint hfoldi_list A (F:nat->A->hprop) (L:list A) (i:nat) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (F i x) \* (hfoldi_list F L' (S i))
  end.

Definition harray (L:list val) (p:loc) : hprop :=
  hfoldi_list (fun q x => q ~~> x) L p.


(* TODO Remark: *)

Fixpoint list_foldi A B (F:nat->A->B->B) (L:list A) (i:nat) (b:B) : B :=
  match L with
  | nil => b
  | x::L' => F i x (list_foldi F L' (S i) b)
  end.

Definition harray'' (L:list val) (p:loc) : hprop :=
  list_foldi (fun q x acc => q ~~> x \* acc) L p \[].



=========


Lemma triple_array_incr' : forall (n:int) L p,
  n = LibListZ.length L ->
  triple (array_incr_par p n)
    (harray (vals_of_ints L) p)
    (fun _ => harray (vals_of_ints (LibList.map (fun x => x + 1) L)) p).
Proof using.
  intros n. induction_wf IH: (wf_downto 0) n.
  introv E. xwp. xapp. xif; intros C1.
  { forwards (x&Hx): length_one_inv L. math. (* TODO math *) subst.
    unfold vals_of_ints. rew_listx. rewrite harray_one_eq. xapp.
    rewrite <- harray_one_eq. xsimpl. }
  { asserts C1': (n <> 1). { intros N. applys C1. fequals. } clear C1. (* TODO cleanup *)
    xapp. xif; intros C2.
    { forwards R: range_split n. { math. }
      xapp. { math. } sets m: (Z.quot n 2).
      xapp. xapp triple_ptr_add. { math. }
      forwards (L1&L2&EL&LL1&LL2): take_app_drop_spec_nonneg m L. { math. }
      rewrite EL. unfold vals_of_ints. rew_listx. rewrite harray_concat_eq.
      xapp (>> IH L1). { math. } { math. }
      rew_listx. asserts_rewrite (abs (p + m) = (LibList.length L1 + p)%nat).
      { apply eq_nat_of_eq_int. rewrite abs_nonneg; math. }
      xapp (>> IH L2). { math. } { math. }
      rewrite harray_concat_eq. rew_listx. unfold vals_of_ints. xsimpl. }
    { asserts En: (n = 0). { math. }
      forwards HL: (length_zero_inv L). { math. }
      xval. subst. unfold vals_of_ints; rew_listx. xsimpl. } }
Qed.


========================


(* ####################################################### *)
(** ** Treatment of uncurried functions *)

(*
  | trm_fixs : var -> list var -> trm -> trm
  | trm_apps : trm -> list trm -> trm


Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t :=
    subst y w t in
  let aux_no_captures xs t :=
    If LibList.mem y xs then t else aux t in
  match t with
  | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                        aux_no_captures xs t1)
  | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
  ...
 end.


Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. simpls. case_var.
  { false* var_fresh_mem_inv. }
  { auto. }
Qed.


  | eval_fixs : forall m f xs t1,
      xs <> nil ->
      eval m (trm_fixs f xs t1) m (val_fixs f xs t1)

  | eval_apps_fixs : forall m1 m2 f xs t3 v0 vs r,
      v0 = val_fixs f xs t3 ->
      var_fixs f (length vs) xs ->
      eval m1 (substn xs vs (subst1 f v0 t3)) m2 r ->
      eval m1 (trm_apps v0 vs) m2 r


Fixpoint var_distinct (xs:vars) : Prop :=
  match xs with
  | nil => True
  | x::xs' => var_fresh x xs' /\ var_distinct xs'
  end.

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.


(** [noduplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive noduplicates A : list A -> Prop :=
  | noduplicates_nil : noduplicates nil
  | noduplicates_cons : forall x l,
      ~ (mem x l) ->
      noduplicates l ->
      noduplicates (x::l).



Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop :=
     var_distinct (f::xs)
  /\ length xs = n
  /\ xs <> nil.

Definition var_fixs_exec (f:bind) (n:nat) (xs:vars) : bool := ..

Lemma var_fixs_exec_eq : forall f (n:nat) xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).


Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* eval_apps_fixs. }
Qed.


Fixpoint trms_to_vals_rec (acc:vals) (ts:trms) : option vals :=
  match ts with
  | nil => Some (List.rev acc)
  | trm_val v :: ts' => trms_to_vals_rec (v::acc) ts'
  | _ => None
  end.

Definition trms_to_vals (ts:trms) : option vals :=
  trms_to_vals_rec nil ts.


Lemma xwp_lemma_fixs : forall F f vs ts xs t H Q,
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f (length vs) xs ->
  H ==> (wpgen (combine (f::xs) (F::vs)) t) Q ->
  triple (trm_apps F ts) H Q.


(* ####################################################### *)
(** ** Coercion for uncurried functions *)

Coercion trm_to_pat : trm >-> pat.

(** Parsing facility: coercions for turning [t1 t2 t3]
    into [trm_apps t1 (t2::t3::nil)] *)

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.

We discuss in the bonus section the treatment
    of native n-ary functions, which is the most practical solution from an
    engineering point of view.
=====================




(** Useful substitution lemmas, generalizing [isubst_rem] and [isubst_rem_2]. *)

Lemma isubst_rem_3 : forall f x1 x2 vf vx1 vx2 E t,
     isubst ((f,vf)::(x1,vx1)::(x2,vx2)::E) t
   = subst x2 vx2 (subst x1 vx1 (subst f vf (isubst (rem x2 (rem x1 (rem f E))) t))).
Proof using.
  intros. do 3 rewrite subst_eq_isubst_one. do 3 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. do 3 rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. simpls. do 3 rewrite lookup_rem in K1. case_var. }
Qed.

Lemma isubst_rem_4 : forall f x1 x2 x3 vf vx1 vx2 vx3 E t,
     isubst ((f,vf)::(x1,vx1)::(x2,vx2)::(x3,vx3)::E) t
   = subst x3 vx3 (subst x2 vx2 (subst x1 vx1 (subst f vf (isubst (rem x3 (rem x2 (rem x1 (rem f E)))) t)))).
Proof using.
  intros. do 4 rewrite subst_eq_isubst_one. do 4 rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. do 4 rewrite lookup_rem. case_var~. }
  { intros y v1 v2 K1 K2. simpls. do 4 rewrite lookup_rem in K1. case_var. }
Qed.




    Reasoning about this substitution function requires a few auxiliary
    lemmas, for example to distribute the substitution function when the
    variable involved are suffic

[[
    Lemma subst_trm_fixs : forall y w f xs t,
      ~ List.In y (f::xs) ->
      subst y w (trm_fixs f xs t) = trm_fixs f xs (subst y w t).
]]
Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q)
             \* (MList L' q)).
Proof using.
  intros. destruct L as [|x L'].
  { xchange MList_nil. intros M. case_if. xsimpl. auto. }
  { xchange MList_cons. intros q. case_if.
    { xchange hfield_not_null. }
    { xsimpl. auto. } }
Qed.


(** Another presentation *)

Lemma triple_get_field_hrecord' : forall p L k v,
  match hrecord_lookup k L with
  | None => True
  | Some v =>
      triple (val_get_field k p)
        (hrecord L p)
        (fun r => \[r = v] \* hrecord L p)
  end.
Proof using.
Admitted.
(*
  induction L.
  None => false
  Some => neq => frame
          eq => frame + apply
Qed.
*)

(** Most real-world programming languages include primitive operations
    for reading and writing in array cells. Yet, in a simple language
    like ours, array cells can be accessed by means of pointer arithmetic.
    It is interesting to see how one may formally reason about this kind
    of encoding. *)



Parameter hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).


Lemma hcells_focus_read : forall p (k:nat) v L, (* TODO *)
  k < length L ->
  v = LibList.nth k L ->
  hcells L p = ((p+k)%nat ~~> v)\* (((p+k)%nat ~~> v) \-* hcells L p).
Proof using.
  introv Hk E. gen k p. induction L as [|x L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case in E. case_if.
    { subst. math_rewrite (p + 0 = p)%nat. xsimpl. }
    { applys himpl_antisym; [| xsimpl ].
      forwards R: IHL' (k-1)%nat E (S p). { math. }
      math_rewrite (S p + (k - 1) = p + k)%nat in R.
      rewrite R at 1. rewrite hstar_comm_assoc. applys himpl_frame_r.
      rewrite hstar_comm.
      rewrite (@hstar_comm (p ~~> x) (hcells L' (S p))).
      applys hstar_hwand. (* TODO: automate *) } }
Qed.

Definition lock (H:hprop) := H.

Lemma harray_focus_read : forall p (k:nat) v L, (* TODO *)
  k < length L ->
  v = LibList.nth k L ->
  harray L p = ((p+k)%nat ~~> v)\* lock (((p+k)%nat ~~> v) \-* harray L p).
Proof using.
  introv Hk E. unfold harray. rewrite* (@hcells_focus_read p k v L).
Admitted.

Lemma triple_array_get : forall p i L,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).
Proof using.
  introv N. xwp. xapp triple_ptr_add. { math. }
  sets v: (LibList.nth (abs i) L).
  xchange (@harray_focus_read p (abs i) v). { skip. (* TODO *) } eauto.
  asserts_rewrite (abs (p + i) = p + abs i)%nat. skip. (*TODO *)
  (* xsimpl simplifies the wand! *)
  xapp triple_get. unfold lock. xsimpl*.
Qed.


Lemma hcells_focus : forall (k:nat) p L,
  k < length L ->
  hcells L p ==>
       ((p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~~> w) \-* hcells (LibList.update k w L) p).
Proof using.
  introv E. gen k p. induction L as [|x L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case. case_if.
    { subst. math_rewrite (p + 0 = p)%nat. xsimpl. intros y.
      rewrite update_zero. (* TODO: rew_listx *) xsimpl.
      simpl. xsimpl. }
    { forwards R: IHL' (k-1)%nat (S p). { math. }
      math_rewrite (S p + (k - 1) = p + k)%nat in R.
      xchange R. xsimpl. intros w. xchange (hforall_specialize w).
      rewrite update_cons_pos; [|math]. simpl. xsimpl. } }
Qed.




Fixpoint get_fun_and_args (a:apps) : trm * list trm :=
  match a with
  | apps_init t1 t2 => (t1, (t2::nil))
  | apps_next a1 t2 =>
      let (t0,ts) := get_fun_and_args a1 in
      (t0,t2::ts)
  end.

Coercion apps_to_trm (a:apps) : trm :=
  let (t0,ts) := get_fun_and_args a in
  trm_apps t0 ts.

  (** A specification lemma for [incr] takes the form [triple (incr p) H Q].
    Recall from the first chapter ([SLFBasic]) the specification of [incr]:

[[
    Parameter triple_incr : forall (p:loc) (n:int),
      triple (trm_app incr p)
        (p ~~> n)
        (fun _ => p ~~> (n+1)).
]]

    The specification that we will write in this chapter (and the
    following ones) will differ in two ways from the one above.

    - First, the heap predicates will now be written [p ~~> n],
      instead of [p ~~> n], for technical reasons that we won't
      detail here.
    - Second, the postcondition will now be of the form
      [fun (v:val) => \[v = val_unit] \* ...] instead of
      [fun (v:unit) => ...], for similar reasons.

    The motivation for these differences is beyond the scope of this
    course. Details are provided in the  chapter [SLFLift]. *)

(* INSTRUCTORS *)
(** [p ~~> n] technically stands for [p ~~> (val_int n)], where
    [val_int] is a coercion. It is an instance of a predicate of
    the form [p ~~> v] for a value [v] of type [val]. In contrast,
    [p ~~> n] stands for [p ~~> (enc n)], where [enc] is a type-class
    function that for translating Coq values into the type [val].
    The type-class mechanism is more complex than the coercion mechanism,
    yet much more general, hence its use in the actual CFML tool. *)
(* /INSTRUCTORS *)




(* EX3? (triple_named_heap) *)
(** Prove the counterpart of [hoare_named_heap] for Separation
    Logic triples.

    Hint: you should exploit the lemma [hoare_named_heap], and
    never unfold the definition of the judgment [hoare]

    Hint: unfold the definition of [triple], exploit [hoare_named_heap],
    then conclude with help of [hoare_conseq] and by exploiting
    basic properties of the Separation Logic operators. *)

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M. unfolds triple. intros H'.
  applys hoare_named_heap. intros h K.
  lets (h1&h2&K1&K2&D&U): hstar_inv K. subst h.
  lets N: M h1 (=h2). applys K1.
  applys hoare_conseq N.
  { intros ? ->. applys* hstar_intro. }
  { intros x. applys himpl_frame_r.
    intros ? ->. applys K2. }
Qed. (* /ADMITTED *)


(** Let us first prove that (1) and (2) are equivalent. *)

Lemma hwand_eq_hwand' :
  hwand = hwand'.
Proof using.
  apply pred_ext_3. intros H1 H2 h. unfold hwand, hwand'. iff M.
  { intros h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. rewrite hstar_comm. applys hstar_intro K0 K1 D. }
  { exists (=h). rewrite hstar_comm. rewrite hstar_hpure. split.
    { intros h3 K3. rewrite hstar_comm in K3.
      destruct K3 as (h1&h2&K1&K2&D&U). subst h1 h3. applys M D K2. }
    { auto. } }
Qed.

(** According to definition (3), an operator [op] denotes a magic wand
   if and only if, for any [H0], [H1], [H2], it satisfies the
   equivalence [(H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2)]. Formally: *)

Definition hwand_characterization (op:hprop->hprop->hprop) :=
  forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H1 \* H0 ==> H2).

(** We prove that an operator [op] satisfies [hwand_characterization]
    if and only if it is equal to [hwand]. This result shows that the
    definitions (2) and (3) are equivalent. *)

Lemma hwand_characterization_iff_eq_hwand : forall op,
  hwand_characterization op <-> op = hwand.
Proof using.
  iff K.
  { apply fun_ext_2. intros H1 H2.
    unfolds hwand_characterization, hwand. apply himpl_antisym.
    { lets (M&_): (K (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite K. applys M. } }
  { subst. unfolds hwand_characterization. apply hwand_equiv. }
Qed.

(** Last, we prove (3) and (4) equivalent. *)

Lemma hwand_characterization_iff_intro_elim_rules : forall op,
  hwand_characterization op <->
  (    (forall H0 H1 H2, (H1 \* H0 ==> H2) -> (H0 ==> op H1 H2))
    /\ (forall H1 H2, (H1 \* (op H1 H2) ==> H2))).
Proof using.
  unfold hwand_characterization. iff K.
  { split.
    { introv M. apply <- K. apply M. }
    { intros. apply K. auto. } }
  { destruct K as (K1&K2). intros. split.
    { introv M. xchange M. rewrite hstar_comm. applys K2. }
    { introv M. applys K1. applys M. } }
Qed.




Lemma hstar_hpure : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure. iff M.
  { destruct M as (h1&h2&(p&M0)&M1&M2&D). hnf in M0. subst. split~.
    rewrite* Fmap.union_empty_l. }
  { destruct M as (p&M0). exists (hea_emptyp.

  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  { split~. } { exists* p. }
Qed.





   (* currently only needed for demo *)
Parameter hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma xchange_demo_hwand_hpure : forall (P:Prop) H1 H2 H3,
  P ->
  H1 \* H3 ==> H2 ->
  (\[P] \-* H1) \* H3 ==> H2.
Proof using.
  introv HP M1. dup 3.
  { xchange (hwand_hpure_l_intro P H1). auto. xchange M1. }
  { xchange hwand_hpure_l_intro. auto. xchange M1. }
  { xchange hwand_hpure_l_intro, M1. auto. }
Qed.



Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using.
  introv HP. rewrite <- hstar_hempty_l at 1.
  forwards~ K: himpl_hempty_hpure P.
  applys himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

=========



Parameter eval_if_trm : forall s1 s2 s3 v b t0 t1 t2,
  eval s1 t0 s2 (val_bool b) ->
  eval s2 (if b then t1 else t2) s3 v ->
  eval s1 (trm_if t0 t1 t2) s3 v.


Lemma hoare_if_trm : forall (Q':bool->hprop) t0 t1 t2 H Q,
  hoare t0 H (fun r => \exists b, \[r = b] \* Q' b) ->
  (forall b, hoare (if b then t1 else t2) (Q' b) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros s1 K1. lets (s2&v0&R2&K2'): M1 K1.
  lets (b'&K2): hexists_inv K2'. rewrite hstar_hpure in K2.
  destruct K2 as (->&K2).
  forwards (s3&v&R&K): M2 K2. exists s3 v. splits.
  { applys eval_if_trm R2 R. }
  { applys K. }
Qed.



Lemma triple_if_trm : forall (Q':bool->hprop) t0 t1 t2 H Q,
  triple t0 H (fun r => \exists b, \[r = b] \* Q' b) ->
  (forall b, triple (if b then t1 else t2) (Q' b) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_if_trm (fun b => Q' b \* HF).
  { applys hoare_conseq. applys M1 HF. { xsimpl. } { xsimpl. auto. } }
  { intros v. applys M2. }
Qed.

Lemma triple_while_inv_not_framable : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  wf R ->
  (forall b X, triple t1 (I b X) (fun r => \exists b', \[r = b'] \* I b' X)) ->
  (forall b X, triple t2 (I b X) (fun _ => \exists b' Y, \[R Y X] \* I b' Y)) ->
  triple (trm_while t1 t2) (\exists b X, I b X) (fun r => \exists Y, I false Y).
Proof using.
  introv WR M1 M2. applys triple_hexists. intros b. applys triple_hexists. intros X.
  gen b. induction_wf IH: WR X. intros. applys triple_while.
  applys triple_if_trm (fun b' => I b' X).
  { applys M1. }
  { intros b'. case_if.
    { applys triple_seq.
      { applys M2. }
      { applys triple_hexists. intros b''. applys triple_hexists. intros Y.
        applys triple_hpure. intros HR. applys IH HR. } }
    { applys triple_val. xsimpl. } }
Qed.

Transparent hwand.
(* TODO: move to extra *)
Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. unfold hwand. xsimpl.
  { intros H0 M. xchange M. applys HP. }
  { xpull. auto. }
Qed.



Lemma himpl_hwand_hpure_l : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using. introv HP. rewrite* hwand_hpure_l. Qed.

Lemma mkstruct_monotone_conseq : forall F1 F2 Q1 Q2,
  (forall Q', F1 Q' ==> F2 Q') ->
  Q1 ===> Q2 ->
  mkstruct F1 Q1 ==> mkstruct F2 Q2.
Proof using.
  introv WF WQ. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'. xchange WQ.
Qed.



(*


Lemma wpgen_while_sound : forall t1 t2 F1 F2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_while t1 t2) (wpgen_while F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_while.
  applys himpl_hforall_l (wp (trm_while t1 t2)).
  applys himpl_trans'. rewrite (wp_eq_mkstruct_wp (trm_while t1 t2)). applys himpl_refl. (* TODO *)
  applys himpl_hwand_hpure_l. intros
  applys mkstruct_himpl_wp. intros Q'.
  applys himpl_trans'. { applys wp_while. }
  applys himpl_trans'.
  { applys wpgen_if_trm_sound.
    { applys S1. }
    { applys mkstruct_sound. applys wpgen_seq_sound.
      { applys S2. }
      { applys mkstruct_sound. applys wp_sound. } }
    { applys mkstruct_sound. applys wpgen_val_sound. } }
  { auto. }
Qed.

*)


(*
Lemma wpgen_while_proof_obligation : forall Q E t1 t2,
  mkstruct (wpgen_while (wpgen E t1) (wpgen E t2)) Q ==> wp (trm_while (isubst E t1) (isubst E t2)) Q.
Proof using.
  intros. lets:wpgen_while_eq.  rewrite <- wpgen_while_eq.
  applys himpl_trans'. applys wpgen_while_sound. unfolds formula_sound. lets: wpgen_sound.
Admitted.
*)


Lemma mkstruct_ramified_trans_protect : forall F H Q1 Q2,
  H ==> mkstruct F Q1 \* protect (Q1 \--* Q2) ->
  H ==> mkstruct F Q2.
Proof using. introv M. xchange M. applys mkstruct_ramified. Qed.

Lemma mkstruct_ramified_trans : forall F H Q1 Q2,
  H ==> mkstruct F Q1 \* (Q1 \--* Q2) ->
  H ==> mkstruct F Q2.
Proof using. introv M. xchange M. applys mkstruct_ramified. Qed.

Lemma mkstruct_cancel : forall H2 F H Q1 Q2,
  H ==> mkstruct F Q1 \* H2 ->
  Q1 \*+ H2 ===> Q2 ->
  H ==> mkstruct F Q2.
Proof using.
  introv M1 M2. xchange M1. rewrite <- qwand_equiv in M2.
  xchange M2. xchange mkstruct_ramified.
Qed.


Lemma mkstruct_erase_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. applys himpl_trans'. applys mkstruct_conseq WQ. xchange mkstruct_erase.
Qed.

(*
Close Scope wp_scope.

Lemma mkstruct_erase_conseq_frame : forall F H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  F Q1 \* H ==> mkstruct F Q2.
Proof using.
  introv WQ.
lets: mkstruct_frame.
 applys himpl_trans'. applys mkstruct_conseq WQ. xchange mkstruct_erase.
Qed.


Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.
*)




    Lemma mkstruct_himpl_wp : forall F t,
      (forall Q, F Q ==> wp t Q) ->
      (forall Q, mkstruct F Q ==> wp t Q).
    Proof using. introv M. applys mkstruct_sound. hnfs*. Qed.



Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. intros Q. unfold mkstruct. xsimpl. intros Q'.
  lets N: M Q'. xchange N. applys wp_ramified.
Qed.

Lemma mkstruct_wp : forall t,
  mkstruct (wp t) = (wp t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { applys mkstruct_sound. applys wp_sound. }
  { applys mkstruct_erase. }
Qed.


Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).
    (* LATER: need to assert that [L] does not contain [val_header] *)
Proof using.
  introv N. xtriple. xapp triple_alloc. { auto. }
  { xpull. intros p. unfold harray_uninit. xsimpl*.
    { rewrite length_make. rewrite* abs_nonneg. } }
Qed.


Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (\[val_not_header v] \* p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  intros. applys triple_hpure. intros N.
  unfold triple. intros H'. applys* hoare_conseq hoare_set; xsimpl~.
Qed.




(* ########################################################### *)
(** ** Updated specifications for [val_get] and [val_set] *)

(*

(** Updated get and set *)

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets (E1&N): hsingle_inv P1. subst s1. applys eval_get_sep U. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma hoare_set : forall H w p v,
  val_not_header v ->
  hoare (val_set (val_loc p) v)
    ((p ~~> w) \* H)
    (fun r => \[r = val_unit] \* (p ~~> v) \* H).
Proof using.
  introv N'. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets (E1&N): hsingle_inv P1.
  exists (Fmap.union (Fmap.single p v) h2) val_unit. split.
  { subst h1. applys eval_set_sep U D. auto. }
  { rewrite hstar_hpure. split~.
    { applys~ hstar_intro.
      { applys~ hsingle_intro. }
      { subst h1. applys Fmap.disjoint_single_set D. } } }
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_get; xsimpl~.
Qed.

Lemma triple_set : forall w p v,
  val_not_header v ->
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  introv R. unfold triple. intros H'. applys* hoare_conseq hoare_set; xsimpl~.
Qed.

Lemma triple_set' : forall w p v,
  triple (val_set (val_loc p) v)
    (\[val_not_header v] \* p ~~> w)
    (fun _ => p ~~> v).
Proof using. intros. applys triple_hpure. intros N. applys* triple_set. Qed.

(* Hint Resolve triple_get triple_set' : triple. *)

*)


(*
Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v) /\ val_not_header v.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope_new.

Local Open Scope hprop_scope_new.

(** Properties of [hsingle]. *)

Lemma hsingle_intro : forall p v,
  val_not_header v ->
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v /\ val_not_header v.
Proof using. auto. Qed.

Lemma hsingle_not_header : forall p v,
  (p ~~> v) ==> (p ~~> v) \* \[val_not_header v].
Proof using.
  intros. unfold hsingle. intros h M.
  rewrite hstar_comm, hstar_hpure. autos*.
Qed.

*)


(** Updated get and set *)

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets (E1&N): hsingle_inv P1. subst s1. applys eval_get_sep U. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_get; xsimpl~.
Qed.





(* ########################################################### *)
(** ** Updated predicate [hsingle] *)

(*
Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v) /\ val_not_header v.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope_new.

Local Open Scope hprop_scope_new.

(** Properties of [hsingle]. *)

Lemma hsingle_intro : forall p v,
  val_not_header v ->
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v /\ val_not_header v.
Proof using. auto. Qed.

Lemma hsingle_not_header : forall p v,
  (p ~~> v) ==> (p ~~> v) \* \[val_not_header v].
Proof using.
  intros. unfold hsingle. intros h M.
  rewrite hstar_comm, hstar_hpure. autos*.
Qed.
*)




(** The two above specifications are somewhat inconvenient for proofs in
    practice because they require explicitly providing the list describing
    the contents of the deallocated cells. (An example illustrating
    the issue is given further on, in lemma [triple_dealloc_mcell].)

    We therefore consider an alternative deallocation rule that avoids the
    quantification over thie list [L]. It is based on a new heap predicate,
    written [hcells_any k p], which describes the contents of [k] cells,
    each of which with an arbitrary contents described through an existential
    quantifier. *)

Fixpoint hcells_any (k:nat) (p:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => (\exists v, p ~~> v) \* (hcells_any k' (S p))
  end.

(** We can prove that the predicate [hcells_any k p] entails [hcells L p]
    for some list [L] of length [k]. This list [L] is obtained by gathering
    the [k] existentially-quantified values that appear recursively in the
    definition of [hcells_any]. *)

Lemma himpl_hcells_any_hcells : forall p k,
  hcells_any k p ==> \exists L, \[length L = k] \* hcells L p.
Proof using.
  intros. gen p. induction k as [|k']; simpl; intros.
  { xsimpl (@nil val). { auto. } { simpl. xsimpl. } }
  { xpull. intros v. xchange IHk'. intros L' EL'.
    xsimpl (v::L'). { rew_list. math. } { simpl. xsimpl. } }
Qed.

(** The specification of the operation [val_dealloc k] can then be
    reformulated using a precondition of the forme [harray_any k p].
    We illustrate its use further, in the verification proof for a
    function that deallocates a list cell ([triple_dealloc_mcell]). *)

Lemma triple_dealloc_hcells_any : forall p k,
  triple (val_dealloc k p)
    (hcells_any k p)
    (fun _ => \[]).
Proof using.
  intros. xtriple. xchange himpl_hcells_any_hcells. intros L EL.
  xapp triple_dealloc_hcells. { auto. } { xsimpl. }
Qed.





(** To prevent undesirable simplifications, we set the definition [hfield]
    to be opaque. Still, it is useful in places to be able to unfold the
    definition. To that end, we state a lemma for unfolding the definition.
    In its statement, we replace the addition [p+1+k] with the addition [k+S p],
    because the later simplifies better in Coq when [k] is a constant. *)

Lemma hfield_eq : forall p k v,
  hfield p k v = ((k+S p)%nat ~~> v \* \[p <> null]).
Proof using. intros. math_rewrite (k+S p = p+1+k)%nat. auto. Qed.

Global Opaque hfield.



Lemma length_hfields_update : forall kvs kvs' k v,
  hfields_update k v kvs = Some kvs' ->
  length kvs' = length kvs.
Proof using.
  intros kvs. induction kvs as [|[ki vi] kvs1]; simpl; introv E.
  { introv _ H. inverts H. }
  { case_if.
    { inverts E. rew_list*. }
    { cases (hfields_update k v kvs1).
      { inverts E. rew_list*. }
      { inverts E. } } }
Qed.


Lemma hrecord_eq_harray : forall p kvs L,
  L = LibList.map snd kvs ->
  hrecord kvs p = harray L p.
Proof using.
  intros. unfolds hrecord, harray. applys himpl_antisym.
  { xpull. intros z M. asserts Hz: (z = length kvs).
    { lets E: length_nat_seq 0%nat z. rewrite <- M in E. rew_listx* in *. }
    xchange* (>> hfields_eq_hcells p M). { rew_listx*. }
    subst. rew_listx. xsimpl. }
  { xsimpl.
Qed.


Lemma triple_mcons : forall (x q:val),
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Hint Resolve triple_new_hrecord_2 : triple.
Proof using. intros. xtriple. unfold mcons. xapp. xsimpl*. applys* triple_new_hrecord_2. Qed.
