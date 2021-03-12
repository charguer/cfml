Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
Require Import UnitTests_ml.

Require TLC.LibListZ. (* TODO NEEDED? *)
(* TODO NEEDED? Import ZsubNoSimpl. *)




(********************************************************************)
(********************************************************************)

(********************************************************************)
(* ** Record with -- TODO: move *)


Lemma recordwith_spec :
  SPEC (recordwith tt)
    PRE \[]
    POST (fun r => r ~~~> `{ mya' := 6; myb' := 5; myc' := 3 }).
Proof using.
  xcf. xapp. intros r. xapp. xsimpl.
Qed.



(********************************************************************)
(* ** Notation for PRE/INV/POST *)


Lemma notation_inv_post_spec_pre : forall (r:loc) (n:int),
  SPEC (notation_inv_post r)
    PRE (r ~~> n)
    POST (fun x => \[x = n] \* r ~~> n).
Proof using. xcf. xapp. xsimpl*. Qed.

Lemma notation_inv_post_spec_inv : forall (r:loc) (n:int),
  SPEC (notation_inv_post r)
    INV (r ~~> n)
    POST \[= n].
Proof using. xcf. xapp. xsimpl*. Qed.

Lemma notation_pre_inv_post_spec_pre : forall (r s:loc) (n m:int),
  SPEC (notation_pre_inv_post r s)
    PRE (r ~~> n \* s ~~> m)
    POST (fun x => \[x = m] \* r ~~> (n+1) \* s ~~> m).
Proof using. xcf. xapp. xapp. xsimpl*. Qed.

Lemma notation_pre_inv_post_spec_inv : forall (r s:loc) (n m:int),
  SPEC (notation_pre_inv_post r s)
    PRE (r ~~> n)
    INV (s ~~> m)
    POST (fun x => \[x = m] \* r ~~> (n+1)).
Proof using. xcf. xapp. xapp. xsimpl*. Qed.

(* TODO:  include one test for each specification syntax
  Lemma notation_inv_postunit_spec :
*)


(********************************************************************)
(* ** Encoding of names *)

Lemma renaming_types : True.
Proof using.
  pose renaming_t'_.
  pose renaming_t2_. pose C'.
  pose renaming_t3_.
  pose renaming_t4_.
  auto.
Qed.



(* TODO MOVE *)
Ltac xletval_core tt ::=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_Val _ (fun x => _)) => idtac x;
     let a := fresh "v" x in
     let Pa := fresh "P" a in
     applys xletval_lemma;
     intros a Pa
  end.

Ltac xletvalas_core tt :=
  xletval_core tt;
  do 2 (let H := get_last_hyp tt in revert H).

Tactic Notation "xletval" "as" := (* TODO: document *)
  xletvalas_core tt.

Lemma renaming_demo_spec :
  SPEC (renaming_demo tt)
    PRE \[]
    POST \[= tt].
Proof using. (* TODO: used as demo for xletval *)
  (* disclaimer: renaming are not visible because Coq display underscore *)
  xcf.
  xletval as. intros x Px. subst x.
  xletvals.
  xletval.
  xletval as. intros.
  xletval as. intros.
  xvals*.
Qed.


(********************************************************************)
(* ** Polymorphic let bindings and value restriction *)

(* TODO
Lemma let_poly_p0_spec :
  SPEC (let_poly_p0 tt) \[] \[= tt].
Proof using.
  xcf. xlet_poly_keep (= true). xapp_skip. intro_subst. xvals~.
Qed.

Lemma let_poly_p1_spec :
  SPEC (let_poly_p1 tt) \[] \[= tt].
Proof using.
  xcf. xfun. xlet_poly_keep (fun B (r:option B) => r = None).
  { xapps. xvals. }
  { intros Hr. xvals~. }
Qed.

Lemma let_poly_p2_spec :
  SPEC (let_poly_p2 tt) \[] \[= tt].
Proof using.
  xcf. xfun. xlet.
  { xlet_poly_keep (fun B (r:option B) => r = None).
    { xapps. xvals. }
    { intros Hr. xvals~. } }
  { xvals~. }
Qed.

Lemma let_poly_p3_spec :
  SPEC (let_poly_p3 tt) \[] \[= tt].
Proof using.
  xcf.
  xlet_poly_keep (= true). { xapp_skip. } intro_subst.
  xapp_skip.
  xlet_poly_keep (= false). { xapp_skip. } intro_subst.
  xapp_skip.
  xvals~.
Qed.

Lemma let_poly_f0_spec : forall A,
  SPEC (let_poly_f0 tt) \[] \[= @nil A].
Proof using.
  xcf. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_f1_spec : forall A,
  SPEC (let_poly_f1 tt) \[] \[= @nil A].
Proof using.
  xcf. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_f2_spec : forall A,
  SPEC (let_poly_f2 tt) \[] \[= @nil A].
Proof using.
  xcf. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_f3_spec :
  SPEC (let_poly_f3 tt) \[] \[= @nil int].
Proof using.
  xcf. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_f4_spec :
  SPEC (let_poly_f4 tt) \[] \[= @nil int].
Proof using.
  xcf. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_g1_spec :
  SPEC (let_poly_g1 tt) \[] \[= 5::nil].
Proof using.
  xcf. xapps. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_g2_spec :
  SPEC (let_poly_g2 tt) \[] \[= 4::nil].
Proof using.
  xcf. xapps. xapps. xapps. xsimpl~.
Qed.

Lemma let_poly_h0_spec : forall A,
  SPEC (let_poly_h0 tt) \[] (fun (r:loc) => r ~~> (@nil A)).
Proof using.
  xcf. xapps. xval~.
Qed.

Lemma let_poly_h1_spec : forall A,
  SPEC (let_poly_h1 tt) \[] (fun (f:func) =>
    \[ SPEC (f tt) \[] (fun (r:loc) => r ~~> (@nil A)) ]).
Proof using.
  xcf. xlet (fun g => \[ SPEC (g tt) \[] (fun (r:loc) => r ~~> (@nil A)) ]).
  { xfun. xvals. xapps. xapps. }
  intros Hg. xvals. xapps.
Qed.

Lemma let_poly_h2_spec : forall A,
  SPEC (let_poly_h2 tt) \[] (fun (f:func) =>
    \[ SPEC (f tt) \[] (fun (r:loc) => r ~~> (@nil A)) ]).
Proof using.
  xcf. xfun. xvals. xapps. xapps.
Qed.

Lemma let_poly_h3_spec : forall A,
  SPEC (let_poly_h3 tt) \[] (fun (r:loc) => r ~~> (@nil A)).
Proof using.
  xcf. xfun. xapps. xapps.
Qed.

Lemma let_poly_k1_spec : forall A,
  SPEC (let_poly_k1 tt) \[] \[= @nil A].
Proof using.
  xcf. xvals~.
Qed.

Lemma let_poly_k2_spec : forall A,
  SPEC (let_poly_k2 tt) \[] (fun (r:loc) => r ~~> (@nil A)).
Proof using.
  xcf. xapps.
Qed.

Lemma let_poly_r1_spec :
  SPEC (let_poly_r1 tt) \[] \[= tt].
Proof using.
  xcf. xapps. xvals~.
  Unshelve. solve_type.
Qed.

Lemma let_poly_r2_spec : forall A,
  SPEC (let_poly_r2 tt) \[] \[= @nil A].
Proof using.
  xcf. xapps. dup 2.
  { xval. xvals~. }
  { xvals. xvals~. }
  Unshelve. solve_type.
Qed.


Lemma let_poly_r3_spec : forall A,
  SPEC (let_poly_r3 tt) \[] \[= @nil A].
Proof using.
  xcf. xlet_poly_keep (fun A (r:list A) => r = nil).
  { xapps. xvals~. }
  intros Hr. xvals. auto.
Qed.
*)


(********************************************************************)
(* ** Top-level values *)

Lemma top_val_int_spec :
  top_val_int = 5.
Proof using.
  dup 5.
  xcf. auto.
  (* demos: *)
  xcf_show. skip.
  xcf_show top_val_int. skip.
  xcf. skip.
Qed.

Lemma top_val_int_list_spec :
  top_val_int_list = @nil int.
Proof using.
  xcf. (* TODO: why solved? *)
Qed.

Lemma top_val_poly_list_spec : forall A `{EA:Enc A},
  top_val_poly_list = @nil A.
Proof using. xcf*. Qed.

Lemma top_val_poly_list_pair_spec : forall A `{EA:Enc A} B `{EB:Enc B},
  top_val_poly_list_pair = (@nil A, @nil B).
Proof using. xcf*. Qed.



(********************************************************************)
(* ** Return *)

Lemma ret_unit_spec :
  SPEC (ret_unit tt)
    PRE \[]
    POST \[= tt]. (* (fun (_:unit) => \[]).*) (* same as (# \[]). *)
Proof using.
  xcf. dup 3.
  { xval. xsimpl. auto. }
  { xvals. auto. }
  { xvals*. }
(* TODO   { xval_no_gc. xsimpl. auto. }
  { xval_no_clean. xsimpl*. } (* differs only on nontrivial goals *)
  { xval_no_pull. xsimpl*. } (* differs only on a let binding *)
  { try xval (fun r => \[r = tt /\ True]).
    xpost. xval (fun r => \[r = tt /\ True]). xsimpl. auto. xsimpl. auto. }
  { try xvals (fun r => \[r = tt /\ True]).
    xpost. xvals (fun r => \[r = tt /\ True]). auto. xsimpl. auto. }
*)
Qed.

Lemma ret_int_spec :
  SPEC (ret_int tt)
    PRE \[]
    POST \[= 3].
Proof using. xcf. xvals*. Qed.

Lemma ret_int_pair_spec :
  SPEC (ret_int_pair tt)
    PRE \[]
    POST \[= (3,4)].
Proof using. xcf_go*. Qed.

Lemma ret_poly_spec : forall A,
  SPEC (ret_poly tt)
    PRE \[]
    POST \[= @nil A].
Proof using. xcf. xgo*. Qed.


(********************************************************************)
(* ** Sequence *)

Axiom ret_unit_spec' : forall A (x:A),
  SPEC (ret_unit x)
    PRE \[]
    POST \[= tt]. (* (fun (_:unit) => \[]).*) (* same as (# \[]). *)

Hint Extern 1 (RegisterSpec ret_unit) => Provide ret_unit_spec'.


(* TODO
Lemma seq_ret_unit_spec :
  SPEC (seq_ret_unit tt)
    PRE \[]
    POST \[= tt].
Proof using.
  xcf.
  (* xlet. -- make sure we get a good error here *)
  xseq.
  xapp1.
  xapp2.
  dup 3.
  { xapp3_no_apply. apply S. }
  { xapp3_no_simpl. skip. skip. }
  { xapp3. }
  dup 4.
  { xseq. xapp. xapp. xsimpl. auto. }
  { xapp. intro_subst. xapp. }
  { xapps. xapps. }
  { xapps. xapps~. }
Abort.
*)


(********************************************************************)
(* ** Let-value *)

Lemma let_val_int_spec :
  SPEC (let_val_int tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf. xlet. xvals*.
  (* TODO dup 7.
  xval. xvals~.
  (* demos *)
  xval as r. xvals~.
  xval as r Er. xvals~.
  xvals. xvals~.
  xval_st (= 3). auto. xvals~.
  xval_st (= 3) as r. auto. xvals~.
  xval_st (= 3) as r Er. auto. xvals~. *)
Qed.

Lemma let_val_pair_int_spec :
  SPEC (let_val_pair_int tt)
    PRE \[]
    POST \[= (3,4)].
Proof using. xcf. xlet. xvals*. Qed.

(* TODO
Lemma let_val_poly_spec :
  SPEC (let_val_poly tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf. dup 3.
  { xval. xval. xsimpl. auto. }
  { xval as r. xvals~. }
  { xvals. xvals~. }
Qed.
*)


(********************************************************************)
(* ** Let-function *)

Lemma let_fun_const_spec :
  SPEC (let_fun_const tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf. dup 10.
  { xfun. apply Sf. xtag_pre_post. xvals~. }
  { xfun as g. apply Sg. skip. }
  { xfun as g. xapp. xval. skip. }
  { xfun as g G. apply G. skip. }
  { xfun_no_simpl (fun g => SPEC (g tt) \[] \[=3]).
    { xapp. skip. }
    { apply Sf. } }
  { xfun_no_simpl (fun g => SPEC (g tt) \[] \[=3]) as h.
    { apply Sh. skip. }
    { apply Sh. } }
  { xfun_no_simpl (fun g => SPEC (g tt) \[] \[=3]) as h H.
    { xapp. skip. }
    { xapp. } }
  { xfun (fun g => SPEC (g tt) \[] \[=3]).
    { xvals~. }
    { apply Sf. } }
  { xfun (fun g => SPEC (g tt) \[] \[=3]) as h.
    { skip. }
    { skip. } }
  { xfun (fun g => SPEC (g tt) \[] \[=3]) as h H.
    { skip. }
    { skip. } }
Qed.

Lemma let_fun_poly_id_spec :
  SPEC (let_fun_poly_id tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf. xfun. dup 2.
  { xapp. xval. xsimpl~. }
  { xapp1.
    xapp2.
    dup 5.
    { apply Spec. xvals. auto. }
    { xapp3_no_apply. 2:{ apply S. } xvals. auto. }
    { xapp3_no_simpl. xvals~. skip. skip. }
    { xapp3. xvals~. }
    { xapp. xval. xsimpl~. } }
Abort.

Lemma let_fun_poly_pair_homogeneous_spec :
  SPEC (let_fun_poly_pair_homogeneous tt)
    PRE \[]
    POST\[= (3,3)].
Proof using.
  xcf.
  xfun.
  xapp.
  xval.
  xsimpl~.
Qed.

Lemma let_fun_on_the_fly_spec :
  SPEC (let_fun_on_the_fly tt)
    PRE \[]
    POST\[= 4].
Proof using.
  xcf.
  xfun.
  xfun.
  xapp.
  xapp.
  xval.
  xsimpl~.
Qed.

Lemma let_fun_in_let_spec :
  SPEC (let_fun_in_let tt)
    PRE \[]
    POST (fun g => \[ forall A (x:A), SPEC (g x) \[] \[= x] ]).
Proof using.
  xcf. xlet (fun g => \[ forall A (x:A), SPEC (g x) \[] \[= x] ]).
    (* TODO: use [xpush] *)
  { xassert. { xval. }
    xfun. xvals. =>>. xapp. xvals~. }
  { =>> M. xvals~. }
Qed.

Lemma let_fun_in_let_spec' :
  SPEC (let_fun_in_let tt)
   PRE \[]
   POST (fun g => \[ forall A (x:A), SPEC (g x) \[] \[= x] ]).
Proof using.
  xcf.
Abort.



(********************************************************************)
(* ** Let-term *)

Lemma let_term_nested_id_calls_spec :
  SPEC (let_term_nested_id_calls tt)
    PRE \[]
    POST \[= 2].
Proof using.
  xcf.
  xfun (fun f => forall (x:int), SPEC (f x) \[] \[= x]). { xvals~. }
  xapps.
  xapps.
  xapps.
  xvals~.
Qed.

Lemma let_term_nested_pairs_calls_spec :
  SPEC (let_term_nested_pairs_calls tt)
    PRE \[]
    POST \[= ((1,2),(3,(4,5))) ].
Proof using.
  xcf.
  xfun (fun f => forall A B (x:A) (y:B), SPEC (f x y) \[] \[= (x,y)]). { xvals~. }
  xapps.
  xapps.
  xapps.
  xapps.
  xvals~.
Qed.

(********************************************************************)
(* ** Pattern-matching *)

Lemma match_pair_as_spec :
  SPEC (match_pair_as tt)
    PRE \[]
    POST \[= (4,(3,4))].
Proof using.
  xcf. dup 8.
  { xmatch. xvals*. }
  { xmatch_subst_alias. xvals*. }
  { xmatch_no_alias. xalias. xalias as L. skip. }
  { xmatch_no_cases. dup 6.
    { xmatch_case.
      { xvals*. }
      { xmatch_case. } }
    { xcase_no_simpl.
      { dup 3.
        { xalias. xalias. xval. xsimpl. xauto*. }
        { xalias as u U.
          xalias as v. skip. }
        { xalias_subst. xalias_subst. skip. } }
      { xdone. } }
    { xcase_no_simpl as E. skip. skip. }
    { xcase_no_intros. intros x y E. skip. intros F. skip. }
    { xcase. skip. skip. }
    { xcase as C. skip. skip.
      (* note: inversion got rid of C *)
    } }
  { xmatch_no_simpl_no_alias. skip. }
  { xmatch_no_simpl_subst_alias. skip. }
  { xmatch_no_intros. skip. }
  { xmatch_no_simpl. inverts C. skip. }
Qed.

Lemma match_nested_spec :
  SPEC (match_nested tt)
    PRE \[]
    POST \[= (2,2)::nil].
Proof using.
  xcf. xval. dup 3.
  { xmatch_no_simpl.
    { xvals*. }
    { false. (* note: [xvals] would produce a ununified [hprop].
     caused by [tryfalse] in [hextract_cleanup]. TODO: avoid this. *) } }
  { xmatch.
    xvals*.
    (* second case is killed by [xcase_post] *) }
  { xmatch_no_intros. skip. skip. }
Qed.


(********************************************************************)
(* ** Let-pattern *)

Lemma let_pattern_pair_int_spec :
  SPEC (let_pattern_pair_int tt)
    PRE \[]
    POST \[= 3].
Proof using. xcf. xmatch. xvals~. Qed.

Lemma let_pattern_pair_int_wildcard_spec :
  SPEC (let_pattern_pair_int_wildcard tt)
    PRE \[]
    POST \[= 3].
Proof using. xcf. xmatch. xvals~. Qed.


(********************************************************************)
(* ** Infix functions *)

Lemma infix_plus_plus_plus_spec : forall x y,
  SPEC (infix_plus_plus_plus__ x y)
    PRE \[]
    POST \[= x + y].
Proof using.
  xcf_go~.
Qed.

Hint Extern 1 (RegisterSpec infix_plus_plus_plus__) => Provide infix_plus_plus_plus_spec.

Lemma infix_aux_spec : forall x y,
  SPEC (infix_aux x y)
    PRE \[]
    POST \[= x + y].
Proof using.
  xcf. xapps~.
Qed.

Hint Extern 1 (RegisterSpec infix_aux) => Provide infix_aux_spec.

Lemma infix_minus_minus_minus_spec : forall x y,
  SPEC (infix_minus_minus_minus__ x y)
    PRE \[]
    POST \[= x + y].
Proof using.
  intros. xcf_show as S. rewrite S. xapps~.
Qed.



(********************************************************************)
(* ** Lazy binary operators *)

Lemma lazyop_val_spec :
  SPEC (lazyop_val tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf. xif. xvals~.
Qed.

(*
Ltac xauto_tilde ::= xauto_tilde_default ltac:(fun _ => auto_tilde).
*)

Lemma lazyop_term_spec :
  SPEC (lazyop_term tt)
    PRE \[] \[= 1].
Proof using.
  xcf. xfun (fun f => forall (x:int),
    SPEC (f x) \[]
    POST \[= isTrue (x = 0)]).
  { xvals*. }
  xapps.
  xlet \[=true].
  { dup 10.
    { xors. xapps. xsimpl~. subst. xclean. xauto*. }
    { xors \[=true]. xapps. xsimpl~. skip. }
    { xor \[=true]. hsimpl. xapps. xsimpl. skip. }
    { xif_no_simpl. skip. skip. }
    { xpost. xif_no_simpl \[= true]. skip. skip. skip. }
    { xpost. xif_no_simpl \[=true] as R.
      { xclean. false. }
      { xapps. xsimpl. subst. xclean. xauto*. }
     xsimpl~. }
    { xpost. xif_no_intros \[=true]. intros R. skip. skip. skip. }
    { xpost. xif_no_simpl_no_intros \[=true]. intros R. skip. skip. skip. }
    { xif. xvals. xapps. xsimpl. skip. }
    { xgo*. subst. xclean. auto. }
      (* todo: maybe extend [xauto_common] with [logics]? or would it be too slow? *)
  }
  intro_subst. xif. xvals~.
Qed.


Lemma lazyop_mixed_spec :
  SPEC (lazyop_mixed tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf.
  xfun (fun f => forall (x:int),
    SPEC (f x) \[] \[= isTrue (x = 0)]).
  { xvals*. }
  xlet \[= true].
  { xif. xapps. xors. xapps. xvals. autos*. }
  { intro_subst. xif. xvals~. }
Qed.




(********************************************************************)
(* ** Comparison operators *)

Lemma compare_poly_spec :
  SPEC (compare_poly tt)
    PRE \[]
    POST\[= tt].
Proof using.
  xcf.
  xlet_poly_keep (= true).
  { xapps. xpolymorphic_eq. xsimpl. subst r. rew_bool_eq~. }
  intro_subst.
  xapp. xpolymorphic_eq. intro_subst.
  xlet_poly_keep (= true).
  { xapps. xpolymorphic_eq. xsimpl. subst r. rew_bool_eq~. }
  intro_subst.
  xapp. xpolymorphic_eq. intro_subst.
  xvals~.
Qed.

Lemma compare_poly_custom_spec : forall (A:Type),
  forall (x:compare_poly_type_ A) (y : compare_poly_type_ int),
  SPEC (compare_poly_custom x y)
    PRE \[] \[=tt].
Proof using.
  xcf.
  xapp. xpolymorphic_eq. intro_subst.
  xapp. xpolymorphic_eq. intro_subst.
  xapp. xpolymorphic_eq. intro_subst.
  xapp. xpolymorphic_eq. intro_subst.
  xvals~.
Qed.

Lemma compare_physical_loc_func_spec :
  SPEC (compare_physical_loc_func tt)
    PRE \[]
    POST \[= tt].
Proof using.
  xcf. xapps. xapps.
  xapp. intro_subst.
  xapp. intro_subst.
  xfun.
  xapp_spec infix_eq_eq_gen_spec. intros.
  xlet (\[=1]).
    xif.
      xapps. xvals~.
      xvals~.
    intro_subst. xvals~.
Qed.

Fixpoint list_update (k:int) (v:int) (l:list (int*int)) :=
  match l with
  | nil => nil
  | (k2,v2)::t2 =>
     let t := (list_update k v t2) in
     let v' := (If k = k2 then v else v2) in
     (k2,v')::t
  end.

Lemma compare_physical_algebraic_spec :
  SPEC (compare_physical_algebraic tt)
    PRE \[]
    POST \[= (1,9)::(4,2)::(2,5)::nil ].
Proof using.
  xcf. xfun_ind (@list_sub (int*int)) (fun f =>
     forall (l:list (int*int)) (k:int) (v:int),
     app f [k v l] \[] \[= list_update k v l ]).
  { xmatch.
    { xvals~. }
    { xapps~. xvals. xif.
      { xvals. cases_if. auto. }
      { xapp_spec infix_emark_eq_gen_spec. intros M. xif.
        { xvals. case_if~. }
        { xvals. case_if~. rewrite~ M. } } } }
   { xapps. xsimpl. subst r. simpl. do 3 case_if. auto. }
Qed.



(********************************************************************)
(* ** Inlined total functions *)

Lemma inlined_fun_arith_spec :
  SPEC (inlined_fun_arith tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf.
  xval.
  xlet.
  (* note: division by a possibly-null constant is not inlined *)
  xapp_skip.
  xvals.
  skip.
Qed.

Lemma inlined_fun_other_spec : forall (n:int),
  SPEC (inlined_fun_others n) \[] \[= n+1].
Proof using.
  xcf. xval. xsimpl. simpl. auto.
Qed.


(********************************************************************)
(* ** Type annotations *)

Lemma annot_let_spec :
  SPEC (annot_let tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf_show.
  xcf. xval. xvals~.
Qed.

Lemma annot_tuple_arg_spec :
  SPEC (annot_tuple_arg tt)
    PRE \[] \[= (3, @nil int)].
Proof using.
  xcf_show.
  xcf. xvals~.
Qed.

Lemma annot_pattern_var_spec : forall (x:list int),
  SPEC (annot_pattern_var x)
    PRE \[]
    POST \[= If x = nil then 1 else 0].
Proof using.
  xcf_show.
  xcf. xmatch; xvals; case_if~.
Qed.

Lemma annot_pattern_constr_spec :
  SPEC (annot_pattern_constr tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf_show.
  xcf. xmatch; xvals~.
Qed.


(********************************************************************)
(* ** Polymorphic functions *)

Lemma top_fun_poly_id_spec : forall A (x:A),
  SPEC (top_fun_poly_id x)
    PRE \[] \[= x].  (* (fun r => \[r = x]). *)
Proof using.
  xcf. xvals~.
Qed.

Lemma top_fun_poly_proj1_spec : forall A B (x:A) (y:B),
  SPEC (top_fun_poly_proj1 (x,y))
    PRE \[]
    POST \[= x].
Proof using.
  xcf. xmatch. xvals~.
Qed.

Lemma top_fun_poly_proj1' : forall A B (p:A*B),
  SPEC (top_fun_poly_proj1 p)
    PRE \[]
    POST \[= Datatypes.fst p].
  (* TODO: maybe it's better if [fst] remains the one from Datatypes
     rather than the one from Pervasives? *)
Proof using.
  xcf. xmatch. xvals~.
Qed.

Lemma top_fun_poly_pair_homogeneous_spec : forall A (x y : A),
  SPEC (top_fun_poly_pair_homogeneous x y)
    PRE \[]
    POST \[= (x,y)].
Proof using.
  xcf. xvals~.
Qed.


(********************************************************************)
(* ** Polymorphic let bindings *)

Lemma let_poly_nil_spec : forall A,
  SPEC (let_poly_nil tt)
    PRE \[]
    POST \[= @nil A].
Proof using.
  xcf. dup 2.
  { xval. xvals. subst x. auto. }
  { xvals. xvals~. }
Qed.

Lemma let_poly_nil_pair_spec : forall A B,
  SPEC (let_poly_nil_pair tt)
    PRE \[]
    POST \[= (@nil A, @nil B)].
Proof using.
  xcf. xvals. xvals~.
Qed.

Lemma let_poly_nil_pair_homogeneous_spec : forall A,
  SPEC (let_poly_nil_pair_homogeneous tt)
    PRE \[]
    POST \[= (@nil A, @nil A)].
Proof using.
  xcf. xvals. xvals~.
Qed.

Lemma let_poly_nil_pair_heterogeneous_spec : forall A,
  SPEC (let_poly_nil_pair_heterogeneous tt)
    PRE \[]
    POST \[= (@nil A, @nil int)].
Proof using.
  xcf. xvals. xvals~.
Qed.



(********************************************************************)
(* ** Fatal Exceptions *)

Lemma exn_assert_false_spec : False ->
  SPEC (exn_assert_false tt)
    PRE \[]
    POST \[= tt].
Proof using.
  xcf. xfail. auto.
Qed.

Lemma exn_failwith_spec : False ->
  SPEC (exn_failwith tt)
    PRE \[]
    POST \[= tt].
Proof using.
  xcf. xfail. auto.
Qed.

Lemma exn_raise_spec : False ->
  SPEC (exn_raise tt)
    PRE \[] \[= tt].
Proof using.
  xcf. xfail. auto.
Qed.


(********************************************************************)
(* ** Assertions *)

Lemma assert_true_spec :
  SPEC (assert_true tt)
    PRE \[]
    POST \[= 3].
Proof using.
  dup 2.
  { xcf. xassert. { xvals~. } xvals~. }
  { xcf_go~. }
Qed.

Lemma assert_pos_spec : forall (x:int),
  x > 0 ->
  SPEC (assert_pos x)
    PRE \[]
    POST \[= 3].
Proof using.
  dup 2.
  { xcf. xassert. { xvals~. } xvals~. }
  { xcf_go~. }
Qed.

Lemma assert_same_spec : forall (x:int),
  SPEC (assert_same x x)
    PRE \[] \[= 3].
Proof using.
  dup 2.
  { xcf. xassert. { xvals~. } xvals~. }
  { xcf_go~. }
Qed.

Lemma assert_let_spec :
  SPEC (assert_let tt)
    PRE \[]
    POST \[= 3].
Proof using.
  dup 2.
  { xcf. xassert. { xvals. xvals~. } xvals~. }
  { xcf_go~. }
Qed.

Lemma assert_seq_spec :
  SPEC (assert_seq tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf. xapp. xassert.
    xapp. xvals.
  (* assert cannot do visible side effects,
     otherwise the semantics could change with -noassert *)
Abort.

Lemma assert_in_seq_spec :
  SPEC (assert_in_seq tt)
    PRE \[]
    POST \[= 4].
Proof using.
  xcf. xlet. xassert. { xvals. } xvals.
  xpulls. xvals~.
Qed.


(********************************************************************)
(* ** Conditionals *)

Lemma if_true_spec :
  SPEC (if_true tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf. xif. xval. xsimpl. auto.
Qed.

Lemma if_term_spec :
  SPEC (if_term tt)
    PRE \[]
    POST \[= 1].
Proof using.
  xcf. xfun. xapp. xval. xpulls.
  xif. xvals~.
Qed.

Lemma if_else_if_spec :
  SPEC (if_else_if tt)
    PRE \[]
    POST \[= 0].
Proof using.
  xcf. xfun (fun f => forall (x:int), SPEC (f x) \[] \[= false]).
    { xvals~. }
  xapps. xif. xapps. xif. xvals~.
Qed.

Lemma if_then_no_else_spec : forall (b:bool),
  SPEC (if_then_no_else b)
    PRE \[]
    POST (fun x => \[ x >= 0]).
Proof using.
  xcf. xapp.
  xseq. xif (Hexists n, \[n >= 0] \* r ~~> n).
   { xapp. xsimpl. math. }
   { xvals. math. }
   { (*xclean.*) xpull ;=>> P. xapp. xpulls. xsimpl. math. }
Qed.




(********************************************************************)
(* ** Evaluation order *)

Lemma order_app_spec :
  SPEC (order_app tt)
    PRE \[]
    POST \[= 2].
Proof using.
  dup 2.
    {
    xcf. xapps. xfun. xfun. xfun.
    xapps. { xapps. xvals~. } xpulls.
    xapps. { xassert. xapps. xvals~. xapps. xvals~. } xpulls.
    xapps. { xassert. xapps. xvals~. xfun.
      xvals~ (fun f => \[AppCurried f [a b] := (Ret (a + b)%I)] \* r ~~> 2). eauto. }
      xpull ;=> Hf.
    xapp. xvals~.
     (* TODO: can we make xval guess the post?
        The idea is to have [(Ret f) H ?Q] where [f:func] and [f] has a spec in hyps
        to instantiate Q with [fun f => H \* \[spec of f]].
        Then, the proof should just be [xgo~]. *)
  }
  { xcf_go*. skip. (* TODO *) }
Qed.

Lemma order_constr_spec :
  SPEC (order_constr tt)
    PRE \[]
    POST \[= 1::1::nil].
Proof using.
  xcf_go*.
Qed.
  (* Details:
  xcf. xapps. xfun. xfun.
  xapps. { xapps. xvals~. } xpulls.
  xapps. { xassert. xapps. xvals~. xvals~. } xpulls.
  xvals~.
  *)


Lemma order_list_spec :
  SPEC (order_list tt)
    PRE \[]
    POST \[= 1::1::nil].
Proof using. xcf_go*. Qed.

Lemma order_tuple_spec :
  SPEC (order_tuple tt)
    PRE \[]
    POST \[= (1,1)].
Proof using. xcf_go*. Qed.

(* TODO:
let order_array () =

let order_record () =
  let r = ref 0 in
  let g () = incr r; [] in
  let f () = assert (!r = 1); 1 in
  { nb = f(); items = g() }
*)




(********************************************************************)
(* ** While loops *)


Lemma while_decr_spec :
  SPEC (while_decr tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf. xapps. xapps. dup 9.
  { xwhile. intros R LR HR.
    cuts PR: (forall k, k >= 0 ->
      R (n ~~> k \* c ~~> (3-k)) (# n ~~> 0 \* c ~~> 3)).
    { xapplys PR. math. }
    intros k. induction_wf IH: (downto 0) k; intros Hk.
    applys (rm HR). xlet.
    { xapps. xvals. }
    { xpulls. xif.
      { xseq. xapps. xapps. simpl. xapplys IH. math. math. math. }
      { xvals. math. math. } }
    xapps. xsimpl~. }
  { xwhile as R. skip. skip. }
  { xwhile_inv (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)) (downto 0).
    { xsimpl*. math. }
    { intros S LS b k FS. xpull. intros. xlet.
      { xapps. xvals. }
      { xpulls. xif.
        { xseq. xapps. xapps. simpl. xapplys FS.
            hnf. math. math. eauto. math. eauto. eauto. }
        { xval. xsimpl. math. math. } } }
    { intros. xapps. xsimpl. math. } }
  { xwhile_inv_basic (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)) (downto 0).
    { xsimpl*. math. }
    { intros b k. xpull ;=> Hk Hb. xapps. xvals. xauto*. math. }
    { intros k. xpull ;=> Hk Hb. xapps. xapps. xsimpl. math. eauto. math. math. }
    { => k Hk Hb. xapp. xsimpl. math. } }
  { (* using a measure [fun k => abs k] *)
    xwhile_inv_basic (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)) (abs).
    skip. skip. skip. skip. }
  { (* defining the measure externally *)
    xwhile_inv_basic_measure (fun b m => Hexists k,
         \[m = k] \* \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)).
    skip. skip. skip. skip. }
  { (* defining the measure externally, downwards *)
    xwhile_inv_basic_measure (fun b m => Hexists i,
         \[m = 3-i] \* \[i <= 3] \* \[b = isTrue (i <= 3)]
                    \* n ~~> (3-i) \* c ~~> i).
    skip. skip. skip. skip. }
  { xwhile_inv_skip (fun b => Hexists k, \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)).
    skip. skip. skip. }
  { xwhile_inv_basic_skip (fun b => Hexists k, \[k >= 0] \* \[b = isTrue (k > 0)]
                         \* n ~~> k \* c ~~> (3-k)).
    skip. skip. skip. skip. }
Abort.


Lemma while_false_spec :
  SPEC (while_false tt)
    PRE \[]
    POST \[= tt].
Proof using.
  xcf. dup 2.
  { xwhile_inv_skip (fun (b:bool)  => \[b = false]). skip. skip. skip. }
  { xwhile_inv_basic (fun (b:bool) (_:unit) => \[b = false]) (fun (_ _:unit) => False).
    { intros_all. constructor. auto_false. }
    { xsimpl*. }
    { intros. xpulls. xvals~. }
    { intros. xpull. auto_false. }
    { xsimpl~. }
  }
Qed.



(*---- TODO: sort out


  Ltac auto_star ::= subst; intuition eauto with maths.

  Lemma while_decr_spec' :
    SPEC (while_decr tt) \[] \[= 3].
  Proof using.
    xcf.
    xapps. xapps.
    xwhile_inv_basic (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                           \* n ~~> k \* c ~~> (3-k)) (downto 0).
      xgo*.
      intros. xpull. intros. xgo*.
      intros. xpull. intros. xgo*.
      xgo*.
    intros. xpull. intros. xgo*.
  Qed.



  Proof using.
    xgo.
    xwhile_inv_basic (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                           \* n ~~> k \* c ~~> (3-k)) (downto 0).
      xgo*.
    xgo*.
  Qed.


  Lemma while_decr_spec :
    SPEC (while_decr tt) \[] \[= 3].
  Proof using.
    xcf.
    (* xlet. xapp1. xapp2. apply Spec. simpl. *)
    xapp.
    xapp.
    xseq.
    { xwhile_inv_basic (fun b k => \[k >= 0] \* \[b = isTrue (k > 0)]
                           \* n ~~> k \* c ~~> (3-k)) (downto 0).
      { xsimpl*. math. }
      { xtag_pre_post. intros b k. xpull ;=> Hk Hb. xapps. xvals. xauto*. math. }
      { xtag_pre_post. intros k. xpull ;=> Hk Hb. xapps. xapps. simpl. xsimpl. math. eauto. math. math. }
     }
   xpull. => k Hk Hb. fold_bool. xclean. xapp. xsimpl. math.
  Abort.

----*)



(********************************************************************)
(* ** For loops *)


Lemma for_to_incr_spec : forall (r:int), r >= 1 ->
  SPEC (for_to_incr r)
    PRE \[]
    POST \[= r].
Proof using.
  xcf. xapps. dup 7.
  { xfor. intros S LS HS.
    cuts PS: (forall i, (i <= r+1) -> S i (n ~~> (i-1)) (# n ~~> r)).
    { applys PS. math. }
    { intros i. induction_wf IH: (upto (r+1)) i. intros Li.
      applys (rm HS). xif.
      { xapps. applys_eq IH 2. hnf. math. math. fequals_rec. math. }
      { xvals. math. } }
    xapps. xsimpl~. }
  { xfor as S. skip. skip. }
  { xfor_inv (fun (i:int) => n ~~> (i-1)).
    { math. }
    { xsimpl. }
    { introv L. simpl. xapps. xsimpl. math. }
    xapps. xsimpl. math. }
  { xseq (# n ~~> r). xfor_inv (fun (i:int) => n ~~> (i-1)).
    skip. skip. skip. skip. skip. }
  { xseq (# n ~~> r). xfor_inv_void. skip. skip. skip. }
  { xfor_inv_void. skip. skip. }
  { try xfor_inv_case (fun (i:int) => n ~~> (i-1)).
    (* fails because no post condition *)
    xseq (# n ~~> r).
    { xfor_inv_case (fun (i:int) => n ~~> (i-1)).
      { xsimpl. }
      { introv L. xapps. xsimpl. math. }
      { xsimpl. math. }
      { math_rewrite (r = 0). xsimpl. } }
    { xapps. xsimpl~. } }
Abort.

Lemma for_to_incr_pred_spec : forall (r:int), r >= 1 ->
  SPEC (for_to_incr_pred r)
    PRE \[]
    POST \[= r].
Proof using.
  xcf. xapps. dup 7.
  { xfor. intros S LS HS.
    cuts PS: (forall i, (i <= r) -> S i (n ~~> i) (# n ~~> r)).
    { applys PS. math. }
    { intros i. induction_wf IH: (upto r) i. intros Li.
      applys (rm HS). xif.
      { xapps. applys_eq IH 2. hnf. math. math. auto. }
      { xvals. math. } }
    xapps. xsimpl~. }
  { xfor as S. skip. skip. }
  { xfor_inv (fun (i:int) => n ~~> i).
    { math. }
    { xsimpl. }
    { introv L. simpl. xapps. }
    xapps. xsimpl. math. }
  { xseq (# n ~~> r). xfor_inv (fun (i:int) => n ~~> i).
    skip. skip. skip. skip. skip. }
  { xseq (# n ~~> r). xfor_inv_void. skip. skip. skip. }
  { xfor_inv_void. skip. skip. }
  { try xfor_inv_case (fun (i:int) => n ~~> i).
    (* fails because no post condition *)
    xseq (# n ~~> r).
    { xfor_inv_case (fun (i:int) => n ~~> i).
      { xsimpl. }
      { introv L. xapps. }
      { xsimpl. }
      { math_rewrite (r = 0). xsimpl. } }
    { xapps. xsimpl~. } }
Abort.

Lemma for_downto_spec : forall (r:int), r >= 0 ->
  SPEC (for_downto r)
    PRE \[]
    POST \[= r].
Proof using.
  xcf. xapps. dup 7.
  { xfor_down. intros S LS HS.
    cuts PS: (forall i, (i >= -1) -> S i (n ~~> (r-1-i)) (# n ~~> r)).
    { xapplys PS. math. math. }
    { intros i. induction_wf IH: (downto (-1)) i. intros Li.
      applys (rm HS). xif.
      { xapps. xapplys IH. hnf. math. math. math. }
      { xvals. math. } }
    xapps. xsimpl~. }
  { xfor_down as S. skip. skip. }
  { xfor_down_inv (fun (i:int) => n ~~> (r-1-i)).
    { math. }
    { xsimpl. math. }
    { introv L. xapps. xsimpl. math. }
    xapps. xsimpl. math. }
  { xseq (# n ~~> r). xfor_down_inv (fun (i:int) => n ~~> (r-1-i)).
    skip. skip. skip. skip. skip. }
  { xseq (# n ~~> r). xfor_down_inv_void. skip. skip. skip. }
  { xfor_down_inv_void. skip. skip. }
  { try xfor_down_inv_case (fun (i:int) => n ~~> (r-1-i)).
    (* fails because no post condition *)
    xseq (# n ~~> r).
    { xfor_down_inv_case (fun (i:int) => n ~~> (r-1-i)).
      { xsimpl. math. }
      { introv L. xapps. xsimpl. math. }
      { xsimpl. math. }
      { math_rewrite (r = 0). xsimpl. } }
    { xapps. xsimpl~. } }
Abort.



(********************************************************************)
(* ** Recursive function *)

Require Import TLC.LibInt.

Lemma rec_partial_half_spec : forall k n,
  n = 2 * k -> k >= 0 ->
  SPEC (rec_partial_half n)
    PRE \[]
    POST \[= k].
Proof using.
  dup 2.
  { => k. induction_wf IH: (downto 0) k. xcf.
    xvals. xif.
    { xvals. math. }
    { xvals. xif.
      { xfail. math. }
      { xapps (k-1). math. math. math.
        xvals. math. } } }
  { xind_skip as IH. xcf. xvals. xif.
    { xgo~. math. }
    { xvals. xif. math. xapps (k-1). math. math. xvals. math. } }
Qed.


(* we can do a simple proof if we are ready to duplicate the verification of [g] *)
Lemma rec_mutual_f_and_g_spec_inlining :
     (forall (x:int), x >= 0 -> SPEC (rec_mutual_f x) PRE \[] \[= x])
  /\ (forall (x:int), x >= -1 -> SPEC (rec_mutual_g x) PRE \[] \[= x+1]).
Proof using.
  logic (forall (A B:Prop), A -> (A -> B) -> A /\ B).
  { intros x. induction_wf IH: (downto 0) x. intros Px.
    xcf. xif. xvals~. xlet.
    xcf. xapp. math. math. xpulls. xvals. math. }
  { intros Sg. introv Px. xcf. xapps. math. }
Qed.

(* the general approach is as follows, using a measure *)

Lemma rec_mutual_f_and_g_spec_measure :
     (forall (x:int), x >= 0 -> SPEC (rec_mutual_f x) PRE \[] POST \[= x])
  /\ (forall (x:int), x >= -1 -> SPEC (rec_mutual_g x) PRE \[] POST \[= x+1]).
Proof using.
  intros. cuts G: (forall (m:int),
     (forall x, -1 <= x /\ 2*x <= m -> SPEC (rec_mutual_f x) \[] \[= x])
  /\ (forall x, -1 <= x /\ 2*x+3 <= m -> SPEC (rec_mutual_g x) \[] \[= x+1])).
  { split; intros x P; specializes G (2*x+3);
      destruct G as [G1 G2]; xapp; try math. }
  => m. induction_wf IH: (downto (-1)) m.
    specializes IH (m-1). split; intros x (Lx&Px).
  { xcf. xif. xvals~. xapp. math. math.
    intro_subst. xvals. math. }
  { xcf. xapp. math. math. }
Qed.

(* the general approach is as follows, using a lexicographical order
 --- TODO: complete

Lemma rec_mutual_f_and_g_spec :
     (forall (x:int), x >= 0 -> SPEC (rec_mutual_f x) \[] \[= x])
  /\ (forall (x:int), x >= -1 -> SPEC (rec_mutual_g x) \[] \[= x+1]).
Proof using.
Search lexico2.
  set (R := lexico2 (downto (-1)) (downto (-1))).
  intros. cuts G: (forall p,
     (forall x, -1 <= x /\ R (x,0) p -> SPEC (rec_mutual_f x) \[] \[= x])
  /\ (forall x, -1 <= x /\ R (x+1,1) p -> SPEC (rec_mutual_g x) \[] \[= x+1])).
  { split; intros x P.
    { specializes G (x+1,0). destruct G as [G1 G2]. xapp.
      unfold R, lexico2. split. math. left. math. }
    { specializes G (x+2,0). destruct G as [G1 G2]. xapp.
      unfold R, lexico2. split. math. left. math. } }
  => p. induction_wf IH: R p. split; intros x (Lx&Px).
    destruct p as [a b]. unfolds R, @lexico2.
  { xcf. xif. xvals~. xapp (x-1,1).
(* todo: lexico2 is defined in a too strong way... *)
    right. math. math.
    intro_subst. xvals. math. }
  { xcf. xapp. math. math. }
Qed.
 *)



(********************************************************************)
(* ** Reference and garbage collection *)

Lemma ref_gc_spec :
  SPEC (ref_gc tt)
    PRE \[]
    POST \[= 3].
Proof using.
  xcf.
  xapp.
  xapp.
  xapp.
  xapp.
  dup 4.
  { xgc (_r3 ~~> 1). skip. }
  { xgc _r3. skip. }
  { xgc_but r1. skip. }
  { xlet (fun x => \[x = 2] \* r1 ~~> 1).
    { xapp. xapp. xsimpl~. } (* auto GC on r5 *)
    { intro_subst. xapps. xvals~. } (* auto GC on r1 *)
  }
Qed.

Lemma ref_gc_dep_spec : forall A (x:A),
  SPEC (ref_gc_dep x)
    PRE \[]
    POST (fun r => r ~~> x).
Proof using.
  xcf.
  xapp.
  xapp.
  dup 2.
  { xgc_post.
    xval.
    intros l.
    xsimpl.
    subst.
    xsimpl.
  }
  { xval. hsimpl. }
Qed.


(********************************************************************)
(* ** Records *)

Lemma sitems_build_spec : forall (A:Type) (n:int),
  SPEC (sitems_build n)
    PRE \[]
    POST (fun r => r ~> `{ nb' := n; items' := @nil A }).
Proof using. xcf_go~. Qed.

Lemma sitems_get_nb_spec : forall (A:Type) (r:loc) (n:int),
  app_keep sitems_get_nb [r]
     (r ~> `{ nb' := n; items' := @nil A })
     \[= n].
Proof using.
  dup 3.
  { intros A. xcf_show as R. applys (R A). xgo~. }
  { xcf_show as R. unfold sitems_ in R. specializes R unit. xgo~. }
  { xcf_go~. Unshelve. solve_type. }
Qed.  (* TODO: can we do better than a manual unshelve for dealing with unused type vars? *)

Lemma sitems_get_nb_spec' : forall (A:Type) (r:sitems_ A) (n:int),
  app_keep sitems_get_nb [r]
     (r ~> `{ nb' := n; items' := @nil A })
     \[= n].
Proof using.
  { xcf_go~. }
Qed.  (* TODO: can we do better than a manual unshelve for dealing with unused type vars? *)

Lemma sitems_incr_nb_spec : forall (A:Type) (L:list A) (r:loc) (n:int),
  SPEC (sitems_incr_nb r)
     (r ~> `{ nb' := n; items' := L })
     (# (r ~> `{ nb' := n+1; items' := L })).
Proof using.
  dup 2.
  { xcf. xapps. xapp. Unshelve. solve_type. }
  { xcf_go*. Grab Existential Variables. solve_type. }
Qed.

Lemma sitems_length_item_spec : forall (A:Type) (r:loc) (L:list A) (n:int),
  app_keep sitems_length_items [r]
     (r ~> `{ nb' := n; items' := L })
     \[= LibListZ.length L ].
Proof using.
  dup 2.
  { xcf. xapps. xvals. }
  { xcf_go*. }
Qed.

Definition Sitems A (L:list A) r :=
  Hexists n, r ~> `{ nb' := n; items' := L } \* \[ n = LibListZ.length L ].

(********************************************************************)
(* ** Recursive records definitions *)

Lemma create_cyclic_node_spec : forall (A:Type) (data:A),
  SPEC (create_cyclic_node data)
    PRE \[]
    POST (fun (r: loc) => r ~> `{ data' := data; prev' := r; next' := r }).
Proof using. xcf_go~. Qed.

(*
Section ProjLemma.
Variables (B:Type) (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).

Lemma proj_lemma_2 : forall  (R:forall (x1:A1) (x2:A2 x1) (t:B), hprop),
  (forall x1 x2 t, R x1 x2 t = t ~> R x1 x2).
Proof using. auto. Qed.

End ProjLemma.

Lemma Sitems_open_gen : True.
Proof.
  pose (@proj_lemma_2 Sitems).
Qed.
*)



Lemma sitems_push_spec : forall (A:Type) (r:loc) (L:list A) (x:A),
  SPEC (sitems_push x r)
    PRE (r ~> Sitems L) (# r ~> Sitems (x::L)).
Proof using.
  xcf. xunfold Sitems. xpull ;=> n E.
  xapps. xapps. xapps. xapp. xsimpl. rew_list; math.
Qed.

(* TODO: enéoncé spec dérivée pour
App' r`.nb'
en terme de Sitems

xapp_spec .. *)

(** Demo of [xopen] and [xclose] *)

Lemma Sitems_open : forall r A (L:list A),
  r ~> Sitems L ==>
  Hexists n, r ~> `{ nb' := n; items' := L } \* \[ n = LibListZ.length L ].
Proof using. intros. xunfolds~ Sitems. Qed.

Lemma Sitems_close : forall r A (L:list A) (n:int),
  n = LibListZ.length L ->
  r ~> `{ nb' := n; items' := L } ==>
  r ~> Sitems L.
Proof using. intros. xunfolds~ Sitems. Qed.

Arguments Sitems_close : clear implicits.
(* TODO comment
r ~> Sitems _
xopen r
xchange (Sitems_open r).
*)

Hint Extern 1 (RegisterOpen (Sitems _)) =>
  Provide Sitems_open.
Hint Extern 1 (RegisterClose (record_repr _)) =>
  Provide Sitems_close.

Lemma sitems_push_spec' : forall (A:Type) (r:loc) (L:list A) (x:A),
  SPEC (sitems_push x r)
    PRE (r ~> Sitems L) (# r ~> Sitems (x::L)).
Proof using.
  xcf. dup 2.
  { xopen r. xpull ;=> n E. skip. }
  { xopenx r ;=> n E. xapps. xapps. xapps. xapp.
    intros v.
    dup 4.
    { (* details *)
      xclose_show_core r. xchange H. skip. skip. (* demo *) }
    { (* with explicit arguments, incorrect instantiation *)
      xclose (>> r L n). auto. skip. skip. (* demo *) }
    { (* with explicit arguments, correct instantiation *)
      xclose (>> r (x::L) (n+1)). rew_list; math. xsimpl~. }
    { (* short form *)
      xclose r. rew_list; math. xsimpl~. } }
Qed.


(********************************************************************)
(* ** Arrays *)

Require Import Array_proof TLC.LibListZ.

Section Array.

Hint Extern 1 (@index _ (list _) _ _ _) => apply index_of_inbound : maths.
Hint Extern 1 (_ < length (?l[?i:=?v])) => rewrite length_update : maths.
Ltac auto_tilde ::= auto with maths.

Lemma array_ops_spec :
  SPEC (array_ops tt) \[] \[= 3].
Proof using.
  xcf.
  xapp. math. => L EL.
  asserts LL: (LibListZ.length L = 3).
  { subst. rewrite LibListZ.length_make; math. }
  xapps. { apply index_of_inbound; math. }
  xapp~.
  xapps~.
  xapps~.
  xapps~.
  xsimpl. subst. rew_array~.
Qed.

End Array.



(********************************************************************)
(* ** Integer arithmetics *)

(* land *)

Goal Z.land 7 28 = 4.
Proof. reflexivity. Qed.

Goal Z.land (-7) 28 = 24.
Proof. reflexivity. Qed.

Goal Z.land 7 (-28) = 4.
Proof. reflexivity. Qed.

Goal Z.land (-7) (-28) = -32.
Proof. reflexivity. Qed.

(* lor *)

Goal Z.lor 7 28 = 31.
Proof. reflexivity. Qed.

Goal Z.lor (-7) 28 = -3.
Proof. reflexivity. Qed.

Goal Z.lor 7 (-28) = -25.
Proof. reflexivity. Qed.

Goal Z.lor (-7) (-28) = -3.
Proof. reflexivity. Qed.

(* lxor *)

Goal Z.lxor 7 28 = 27.
Proof. reflexivity. Qed.

Goal Z.lxor (-7) 28 = -27.
Proof. reflexivity. Qed.

Goal Z.lxor 7 (-28) = -29.
Proof. reflexivity. Qed.

Goal Z.lxor (-7) (-28) = 29.
Proof. reflexivity. Qed.

(* lnot *)

Goal Zlnot 44 = -45.
Proof. reflexivity. Qed.

Goal Zlnot (-44) = 43.
Proof. reflexivity. Qed.

(* shiftl *)

Goal Z.shiftl 7 2 = 28.
Proof. reflexivity. Qed.

Goal Z.shiftl (-7) 2 = -28.
Proof. reflexivity. Qed.

(* shiftr *)

Goal Z.shiftr 7 2 = 1.
Proof. reflexivity. Qed.

Goal Z.shiftr 7 2 = 1.
Proof. reflexivity. Qed.

Goal Z.shiftr (-7) 2 = -2.
Proof. reflexivity. Qed.




(********************************************************************)
(********************************************************************)
(********************************************************************)

(* TODO LATER


(********************************************************************)
(* ** Partial applications *)

Lemma app_partial_2_1 () =
   let f x y = (x,y) in
   f 3
Proof using.
  xcf.
Qed.

Lemma app_partial_3_2 () =
   let f x y z = (x,z) in
   f 2 4
Proof using.
  xcf.
Qed.

Lemma app_partial_add () =
  let add x y = x + y in
  let g = add 1 in g 2
Proof using.
  xcf.
Qed.

Lemma app_partial_appto () =
  let appto x f = f x in
  let _r = appto 3 ((+) 1) in
  appto 3 (fun x -> x + 1)
Proof using.
  xcf.
Qed.

Lemma test_partial_app_arities () =
   let func4 a b c d = a + b + c + d in
   let f1 = func4 1 in
   let f2 = func4 1 2 in
   let f3 = func4 1 2 3 in
   f1 2 3 4 + f2 3 4 + f3 4
Proof using.
  xcf.
Qed.

Lemma app_partial_builtin () =
  let f = (+) 1 in
  f 2
Proof using.
  xcf.
Qed.


let app_partial_builtin_and () =
  let f = (&&) true in
  f false




(********************************************************************)
(* ** Over applications *)

Lemma app_over_id () =
   let f x = x in
   f f 3
Proof using.
  xcf.
Qed.





*)
