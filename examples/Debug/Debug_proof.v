Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Debug_ml.

(*Close Scope wp_scope.

Notation "'LetX' x ':=' F1 'in' F2" :=
 ( (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  only printing,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetX'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'").
*)

Notation "'int'" := (Z%type).

Lemma mkstruct_erase_trans : forall A1 (Q1:A1->hprop) A2 (Q2:A2->hprop) f1 f2,
  f1 Q1 ==> f2 Q2 ->
  f1 Q1 ==> mkstruct f2 Q2.
Proof using. introv M. unfold mkstruct. xchanges M. Qed.


Lemma MkStruct_erase_l_Post : forall (F1:Formula) A (EA:Enc A) (Q:A->hprop) (f2:formula),
  structural f2 ->
  (forall A1 (EA1:Enc A1) (Q1:A1->hprop), ^F1 Q1 ==> f2 (Post Q1)) ->
  ^(MkStruct F1) Q ==> f2 (Post Q).
Proof using.
  introv HS M1. unfold MkStruct.
  rewrites~ (>> eq_mkstruct_of_structural f2).
  unfold mkstruct. xpull. intros Q'. xchange M1. xsimpl.
  intros x. unfold Post. xpull. intros V E. xsimpl*.
Qed.


Lemma hand_weaken : forall H1 H2 H1' H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  hand H1 H2 ==> hand H1' H2'.
Proof using.
  introv M1 M2. do 2 rewrite hand_eq_forall_bool.
  applys himpl_hforall_r. intros b. applys himpl_hforall_l b.
  case_if*.
Qed.

Lemma hwand_weaken : forall H1 H2 H1' H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using. introv M1 M2. xsimpl. xchanges* M1. Qed.

Lemma himpl_hwand_hpure_l : forall (P:Prop) H1 H2,
  P ->
  H1 ==> H2 ->
  (\[P] \-* H1) ==> H2.
Proof using. introv HP M. rewrite* hwand_hpure_l. Qed.


(********************************************************************)
(** ** Primitive ops *)

Axiom triple_infix_plus__ : forall (n1 n2:int),
  triple (infix_plus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).


Axiom triple_infix_amp_amp__ : forall (b1 b2:bool),
  triple (infix_amp_amp__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 && b2)]).

Axiom triple_infix_bar_bar__ : forall (b1 b2:bool),
  triple (infix_bar_bar__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 || b2)]).



(********************************************************************)
(** ** Formula_formula *)

(*
Axiom triple_app_fix_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
*)

(*
From TLC Require Import LibListExec.
*)

Lemma triple_apps_funs' : forall F vs ts xs t H (Q:val->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (length vs) ->
  H ==> (wpgen (LibListExec.combine xs vs) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_funs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rewrite LibListExec.combine_eq in M; auto. (* rew_list_exec in M. *) 
  applys* triple_apps_funs. rewrite~ <- isubstn_eq_substn.
  applys* triple_isubst_of_wpgen.
Qed.

Lemma triple_apps_fixs' : forall F vs ts xs t H (Q:val->hprop) (f:var),
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec (bind_var f) xs (length vs) ->
  H ==> (wpgen (LibListExec.combine (f::xs) (F::vs)) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Proof.
  introv HF Hvs Hxs M. applys triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_fixs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rewrite LibListExec.combine_eq in M; rew_list; auto. (* rew_list_exec in M. *) 
  applys* triple_apps_fixs. rewrite <- isubstn_eq_substn; [|rew_list~].
  applys* triple_isubst_of_wpgen.
Qed.
(* LATER: simplify proof of xwp_lemma_fixs using the above *)


Definition Formula_formula (F1:Formula) (f1:formula) : Prop :=
  forall A (EA:Enc A) (Q:A->hprop), ^F1 Q ==> f1 (Post Q).

Lemma Formula_formula_intro_gc : forall (F1:Formula) (f1:formula) A (EA:Enc A) (Q:A->hprop),
  Formula_formula F1 f1 ->
  ^F1 (Q \*+ \GC) ==> f1 (Post Q \*+ \GC).
Proof using. Admitted.

Transparent Triple.

Lemma Formula_formula_wp : forall t,
  Formula_formula (Wp t) (wp t).
Proof using.
  intros. hnf. intros. unfold wp, Wp, Weakestpre, Triple.
  applys himpl_refl.
Qed.

(*
Lemma Formula_formula_wp' : forall t t',
  t = t' ->
  Formula_formula (Wp t) (wp t').
Proof using.
  introv ->. applys* Formula_formula_wp.
Qed.
*)

Lemma Formula_formula_mkstruct : forall F1 f1,
  Formula_formula F1 f1 ->
  Formula_formula (MkStruct F1) (mkstruct f1).
Proof using.
  introv M. hnf. intros.
  applys MkStruct_erase_l_Post. applys structural_mkstruct.
  intros. applys himpl_trans; [ | eapply mkstruct_erase ]. applys M.
Qed.


(*
Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkstruct (fun Q =>
  F1 (fun X => F2of X Q)).

Definition Wpgen_let_trm (F1:Formula) A1 {EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \exists (Q1:A1->hprop), ^F1 Q1 \* \[forall (X:A1), Q1 X ==> ^(F2of X) Q]).
*)

Lemma Formula_formula_inv : forall F f A {EA:Enc A} (Q:A->hprop) q,
  Formula_formula F f ->
  (Post Q) ===> q ->
  structural f ->
  ^F Q ==> f q.
Proof using.
  introv M W S. xchange M. applys* structural_conseq W.
Qed.

Lemma Formula_formula_let : forall F1 f1 A1 {EA1:Enc A1} (F2of:A1->Formula) f2of,
  (Formula_formula F1 f1) ->
  (forall (X:A1), Formula_formula (F2of X) (f2of (enc X))) ->
  structural f1 ->
  Formula_formula (Wpgen_let_trm F1 F2of) (wpgen_let f1 f2of).
Proof using.
  introv M1 M2 S1.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. xpull. intros Q1 HQ1. applys* Formula_formula_inv M1.
  intros x. unfold Post at 1. xpull. intros X1 ->.
  xchange HQ1. applys M2.
Qed.

Lemma Formula_formula_app : forall (A:Type) {EA:Enc A} (f:val) (Vs:dyns) (vs:vals),
  LibList.map (fun V => trm_val (dyn_to_val V)) Vs = trms_vals vs ->
  Formula_formula (@Wpgen_app A EA f Vs) (wpgen_app f vs).
Proof using.
  introv E. hnf. intros.
  unfolds Wpgen_app, wpgen_app.
  applys Formula_formula_mkstruct.
  unfold Trm_apps. rewrite <- E.
  applys Formula_formula_wp.
Qed.

Lemma Formula_formula_let_inlined_fun : forall F1 f1of (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Formula_formula F1 (f1of r) ->
  Formula_formula F1 (wpgen_let (wpgen_app f vs) f1of).
Proof using.
  introv Hf M1. hnf. intros.
  unfold wpgen_let. applys mkstruct_erase_trans.
  unfold wpgen_app. applys mkstruct_erase_trans.
  rewrite <- triple_eq_himpl_wp. applys triple_conseq_frame Hf. xsimpl.
  xpull. intros x ->. applys M1.
Qed.


Lemma Formula_formula_if : forall F1 f1 F2 f2 b (v:val),
  v = ``b ->
  (Formula_formula F1 f1) ->
  (Formula_formula F2 f2) ->
  Formula_formula (Wpgen_if b F1 F2) (wpgen_if_val v f1 f2).
Proof using.
  introv E M1 M2.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. subst v. xsimpl b. auto.
  case_if. { applys M1. } { applys M2. }
Qed.




(*
Wpgen_let_trm (Wpgen_app int infix_emark__ ((Dyn r) :: nil))
  (fun x0__ : int => Wpgen_app unit infix_colon_eq__ ((Dyn r) :: (Dyn x0__ + n) :: nil)) EA
  (Q \*+ \GC) ==>
wpgen_let (wpgen_app infix_emark__ ``[ r])
  (fun X : val =>
   wpgen_let (wpgen_app infix_plus__ (X :: ``[ n]))
     (fun v1 : val => wpgen_app infix_colon_eq__ (``r :: v1 :: nil))) (Post Q \*+ \GC)
*)


Lemma Triple_of_CF_and_Formula_formula_funs : forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F xs Vs vs t,
  F = val_funs xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_funs_exec xs (LibListExec.length vs) ->
  Formula_formula F1 (wpgen (LibListExec.combine xs vs) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_funs' EF Evs Hxs.
  xchange HF1. applys Formula_formula_intro_gc Ff.
Qed.

Lemma Triple_of_CF_and_Formula_formula_fixs : forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F (f:var) xs Vs (vs:vals) t,
  F = val_fixs f xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_fixs_exec (bind_var f) xs (LibListExec.length vs) ->
  Formula_formula F1 (wpgen (LibListExec.combine (f::xs) (F::vs)) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_fixs' EF Evs Hxs.
  xchange HF1. applys Formula_formula_intro_gc Ff.
Qed.

Lemma Formula_formula_val : forall A (EA:Enc A) (V:A) v,
  v = enc V ->
  Formula_formula (Wpgen_val V) (wpgen_val v).
Proof using.
  introv M. applys Formula_formula_mkstruct. hnf. intros A' EA' Q.
  unfold PostCast. xpull. intros V' E.
  unfold Post. xsimpl V'. subst*.
Qed.


Lemma Formula_formula_inlined_fun : forall F1 (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Formula_formula F1 (wpgen_val r) ->
  Formula_formula F1 (wpgen_app f vs).
Proof using.
  introv Hf M1. hnf. intros.
  unfold wpgen_app. xchange M1. applys mkstruct_weaken. clear Q. intros Q.
  rewrite <- triple_eq_himpl_wp. applys triple_conseq_frame Hf. xsimpl.
  intros x. xpull; intros ->. xsimpl.
Qed.

Lemma Formula_formula_case : forall F1 f1 F2 f2 (P1 P2:Prop),
  (P2 -> P1) ->
  (Formula_formula F1 f1) ->
  (P1 -> Formula_formula F2 f2) ->
  Formula_formula (Wpgen_case F1 P1 F2) (wpgen_case_val f1 P2 f2).
Proof using.
  introv HP M1 M2.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. applys hand_weaken.
  { applys M1. }
  { xsimpl. intros HP2. lets HP1: HP HP2.
    applys himpl_hwand_hpure_l.
    { applys* HP. } { applys* M2. } }
Qed.

Lemma Formula_formula_fail :
  Formula_formula Wpgen_fail wpgen_fail.
Proof using.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. xsimpl.
Qed.

Lemma Formula_formula_fail_false : forall F,
  False ->
  Formula_formula F wpgen_fail.
Proof using. intros. false. Qed.


(********************************************************************)

Ltac xwpgen_simpl :=
  cbn beta delta [
  LibListExec.app LibListExec.combine LibListExec.rev LibListExec.fold_right LibListExec.map
  Datatypes.app List.combine List.rev List.fold_right List.map
  wpaux_var
  (* wpgen Wpaux_apps Wpaux_constr Wpaux_var Wpaux_match *)
  hforall_vars forall_vars
  trm_to_pat patvars patsubst combiner_to_trm
  Ctx.app Ctx.empty Ctx.lookup Ctx.add Ctx.rev
  Ctx.rem Ctx.rem_var Ctx.rem_vars Ctx.combine isubst
  var_eq eq_var_dec
  string_dec string_rec string_rect
  sumbool_rec sumbool_rect
  Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect ] iota zeta.

Ltac cf_main :=
  let CF := fresh "CF" in
  hnf; introv CF; 
  first [ applys Triple_of_CF_and_Formula_formula_funs (rm CF); [ reflexivity | | | ]
        | applys Triple_of_CF_and_Formula_formula_fixs (rm CF); [ reflexivity | | | ] ];
  try reflexivity;
  unfold Wptag, dyn_to_val; simpl; xwpgen_simpl.


Lemma triple_builtin_search_1 : forall F ts v1 H (Q:val->hprop),
  triple (combiner_to_trm (combiner_nil (trm_val F) (trm_val v1))) H Q ->
  combiner_to_trm (combiner_nil (trm_val F) (trm_val v1)) = (trm_apps (trm_val F) ts) ->
  triple (trm_apps (trm_val F) ts) H Q.
Proof using. introv M <-. auto. Qed.

Lemma triple_builtin_search_2 : forall F ts v1 v2 H (Q:val->hprop),
  triple (combiner_to_trm (combiner_cons (combiner_nil (trm_val F) (trm_val v1)) (trm_val v2))) H Q ->
  combiner_to_trm (combiner_cons (combiner_nil (trm_val F) (trm_val v1)) (trm_val v2)) = (trm_apps (trm_val F) ts) ->
  triple (trm_apps (trm_val F) ts) H Q.
Proof using. introv M <-. auto. Qed.

Hint Resolve triple_infix_plus__ triple_infix_bar_bar__ triple_infix_amp_amp__
 : triple_builtin.

Ltac cf_triple_builtin :=
  first [ eapply triple_builtin_search_2; [  eauto with triple_builtin | reflexivity ]
        | eapply triple_builtin_search_1; [  eauto with triple_builtin | reflexivity ] ].



Ltac cf_app :=
  eapply Formula_formula_app; [ reflexivity ].

Ltac cf_let := 
  eapply Formula_formula_let; [ | | applys structural_mkstruct ].

Ltac cf_val :=
  eapply Formula_formula_val; [ reflexivity ].

Ltac cf_inlined :=
  eapply Formula_formula_inlined_fun; [ try cf_triple_builtin | ].

Ltac cf_letinlined :=
  eapply Formula_formula_let_inlined_fun; [ try cf_triple_builtin | ].

Ltac cf_if :=
  eapply Formula_formula_if; [ reflexivity | | ].

(********************************************************************)
(** ** CF proof for polydepth *)

(*
let rec polydepth : 'a. 'a poly -> int = fun s ->
  match s with
  | Empty _ -> 0
  | Pair s2 -> 1 + polydepth s2
*)

Lemma polydepth_cf_def : polydepth_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_case.
  { intros HN. hnf. intros. applys Enc_neq_inv. applys HN. }
  { clears A. unfold Formula_formula. intros A EA Q.
    xsimpl. introv E. destruct s; tryfalse.
    applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ]. simpls. inverts E.
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1.
    clears A. unfold Formula_formula. intros A EA Q.
    applys Formula_formula_case.
    { intros HN. hnf. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct s as [|s2]. 1:{ false. }
      rew_enc in E. inverts E.
      applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros n. applys Formula_formula_inlined_fun; [ applys triple_infix_plus__ |  ].
        applys Formula_formula_val; [ reflexivity ]. } }
    { intros N2. applys Formula_formula_fail_false.
      destruct s; try false*. } }
Qed.


(********************************************************************)
(** ** CF proof for bools *)

(*
let bools b =

  if true then b || false else b && true
*)

Lemma bools_cf_def : bools_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_if; [ reflexivity | | ].
  { applys Formula_formula_inlined_fun; [ applys triple_infix_bar_bar__ | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { applys Formula_formula_inlined_fun; [ applys triple_infix_amp_amp__ | ].
    applys Formula_formula_val; [ reflexivity ]. }
Qed.

Lemma bools_cf_def' : bools_cf_def__.
Proof using.
  cf_main. cf_if.
  { cf_inlined. cf_val. }
  { cf_inlined. cf_val. }
Qed.



(********************************************************************)
(** ** CF proof for pair_swap *)

(*
let pair_swap (x,y) =
  (y,x)
*)

Lemma pair_swap_cf_def : pair_swap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { clears A. unfold Formula_formula. intros A EA Q.
    xsimpl. intros x y E.
    destruct x0__ as [X Y]. rew_enc in E. inverts E.
    do 2 applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_val; [ reflexivity ]. }
  { intros N. applys Formula_formula_fail_false.
    destruct x0__. false N. reflexivity. }
Qed.



(********************************************************************)
(** ** CF proof for list map *)

(*
let rec listmap f l =
  match l with
  | [] -> []
  | x::t -> f x :: listmap f t
*)

Lemma listmap_cf_def : listmap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { clears A. unfold Formula_formula. intros A EA Q.
    xsimpl. intros HN. destruct l. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1.
    clears A. unfold Formula_formula. intros A EA Q.
   applys Formula_formula_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros t2.
        applys Formula_formula_let; [ | | applys structural_mkstruct ].
        { applys Formula_formula_app; [ reflexivity ]. }
        { intros r. applys Formula_formula_val; [ reflexivity ]. } } }
    { intros N2. applys Formula_formula_fail_false.
      destruct l; try false*. } }
Qed.



(********************************************************************)
(** ** CF proof for custom list map *)

(*
type 'a mylist = Nil | Cons of 'a * 'a mylist

let rec mymap f l =
  match l with
  | Nil -> Nil
  | Cons(x,t) -> Cons (f x, mymap f t)
*)

Lemma mymap_cf_def : mymap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { clears A. unfold Formula_formula. intros A EA Q.
    xsimpl. intros HN. destruct l. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1.
    clears A. unfold Formula_formula. intros A EA Q.
   applys Formula_formula_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros t2.
        applys Formula_formula_let; [ | | applys structural_mkstruct ].
        { applys Formula_formula_app; [ reflexivity ]. }
        { intros r. applys Formula_formula_val; [ reflexivity ]. } } }
    { intros N2. applys Formula_formula_fail_false.
      destruct l; try false*. } }
Qed.


(********************************************************************) 
(** ** CF proof for id *)

(*
let id x = x
*)

Lemma id_cf_def : id_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_val; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for apply *)

(*
let apply f x = f x
*)

Lemma apply_cf_def : apply_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_app; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for idapp *)

(*
let idapp =
  let a = id 1 in
  let b = id true in
  2
*)

Lemma idapp_cf_def : idapp_cf_def__.
Proof using.
  cf_main.
  (* hnf. introv CF. applys Triple_of_CF_and_Formula_formula (rm CF); try reflexivity.
  unfold Wptag, dyn_to_val; simpl. xwpgen_simpl. *)
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros a.
    applys Formula_formula_let; [ | | applys structural_mkstruct ].
    { applys Formula_formula_app; [ reflexivity ]. }
    { intros b.
      applys Formula_formula_val; [ reflexivity ]. } }
Qed.


(********************************************************************)
(** ** CF proof for f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)

Lemma f_cf_def : f_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros X.
    applys Formula_formula_let_inlined_fun; [ applys triple_infix_plus__ | ].
    applys Formula_formula_app; [ reflexivity ]. }
Qed.



(********************************************************************)
(** ** Verification of f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)


Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.


(*

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)

















