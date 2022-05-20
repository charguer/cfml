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

(********************************************************************)
(** ** Formula_formula *)

(*
Axiom triple_app_fix_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
*)

Lemma triple_apps_funs : forall F vs ts xs t H (Q:val->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (length vs) ->
  H ==> (wpgen (LibListExec.combine xs vs) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Admitted.

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




(*
Wpgen_let_trm (Wpgen_app int infix_emark__ ((Dyn r) :: nil))
  (fun x0__ : int => Wpgen_app unit infix_colon_eq__ ((Dyn r) :: (Dyn x0__ + n) :: nil)) EA 
  (Q \*+ \GC) ==>
wpgen_let (wpgen_app infix_emark__ ``[ r])
  (fun X : val =>
   wpgen_let (wpgen_app infix_plus__ (X :: ``[ n]))
     (fun v1 : val => wpgen_app infix_colon_eq__ (``r :: v1 :: nil))) (Post Q \*+ \GC)
*)

Axiom triple_infix_plus__ : forall (n1 n2:int),
  triple (infix_plus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).


Lemma Triple_of_CF_and_Formula_formula : forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F xs Vs vs t,
  H ==> ^F1 (Q \*+ \GC) ->
  F = val_funs xs t ->
  trms_to_vals (map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_funs_exec xs (LibListExec.length vs) ->
  Formula_formula F1 (wpgen (LibListExec.combine xs vs) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv HF1 EF Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
   applys triple_apps_funs EF Evs Hxs. 
  xchange HF1. applys Formula_formula_intro_gc Ff.
Qed.

Lemma Formula_formula_val : forall A (EA:Enc A) (V:A) v,
  v = enc V ->
  Enc_injective EA ->
  Formula_formula (Wpgen_val V) (wpgen_val v).
Proof using.
  introv M IEA. applys Formula_formula_mkstruct.
  hnf. intros A' EA' Q.
(*
  xchange qimpl_PostCast_l. eapp
 unfold PostCast. xpull. intros V' E.
 eapply IEA. hnf.
  Search PostCast. unfold Wpgen_val. hnf.
Qed.

qimpl_PostCast_l: forall [A : Type] {EA : Enc A} [Q : A -> hprop], Enc_injective EA -> 
*)
Admitted.

Search Enc_injective.

(********************************************************************)
(** ** CF proof for id *)

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


Lemma id_cf_def_proof : id_cf_def__.
Proof using.
  hnf. introv CF. applys Triple_of_CF_and_Formula_formula (rm CF); try reflexivity.
  unfold Wptag, dyn_to_val; simpl.
  xwpgen_simpl.
  
  hnf. introv CF. applys Triple_of_CF_and_Formula_formula CF; try reflexivity.
  unfold Wptag.
  apply Formula_formula_intro_gc.
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros X.
    applys Formula_formula_let_inlined_fun; [ applys triple_infix_plus__ | ].
    applys Formula_formula_app; [ reflexivity ]. }
Qed.

wpgen (LibListExec.combine ("x" :: nil) (List.rev ``[ x])) "x"
H0 : forall (F : val) (vs : vals) (ts : trms) (xs : list var) (t : trm) (H : hprop) (Q : val -> hprop),


  


(********************************************************************)
(** ** CF proof for idapp *)

(********************************************************************)
(** ** CF proof for apply *)

(*
let id x = x

let idapp =
  let a = id 1 in
  let b = id true in
  2

let apply f x = f x
*)


(********************************************************************)
(** ** CF proof for f *)


Lemma f_cf_def_proof : f_cf_def__.
Proof using.
  hnf. introv CF. applys Triple_of_CF_and_Formula_formula (rm CF); try reflexivity.
  unfold Wptag, dyn_to_val; simpl.
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros X.
    applys Formula_formula_let_inlined_fun; [ applys triple_infix_plus__ | ].
    applys Formula_formula_app; [ reflexivity ]. }
Qed.



(********************************************************************)
(** ** Verification of f *)


Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.




(*
let f r n =
  let x = !r in
  r := x + n

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)

