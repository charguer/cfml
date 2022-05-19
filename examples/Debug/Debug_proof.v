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
(** ** Function calls: [xapp] *)

Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.

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


Lemma f_cf_def_proof : f_cf_def__.
Proof using.
  hnf. introv CF.
  unfold Triple.
  unfold Trm_apps. rew_listx. rew_enc_dyn.
  eapply triple_apps_funs; try reflexivity. simpl.
  xchange (rm CF). unfold Wptag.
  apply Formula_formula_intro_gc.
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros X.
    applys Formula_formula_let_inlined_fun; [ applys triple_infix_plus__ | ].
    applys Formula_formula_app; [ reflexivity ]. }
Qed.



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

