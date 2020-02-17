(**

Separation Logic Foundations

Chapter: "Rich".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SLFExtra TLCbuffer.
From Sep Require SLFBasic.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Types b : bool.
Implicit Types L : list val.


(* ####################################################### *)
(** * Chapter in a rush *)

(** This chapter introduces support for additional language constructs:
    - while-loops and for-loops,
    - assertions,
    - n-ary functions.

    Regarding loops, we explain why conventional-style reasoning rules
    based on loop invariants are limited in that they prevent useful
    applications of the frame rule. We present alternative reasoning rules
    compatible with the frame rule, and demonstrate their benefits on
    practical examples.

    Regarding assertions, we present a reasoning rule such that:
    - assertions may be expressed in terms of mutable data, and possibly
      to perform local side-effects, and
    - the program remains correct whether assertions are executed or not.

    Regarding n-ary functions, that is, functions with several arguments
    there are essentially three possible approaches:

    - native n-ary functions, e.g., [function(x, y) { t } ] in C syntax;
    - curried functions, e.g., [fun x => fun y => t] in OCaml syntax;
    - tupled functions, e.g., [fun (x,y) => t] in OCaml syntax.

    In this chapter, we present reasoning rules for curried functions and
    for native n-ary functions. The former requires minimal extension to the
    syntax and semantics of our language. The latter corresponds to the most
    practical solution from an engineering perspective.

*)


(* ####################################################### *)
(** ** If with a term as condition *)

Parameter eval_if_trm : forall s1 s2 s3 v b t0 t1 t2,
  eval s1 t0 s2 (val_bool b) ->
  eval s2 (if b then t1 else t2) s3 v ->
  eval s1 (trm_if t0 t1 t2) s3 v.

Parameter eval_if_trm' : forall s1 s2 s3 v0 v t0 t1 t2,
  eval s1 t0 s2 v0 ->
  eval s2 (trm_if v0 t1 t2) s3 v ->
  eval s1 (trm_if t0 t1 t2) s3 v.

Lemma hoare_if_trm' : forall Q' t0 t1 t2 H Q,
  hoare t0 H Q' ->
  (forall v, hoare (trm_if v t1 t2) (Q' v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros s1 K1. lets (s2&v0&R2&K2): M1 K1.
  forwards (s3&v&R3&K3): M2 K2. exists s3 v. splits.
  { applys eval_if_trm' R2 R3. }
  { applys K3. }
Qed.

Lemma triple_if_trm' : forall Q' t0 t1 t2 H Q,
  triple t0 H Q' ->
  (forall v, triple (trm_if v t1 t2) (Q' v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_if_trm' (Q' \*+ HF).
  { applys hoare_conseq. applys M1 HF. { xsimpl. } { xsimpl. } }
  { intros v. applys M2. }
Qed.

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

Lemma wp_if_trm' : forall t0 t1 t2 Q,
  wp t0 (fun v => wp (trm_if v t1 t2) Q) ==> wp (trm_if t0 t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl; intros H M H'. applys hoare_if_trm'.
  { applys M. }
  { intros v. simpl. rewrite hstar_hexists. applys hoare_hexists. intros HF.
    rewrite (hstar_comm HF). rewrite hstar_assoc. applys hoare_hpure.
    intros N. applys N. }
Qed.



(* ####################################################### *)
(** ** Limitation of loop invariants in Separation Logic *)


(* ####################################################### *)
(** ** Separation-Logic-friendly reasoning rule for while-loops *)

Module WhileLoops.

Parameter trm_while : trm -> trm -> trm.

Parameter eval_while : forall s1 s2 t1 t2 v,
  eval s1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) s2 v ->
  eval s1 (trm_while t1 t2) s2 v.

Lemma hoare_while : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  introv M K. forwards* (s'&v&R1&K1): M.
  exists s' v. splits*. { applys* eval_while. }
Qed.

Lemma triple_while : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. intros H'. apply hoare_while. applys* M.
Qed.

Lemma triple_while_abstract : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. applys M. introv K. applys triple_while. applys K.
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

Lemma triple_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
  (forall t b X,
    (forall b' Y, R Y X -> triple t (I b' Y) Q) ->
    triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) (\exists b X, I b X) Q.
Proof using.
  introv WR M. applys triple_hexists. intros b0. applys triple_hexists. intros X0.
  gen b0. induction_wf IH: WR X0. intros. applys triple_while.
  applys M. intros b' Y HR'. applys IH HR'.
Qed.

Lemma triple_while_inv_conseq_frame : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' Y, R Y X -> triple t (I b' Y) Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q (* add [\*+ \GC] for affine logic *) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH M WQ. applys triple_conseq_frame WH WQ.
  applys triple_while_inv WR M.
Qed.


Parameter triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.

Lemma triple_while_inv_conseq_frame_gc : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' Y, R Y X -> triple t (I b' Y) Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q \*+ \GC ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH M WQ. applys triple_conseq_frame_hgc WH WQ.
  applys triple_while_inv WR M.
Qed.


Lemma wp_while_inv_conseq : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
     (\exists b X, I b X)
  \* \[forall t b X,
      (forall b' Y, R Y X -> (I b' Y) ==> wp t Q) ->
       (I b X) ==> wp (trm_if t1 (trm_seq t2 t) val_unit) Q]
   ==> wp (trm_while t1 t2) Q.
Proof using.
  introv WR. sets H: (\exists b X, I b X). xpull. intros M.
  rewrite wp_equiv. applys triple_while_inv WR.
  introv N. rewrite <- wp_equiv. applys M.
  introv HR. rewrite wp_equiv. applys N HR.
Qed.

(*
[[
   mkstruct_sound:
     (forall Q, F Q ==> wp t Q)
     (forall Q, mkstruct F Q ==> wp t Q)
]]
*)

Close Scope wp_scope.


Lemma wp_eq_mkstruct_wp : forall t,
  wp t = mkstruct (wp t).
Proof using.
  intros. applys fun_ext_1. intros Q. applys himpl_antisym.
  { applys mkstruct_erase. }
  { lets R: mkstruct_sound. unfolds formula_sound. applys R. xsimpl. }
Qed.



Definition wpgen_if_trm (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

Definition wpgen_while (F1 F2:formula) : formula := fun Q =>
  \forall R,
     \[forall Q',    mkstruct (wpgen_if_trm F1 (mkstruct (wpgen_seq F2 (mkstruct R))) (mkstruct (wpgen_val val_unit))) Q'
                 ==> mkstruct R Q']
  \-* (mkstruct R Q).

Parameter wpgen_while_eq : forall E t1 t2,
  wpgen E (trm_while t1 t2) = mkstruct (wpgen_while (wpgen E t1) (wpgen E t2)).

Lemma wp_while : forall t1 t2 Q,
      wp (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) Q
  ==> wp (trm_while t1 t2) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hoare_while. applys M.
Qed.

Lemma mkstruct_monotone : forall F1 F2 Q,
  (forall Q, F1 Q ==> F2 Q) ->
  mkstruct F1 Q ==> mkstruct F2 Q.
Proof using.
  introv WF. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'.
Qed.


Lemma mkstruct_monotone_conseq : forall F1 F2 Q1 Q2,
  (forall Q', F1 Q' ==> F2 Q') ->
  Q1 ===> Q2 ->
  mkstruct F1 Q1 ==> mkstruct F2 Q2.
Proof using.
  introv WF WQ. unfolds mkstruct. xpull. intros Q'. xchange WF. xsimpl Q'. xchange WQ.
Qed.

Section Hwand.

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

Lemma himpl_hwand_hpure_r : forall H1 H2 P,
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. xsimpl. applys M. Qed.

Lemma himpl_hwand_hpure_l : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using. introv HP. rewrite* hwand_hpure_l. Qed.

End Hwand.

Lemma mkstruct_himpl_wp : forall F t,
  (forall Q, F Q ==> wp t Q) ->
  (forall Q, mkstruct F Q ==> wp t Q).
Proof using. introv M. applys mkstruct_sound. hnfs*. Qed.


Lemma wpgen_if_trm_sound : forall F0 F1 F2 t0 t1 t2,
  formula_sound t0 F0 ->
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if t0 t1 t2) (wpgen_if_trm F0 F1 F2).
Proof using.
  introv S0 S1 S2. unfold wpgen_if_trm. intros Q. unfold wpgen_let.
  applys himpl_trans S0. applys himpl_trans; [ | applys wp_if_trm' ].
  applys wp_conseq. intros v.
  applys mkstruct_himpl_wp. intros Q'. applys wpgen_if_sound S1 S2.
Qed.

Lemma himpl_trans' : forall H2 H1 H3,
  H2 ==> H3 ->
  H1 ==> H2 ->
  H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.


Lemma wpgen_while_sound : forall t1 t2 F1 F2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_while t1 t2) (wpgen_while F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_while.
  applys himpl_hforall_l (wp (trm_while t1 t2)).
  applys himpl_trans'. rewrite (wp_eq_mkstruct_wp (trm_while t1 t2)). applys himpl_refl. (* TODO *)
  applys himpl_hwand_hpure_l. intros Q'.
  applys mkstruct_monotone. intros Q''.
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

Notation "'While' F1 'Do' F2 'Done'" :=
  ((wpgen_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' 'While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : wpgen_scope.

Notation "'If_trm' F0 'Then' F1 'Else' F2" :=
  ((wpgen_if_trm F0 F1 F2))
  (at level 69) : wp_scope.



(* ########################################################### *)
(** ** Frame during loop iterations *)

Section DemoLoopFrame.
Import SLFProgramSyntax SLFBasic.

Notation "'While' t1 'Do' t2 'Done'" :=
  (trm_while t1 t2)
  (at level 69, t2 at level 68,
   format "'[v' 'While'  t1  'Do'  '/' '[' t2 ']' '/'  'Done' ']'")
   : trm_scope.



(** The following function

[[
    let mlength_loop p =
      let a = ref 0 in
      let r = ref p in
      while !p != null do
        incr a;
        r := !p.tail;
      done;
      let n = !a in
      free a;
      free r;
      n
]]

*)

Definition mlength_loop : val :=
  Fun 'p :=
    Let 'a := 'ref 0 in
    Let 'r := 'ref 'p in
    While Let 'p1 := '!'r in ('p1 '<> null) Do
      incr 'a';
      Let 'p1 := '!'r in
      Let 'q := 'p1'.tail in
      'r ':= 'q
    Done ';
    Let 'n := '!'a in
    'free 'a ';
    'free 'r ';
    'n.

(** The append function is specified and verified as follows. *)

Lemma MList_nil_intro :
  \[] ==> (MList nil null).
Proof using. intros. rewrite* MList_nil. xsimpl*. Qed.

Opaque MList.

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

Lemma mkstruct_apply : forall H1 H2 F Q1 Q2,
  H1 ==> mkstruct F Q1 ->
  H2 ==> H1 \* (Q1 \--* protect Q2) ->
  H2 ==> mkstruct F Q2.
Proof using.
  introv M1 M2. xchange M2. xchange M1. applys mkstruct_ramified.
Qed.

Lemma Triple_mlength_loop : forall L p,
  triple (mlength_loop p)
    (MList L p)
    (fun r => \[r = length L] \* MList L p).
Proof using.
  xwp. xapp. intros a. xapp. intros r.
  xseq. rewrite wpgen_while_eq. xwp_simpl.
  (* xwhile TODO *)
  applys himpl_trans; [ | applys mkstruct_conseq].
  xstruct. unfold wpgen_while. xsimpl. intros R HR.
  asserts KR: (forall n,     r ~~> p \* a ~~> n \* MList L p
                         ==> `R (fun _ =>  r ~~> null \* a ~~> (length L + n) \* MList L p)).
  { gen p. induction_wf IH: list_sub L. intros.
    applys himpl_trans HR. clear HR.
    unfold wpgen_if_trm. xlet. (* TODO xif_trm *)
    xapp. xapp. xchange MList_if. xif; intros C; case_if.
    { xpull. intros x q L' ->. xseq. xapp. xapp. xapp. xapp.
      (* recursive call, framing the head cell: *)
      applys mkstruct_apply. applys (IH L'). { auto. } xsimpl. unfold protect.
      intros _. xchange <- MList_cons. xsimpl. { rew_list. math. }
        (* Close Scope wp_scope. *)
        (* eapply mkstruct_ramified_trans_protect. xsimpl. unfold protect.
        rewrite qwand_equiv. intros _. xchange <- MList_cons. xsimpl. rew_list. math.  *)
    }
    { xpull. intros ->. xval. xsimpl. auto. subst. xchange MList_nil_intro. }
  }
  { applys KR. }
  xpull. xapp. xapp. xapp. xval. xsimpl. math.
Qed.

End DemoLoopFrame.

End WhileLoops.


(* ####################################################### *)
(** ** Reasoning rule for for-loops *)


(* ####################################################### *)
(** ** Reasoning rule for assertions *)

Module Assertions.

Parameter val_assert : prim.

Parameter eval_assert_enabled : forall s t s',
  eval s t s' (val_bool true) ->
  eval s (val_assert t) s' val_unit.

Parameter eval_assert_disabled : forall s t,
  eval s (val_assert t) s val_unit.

Parameter eval_assert_both : forall s t s' v, (* too restrictive *)
  eval s t s' v ->
  eval s val_unit s' v ->
  eval s (val_assert t) s' v.

Lemma hoare_assert : forall t H,
  hoare t H (fun r => \[r = true] \* H) ->
  hoare (val_assert t) H (fun _ => H).
Proof using.
  introv M. intros s K. forwards (s'&v&R&N): M K.
  rewrite hstar_hpure in N. destruct N as (->&K').
  dup. (* Duplicate the proof obligation to cover two cases *)
  (* Case assertions are enabled *)
  { exists s' val_unit. split.
    { applys eval_assert_enabled R. }
    { applys K'. } }
  (* Case assertions are disabled *)
  { exists s val_unit. split.
    { applys eval_assert_disabled. }
    { applys K. } }
Qed.

Lemma triple_assert : forall t H,
  triple t H (fun r => \[r = true] \* H) ->
  triple (val_assert t) H (fun _ => H).
Proof using.
  introv M. intros H'. specializes M H'. applys hoare_assert.
  applys hoare_conseq M. { xsimpl. } { xsimpl. auto. }
Qed.

End Assertions.


(* ####################################################### *)
(** ** Curried functions of several arguments *)

Module CurriedFun.
Open Scope liblist_scope.
Implicit Types f : var.

(** We next give a quick presentation of the notation, lemmas and
    tactics involved in the manipulation of curried functions of
    several arguments.

    We focus here on the particular case of recursive functions with 2
    arguments, to illustrate the principles. Set up for non-recursive and
    recursive functions of arity 2 and 3 can be found in the file [SLFExtra].
    One may attempt to generalize these definitions to handle arbitrary
    arities. Yet, to obtain an arity-generic treatment of functions, it is
    much simpler to work with primitive n-ary functions, whose treatment is
    presented further on.

    Consider a curried recursive functions that expects two arguments.
    [val_fix f x1 (trm_fun x2 t)] describes such a function, where [f]
    denotes the name of the function for recursive calls, [x1] and [x2]
    denote the arguments, and [t] denotes the body. Observe that the
    inner function, the one that expects [x2], is not recursive, and that
    it is not a value but a term (because it may refer to the variable [x1]
    bound outside of it).

    We introduce the notation [Fix f x1 x2 := t] to generalize the notation
    [Fix f x := t] to the case of a recursive function of two arguments. *)

Notation "'Fix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f, x1, x2 at level 0,
  format "'Fix'  f  x1  x2  ':='  t").

(** An application of a function of two arguments takes the form
    [f v1 v2], which is actually parsed as [trm_app (trm_app f v1) v2].

    This expression is an application of a term to a value, and not of
    a value to a value. Thus, this expression cannot be evaluated using
    the rule [eval_app_fun]. We need a distinct rule for first evaluating
    the arguments of a function application to values, before we can
    evaluate the application of a value to a value.

    The rule [eval_app_args] serves that purpose. To state it, we first
    need to characterize whether a term is a value or not, using the
    predicate [trm_is_val t] defined next. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** The statement of [eval_app_args] then takes the following form.
    For an expression [trm_app t1 t2] where either [t1] or [t2] is
    not a value, it enables reducing both [t1] and [t2] to values,
    leaving a premise of the form [trm_app v1 v2], which is subject
    to the rule [eval_app_fun] for evaluating functions. *)

Parameter eval_app_args : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
  (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
  eval s1 t1 s2 v1 ->
  eval s2 t2 s3 v2 ->
  eval s3 (trm_app v1 v2) s4 r ->
  eval s1 (trm_app t1 t2) s4 r.

(** Using this rule, we can establish an evaluation rule for the
    term [v0 v1 v2]. There, [v0] is a recursive function of two
    arguments named [x1] and [x2], the values [v1] and [v2] denote
    the corresponding arguments, and [f] denotes the name of the
    function available for making recursive calls from the body [t1].

    The key idea is that the behavior of [v0 v1 v2] is similar to
    that of the term [subst x2 v2 (subst x1 v1 (subst f v0 t1))].
    We state this property using the predicate [eval_like], introduced
    in the chapter [SLFRules]. *)

Lemma eval_like_app_fix2 : forall v0 v1 v2 f x1 x2 t1,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst f v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R. applys* eval_app_args.
  { applys eval_app_fix E. simpl. do 2 (rewrite var_eq_spec; case_if).
    applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed.

(** From this result, we can easily prove the specification triple
    for applications of the form [v0 v1 v2]. *)

Lemma triple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(** We can exploit the same result to esablish the corresponding
    weakest-precondition style version of the reasoning rule. *)

Lemma wp_app_fix2 : forall f x1 x2 v0 v1 v2 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  wp (subst x2 v2 (subst x1 v1 (subst f v0 t1))) Q ==> wp (trm_app v0 v1 v2) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix2. Qed.

(** We can then reformulate this wp-style rule in a way that suits
    the needs of the [xwp] tactic, using a conclusion expressed
    using a [triple], and using a premise expressed using [wpgen].
    Observe the substitution context, which is instantiated as
    [(f,v0)::(x1,v1)::(x2,v2)::nil]. Note also how the side-conditions
    expressing the fact that the variables are distinct are stated
    using a comparison function for variables that computes in Coq. *)

Lemma xwp_lemma_fix2 : forall f v0 v1 v2 x1 x2 t H Q,
  v0 = val_fix f x1 (trm_fun x2 t) ->
  (var_eq x1 x2 = false /\ var_eq f x2 = false) ->
  H ==> wpgen ((f,v0)::(x1,v1)::(x2,v2)::nil) t Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((f,v0)::nil) ++ ((x1,v1)::nil) ++ ((x2,v2)::nil)) t Q).
  do 2 rewrite isubst_app. do 3 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix2.
Qed.

(** Finally, we can generalize the [xwp] tactic by integrating in
    its implementation an attempt to invoke the above lemma. *)

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ]
        | applys xwp_lemma_fix2; [ reflexivity | splits; reflexivity | ] ];
  xwp_simpl.

(** The generalized version of [xwp] following this line is
    formalized in the file [SLFExtra.v] and was put to practice
    in several examples from the chapter [SLFBasic]. *)

End CurriedFun.


(* ####################################################### *)
(** ** Primitive n-ary functions *)

Module PrimitiveNaryFun.

(** We next present an alternative treatment to functions of several
    arguments. The idea is to represent arguments using lists.

    On the one hand, the manipulation of lists adds a little bit of
    boilerplate. On the other hand, when using this representation, all
    the definitions and lemmas are inherently arity-generic, that is,
    they work for any number of arguments.

    We introduce the short names [vars], [vals] and [trms] to denote lists
    of variables, lists of values, and lists of terms, respectively.
    These names are not only useful to improve conciseness, they also enable
    the set up of useful coercions, as we will detail shortly afterwards. *)

Definition vars : Type := list var.
Definition vals : Type := list val.
Definition trms : Type := list trm.

Implicit Types xs : vars.
Implicit Types vs : vals.
Implicit Types ts : trms.

(** We assume the grammar of terms and values to include primitive n-ary
    functions and n-ary applications, featuring list of arguments.
    Thereafter, for conciseness, we omit non-recursive functions, and
    focus on the treatment of the more-general recursive functions. *)

Parameter val_fixs : var -> vars -> trm -> val.
Parameter trm_fixs : var -> vars -> trm -> trm.
Parameter trm_apps : trm -> trms -> trm.

(** The substitution function is a bit tricky to update for dealing with
    list of variables. A definition along the following lines works well.
    On the one hand, it prevents variables capture. On the other hand,
    it traverses recursively the list of arguments, in a way that is
    recognized as structurally recursive.

[[
    Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
      let aux t := (subst y w t) in
      let aux_no_captures xs t := (If List.In y xs then t else aux t) in
      match t with
      | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                            aux_no_captures xs t1)
      | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
      ...
     end.
]]

    For additional details, we refer to the implementation of CFML.
*)

(** The evaluation rules need to be updated accordingly. A n-ary function
    from the grammar of terms evaluates to the corresponding n-ary
    function from the grammar of values. For technical reasons, we
    need to ensure that the program is well-formed and that the list
    of arguments to the function is nonempty. Indeed, a function of
    zero arguments is not considered a function in our language.
    (Otherwise, such a function [f] would beta-reduce to its body
    as soon as it is defined, because it waits for no arguments.) *)

Parameter eval_fixs : forall m f xs t1,
  xs <> nil ->
  eval m (trm_fixs f xs t1) m (val_fixs f xs t1).

(** The application of a n-ary function to values takes the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. ::(trm_val vn)::nil)].
    If the function [v0] is defined as [val_fixs f xs t1], where [xs]
    denotes the list [x1::x2::...::xn::nil], then the beta-reduction
    of the function application triggers the evaluation of the
    substitution [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)].

    To describe the evaluation rule in an arity-generic way, we need to
    introduce the list [vs] made of the values provided as arguments,
    that is, the list [v1::v2::..::vn::nil].

    With this list [vs], the n-ary application can then be written as the
    term [trm_apps (trm_val v0) (trms_vals vs)], where the operation
    [trms_vals] converts a list of values into a list of terms by
    applying the constructor [trm_val] to every value from the list. *)

Coercion trms_vals (vs:vals) : trms :=
  LibList.map trm_val vs.

(** Note that we declare the operation [trms_vals] as a coercion, just
    like [trm_val] is a coercion. Doing so enables us to write a n-ary
    application in the form [v0 vs]. *)

(** To describe the iterated substitution
    [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)], we introduce
    the operation [substn xs vs t], which substitutes the variables [xs]
    with the values [vs] inside the [t]. It is defined recursively,
    by iterating calls to the function [subst] for substituting the
    variables one by one. *)

Fixpoint substn (xs:list var) (vs:list val) (t:trm) : trm :=
  match xs,vs with
  | x::xs', v::vs' => substn xs' vs' (subst x v t)
  | _,_ => t
  end.

(** This substitution operation is well-behaved only if the list [xs]
    and the list [vs] have the same lengths. It is also desirable for
    reasoning about the evaluation rule to guarantee that the list of
    variables [xs] contains variables that are distinct from each others
    and distinct from [f], and to guarantee that the list [xs] is not empty.

    To formally capture all these invariants, we introduce the predicate
    [var_fixs f xs n], where [n] denotes the number of arguments the
    function is being applied to. Typically, [n] is equal to the length
    of the list of arguments [vs]). *)

Definition var_fixs (f:var) (xs:vars) (n:nat) : Prop :=
     LibList.noduplicates (f::xs)
  /\ length xs = n
  /\ xs <> nil.

(** The evaluation of a recursive function [v0] defined as [val_fixs f xs t1]
    on a list of arguments [vs] triggers the evaluation of the term
    [substn xs vs (subst f v0 t1)], same as [substn (f::xs) (v0::vs) t1].
    The evaluation rule is stated as follows, using the predicate [var_fixs]
    to enforce the appropriate invariants on the variable names. *)

Parameter eval_apps_fixs : forall v0 vs f xs t1 s1 s2 r,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs) ->
  eval s1 (substn (f::xs) (v0::vs) t1) s2 r ->
  eval s1 (trm_apps v0 (trms_vals vs)) s2 r.

(** The corresponding reasoning rule has a somewhat similar statement. *)

Lemma triple_apps_fixs : forall v0 vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 vs) H Q.
Proof using.
  introv E N M. applys triple_eval_like M.
  introv R. applys* eval_apps_fixs.
Qed.

(** The statement of the above lemma applies only to terms that are
    of the form [trm_apps (trm_val v0) (trms_vals vs)]. Yet, in practice,
    goals are generally of the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. :: (trm_val vn)::nil)].
    The two forms are convertible, yet in general Coq is not able to
    synthetize the list [vs] during the unification process.

    Fortunately, it is possible to reformulate the lemma using an auxiliary
    conversion function named [trms_to_vals], whose evaluation by Coq's
    unification process is able to synthetize the list [vs].

    The operation [trms_to_vals ts], if all the terms in [ts] are of the
    form [trm_val vi], returns a list of values [vs] such that [ts] is
    equal to [trms_vals vs]. Otherwise, the operation returns [None].
    The definition and specification of the operation [trms_to_vals]
    are as follows. *)

Fixpoint trms_to_vals (ts:trms) : option vals :=
  match ts with
  | nil => Some nil
  | (trm_val v)::ts' =>
      match trms_to_vals ts' with
      | None => None
      | Some vs' => Some (v::vs')
      end
  | _ => None
  end.

Lemma trms_to_vals_spec : forall ts vs,
  trms_to_vals ts = Some vs ->
  ts = trms_vals vs.
Proof using.
  intros ts. induction ts as [|t ts']; simpl; introv E.
  { inverts E. auto. }
  { destruct t; inverts E as E. cases (trms_to_vals ts') as C; inverts E.
    rename v0 into vs'. rewrite* (IHts' vs'). }
Qed.

Lemma demo_trms_to_vals : forall v1 v2 v3,
  exists vs,
     trms_to_vals ((trm_val v1)::(trm_val v2)::(trm_val v3)::nil) = Some vs
  /\ vs = vs.
Proof using.
  (* activate the display of coercions to play this demo *)
  intros. esplit. split. simpl. eauto. (* [vs] was inferred. *)
Abort.

(** Using [trms_to_vals], we can reformulate [triple_apps_fixs'] in such
    a way that the rule can be smoothly applied on practical goals. *)

Lemma triple_apps_fixs' : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 ts) H Q.
Proof using.
  introv E T N M. rewrites (@trms_to_vals_spec _ _ T).
  applys* triple_apps_fixs.
Qed.

(** To set up the tactic [xwp] to handle n-ary applications, we reformulate
    the lemma above by making two changes.

    The first change is to replace the predicate [var_fixs] which checks
    the well-formedness properties of the list of variables [xs] by an
    executable version of this predicate, with a result in [bool]. This way,
    the tactic [reflexivity] can prove all the desired facts, when the lemma
    in invoked on a concrete function. We omit the details, and simply
    state the type of the boolean function [var_fixs_exec]. *)

Parameter var_fixs_exec : var -> vars -> nat -> bool.

(** The second change is to introduce the [wpgen] function in place of
    the triple for the evaluation of the body of the function. The
    substitution [substn (f::xs) (v0::vs)] then gets described by the
    substitution context [List.combine (f::xs) (v0::vs)], which describes
    a list of pairs of type [list (var * val)].

    The statement of the lemma for [xwp] is as follows. We omit the proof
    details---they may be found in the implementation of the CFML tool. *)

Parameter xwp_lemma_fixs : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f xs (LibList.length vs) ->
  H ==> (wpgen (combine (f::xs) (v0::vs)) t1) Q ->
  triple (trm_apps v0 ts) H Q.

(** One last practical details is the set up of the coercion for writing
    function applications in a concise way. With n-ary functions, the
    application of a function [f] to two arguments [x] and [y] takes the
    form [trm_apps f (x::y::nil)]. This syntax is fairly verbose in
    comparison with the syntax [f x y], which we were able to set up by
    declaring [trm_app] as a [Funclass] coercion (recall chapter [SLFRules]).

    If we simply declare [trm_apps] as a [Funclass] coercion, we can write
    [f (x::y::nil)] to denote the application, but we still have to write
    the list constructors explicitly.

    Fortunately, there is a trick to get the expression [f x y] to be
    interpreted by Coq as [trm_apps f (x::y::nil)], a trick that works
    for any number of arguments. The trick is described next. *)

Module NarySyntax.

(** To illustrate the construction, let us consider a simplified grammar
    of terms that includes the constructor [trm_apps] for n-ary applications. *)

Inductive trm : Type :=
  | trm_val : val -> trm
  | trm_apps : trm -> list trm -> trm.

(** We introduce the data type [apps] to represent the syntax tree
    associated with iterated applications of terms to terms.

    - The application of a term to a term, that is, [t1 t2], gets interpreted
      via a [Funclass] coercion as [apps_init t1 t2], which is an expression
      of type [apps].
    - The application of an object of type [apps] to a term, that is [a1 t2],
      gets interpreted via another [Funclass] coercion as [apps_next a1 t2].

*)

Inductive apps : Type :=
  | apps_init : trm -> trm -> apps
  | apps_next : apps -> trm -> apps.

Coercion apps_init : trm >-> Funclass.
Coercion apps_next : apps >-> Funclass.

(** For example, the expression [f x y z] gets parsed by Coq as
    [apps_next (apps_next (apps_init f x) y) z]. From there, the
    desired term [trm_apps f (x::y::z::nil)] can be computed by a
    Coq function, called [apps_to_trm], that process the syntax tree
    of the [apps] expression.

    - In the base case, [apps_init t1 t2] describes the application
      of a function to one argument: [trm_apps t1 (t2::nil)].
    - Next, if an apps structure [a1] describes a term [trm_apps t0 ts],
      then [apps_next a1 t2] describes the term [trm_apps t0 (ts++t2::nil)],
      that is, an application to one more argument. *)

Fixpoint apps_to_trm (a:apps) : trm :=
  match a with
  | apps_init t1 t2 => trm_apps t1 (t2::nil)
  | apps_next a1 t2 =>
      match apps_to_trm a1 with
      | trm_apps t0 ts => trm_apps t0 (List.app ts (t2::nil))
      | t0 => trm_apps t0 (t2::nil)
      end
  end.

(** The function [apps_to_trm] is declared as a coercion from [apps]
    to [trm], so that any iterated application can be interpreted as
    the corresponding [trm_apps] term. (Coq raises an "ambiguous coercion
    path" warning, but this warning may be safely ignored here.) *)

Coercion apps_to_trm : apps >-> trm.

(** The following demo shows how the term [f x y z] is parsed as
    [apps_to_trm (apps_next (apps_next (apps_init f x) y) z)], which
    then simplifies by [simpl] to [trm_apps f (x::y::z::nil)]. *)

Lemma apps_demo : forall (f x y z:trm),
  (f x y z : trm) = trm_apps f (x::y::z::nil).
Proof using. intros. (* activate display of coercions *) simpl. Abort.

End NarySyntax.

End PrimitiveNaryFun.


