(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [LambdaWPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWPLifted.
Open Scope heap_scope.
Generalizable Variables A B.

Implicit Types v w : val.
Implicit Types t : trm.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.



(* ********************************************************************** *)
(* * Demo *)

Ltac hsimpl_wand ::=
  first [ applys qwand_of_qimpl 
        | applys hwand_of_himpl ].




(* ---------------------------------------------------------------------- *)
(** Notation for triples *)

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1 x2, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident, x2 ident) : triple_scope.

Open Scope triple_scope.


(* ---------------------------------------------------------------------- *)
(* ** Tactic *) 

Lemma Wp_Triple_of_Wp : forall t H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  H ==> ^(Wp_Triple t) Q.
Proof using. introv M. applys himpl_weakestpre. applys* Triple_of_Wp. Qed.



Lemma Local_erase' : forall H F `{EA:Enc A} (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Local F) Q.
Proof using.
  introv M. hchanges M. applys local_erase.
Qed.

(*
Lemma xlet_lemma : forall Q1 (F1:formula) (F2of:forall `{EA1:Enc A1},A1->Formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> Wp_let F1 F2of Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.



Definition Wp_let (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1) ,
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

*)

(* use:  notypeclasses refine (xlet_instantiate _ _ _). *)

Lemma xlet_instantiate' : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.

Lemma xlet_instantiate : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall `{EA1:Enc A2},A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of X) Q) ->
  H ==> ^(Wp_let F1 (@F2of)) Q.
Proof using.
  introv M. applys Local_erase'. notypeclasses refine (xlet_instantiate' _ _ _). applys M.
Qed.

(*
Lemma xlet_typed_instantiate : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.
*)

Lemma xapp_triple_to_Wp_Triple : forall A `{EA:Enc A} (Q1:A->hprop) t H1,
  Triple t H1 Q1 ->
  H1 ==> ^(Wp_Triple t) Q1.
Proof using. introv M. applys* himpl_weakestpre. Qed.

Lemma xapp_lemma' : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Wp_Triple t) Q.
Proof using. 
  introv M1 M2. lets M: xapp_triple_to_Wp_Triple (rm M1).
  hchanges (rm M2). hchanges (rm M).
  applys weakestpre_conseq_wand.
  applys is_local_Triple.
Qed.

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Local (Wp_Triple t)) Q.
Proof using.
  introv M1 M2. applys Local_erase'. applys* xapp_lemma'.
Qed.



Lemma xval_lemma : forall `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase'. hsimpl~ V. Qed.

Lemma xval_lemma_val : forall `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase'. hsimpl~ (``V). Qed.



Lemma xcase_lemma : forall F1 (P:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (H ==> ^F1 Q) ->
  (P -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val F1 P F2) Q.
Proof using. 
  introv M1 M2. apply Local_erase'. applys himpl_hand_r. 
  { auto. }
  { applys* hwand_move_l_pure. }
Qed.

Lemma xcase_lemma0 : forall F1 (P1 P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (P1 -> H ==> ^F1 Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val (fun `{EA1:Enc A1} (Q:A1->hprop) => \[P1] \-* ^F1 Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma. { applys* hwand_move_l_pure. }
Qed.

Lemma xcase_lemma2 : forall (F1:val->val->Formula) (P1:val->val->Prop) (P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (forall x1 x2, P1 x1 x2 -> H ==> ^(F1 x1 x2) Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val (fun `{EA1:Enc A1} (Q:A1->hprop) => \forall x1 x2, \[P1 x1 x2] \-* ^(F1 x1 x2) Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma.
  { repeat (applys himpl_hforall_r ;=> ?). applys* hwand_move_l_pure. }
Qed.

Lemma xmatch_list : forall `{EA:Enc A} (L:list A) (F1:Formula) (F2:val->val->Formula) H `{HB:Enc B} (Q:B->hprop),
  (L = nil -> H ==> ^F1 Q) ->
  (forall X L', L = X::L' -> H ==> ^(F2 ``X ``L') Q) ->
  H ==> ^(`Match ``L With
         '| 'nil '=> F1
         '| vX ':: vL' [vX vL'] '=> F2 vX vL') Q.
Proof using.
  introv M1 M2. applys xcase_lemma0 ;=> E1.
  { destruct L; rew_enc in *; tryfalse. applys* M1. }
  { destruct L; rew_enc in *; tryfalse. applys xcase_lemma2.
    { intros x1 x2 Hx. inverts Hx. applys* M2. }
    { intros N. false* N. } }
Qed.



(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

(*
Lemma Substn_eq_isubstn : forall xs (Vs:dyns) t,
  length xs = length Vs ->
  Substn xs Vs t = isubstn xs (encs Vs) t.
Proof using.
  introv E. unfold Substn. rewrite~ isubstn_eq_substn.
  rewrite* length_encs.
Qed.

*)

Lemma Triple_apps_funs_of_Wp : forall F (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
Admitted.
(*
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Triple_apps_funs. 
  unfolds in N. rewrite* Substn_eq_isubstn.
  applys* Triple_isubst_of_Wp.
Qed.
*)

Lemma Triple_apps_fixs_of_Wp : forall F (f:var) (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  vs = encs Vs ->
  var_fixs_exec f (length Vs) xs ->
  H ==> ^(Wp (combine (f::xs) (encs ((Dyn F)::Vs))) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
Admitted.
(*
  introv EF EV N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
  subst. applys* Triple_apps_fixs.
  rewrite~ Substn_eq_isubstn. 
  { applys @Triple_isubst_of_Wp M. }
  { rew_list. math. }
Qed.
*)

(* todo: factorize above two using anon? *)


Lemma Triple_apps_funs_of_Wp' : forall F (Vs:dyns) (vs:vals) (ts:trms) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  ts = trms_vals vs ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F ts) H Q.
Proof using.
  intros. subst. applys* Triple_apps_funs_of_Wp.
Qed.
(*
  xcf_prepare_args tt. (* -- not needed here *)
*)

Lemma Triple_apps_funs_of_Wp'' : forall F (vs:vals) (ts:trms) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec (length vs) xs ->
  H ==> ^(Wp (combine xs vs) t) Q ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv M1 M2 M3 M4. lets: trms_to_vals_spec M2.
  skip.
Qed.
(*
  xcf_prepare_args tt. (* -- not needed here *)
*)



(* ---------------------------------------------------------------------- *)
(* * Example proofs *)

Module Test.




(* ---------------------------------------------------------------------- *)
(* ** Increment *)

Definition val_incr : val :=
  ValFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  ValFun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)


Lemma triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  intros.
  (* xcf details: *)
  simpl combiner_to_trm.
  (* xcf_prepare_args tt.  -- not needed here *)
  (* let f := xcf_get_fun tt in 
  unfold f. 
  rew_trms_vals. *)
  applys Triple_apps_funs_of_Wp''.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl. rew_enc_dyn. (* xcf_post tt. *)
  (* fst call *)
  apply Local_erase'.
  apply Local_erase'.
  applys @xapp_lemma. { applys Triple_get. }
  hsimpl.
  hsimpl_wand. (* todo: extend hsimpl to do this step *)
  hpull ;=> ? ->.
  (* return *)
  applys @Formula_typed_val. 
  (* snd call *)
  applys @xapp_lemma. { eapply @Triple_set. }
  hsimpl.
  hsimpl_wand.
  hsimpl.
Qed.

(* SHOULD BE:

  xcf.
  xlet. { xapp. xapplys triple_get. }
  hpull ;=> ? ->.
  xlet. { xapp. xapplys triple_add. }
  hpull ;=> ? ->.
  xapp. xapplys triple_set. auto.


then just:

  xcf.
  xapp.
  xapp.
  xapp.


*)



(* ---------------------------------------------------------------------- *)
(* ** Case without variables *)

Definition val_test1 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else 'Fail.

Lemma triple_test1 : forall (p:loc),
  TRIPLE (val_test1 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xcf details: *)
  simpl combiner_to_trm.
  applys Triple_apps_funs_of_Wp''; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Case with 1 variable *)

Definition val_test2 : val :=
  ValFun 'p :=
    Case' 'p = 'x Then 'x Else 'Fail.

Lemma triple_test2 : forall (p:loc),
  TRIPLE (val_test2 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xcf details: *)
 (* simpl combiner_to_trm.
  xcf_prepare_args tt. (* -- not needed here *)
  let f := xcf_get_fun tt in 
  unfold f.
  rew_trms_vals. *)
  applys Triple_apps_funs_of_Wp''; try reflexivity. simpl.
  (* unfold Wp_var. simpl. *)
Admitted.



(* ---------------------------------------------------------------------- *)
(* ** Stack *)

(* TODO: is_empty, append *)

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

Definition Stack `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


Lemma triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop ``p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  intros.
  (* xcf details: 
  simpl combiner_to_trm.
  applys Triple_apps_funs_of_Wp'.
  { reflexivity. }
  { rew_trms_vals. reflexivity. }
  { try xeq_encs. }
  { reflexivity. } *)
  applys Triple_apps_funs_of_Wp''.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* simpl; unfold Wp_var; simpl. *)
  (* start *)
  xunfold Stack.
  (* xlet *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_get. }
  hsimpl; hsimpl_wand; hsimpl ;=> ? ->.
  dup.
  (* xcase manual *)
  { applys xcase_lemma0 ;=> E1.
    { destruct L; tryfalse. }
    { applys xcase_lemma2.
      2: { intros E. destruct L; rew_enc in *; tryfalse. }
      { intros x1 x2 E2. destruct L as [|x L']; rew_enc in *; tryfalse.
        inverts E2.
        (* xseq *)
        (* applys xseq_lemma. *)  apply Local_erase'.
        (* xapp *)
        applys @xapp_lemma. { applys @Triple_set. }
        hsimpl; hsimpl_wand. hsimpl.
        (* xval *)
       applys~ xval_lemma.
        (* post *)
        hsimpl~. } } }
  (* xcase with lemma for match list *)
  { applys xmatch_list.
    { intros HL. false. }
    { intros X L' HL. 
      (* xseq *)
      (* applys xseq_lemma. *)  apply Local_erase'.
      (* xapp *)
      applys @xapp_lemma. { applys @Triple_set. }
      hsimpl; hsimpl_wand. hsimpl.
      (* xval *)
     applys~ xval_lemma.
      (* post *)
      hsimpl~. } }
Qed.



Lemma triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty ``u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  intros.
  (* xcf details: *)
  applys Triple_apps_funs_of_Wp''; try reflexivity. simpl.
  (* xletval *)
  apply Local_erase'.
  (* xval *)
  applys~ (xval_lemma_val (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. }
  hsimpl; hsimpl_wand.
  hsimpl.
Qed.

(*
Definition enc_list `{Enc A} := (fix f (l:list A) :=
  match l with
  | nil => val_constr 0%nat nil
  | x::l' => val_constr 1%nat ((``x)::(f l')::nil)
  end).

Instance Enc_list2 : forall `{Enc A}, Enc (list A).
Proof using. constructor. applys enc_list. Defined.

Opaque enc_list.
*)

Lemma triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push ``p ``x)
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  intros.
  (* xcf details: *)
  applys Triple_apps_funs_of_Wp''; try reflexivity. simpl.
  (* xunfold *)
  xunfold Stack.
  (* xval *)
  apply Local_erase'.
  (* xlet *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_get. }
  hsimpl. hsimpl_wand. hsimpl ;=> ? ->.
  (* xval *)
  applys~ (xval_lemma_val (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. }
  hsimpl. hsimpl_wand. hsimpl ;=> ? ->.
Qed.



End Test.




