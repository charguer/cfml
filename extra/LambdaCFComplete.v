
(* ********************************************************************** *)
(* ** Completeness proof *)

(* TO BE COMPLETED *)


(*

Section Completeness.

Ltac simpl_Trm :=
  match goal with E: _ = trm_of_Trm ?T |- _ => destruct T; inverts E end.




Hint Resolve is_local_cf.
Lemma local_name : forall F (H:hprop) (Q:val->hprop),
  is_local F ->
  (forall m, H m -> F (= m) Q) ->
  F H Q.
Proof.
  introv L M. rewrite L. intros m Hm.
  exists (= m) \[] Q. splits~.
  { exists~ m fmap_empty. }
  { intros h. applys himpl_cancel_r. intros h' Hh'. applys~ htop_intro. }
Qed.

Lemma cf_name : forall T (H:hprop) (Q:val->hprop),
  (forall m, H m -> cf T (= m) Q) ->
  cf T H Q.
Proof. intros. apply~ local_name. Qed.

Definition spost (m:state) (v:val) :=
  fun x => \[x = v] \* (= m).


Fixpoint Trm_of_trm (t : trm) : Trm :=
  let aux := Trm_of_trm in
  match t with
  | trm_val v => Trm_val v
  | trm_if v t1 t2 => Trm_if v (aux t1) (aux t2)
  | trm_let x t1 t2 => Trm_let x (aux t1) (aux t2)
  | trm_app v1 v2 => Trm_app v1 v2
  end.


Axiom trm_of_Trm_on_Trm_of_trm : forall t,
  trm_of_Trm (Trm_of_trm t) = t.

Axiom trm_of_Trm_on_subst_Trm : forall f v T,
  trm_of_Trm (subst_Trm f v T) = subst_trm f v (trm_of_Trm T).

Hint Rewrite trm_of_Trm_on_Trm_of_trm trm_of_Trm_on_subst_Trm : simpl_tr.

Tactic Notation "simpl_tr" := autorewrite with simpl_tr.
Tactic Notation "simpl_tr" "~" := simpl_tr; auto_tilde.


Lemma rule_conseq_frame : forall H'' t H' Q' H Q,
  H ==> H' \* H'' ->
  triple t H' Q' ->
  Q' \*+ H'' ===> Q ->
  triple t H Q.
Proof using. intros. applys* rule_consequence. applys* rule_frame. Qed.


Theorem cf_complete_wrt_semantics : forall (T:Trm) m m' v',
  red m T m' v' -> (cf T) (= m) (spost m' v').
Proof using.
  introv H. gen_eq t: (trm_of_Trm T); gen T; induction H; intros T E.
  { simpl_Trm. simpl_cf. applys local_erase. hnf.
    intros m' E. subst. exists~ (fmap_empty:state) m. }
  { simpl_Trm. simpl_cf. applys local_erase. hnf.
    case_if; applys~ IHred. }
  { simpl_Trm.
    { simpl_cf. applys local_erase. hnf.
      exists (spost m2 v1). split.
      { applys~ IHred1. }
      { intros X. unfold spost. applys~ local_extract_hprop.
        intros E. subst. applys~ IHred2. rewrite~ subst_trm_of_Trm. } }
    { simpl_cf. applys local_erase. hnf.
      intros F HF. inverts H. clear IHred1.
      rename v into f, v0 into x.
      specializes IHred2
       (subst_Trm f (val_fix f x (trm_of_Trm T1)) T2) __. { simpl_tr~. }
      (* specializes HF (val_fix f x (trm_of_Trm T1)). *)
      skip E: (F = (val_fix f x (trm_of_Trm T1))). (* from CF extended *)
      rewrite <- E in *. applys IHred2.
      } }
   { simpl_Trm. simpl_cf. applys local_erase. unfold cf_app, app.
     sets U: (subst_Trm f (val_fix f x t) (subst_Trm x v0 (Trm_of_trm t))).
     applys* rule_app. applys_eq (>> sound_for_cf U) 3.
     { applys IHred. unfold U. simpl_tr~. }
     { unfold U. subst v. simpl_tr~. } }
  { simpl_Trm. simpl_cf. apply local_erase. unfolds. unfolds.
    lets: rule_new. applys rule_conseq_frame (= ma) \[].
    { admit. }
    { applys rule_new. }
    { intros r. unfold spost. subst mb.
      Transparent hsingle. unfold hsingle. admit. }
  { admit. }
  { admit. }
Qed.



End Completeness.


*)
