(* UNDER DEVELOPMENT *)

(*

(* ********************************************************************** *)
(* * Reasoning rules, high-level proofs *)

(*
Module TripleHighLevel.


(* ---------------------------------------------------------------------- *)
(* ** Definition of triples *)

Program Definition only_rw (h:heap) : heap :=
  (h^f, fmap_empty).


Program Definition triple t (H:hprop) (Q:val->hprop) :=
  forall H' h, (H \* H') h ->
  exists (h':heap) v,
       red h t h' v
    /\ (Q v \* \Top \* H') (only_rw h')
    /\ h'^r = h^r.



(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF h N. rew_heap in N.
  rewrite hstar_pure in N.
  destruct N as (HP&N). applys* M.
Qed.

Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma rule_consequence : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K&E): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.

Lemma rule_frame : forall H' t H Q,
  triple t H Q ->
  normal H' ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M NH'. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K&E): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.

Lemma rule_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K&E): (rm M) HF h.
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma rule_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. intros HF h N.
  forwards~ (h'&v&R&K&E): (rm M) (HF \* \Top) h. { hhsimpl~. }
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma rule_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M NH2. intros HF h N.
  rewrite hstar_comm in M.
  rewrite (@hstar_comm H1) in N. rew_heap in *.
  destruct N as (h2&h1&D&P2&P1&EQ).
  forwards Eh2r: NH2 P2.
 (* destruct h2 as ((h2f,h2r),D2). simpls. subst h2r.
  simpls. *)
  forwards~ C2: heap_compat_ro_l h2 h1.
  forwards (h'&v&R&K&E): (rm M) ((= heap_ro h2) \* HF) (heap_ro h2 \u h1).
  { rewrite hstar_comm_assoc. rew_heap.
    rewrite <- hstar_assoc. exists (heap_ro h2) h1. splits~.
    { exists (heap_ro h2) (heap_ro h2).
      forwards X: heap_compat_refl_if_ro (heap_ro h2). { rew_heap~. }
      splits~.
      { applys~ heap_ro_pred. }
       { applys heap_eq. split.
         { rew_heap~. fmap_eq. } (* todo clean *)
         { rewrite~ heap_union_r. rewrite~ fmap_union_self. } } } }
  do 2 rewrite <- (hstar_comm_assoc (= heap_ro h2)) in K.
  destruct K as (h2'&h1'&D'&P2'&P1'&EQ'). subst h2'.
(*
  (* forwards T: heap_fmap_def h2. rewrites (>> NH2 P2) in T. rew_state~. *)
  asserts S: (h1'^r = h1^r). {  (* todo clean *)
    clears R P1 P1'. specializes NH2 P2. clears P2.
    rewrite EQ' in E. rewrite <- (heap_union_comm h1) in E.
    rewrite <- (heap_union_comm h1') in E.
    do 2 rewrite~ heap_union_r in E.
    destruct D as (Da&Db).
    destruct D' as (Da'&Db').
    destruct C2 as (C2a&C2b).
    lets DH2: (heap_disjoint_components h2).
    rew_heap in *. rewrite NH2 in *. clears NH2. rew_state.
     (*
    applys fmap_union_eq_inv_of_disjoint E. rewrite heap_ro_r.
     rewrites (>> NH2 P2). destruct D' as (D1&D2).*)
     admit.
   }

*)

  asserts F: (heap_compat h2 h1'). {
    clears h P1 P1'. specializes NH2 P2. clears P2.
    destruct D as (Da&Db).
    destruct D' as (Da'&Db').
    destruct (id C2) as (C2a&C2b).
    lets DH2: (heap_disjoint_components h2).
    rew_heap~ in *.
    split.
    { rewrite~ NH2. applys fmap_agree_empty_l. }
    { rewrite fmap_disjoint_3_unfold. splits.
      { auto. }
      { auto. }
      { rewrite NH2. cuts_rewrite (h1'^r = fmap_empty).
            auto.
        lets (_&K): heap_eq_forward EQ'. simpls. rew_heap~ in K.
        forwards~: fmap_union_eq_empty_inv_r (eq_sym K).
     } } }
lets (K1&K2): heap_eq_forward EQ'. simpls. rew_heap~ in K2.
    forwards~ K3: fmap_union_eq_empty_inv_r (eq_sym K2).
    forwards~ K4: fmap_union_eq_empty_inv_l (eq_sym K2).
    forwards~ K5: fmap_union_eq_empty_inv_r K4.
    forwards~ K6: fmap_union_eq_empty_inv_l K4.
    rew_heap~ in K1. rew_state~.
  exists (h1' \u h2) v. splits~.
  { fmap_red~.
    { rewrite~ heap_ro_state. }
    { do 3 rewrite heap_fmap_def.
    rewrite E. rew_heap~.  rewrite K1,K3,K5,K6. fmap_eq. simpls. admit.  } }
  { asserts_rewrite (only_rw h' = h2 \u h1').
    {

    applys heap_eq. simpls. rew_heap~. rewrite K5,K6,K3. splits; fmap_eq~.
    rewrite K1. rew_heap~. fmap_eq. }

    rewrite <- (hstar_comm H2). rew_heap. exists h2 h1'.
    splits~. }
  { subst h. rewrite E. rew_heap~. rewrite Eh2r.
    rewrite EQ' in E.
    rew_heap~ in E. rewrites (>> NH2 P2). rew_state~. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Term rules *)

Lemma rule_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF h N. exists h v. splits~.
  { applys red_val. }
  { hhsimpl. hchanges M. }
Qed.

Lemma rule_if : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v'&R&K&E): (rm M) HF h.
  exists h' v'. splits~. { applys~ red_if. }
Qed.

Lemma rule_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst_trm x X t2) (Q1 X) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1&E1): (rm M1) HF h.
  forwards* (h2'&v2&R2&K2&E2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_let R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
  { congruence. }
Qed.

Lemma rule_let_val : forall x v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst_trm x X t2) H Q) ->
  triple (trm_let x (trm_val v1) t2) H Q.
Proof using.
  introv M. forwards~ M': (rm M).
  applys_eq~ (>> rule_let H (fun x => \[x = v1] \* H)) 2.
  { applys rule_val. hsimpl~. }
  { intros X. applys rule_extract_hprop. intro_subst. applys M'. }
Qed.

Lemma rule_app : forall f x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst_trm f F (subst_trm x V t1)) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_arg. }
  admit.
  admit.
Qed.

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val),
    (forall X H' Q',
      triple (subst_trm f F (subst_trm x X t1)) H' Q' ->
      triple (trm_app F X) H' Q') ->
    triple (subst_trm f F t2) H Q) ->
  triple (trm_let f (trm_val (val_fix f x t1)) t2) H Q.
Proof using.
  introv M. applys rule_let_val. intros F EF.
  applys (rm M). clears H Q. intros X H Q. applys~ rule_app.
Qed.

Section RulesPrimitiveOps.
Transparent hstar hsingle.
Hint Resolve heap_compat_union_l heap_compat_union_r.
Hint Resolve fmap_agree_empty_l fmap_agree_empty_r.

Lemma rule_ref : forall v,
  triple (val_ref v) \[] (fun r => Hexists l, \[r = val_loc l] \* l ~~> v).
Proof using.
  intros. intros HF h N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null (heap_state h) v).
  lets~ (h1'&E1&E2): heap_make (fmap_single l v) (fmap_empty:state).
  asserts E3: (heap_state h1' = fmap_single l v).
  { unstate. rewrite E1,E2. fmap_eq. }
  asserts D1': (\# (heap_state h) (heap_state h1')).
  { unfold heap_state at 2. rewrite E1,E2. fmap_disjoint. }
  asserts C: (heap_compat h1' h).
  { split.
    { rewrite~ E2. }
    { rewrite E1,E2. lets: heap_disjoint_components h.
      fmap_disjoint. } }
  exists (h1' \u h) (val_loc l). splits~.
  { rew_state~. applys~ red_ref. }
  { exists h1' h. split~. splits~.
    { exists l. applys~ himpl_hpure_r (l ~~> v). hnfs~. }
    { rew_heap in N. hhsimpl~. } }
  { rew_heap~. rewrite E2. fmap_eq. }
Qed.
(*
Lemma rule_get_ro : forall v l,
  triple (val_get (val_loc l)) (RO (l ~~> v)) (fun x => \[x = v]).
Proof using.
  intros. intros HF h N.
  exists h v. splits~.
  { applys red_get. destruct N as (h1&h2&D&P1&P2&E).
    destruct P1 as (h11&(Q1&Q2)&E1&E2).
    subst h. rewrite heap_fmap_def. (* todo: cleanup *)
    rewrite fmap_union_comm_of_disjoint; [|rew_heap~].
    rew_heap~. rewrite E1,E2,Q1,Q2. rew_state.
    applys~ fmap_union_single_l_read. }
  { rewrite hstar_pure. split~. hhsimpl~. }
Qed.

Lemma rule_set : forall w l v,
  triple (val_set (val_pair (val_loc l) w)) (l ~~> v) (fun r => \[r = val_unit] \* l ~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&D&P1&P2&E).
  destruct P1 as (Q1&Q2).
  lets~ (h1'&E1'&E2'): heap_make (fmap_single l w) (fmap_empty:state).
  asserts Dl: (fmap_disjoint (fmap_single l w) (heap_state h2)).
  { destruct D as (D1&D2). rewrite Q1 in D2. unstate.
    applys fmap_disjoint_single_set v. auto. }
  asserts C: (heap_compat h1' h2).
  { destruct D as (D1&D2). unfolds. rewrite E1',E2'.
    unfold heap_state in Dl. split~. }
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. rew_state~. rewrite E.  (* todo: cleanup *)
    rewrite (@heap_fmap_def h1'). rewrite (@heap_fmap_def h2).
    rewrite E1',E2'. rew_state~.
    applys~ fmap_union_single_to_update v w.
    rewrite (@heap_fmap_def h1). rewrite Q1,Q2. fmap_eq. }
  { rew_heap. rewrite hstar_pure. split~.
    { exists h1' h2. splits~.
      { hnfs~. }
      { clear Dl E C. (* todo *) hhsimpl~. } } }
  { rewrite E. rew_heap~. rewrite Q2,E2'. auto. }
Qed.
*)

End RulesPrimitiveOps.

End TripleHighLevel.

*)


(* ********************************************************************** *)
(* * Reasoning rules, high-level proofs *)


(** PROOF TO BE COMPLETED *)

Module TripleHighLevel.


(* ---------------------------------------------------------------------- *)
(* ** Definition and properties of [on_rw] *)

Program Definition on_rw H h :=
  H h /\ h^r = fmap_empty.

Lemma on_rw_base : forall H h,
  H h ->
  h^r = fmap_empty ->
  on_rw H h.
Proof using. intros H h M N. splits~. Qed.

Lemma on_rw_htop : forall H h,
  on_rw (H \* \Top) h ->
  on_rw H h.
Proof using.
admit.
Qed.

Lemma on_rw_htop' : forall H h,
  (H \* \Top) h ->
  normal H ->
  on_rw H h.
Proof using.
admit.
Qed.

Lemma on_rw_htop_inv : forall H h,
  on_rw H h ->
  (H \* \Top) h.
Proof using.
  introv M. admit.
Qed.

Lemma on_rw_union_r : forall H h1 h2,
  on_rw H h1 ->
  heap_compat h1 h2 ->
  on_rw H (h1 \u h2).
Proof using.
  admit.
Qed.

Lemma on_rw_hstar_normal : forall H H',
  normal H' ->
  on_rw H \* H' ==> on_rw (H \* H').
Proof using.
  introv M. intros h (h1&h2&D&(N1a&N1b)&N2&E).
  specializes M N2. split.
  { exists~ h1 h2. }
  { subst. rew_heap~. rewrite M,N1b. rew_state~. }
Qed.

Lemma on_rw_hstar_l : forall H H',
  on_rw (H \* H') ==> on_rw H \* H'.
Proof using.
  intros. intros h ((h1&h2&D&N1&N2&E)&P2).
  subst h. rew_heap~ in *.
  forwards~ Q: fmap_union_eq_empty_inv_l P2.
  exists h1 h2. splits~. { split~. }
Qed.

Lemma on_rw_weaken : forall Q Q' v,
  Q ===> Q' ->
  on_rw (Q v) ==> on_rw (Q' v).
Proof using.
  admit.
Qed.

Lemma on_rw_weaken' : forall H H',
  H ==> H' ->
  on_rw H ==> on_rw H'.
Proof using.
  admit.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of triples *)

Definition triple t (H:hprop) (Q:val->hprop) :=
  forall H' h, (H \* H') h ->
  (* normal H' -- TODO*)
  exists (h':heap) v,
       red h t h' v
    /\ (on_rw (Q v) \* \Top \* H') h'
    /\ h'^r = h^r.


(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF h N. rew_heap in N.
  rewrite hstar_pure in N.
  destruct N as (HP&N). applys* M.
Qed.

Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma rule_consequence : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K&E): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. applys* on_rw_weaken MQ. }
Qed.

Lemma rule_frame : forall H' t H Q,
  triple t H Q ->
  normal H' ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M NH'. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K&E): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.

Lemma rule_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K&E): (rm M) HF h.
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma rule_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. intros HF h N.
  forwards~ (h'&v&R&K&E): (rm M) (HF \* \Top) h. { hhsimpl~. }
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma rule_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
(*
  introv M NH2. intros HF h N.
  rewrite hstar_comm in M.
  rewrite (@hstar_comm H1) in N. rew_heap in *.
  destruct N as (h2&h1&D&P2&P1&EQ).
  forwards~ C2: heap_compat_ro_l h2 h1.
  forwards (h'&v&R&K&E): (rm M) HF (heap_ro h2 \u h1).
  { rewrite hstar_assoc.
    exists (heap_ro h2) h1. splits~.
    { applys~ heap_ro_pred. } }
  rew_heap~ in E.
  lets DD: (heap_disjoint_components h').
  rewrite E in DD.
  lets H2r: (>> NH2 P2). rewrite H2r in E.
  forwards~ (h1'&Th1'f&Th1'r): heap_make (h'^f \+ h2^f) (h1^r).
  (*lets DD': DD. rewrite <- Th1'f in DD'.*)

  asserts Eh': (heap_state h1' = heap_state h').
  {  rewrite (heap_fmap_def h').
      rewrite (heap_fmap_def h1').
      rewrite  Th1'f. rewrite E.
      fmap_eq~. }

  asserts HC: (heap_compat h2 h1').
  { admit. }

(*
N3 : h1'^r = h11^r \+ h12^f
N4 : on_rw_sub (Q1 v) h1'
G : \# (h1'^f) (h1'^r)
h1'' : heap
F1 : h1''^f = h1'^f \+ h12^f
F2 : h1''^r = h11^r


*)

(*
  forwards~ (h2'&Th2'f&Th2'r): heap_make (fmap_empty:state) (fmap_empty:state).
  asserts Eh': (heap_state h2' \+ heap_state h1' = heap_state h').
  {  rewrite (heap_fmap_def h').
      rewrite (heap_fmap_def h2').
      rewrite (heap_fmap_def h1').
      rewrite  Th1'f,Th2'f,Th2'r. rewrite E.
      fmap_eq~. }

*)
  exists (h2 \u h1') v. splits~.
  { fmap_red~.
    { rewrite~ heap_ro_state. } rewrite Eh'.
      *)



(*
  { (* on_rw_hstar_normal *)
    asserts_rewrite (on_rw (Q1 v \* H2) = on_rw (Q1 v) \* H2). skip.
    rewrite <- (hstar_comm H2). rew_heap.
    exists h2 h1'.
    splits~.
    applys_eq K 1. }
  { subst h. rew_heap~.
    rewrite EQ' in E.
    rew_heap~ in E. rewrites (>> NH2 P2). rew_state~. }




  forwards (h'&v&R&K&E): (rm M) ((= heap_ro h2) \* HF) (heap_ro h2 \u h1).
  { rewrite hstar_comm_assoc. rew_heap.
    rewrite <- hstar_assoc. exists (heap_ro h2) h1. splits~.
    { exists (heap_ro h2) (heap_ro h2).
      forwards X: heap_compat_refl_if_ro (heap_ro h2). { rew_heap~. }
      splits~.
      { applys~ heap_ro_pred. }
       { applys heap_eq. split.
         { rew_heap~. fmap_eq. } (* todo clean *)
         { rewrite~ heap_union_r. rewrite~ fmap_union_self. } } } }
  do 2 rewrite <- (hstar_comm_assoc (= heap_ro h2)) in K.
  destruct K as (h2'&h1'&D'&P2'&P1'&EQ'). subst h2'.
  (* forwards T: heap_fmap_def h2. rewrites (>> NH2 P2) in T. rew_state~. *)
  asserts S: (h1'^r = h1^r). {  (* todo clean *)
    clears R P1 P1'. specializes NH2 P2. clears P2.
    rewrite EQ' in E. rewrite <- (heap_union_comm h1) in E.
    rewrite <- (heap_union_comm h1') in E.
    do 2 rewrite~ heap_union_r in E.
    destruct D as (Da&Db).
    destruct D' as (Da'&Db').
    destruct C2 as (C2a&C2b).
    lets DH2: (heap_disjoint_components h2).
    rew_heap in *. rewrite NH2 in *. clears NH2. rew_state.
(*
    applys fmap_union_eq_inv_of_disjoint E. rewrite heap_ro_r.
     rewrites (>> NH2 P2). destruct D' as (D1&D2).*)
     admit.
   }
  asserts F: (heap_compat h2 h1'). {
    clears h h' P1 P1'. specializes NH2 P2. clears P2.
    destruct D as (Da&Db).
    destruct D' as (Da'&Db').
    destruct C2 as (C2a&C2b).
    lets DH2: (heap_disjoint_components h2).
    rew_heap in *.
    split.
    { rewrite NH2. applys fmap_agree_empty_l. }
    { rewrite fmap_disjoint_3_unfold. splits.
      { auto. }
      { auto. }
      { rewrite NH2. rewrite~ S. } } }
  exists (h2 \u h1') v. splits~.
  { fmap_red~.
    { rewrite~ heap_ro_state. }
    { rewrite~ heap_ro_state. } }
  {
*)
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Term rules *)

Lemma rule_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF h N. exists h v. splits~.
  { applys red_val. }
  { hhsimpl. hchanges M. }
Qed.

Lemma rule_if : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v'&R&K&E): (rm M) HF h.
  exists h' v'. splits~. { applys~ red_if. }
Qed.

Lemma rule_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst_trm x X t2) (Q1 X) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1&E1): (rm M1) HF h.
  forwards* (h2'&v2&R2&K2&E2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_let R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
  { congruence. }
Qed.

Lemma rule_let_val : forall x v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst_trm x X t2) H Q) ->
  triple (trm_let x (trm_val v1) t2) H Q.
Proof using.
  introv M. forwards~ M': (rm M).
  applys_eq~ (>> rule_let H (fun x => \[x = v1] \* H)) 2.
  { applys rule_val. hsimpl~. }
  { intros X. applys rule_extract_hprop. intro_subst. applys M'. }
Qed.

Lemma rule_app : forall f x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst_trm f F (subst_trm x V t1)) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_arg. }
  admit.
  admit.
Qed.

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val),
    (forall X H' Q',
      triple (subst_trm f F (subst_trm x X t1)) H' Q' ->
      triple (trm_app F X) H' Q') ->
    triple (subst_trm f F t2) H Q) ->
  triple (trm_let f (trm_val (val_fix f x t1)) t2) H Q.
Proof using.
  introv M. applys rule_let_val. intros F EF.
  applys (rm M). clears H Q. intros X H Q. applys~ rule_app.
Qed.

Section RulesPrimitiveOps.
Transparent hstar hsingle.
Hint Resolve heap_compat_union_l heap_compat_union_r.
Hint Resolve fmap_agree_empty_l fmap_agree_empty_r.

Lemma rule_ref : forall v,
  triple (val_ref v) \[] (fun r => Hexists l, \[r = val_loc l] \* l ~~> v).
Proof using.
  intros. intros HF h N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null (heap_state h) v).
  lets~ (h1'&E1&E2): heap_make (fmap_single l v) (fmap_empty:state).
  asserts E3: (heap_state h1' = fmap_single l v).
  { unstate. rewrite E1,E2. fmap_eq. }
  asserts D1': (\# (heap_state h) (heap_state h1')).
  { unfold heap_state at 2. rewrite E1,E2. fmap_disjoint. }
  asserts C: (heap_compat h1' h).
  { split.
    { rewrite~ E2. }
    { rewrite E1,E2. lets: heap_disjoint_components h.
      fmap_disjoint. } }
  exists (h1' \u h) (val_loc l). splits~.
  { rew_state~. applys~ red_ref. }
  { exists h1' h. split~. splits~.
    { exists l. applys~ himpl_hpure_r (l ~~> v). hnfs~. }
    { rew_heap in N. hhsimpl~. } }
  { rew_heap~. rewrite E2. fmap_eq. }
Qed.
(*
Lemma rule_get_ro : forall v l,
  triple (val_get (val_loc l)) (RO (l ~~> v)) (fun x => \[x = v]).
Proof using.
  intros. intros HF h N.
  exists h v. splits~.
  { applys red_get. destruct N as (h1&h2&D&P1&P2&E).
    destruct P1 as (h11&(Q1&Q2)&E1&E2).
    subst h. rewrite heap_fmap_def. (* todo: cleanup *)
    rewrite fmap_union_comm_of_disjoint; [|rew_heap~].
    rew_heap~. rewrite E1,E2,Q1,Q2. rew_state.
    applys~ fmap_union_single_l_read. }
  { rewrite hstar_pure. split~. hhsimpl~. }
Qed.

Lemma rule_set : forall w l v,
  triple (val_set (val_pair (val_loc l) w)) (l ~~> v) (fun r => \[r = val_unit] \* l ~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&D&P1&P2&E).
  destruct P1 as (Q1&Q2).
  lets~ (h1'&E1'&E2'): heap_make (fmap_single l w) (fmap_empty:state).
  asserts Dl: (fmap_disjoint (fmap_single l w) (heap_state h2)).
  { destruct D as (D1&D2). rewrite Q1 in D2. unstate.
    applys fmap_disjoint_single_set v. auto. }
  asserts C: (heap_compat h1' h2).
  { destruct D as (D1&D2). unfolds. rewrite E1',E2'.
    unfold heap_state in Dl. split~. }
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. rew_state~. rewrite E.  (* todo: cleanup *)
    rewrite (@heap_fmap_def h1'). rewrite (@heap_fmap_def h2).
    rewrite E1',E2'. rew_state~.
    applys~ fmap_union_single_to_update v w.
    rewrite (@heap_fmap_def h1). rewrite Q1,Q2. fmap_eq. }
  { rew_heap. rewrite hstar_pure. split~.
    { exists h1' h2. splits~.
      { hnfs~. }
      { clear Dl E C. (* todo *) hhsimpl~. } } }
  { rewrite E. rew_heap~. rewrite Q2,E2'. auto. }
Qed.
*)

End RulesPrimitiveOps.

End TripleHighLevel.
*)
