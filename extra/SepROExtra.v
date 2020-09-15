(* not needed *)
Lemma to_ro_duplicatable : forall h,
  duplicatable (= to_ro h).
Proof using.
  intros h. unfolds. intros h' E. subst.
  lets D: heap_compat_refl_to_ro h. do 2 esplit. splits*. 
  rewrite* heap_union_eq_of_compat. rewrite* union_same.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Extra *)



Lemma decomposition : forall H,
  H ==> (\exists H1 H2, \[Normal H1 /\ (haffine H -> haffine H1)]
                     \* \[ReadOnly H2] \* (H1 \* H2)). 
Proof using.
  intros H h K. rewrite (heap_eq_union_rw_ro h).
  exists (= h^rw) (= h^ro). do 2 rewrite hstar_hpure. splits.
  { splits. 
    { intros ? ->. rew_heap*. }
    { intros F. Transparent haffine. unfolds haffine. intros ? ->.
      specializes F K. rewrite (heap_eq_union_rw_ro h) in F. 
      forwards*: heap_affine_union_inv F. } }
  { intros ? ->. rew_heap*. } 
  { do 2 esplit. splits*. }
Qed.

Lemma triple_decomposition : forall t H H' Q,
  (forall H1 H2, Normal H1 -> ReadOnly H2 -> (haffine H' -> haffine H1) ->
                 triple t (H \* H1 \* H2) Q) ->
  triple t (H \* H') Q.
Proof using.
  introv M.
  forwards K: decomposition H'.
  lets WH: himpl_frame_r H K.
  applys* triple_conseq WH. 
  rewrite hstar_comm. (* manual xpull *)
  rewrite hstar_hexists. applys triple_hexists. intros H1.
  rewrite hstar_hexists. applys triple_hexists. intros H2.
  rewrite hstar_assoc. applys triple_hpure. intros (N1&F1).
  rewrite hstar_assoc. applys triple_hpure. intros N2.
  rewrite hstar_comm. rewrite <- hstar_assoc.
  rewrite hstar_assoc. applys* M.
Qed.

Lemma triple_haffine_pre' : forall t H H' Q,
  triple t H Q ->
  haffine H' ->
  triple t (H \* H') Q.
Proof using.
  introv M F. applys triple_decomposition.
  intros H1 H2 N1 N2 NF. rewrite <- hstar_assoc.
  applys* triple_frame_ReadOnly.
  applys* triple_haffine_pre.
Qed.



(* not needed, except for next lemma *)
Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using.
  intros. apply himpl_antisym.
  { intros h K. applys hexists_intro h.
    rewrite* hstar_hpure_l. }
  { xpull. intros h K. intros ? ->. auto. }
Qed.

(* not needed *)
Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using.
  introv M. rewrite (hexists_named_eq H).
  applys triple_hexists. intros h.
  applys* triple_hpure.
Qed.





Lemma disjoint_filter_mode : forall h1 h2 m1 m2,
  disjoint h1 h2 ->
  disjoint (filter_mode m1 h1) (filter_mode m2 h2).
Proof using.
  introv D. rewrite disjoint_eq_not_indom_both in *.
  unfold filter_mode. intros x M1 M2.
  rewrite (@indom_filter_eq _ _ val_mode_inhab) in M1,M2.
  false*.
Qed.

Lemma agree_filter_mode : forall h1 h2 m1 m2,
  agree h1 h2 ->
  agree (filter_mode m1 h1) (filter_mode m2 h2).
Proof using.
  introv D. intros l v1 v2 E1 E2. 
  unfold filter_mode in *. intros x M1 M2.
  rewrite (@indom_filter_eq _ _ val_mode_inhab) in M1,M2.
  false*.
Qed.




Lemma heap_union_f : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^rw = h1^rw \u h2^rw.
Proof using. skip. (*
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq. *)
Qed.

Lemma heap_union_r : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^ro = h1^ro \u h2^ro.
Proof using. skip. (*
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq. *)
Qed.

(*
Lemma heap_union_def : forall h1 h2,
  heap_compat h1 h2 ->
  exists D,
  h1 \u h2 = exist (h1^rw \+ h2^rw, h1^ro \+ h2^ro) D.
Proof using.
  introv M. unfold heap_union.
  rewrite (classicT_l M). esplit. destruct~ M.
Qed.

Lemma heap_union_spec : forall h1 h2,
  heap_compat h1 h2 ->
     (h1 \u h2)^rw = h1^rw \+ h2^rw
  /\ (h1 \u h2)^ro = h1^ro \+ h2^ro.
Proof using.
  introv M. lets (D&E): heap_union_def M. rewrite~ E.
Qed.



Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using. 
  intros. unfold RO. applys himpl_antisym.
  { xpull ;=> h' R.
    lets (h''&R'): hexists_inv (rm R).
    rewrite hstar_hpure_l in R'. destruct R' as [N ->].
    rewrite to_ro_idempotent. xsimpl*. }
  { xpull ;=> h' R. xsimpl (to_ro h').
    { applys hexists_intro h'. rewrite* hstar_hpure_l. }
    { rewrite* to_ro_idempotent. } } 
Qed.
*)