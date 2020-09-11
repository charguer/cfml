
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
