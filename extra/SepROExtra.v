
(* needed?
Lemma RO_ro : forall h,
  RO (= (h^ro)) (h^ro).
Proof using.
  intros. exists h. split~.
Qed.
*)


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




(* TODO:

Module FMaps.
Section Map.
Transparent Fmap.map.
(* TODO: this function only maps values, we'd need another function to map keys as well *)

Program Definition map_ A B1 B2 `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:fmap A B1) : fmap A B2 :=
  Fmap.make (fun (x:A) => match Fmap.read M x with
    | None => None
    | Some y => Some (f x y)
    end) _.
(*
Transparent update (*update_inst*) bag_update_as_union_single single_bind single_bind_inst LibMap.union_inst LibContainer.union.
*)
Lemma map_update : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:Fmap.map A B1) x y,
  map_ f (Fmap.update M x y) = Fmap.update (map_ f M) x (f x y).
Proof using.
  intros. extens. intros a. unfold map_. simpl. unfold bag_update_as_union_single.
  unfold single_bind. simpl. unfold single_bind_impl. unfold LibContainer.union. simpl.
  unfold LibMap.union_impl.
  case_if; subst. autos*. destruct* (M a). (* TODO: cleanup *)
Qed.

Transparent dom dom_inst.

Lemma dom_map : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:map A B1),
  dom (map_ f M) = dom M.
Proof using.
  intros. unfold map_. simpl. unfold dom_impl.
  fequal. extens. intros x. destruct (M x); auto_false.
Qed.

Transparent read LibMap.read_inst.

Lemma read_map : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:map A B1) (x:A),
  x \indom M ->
  (map_ f M)[x] = f x (M[x]).
Proof using.
  introv Hx. unfold map_. simpl. unfold read, LibMap.read_inst. unfold LibMap.read_impl.
  unfold dom, LibMap.dom_inst, dom_impl in Hx. rewrite in_set_st_eq in Hx.
  destruct (M x); auto_false.
Qed.

Axiom extens : forall A `{Inhab B} (M1 M2:map A B),
  dom M1 = dom M2 ->
  (forall (x:A), x \indom M1 -> M1[x] = M2[x]) ->
  M1 = M2.

End Map.

Section Filter.
Transparent map.

Definition filter A `{Inhab B} (f:A->B->Prop) (M:map A B) : map A B :=
  fun (x:A) => match M x with
    | None => None
    | Some y => If f x y then Some y else None
    end.

Transparent update bag_update_as_union_single single_bind single_bind_inst LibMap.union_inst LibContainer.union.

Transparent dom dom_inst.

Lemma dom_filter : forall A `{Inhab B} (f:A->B->Prop) (M:map A B),
  dom (filter f M) \c dom M.
Proof using.
Admitted.

Transparent read LibMap.read_inst.

Lemma read_filter : forall A `{Inhab B} (f:A->B->Prop) (M:map A B) x,
  x \indom M ->
  f x (M[x]) ->
  (filter f M)[x] = M[x].
Proof using.
Admitted.

End Filter.

End FMaps.
*)



(* Hint Resolve Fmap.agree_sym. *)


(* TODO: check what's actually needed *)
Lemma heap_eq_forward : forall h1 h2,
  h1 = h2 ->
  h1^rw = h2^rw /\ h1^ro = h2^ro.
Proof using. intros. subst*. Qed.



(* ---------------------------------------------------------------------- *)
(* ** Equalities on heaps *)

Lemma heap_eq : forall h1 h2,
  h1^rw = h2^rw ->
  h1^ro = h2^ro ->
  h1 = h2.
Proof using.
  introv M1 M2. forwards (E1&_): heap_eq_disjoint_union_rw_ro h1.
  forwards (E2&_): heap_eq_disjoint_union_rw_ro h2. congruence.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_empty] *)

(* not needed
Lemma heap_empty_state : heap_state heap_empty = Fmap.empty.
Proof using.
  unfold heap_empty. unfold heap_state. rewrite* map_empty.
Qed.

Hint Rewrite heap_empty_state : rew_heap.
*)


(* not needed? *)
Lemma heap_union_state : forall h1 h2,
  heap_compat h1 h2 ->
  heap_state (h1 \u h2) = heap_state h1 \+ heap_state h2.
Proof using. introv D. rew_fmap*. Qed.



(* ---------------------------------------------------------------------- *)
(* ** Properties  *)

Lemma heap_state_components : forall h,
  heap_state h = heap_state (h^rw) \+ heap_state (h^ro).
Proof using.
  intros. lets (E&D): heap_eq_disjoint_union_rw_ro h.
  rewrite E at 1. rew_fmap*. applys* heap_compat_of_disjoint.
Qed.


(*
Lemma hgc_intro : forall h,
  \GC h.
Proof using. intros. applys hgc_of_heap_affine. hnfs*. Qed.
*)


(* equivalent to:
Definition RO' (H:hprop) : hprop :=
  \exists h', \[H h'] \* (= to_ro h').
 *)



Lemma proj_proj_swap : forall h m1 m2,
  (h^m1)^m2 = (h^m2)^m1.
Proof using.
  intros. unfold proj. applys* filter_swap.
Qed.

(* Corollary for automation *)
Lemma disjoint_proj_proj_swap : forall h1 h2 m11 m12 m21 m22,
  disjoint (h1^m11) (h2^m21) ->
  disjoint ((h1^m12)^m11) ((h2^m22)^m21).
Proof using.
  introv D. rewrite (proj_proj_swap h1), (proj_proj_swap h2).
  applys* disjoint_proj.
Qed.