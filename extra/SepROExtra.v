

Lemma hoare_frame_read_only : forall t H1 Q1 H2,
  hoare t (H1 \* RO H2) Q1 ->
  onlyrw H2 ->
  hoare t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  hint heap_compat_union_l, heap_compat_union_r, heap_compat_toro_r.
  introv M N. intros ? (h1&h2&P1&P2&C1&->).
  forwards (h'&v&R&L&S): M (h1 \u toro h2).
  { applys* hstar_intro h1 (toro h2). { applys* toro_pred. } }
  lets (D'&E'): heap_components h'.
  lets C1': heap_compat_toro_r C1.
  rewrites S in *. rew_heap* in *.
  forwards* (D1'&D2'): heap_compat_union_r_inv (rm D').
  forwards D2'': heap_compat_toro_r_inv D2'. { rew_heap*. }
  exists ((h'^rw) \u (h1^ro) \u h2) v. splits.
  { applys_eq R.
     { rew_fmap*. }
     { rewrites (rm E'). rew_heap*. rew_fmap*. } }
  { rew_heap*. erewrite (@onlyrw_proj_rw h2); eauto. (* TODO tactic *)
    applys* hstar_intro. }
  { rew_heap*. }
Qed.



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



(* NOW: remove *)
Lemma disjoint_to_ro : forall h1 h2,
  disjoint h1 h2 ->
  disjoint h1 (to_ro h2).
Proof using. introv M. rewrite* disjoint_to_ro_eq. Qed.





(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [normal] *)

Class Normal (H:hprop) : Prop :=
  normal_emp h : H h -> h^ro = Fmap.empty.
Hint Mode Normal ! : typeclass_instances.

Notation Normal_post Q := (forall x, Normal (Q x)).

Instance Normal_hempty :
  Normal \[].
Proof using.
  Transparent hempty hpure.
  introv M. unfolds hempty, hpure. subst. autos*.
Qed.

Instance Normal_hpure : forall P,
  Normal \[P].
Proof using.
  Transparent hpure.
  introv (p&M). unfolds hempty. subst. auto.
Qed.

Lemma Normal_hempty' : (* simpler proof *)
  Normal \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ Normal_hpure.
Qed.

Instance Normal_hsingle : forall l v,
  Normal (hsingle l v).
Proof using.
  Transparent hsingle.
  introv M. unfolds hsingle. autos*.
Qed.

Instance Normal_hstar : forall H1 H2,
  Normal H1 ->
  Normal H2 ->
  Normal (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ).
  lets (_&E): heap_eq_forward EQ. simpls. rewrite E.
  rewrite~ heap_union_r.
  rewrites (>> N1 P1). rewrites (>> N2 P2).
  rewrite~ Fmap.union_empty_r.
Qed.

Generalizable Variables A. (* TODO: move *)

Instance Normal_hexists : forall A (J:A->hprop),
  Normal_post J ->
  Normal (hexists J).
Proof using. introv M (x&N). rewrites~ (>> M N). Qed.

Instance Normal_hforall_inhab : forall `{Inhab A} (J:A->hprop),
  Normal_post J ->
  Normal (hforall J).
Proof using.
  introv IA M N. lets M': M (arbitrary (A:=A)). 
  lets N': N (arbitrary (A:=A)). applys M' N'.
Qed.

Instance Normal_hforall : forall A (x:A) (J:A->hprop),
  Normal (J x) ->
  Normal (hforall J).
Proof using. introv M N. applys M N. Qed.

Instance Normal_hor : forall H1 H2,
  Normal H1 ->
  Normal H2 ->
  Normal (hor H1 H2).
Proof using. introv M1 M2. applys Normal_hexists. intros b. case_if*. Qed.

Instance Normal_hand_l : forall H1 H2,
  Normal H1 ->
  Normal (hand H1 H2).
Proof using. introv M1. applys* Normal_hforall true. Qed.

Instance Normal_hand_r : forall H1 H2,
  Normal H2 ->
  Normal (hand H1 H2).
Proof using. introv M1. applys* Normal_hforall false. Qed.

Lemma Normal_himpl : forall H1 H2,
  Normal H2 ->
  (H1 ==> H2) ->
  Normal H1.
Proof using. introv HS HI M. lets: HI M. applys* HS. Qed.

(* Note: Normal_hwand is not true *)

Lemma Normal_hpure_star_hpure : forall (P:Prop) H,
  (P -> Normal H) ->
  Normal (\[P] \* H).
Proof using.
  introv N (h1&h2&P1&P2&M1&EQ).
  lets (_&E): heap_eq_forward EQ. simpls. rewrite E.
  rewrite~ heap_union_r.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rewrites~ (>> N P2). rew_fmap~.
Qed.



Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ heap_union_empty_l. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  intros. unfold hprop, hstar. extens. intros h.
  hint Fmap.agree_sym.
  iff (h1&h2&M1&M2&D&U).
  { exists h2 h1. subst. splits~. }
  { exists h2 h1. subst. splits~. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. unfold hprop, hstar. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M2&P1&P2&E1)&M3&M1&E2). subst h'.
    lets~ (M1a&M1b): heap_compat_union_l_inv M1.
    exists h1 (h2 \u h3). splits.
    { auto. }
    { exists h2 h3. splits*. }
    { applys* heap_compat_union_r. }
    { subst. applys~ heap_union_assoc. } }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&E1)&M1&E2). subst h'.
    lets~ (M1a&M1b): heap_compat_union_r_inv M1.
    exists (h1 \u h2) h3. splits.
    { exists h1 h2. splits*. }
    { auto. }
    { applys* heap_compat_union_l. }
    { subst. symmetry. applys~ heap_union_assoc. } }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. rewrite (hempty_inv K). applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 (h1&h2&K1&K2&D&->). applys* heap_affine_union.
Qed



Definition onlyrw (H:hprop) : Prop :=
  forall h, H h -> h^^ro = Fmap.empty.

Definition onlyrw_post A (Q:A->hprop) : Prop :=
  forall x, onlyrw (Q x).

Lemma onlyrw_part_ro : forall H h,
  onlyrw H ->
  H h ->
  h^^ro = Fmap.empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyrw_part_rw : forall H h,
  onlyrw H ->
  H h ->
  h^^rw = h.
Proof using.
  introv N K. specializes N (rm K).
  rewrite heap_state_def. rewrite N. rew_fmap*.
Qed.

Lemma onlyrw_proj_ro : forall H h,
  onlyrw H ->
  H h ->
  h^ro = heap_empty.
Proof using. introv N K. applys heap_eq; simple*. Qed.

Lemma onlyrw_proj_rw : forall H h,
  onlyrw H ->
  H h ->
  h^rw = h.
Proof using.
  introv N K.
  applys heap_eq_projs; rew_heap*.
  specializes N (rm K).

 applys heap_eq. split*. rew_heap.

  heap_eq_projs

Qed.
  introv N K. specializes N (rm K).
  rewrite heap_state_def. rewrite N. rew_fmap*.
Qed.

Lemma onlyrw_of_haffine : forall H,
  haffine H ->
  onlyrw H.
Proof using.
  introv M. intros h K. rewrite haffine_eq in M.
  specializes M K. applys* heap_affine_onlyrw.
Qed.

Lemma onlyrw_hempty :
  onlyrw \[].
Proof using.
  Transparent hempty hpure.
  introv M. unfolds hempty, hpure. subst. rew_heap*.
Qed.

Lemma onlyrw_hpure : forall P,
  onlyrw \[P].
Proof using.
  Transparent hpure.
  introv (p&M). unfolds hempty. subst. rew_heap*.
Qed.

Lemma onlyrw_hgc :
  onlyrw \GC.
Proof using.
  introv (H&M). rewrite hstar_hpure_l in M. destruct M as (F&R).
  applys* heap_affine_onlyrw. rewrite haffine_eq in F. applys* F.
Qed.

Lemma onlyrw_hempty' : (* simpler proof *)
  onlyrw \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ onlyrw_hpure.
Qed.

Lemma onlyrw_hsingle : forall l v,
  onlyrw (hsingle l v).
Proof using. introv (E&N). autos*. Qed.

Lemma onlyrw_hstar : forall H1 H2,
  onlyrw H1 ->
  onlyrw H2 ->
  onlyrw (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&->). rew_heap*.
  rewrites (>> N1 P1). rewrites (>> N2 P2). rew_fmap*.
Qed.

Lemma onlyrw_hexists : forall A (J:A->hprop),
  onlyrw_post J ->
  onlyrw (hexists J).
Proof using. introv M (x&N). rewrites~ (>> M N). Qed.

Hint Resolve onlyrw_hempty onlyrw_hstar onlyrw_hgc : onlyrw.

(* Remaining lemmas are not needed for the soundness proof,
   but may be needed by clients. *)

Lemma onlyrw_hforall_inhab : forall `{Inhab A} (J:A->hprop),
  onlyrw_post J ->
  onlyrw (hforall J).
Proof using.
  introv IA M N. lets M': M (arbitrary (A:=A)). lets N': N (arbitrary (A:=A)).
  applys M' N'.
Qed.

Lemma onlyrw_hforall : forall A (x:A) (J:A->hprop),
  onlyrw (J x) ->
  onlyrw (hforall J).
Proof using. introv M N. applys M N. Qed.

Lemma onlyrw_hor : forall H1 H2,
  onlyrw H1 ->
  onlyrw H2 ->
  onlyrw (hor H1 H2).
Proof using. introv M1 M2. applys onlyrw_hexists. intros b. case_if*. Qed.

Lemma onlyrw_hand_l : forall H1 H2,
  onlyrw H1 ->
  onlyrw (hand H1 H2).
Proof using. introv M1. applys* onlyrw_hforall true. Qed.

Lemma onlyrw_hand_r : forall H1 H2,
  onlyrw H2 ->
  onlyrw (hand H1 H2).
Proof using. introv M1. applys* onlyrw_hforall false. Qed.

Lemma onlyrw_himpl : forall H1 H2,
  onlyrw H2 ->
  (H1 ==> H2) ->
  onlyrw H1.
Proof using. introv HS HI M. lets: HI M. applys* HS. Qed.

(* Note: onlyrw_hwand is not true *)

Lemma onlyrw_hpure_star_hpure : forall (P:Prop) H,
  (P -> onlyrw H) ->
  onlyrw (\[P] \* H).
Proof using.
  introv N (h1&h2&P1&P2&M1&->). rew_heap*.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rew_fmap. rewrites~ (>> N P2).
Qed.