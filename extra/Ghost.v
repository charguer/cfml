
(*-------------------------

Notes for


Lemma hwand_eq : forall (H1 H2:hprop), hwand H1 H2 =
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].
Proof using. auto. Qed.

Lemma hwand_heq_self_inv : forall s H,
  ((= s) \-* H) s ->
  H s.
Proof using.
Admitted.


Lemma wps_eq : forall t Q,
  wps t Q =
     hor (\exists v, \[t = trm_val v] \* Q v)
         (\forall s, (= s) \-*
            hand ((= s) \* \[reducible s t])
                 (\forall s' t', \[step s t s' t'] \-* (= s') \* wps t' Q)).
Proof using.
  Local Transparent hexists hforall hor hand.
  intros. extens. intros s. rewrite wps_step.
  (*unfold hor, hand, hexists, hforall. *)
  iff M.
  { destruct M as [(v&->&Hv)|(HR&HS)].
    { exists true. exists v. rewrite* hstar_hpure_l. }
    { exists false. admit. }
    (* intros s'. rewrite hwand_eq. unfold hexists. Search hwand. intros b. case_if.
      { rewrite hstar_hpure_r. splits*. *) }
  { unfold hor in M. lets (b&M1): hexists_inv (rm M). case_if.
    { left. lets (v&M2): hexists_inv (rm M1). rewrite hstar_hpure_l in M2.
      destruct M2. subst*. }
    { right. specializes M1 s. lets M2: hwand_heq_self_inv (rm M1).
      unfold hand in M2. split.
      { lets Ma: (rm M2) true. rewrite hstar_hpure_r in Ma. autos*. }
      { lets Mb: (rm M2) false.
        intros s' t' HR. specializes Mb s'. specializes Mb t'.
        rewrite* hwand_hpure_l in Mb.


  destruct M as [|].
Qed.
*)


