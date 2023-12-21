(* TODO


(** Useful for queues *)

Lemma MCell_eq : forall `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (q:A2) (p:loc),
  (p ~> MCell v q) = (p `.` hd ~~> v) \* (p `.` tl ~~> q).
Proof using.
  intros. do 2 rewrite Record_cons. rewrite Record_nil. hsimpl.
Qed.

Lemma MCell_hstar_MCell_inv : forall `{EA1:Enc A1} `{EA2:Enc A2} (p1 p2:loc) (x1 x2:A1) (y1 y2:A2),
  p1 ~> MCell x1 y1 \* p2 ~> MCell x2 y2 ==+> \[p1 <> p2].
Proof using.
Admitted.
(*
  intros. rewrite MCell_eq. tests C: (p1 = p2).
  { unfold Hfield. repeat xunfold at 1.
    rewrite Record_cons. hchanges (@hstar_hfield_same_loc_disjoint p2 hd).  }
  { hsimpl~. }
*)

Lemma MListSeg_then_MCell_inv_neq : forall `{EA:Enc A} `{EA1:Enc A1} `{EA2:Enc A2},
 forall (p q:loc) (L:list A) (v1:A1) (v2:A2),
  p ~> MListSeg q L \* q ~> MCell v1 v2 ==+> \[L = nil <-> p = q].
Proof using.
Admitted.
(*
  intros. destruct L.
  { rewrite MListSeg_nil_eq. hsimpl*. split*. (* TODO: why not proved? *) }
  { rewrite MListSeg_cons_eq. hpull ;=> p'. tests: (p = q).
    { lets: (>> MCell_hstar_MCell_inv q q v1 a v2 p').  }
    { hsimpl. split; auto_false. } }
Qed.
*)

(*
Proof using.
  xcf. xunfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapps.
  xchanges (>> MListSeg_then_MCell_inv_neq pf pb). ;=> R.
  (* xchange (MListSeg_then_MCell_inv_neq pf pb). xpull ;=> R. *)
  xapp. hsimpl. isubst. fequals. rew_bool_eq. rewrite R. iff; congruence.
Qed.
*)


*)
