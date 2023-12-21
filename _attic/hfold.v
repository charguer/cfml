

Lemma hfold_list_nil : forall f,
  hfold_list f nil = \[].
Proof using. auto. Qed.
(* intros. rewrite hfold_list_eq; unfold hfold_list'. rewrite~ fold_nil. *)

Lemma hfold_list_cons : forall f x l,
  hfold_list f (x::l) = (f x) \* (hfold_list f l).
Proof using. auto. Qed.
(* intros. repeat rewrite hfold_list_eq; unfold hfold_list'. rewrite~ fold_cons. *)

Lemma hfold_list_one : forall f x,
  hfold_list f (x::nil) = f x.
Proof using. intros. simpl. xsimpl. Qed.
(*
Proof using. intros. rewrite hfold_list_eq; unfold hfold_list'. rewrite~ fold_one. Qed.
*)
(*

Lemma hfold_list_app : forall f l1 l2,
  hfold_list f (l1 ++ l2) = (hfold_list f l1) \* (hfold_list f l2).
Proof using. intros. repeat rewrite hfold_list_eq; unfold hfold_list'. rewrite~ fold_app. Qed.

Lemma hfold_list_last : forall f x l,
  hfold_list f (l & x) = (hfold_list f l) \* (f x).
Proof using. intros. repeat rewrite hfold_list_eq; unfold hfold_list'. rewrite~ fold_last. Qed.
*)

End HfoldList.

Hint Rewrite hfold_list_nil hfold_list_cons hfold_list_one : rew_heapx.
(* hfold_list_app hfold_list_last*)

(*
Definition hfold_list2' A B (f:A->B->hprop) (l1:list A) (l2:list B) : hprop :=
  hfold_list' (fun '(x1,x2) => f x1 x2) (LibList.combine l1 l2).

-- only for same lengths
Lemma hfold_list2_eq : 
  hfold_list2 = hfold_list2'.
Proof using.
  unfold hfold_list2', hfold_list'. applys fun_ext_5 ;=> A B f l1.
  induction l1 as [|x1 l1']; intros l2; destruct l2 as [|x2 l2'].
  { rewrite . }
  { unfold hfold_list'. rewrite fold_cons. simpl. rewrite~ IHl'. }
Qed.
*)

(* intros. unfold hfold_list2. rew_listx. rewrite~ hfold_list_nil.  *)




=========


(* LATER
Lemma MList_contents_Cons : forall A `{EA:Enc A} (L:list A) x p',
  (MList_contents (Cons x p') L) ==> \exists L', \[L = x::L'] \* (p' ~> MList L').
Proof using.
  intros. unfold MList_contents. destruct L.
  { xsimpl. }
  { xpull ;=> p'' E. unfolds @Cons.
    rewrite (enc_loc_eq p'), (enc_loc_eq p'') in E. (* rew_enc in *. *)
    asserts_rewrite (x = a). { admit. }
    (* Enc_injective EA --- all encoders should be injective!  *)
    inverts E. xsimpl~. }
Admitted.
*)

(* ---------------------------------------------------------------------- *)
(** Detailed proof for set_head *)

(*
Lemma Triple_set_head' : forall A `{EA:Enc A} (L:list A) p x y,
  TRIPLE (set_head ``p ``y)
    PRE (p ~> MList (x::L))
    POST (fun (_:unit) => p ~> MList (y::L)).
Proof using.
  intros. (*  xwp. xgc_post. *) xwp_fun' tt.
  xchange MList_cons_unfold ;=> q. xapp.
  applys xcase_lemma0 ;=> E1.
  { false. }
  { applys xcase_lemma2.
    { intros x' q' E. unfold Cons in E. rew_enc in E. inverts E.
      xval (Cons y q). xapp. xchanges MList_cons. }
    { intros N. false N. reflexivity. } }
Qed.
*)


Lemma MListOf_eq : forall A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc),
  p ~> MListOf R L =
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ Field.head := x; Field.tail := p'} 
                   \* (x ~> R X) \* (p' ~> MListOf R L')
  end.
Proof using. intros. xunfold MListOf at 1. destruct~ L. Qed.
*)


(* Bad:


Fixpoint MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf R L')
  end.

Lemma MListOf_eq : forall A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc),
  p ~> MListOf R L =
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf R L')
  end.
Proof using. intros. xunfold MListOf at 1. destruct~ L. Qed.


*)
