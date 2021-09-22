(**

Formalization of arrays, with lifting.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require LibListZ.
From CFML Require Export WPArrayNonlifted.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types f : var.
Implicit Types k : field.
Implicit Type l p q : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Lifted access rules for arrays *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint Cells A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (Cells L' (S p))
  end.

Definition Array A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  hheader (length L) p \* Cells L (p+1)%nat.

Lemma Heapdata_Array : forall (A:Type) (EA:Enc A),
    Heapdata (Array (A:=A)).
Proof.
  constructor. intros x y X Y.
  unfold Array. repeat rewrite repr_eq.
  rewrite <- (repr_eq (hheader (length X)) x).
  rewrite <- (repr_eq (hheader (length Y)) y).
  xchanges* Heapdata_hheader.
Qed.

(* TODO: not true with headers
         avoid name clash with the non-lifted version
Section ArrayProp.
Context A `{EA:Enc A}.
Implicit Types L : list A.
Implicit Types x : A.

Lemma Array_nil_eq : forall p,
  p ~> Array (@nil A)  = \[].
Proof using. auto. Qed.

Lemma Array_cons_eq : forall p x L,
  p ~> Array (x::L) = (p ~~> x) \* (S p) ~> Array L.
Proof using. auto. Qed.

End ArrayProp.
*)

(** Affinity *)

Lemma haffine_Cells : forall A `{EA:Enc A} p (L:list A),
  haffine (p ~> Cells L).
Proof.
  intros. gen p. induction L; intros; xunfold Cells; xaffine.
  rewrite <- (repr_eq (Cells L)). xaffine.
Qed.

Hint Resolve haffine_Cells : haffine.

Lemma haffine_Array : forall A `{EA:Enc A} p (L: list A),
  haffine (p ~> Array L).
Proof using.
  intros. xunfold Array. rewrite <- (repr_eq (Cells L)). xaffine.
Qed.

Hint Resolve haffine_Array : haffine.

(* TODO LATER

(* TODO ??
Lemma Array_eq_array : forall L p,
  Array L p = Array (LibList.map enc L) p.
Proof using.
  intros L. induction L; intros.
  { auto. }
  { simpl. rewrite IHL. rew_listx. auto. }
Qed.

Lemma Array_unlift : forall L p,
  p ~> Array L = array (LibList.map enc L) p.
Proof using. intros. rewrite Array_eq_array. Qed.
*)

Lemma Array_one_eq : forall p x,
  p ~> Array (x::nil) = (p ~~> x).
Proof using. intros. rewrite Array_cons_eq, Array_nil_eq. rew_heap~. Qed.

Lemma Array_concat_eq : forall p L1 L2,
   p ~> Array (L1++L2) = p ~> Array L1 \* (p + length L1)%nat ~> Array L2.
Proof using.
  intros. repeat rewrite Array_unlift. rew_listx. rewrite Array_concat_eq.
   rewrite length_map. auto. (* TODO: add to rew_listx. *)
Qed.

Lemma Array_last_eq : forall p x L,
  p ~> Array (L&x) = p ~> Array L \* ((p + length L)%nat ~~> x).
Proof using. intros. rewrite Array_concat_eq. rewrite~ Array_one_eq. Qed.

Transparent loc. (* TODO: avoid the need for this by
   using pointer arithmetic operator for p+n *)

Lemma Array_middle_eq : forall n p L,
  0 <= n < length L ->
  (p ~> Array L) = \exists L1 x L2, \[L = L1++x::L2] \* \[length L1 = n :> int] \*
    p ~> Array L1 \* (abs(p+n) ~~> x) \* (p + length L1 + 1)%nat ~> Array L2.
Proof using.
  intros. repeat rewrite Array_unlift.
  rewrites (>> Array_middle_eq n p (map enc L)).
  rewrite length_map. auto. (* TODO: add to rew_listx. *)
  apply himpl_antisym.
  { xpull ;=> L1 x L2 N1 N2.
    lets (L1'&X'&L2'&E1&E2&E3&E4): map_eq_middle_inv N1. subst.
    rewrite length_map. xsimpl~ L1' X' L2'.
    do 2 rewrite Array_unlift. xsimpl. }
  { xpull ;=> L1 x L2 N1 N2. xsimpl (map enc L1) (enc x) (map enc L2).
    repeat rewrite Array_unlift. rewrite length_map. (* todo rew_list *) xsimpl.
    rewrite~ length_map. subst L. rew_listx~. }
Qed.

End ArrayProp.

Global Opaque Array.

Lemma Triple_alloc_array : forall n,
  n >= 0 ->
  TRIPLE Triple (val_alloc ``n)
    PRE \[]
    POST (fun p => \exists (L:list val), \[length L = n :> int] \* p ~> Array L).
Proof using.
  intros. unfold Triple. xapplys~ triple_alloc_array.
  intros r x L. intros E N. subst. unfold Post. xsimpl~ L.
  rewrite Array_unlift. rewrite map_id_ext. xsimpl.
  { intros v. rewrite~ enc_val_eq. }
Qed.

Import LibListZ.
Implicit Types i ofs len : int.

Section ArrayRules.
Context A `{EA:Enc A} `{IA:Inhab A}.
Implicit Types L : list A.

Hint Resolve index_map.

Lemma Triple_array_get : forall p i L,
  index L i ->
  TRIPLE Triple (val_array_get ``p ``i)
    PRE (p ~> Array L)
    POST (fun (r:A) => \[r = L[i]] \* p ~> Array L).
Proof using.
  intros. unfold Triple. rewrite Array_unlift.
  xapplys~ triple_array_get. intros r E.
 lets M: (@read_map A _ val) L. rewrites~ (rm M) in E. (* todo: polish *)
  unfold Post. subst. xsimpl*.
Qed.

Lemma Triple_array_set : forall p i v L,
  index L i ->
  TRIPLE Triple (val_array_set ``p ``i ``v)
    PRE (p ~> Array L)
    POST (fun (_:unit) => p ~> Array (L[i:=v])).
Proof using.
  intros. unfold Triple. rewrite Array_unlift.
  xapplys~ triple_array_set. intros r E.
  rewrite~ <- map_update.
  unfold Post. subst. rewrite Array_unlift. xsimpl~ tt.
Qed.

Lemma Triple_array_make : forall n v,
  n >= 0 ->
  TRIPLE Triple (val_array_make ``n ``v)
    PRE \[]
    POST (fun p => \exists L, \[L = make n v] \* p ~> Array L).
Proof using.
  intros. unfold Triple. xapplys~ triple_array_make.
  intros r p L E N. unfold Post. xsimpl~ p (make n v).
  rewrite Array_unlift. subst L. rewrite map_make; [|math]. xsimpl.
Qed.

End ArrayRules.

Hint Extern 1 (Register_Spec val_array_get) => Provide Triple_array_get.
Hint Extern 1 (Register_Spec val_array_set) => Provide Triple_array_set.
Hint Extern 1 (Register_Spec val_array_make) => Provide Triple_array_make.

*)
