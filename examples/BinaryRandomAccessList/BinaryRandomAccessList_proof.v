Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import BinaryRandomAccessList_ml.
From TLC Require Import LibListZ.

Axiom pow2_succ : forall n, n >= 0 -> 2^(n+1) = 2*2^n. (* TOMOVE *)
Axiom pow2_pos : forall n, n >= 0 -> 2^n >= 1.
Axiom div2_pow2_succ : forall n, n >= 0 -> 2^(n+1)÷ 2 = 2^n.

Notation "'SPECP' t 'POST' P" :=
  (Triple t \[] (fun r => \[P r]))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPECP'  t  '/'  'POST'  P ']'") : triple_scope.

Ltac prove_measure := hnf; simpl; math.
Hint Extern 1 (measure _ _ _) => prove_measure.



Section Index.
Variables (A : Type).
Implicit Types l : list A.
Implicit Types n i : int.

Lemma index_nil_eq : forall i,
  index (@nil A) i = False.
Proof using.
  intros. rewrite index_eq_inbound. extens. iff M; rew_list in *. math. false.
Qed.

Lemma index_one_eq : forall i (x:A),
  index (x :: nil) i = (i = 0).
Proof using.
  intros. rewrite index_eq_inbound. extens. iff M; rew_list in *; math.
Qed.

Lemma index_one_inv : forall i (x:A),
  index (x :: nil) i ->
  i = 0.
Proof using.
  introv M. rewrite* index_one_eq in M.
Qed.
End Index.

Hint Rewrite index_nil_eq index_one_eq : rew_listx.


(** Invariant *)

Inductive btree (A:Type) : int -> tree_ A -> list A -> Prop :=
  | btree_nil : forall x,
      btree 0 (Leaf x) (x::nil)
  | btree_cons : forall p p' n t1 t2 L1 L2 L',
      btree p t1 L1 ->
      btree p t2 L2 ->
      p' =' p+1 ->
      n =' 2^p' ->
      L' =' L1 ++ L2 ->
      btree p' (Node n t1 t2) L'.

Inductive inv (A:Type) : int -> rlist_ A -> list A -> Prop :=
  | inv_nil : forall p,
      p >= 0 ->
      inv p nil nil
  | inv_zero : forall p ts L,
      inv (p+1) ts L ->
      L <> nil ->
      p >= 0 ->
      inv p (Zero :: ts) L
  | inv_one : forall p t ts L L' T,
      btree p t T ->
      inv (p+1) ts L ->
      L' =' T ++ L ->
      L' <> nil ->
      p >= 0 ->
      inv p (One t :: ts) L'.


(** Auxiliary definitions *)

Fixpoint tree_size (A:Type) (t:tree_ A) : nat :=
  match t with
  | Leaf _ => 0%nat
  | Node _ t1 t2 => (1 + tree_size t1 + tree_size t2)%nat
  end.

Definition Size (A:Type) (t:tree_ A) : int :=
  match t with
  | Leaf _ => 1
  | Node w _ _ => w
  end.

(** Automation *)

Hint Constructors btree inv.

Ltac auto_tilde ::= eauto with maths.

Hint Extern 1 (index _ _) => rewrite index_eq_inbound in *; rew_list in *.


(** Properties of the invariant *)

Section Properties.
Context (A : Type) {IA:Inhab A}.
Implicit Types i : int.
Implicit Types t : tree_ A. 
Implicit Types ts : rlist_ A.
Implicit Types L : list A. 


Lemma btree_unique : forall t n1 n2 E1 E2,
  btree n1 t E1 ->
  btree n2 t E2 ->
  E1 = E2.
Proof.
  introv H1. gen n2 E2.
  induction H1; introv H2; inverts H2 as.
  { auto. }
  { intros. subst. fequals*. }
Qed.

Lemma btree_size_correct : forall p t L,
  btree p t L ->
  Size t = 2^p.
Proof. introv Rt. inverts~ Rt. Qed.

Hint Resolve btree_size_correct.

Lemma btree_p_pos : forall p t L,
  btree p t L ->
  p >= 0.
Proof. introv Rt. inductions Rt; math. Qed.

Hint Resolve btree_p_pos.

Lemma btree_size_pos : forall p t L,
  btree p t L ->
  p >= 0.
Proof. introv Rt. induction Rt; unfolds eq'; math. Qed.

Hint Resolve btree_size_pos.

Lemma btree_inv_length : forall t p L,
  btree p t L ->
  length L = 2^p :> int.
Proof.
  introv Rt. induction Rt. auto.
  unfolds eq'. subst. rew_list. rewrite~ pow2_succ.
Qed.

Lemma to_empty : forall p L,
  inv p nil L ->
  L = nil.
Proof. introv RL. inverts~ RL. Qed.

Lemma from_empty : forall p ts,
  inv p ts nil ->
  ts = nil.
Proof. introv RL. inverts RL; auto_false. Qed.

Lemma btree_not_empty : forall p t L,
  btree p t L ->
  L <> nil.
Proof.
  introv Rt. lets: (btree_inv_length Rt). intro_subst_hyp.
  rew_list in H. forwards~: (@pow2_pos p). math.
Qed.

Hint Resolve btree_not_empty.

(** Verification *)

Lemma size_spec : forall t,
 SPECP (size t)
   POST (fun n => n = Size t).
Proof. xcf~. typeclass. xgo~. Qed.

Hint Extern 1 (RegisterSpec size) => Provide size_spec.





(*-----------------------------*)

Lemma lookup_tree_spec : forall t i p L,
  btree p t L ->
  index L i ->
  SPECP (lookup_tree i t)
   POST (fun r => r = L[i]).
Proof using.
  intros t. induction_wf IH: (fun t => tree_size t) t.
  introv Rt Bi. xcf. xmatch; inverts Rt as. 
  { rew_listx in *. subst. xlets. xif; [ intros _ | math ].
    xvals. rew_list~. }
  { introv M1 M2 -> -> ->. rewrite~ div2_pow2_succ. rewrite read_app.
    lets N1: btree_inv_length M1. lets N2: btree_inv_length M2.
    xif; intros D; case_if.
    { xapp~. xsimpl~. }
    { xapp~. xsimpl~. fequal~. } }
Qed.

Hint Extern 1 (RegisterSpec lookup_tree) => Provide lookup_tree_spec.


Lemma lookup_spec_ind : forall ts i p L,
  inv p ts L ->
  index L i ->
  SPECP (lookup i ts)
   POST (fun r => r = L[i]).
Proof.
  intros ts. induction_wf IH: (fun ts => List.length ts) ts.
  introv Rts Bi. xcf. xmatch; inverts Rts as.
  { intros. rew_listx in Bi. xfail. }
  { intros. xapp~. xsimpl~. }
  { introv Mt Mr -> HL Hp.
    forwards~ R1: (@btree_inv_length t).
    forwards~ R2: (>> btree_size_correct t).
    xapp~. rewrite read_app. xif; intros D; case_if.
    { xapp~. xsimpl~. }
    { xapp~. xapp~. xsimpl. fequals~. } }
Qed.







(*------------

Lemma empty_spec :
  rep (@empty a) (@nil A).
Proof. generalizes RA A. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec :
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. introv RL. simpl in RL. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma size_spec :
  Total size (t:tree a) >> = Size t.
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec size) => Provide size_spec.

Lemma link_spec :
  Spec link (t1:tree a) (t2:tree a) |R>>
    forall p L1 L2, btree p t1 L1 -> btree p t2 L2 ->
    R (fun t' => btree (p+1) t' (L1++L2)).
Proof.
  xgo. subst. constructors~.
  do 2 (erewrite btree_size_correct;eauto).
  rewrite~ pow2_succ.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma cons_tree_spec :
  Spec cons_tree (t:tree a) (ts:rlist a) |R>>
    forall p T L, btree p t T -> inv p ts L ->
    R (fun ts' => inv p ts' (T++L)).
Proof.
  xinduction (fun (t:tree a) (ts:rlist a) => length ts).
  xcf. introv IH Rt Rts. inverts Rts; xgo~.
  constructors~.
  subst. rew_list in P_x1. auto~.
Qed.

Hint Extern 1 (RegisterSpec cons_tree) => Provide cons_tree_spec.

Lemma cons_spec :
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ;- rlist a.
Proof. xcf. introv RX RL. simpl in RL. xgo~. Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma uncons_tree_spec :
  Spec uncons_tree (ts:rlist a) |R>>
    forall p L, inv p ts L -> ts <> nil ->
    R (fun r => let (t',ts') := r : tree a * rlist a in
       exists T' L', btree p t' T' /\ inv p ts' L' /\ L = T' ++ L').
Proof.
  xinduction (fun (ts:rlist a) => length ts).
  xcf. introv IH Rts Ne. xmatch.
  xgo. inverts Rts as RT RL. inverts RL. subst. exists___; auto~.
  xgo. inverts Rts.
   asserts: (L0 <> nil). intro_subst_hyp. eapply C0. fequals. apply~ from_empty.
   subst. exists___; auto~.
  inverts Rts.
   asserts: (ts <> nil). intro_subst_hyp. inverts H1. false.
   xapp~. intuit _x1. xmatch.
   xgo. inverts H3. maths (p0 = p). subst. exists___. splits~. rew_list~.
   xgo. inverts H3. math. applys~ C2.
Qed.

Hint Extern 1 (RegisterSpec uncons_tree) => Provide uncons_tree_spec.

Lemma head_spec :
  RepSpec head (L;rlist a) |R>>
    L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv Rts NE. simpl in Rts. xgo~.
  inverts Rts; auto_false.
  destruct P_x0 as (T'&L'&RT'&RL'&E). inverts RT'. rew_list in E. xrep~.
  intuit _x0. inverts H0.
    applys~ C.
    forwards: (btree_size_pos H3). math.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;rlist a) |R>>
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
  xcf. introv Rts NE. simpl in Rts. xgo~.
  inverts Rts; auto_false.
  intuit P_x0. inverts H0.
    eauto.
    false. forwards~: (btree_size_pos H3). math.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

Require Import LibInt.




Lemma update_tree_spec :
  Spec update_tree (i:int) (x:a) (t:tree a) |R>>
    forall p X L, rep x X -> btree p t L -> ZInbound i L ->
    R (fun t' => exists L', btree p t' L' /\ ZUpdate i X L L').
Proof.
  xinduction (fun (i:int) (x:a) t => tree_size t).
  xcf. intros i x t. introv IH Rx Rt Bi. inverts Rt; xmatch.
  xgo. xrep~. apply~ ZInbound_one_pos_inv.
  xif. subst. rewrite~ pow2_succ in C0. rewrite~ div2_odd in C0. xapp~.
    subst. apply~ ZInbound_app_l_inv. rewrite~ (btree_inv_length H).
    xret. xrep in P_x7. xrep~. apply~ ZUpdate_app_l.
  subst. rewrite~ pow2_succ in C0. rewrite~ div2_odd in C0.
   rewrite~ pow2_succ. rewrite~ div2_odd. xapp~.
    apply~ ZInbound_app_r_inv. rewrite~ (btree_inv_length H).
    xret. xrep in P_x4. xrep~.
      constructors~. rewrite~ pow2_succ.
      apply~ ZUpdate_app_r. rewrite~ (btree_inv_length H).
Qed.

Hint Extern 1 (RegisterSpec update_tree) => Provide update_tree_spec.


Lemma update_spec_ind :
  Spec update (i:int) (x:a) (ts:rlist a) |R>>
    forall p X L, rep x X -> inv p ts L -> ZInbound i L ->
    R (fun ts' => exists L', inv p ts' L' /\ ZUpdate i X L L').
Proof.
  xinduction (fun (i:int) (x:a) (ts:rlist a) => length ts).
  xcf. intros i x ts. introv IH Rx Rts Bi. xmatch; inverts Rts.
  xgo. apply~ ZInbound_nil_inv.
  xgo~. xrep in P_x1 as L'. xrep~.
  forwards~: (@btree_inv_length t).
   forwards~: (>>> btree_size_correct t). xgo~.
    subst. apply~ ZInbound_app_l_inv.
    xrep in P_x7. xrep~. subst. apply~ ZUpdate_app_l.
    subst. apply~ ZInbound_app_r_inv.
    xrep in P_x4. xrep~. subst. apply~ ZUpdate_app_r.
Qed.

Lemma update_spec :
  RepSpec update (i;int) (X;a) (L;rlist a) |R>>
    ZInbound i L -> R (ZUpdate i X L ;; rlist a).
Proof.
  xweaken update_spec_ind. introv W H Ri Rx Rts Bi.
  inverts Ri. simpl in Rts. applys~ H.
Qed.

Hint Extern 1 (@lt nat _ _ _) => rew_list; math.
*)

End Properties.



(*
Lemma lookup_tree_spec : forall i t p L,
  btree p t L ->
  index L i ->
  SPEC (lookup_tree i t)
    PRE \[]
    POST (fun (r:A) => \[r = L[i]]).
*)