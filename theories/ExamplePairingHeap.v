(**

Formalization of 
- purely functional pairing heaps in Coq
- ephemeral (pointer-based) pairing heaps in CFML2

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore LibMultiset.


Tactic Notation "multiset_eq" := (* TODO: move to TLC *)
  check_noevar_goal; permut_simpl.



(** For simplicity, assume the heap stores integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).


(* ####################################################### *)
(** * Purely functional pairing heaps *)

Module PurePairing.


(* ******************************************************* *)
(** ** Data types *)

Inductive heap : Type :=
  | Empty : heap
  | Node : elem -> list heap -> heap.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val Empty. Qed.


(* ******************************************************* *)
(** ** Operations *)

Definition empty : heap :=
  Empty.

Definition is_empty (h:heap) : bool :=
  match h with
  | Empty => true
  | _ => false
  end.

Definition merge (h1 h2:heap) : heap :=
  match h1, h2 with
   | _, Empty => h1
   | Empty, _ => h2
   | Node x hs1, Node y hs2 =>
       If x < y
          then Node x (h2::hs1)
          else Node y (h1::hs2)
   end.

Definition insert (h:heap) (x:elem) : heap :=
  merge (Node x nil) h.

Fixpoint merge_pairs (hs:list heap) : heap :=
  match hs with
  | nil => Empty
  | h::nil => h
  | h1::h2::hs' => merge (merge h1 h2) (merge_pairs hs')
  end.

Definition pop_min (h:heap) : elem * heap :=
  match h with
  | Node x hs => (x, merge_pairs hs)
  | _ => arbitrary
  end.


(* ******************************************************* *)
(** ** Invariant *)

Implicit Types x y : elem.
Implicit Types h : heap.
Implicit Types hs : list heap.
Implicit Types E : elems.
Implicit Types Es : list elems.

Definition min_of (E:elems) (x:elem) := 
  x \in E /\ forall_ y \in E, x <= y.

Definition removed_min (E E':elems) : Prop :=
  exists x, min_of E x /\ E = \{x} \u E'.

Definition is_ge (x y:elem) : Prop :=
  x <= y.

Definition list_union (Es:list elems) := 
  LibList.fold_right union \{} Es.

Inductive inv : heap -> elems -> Prop :=
  | inv_Empty : 
      inv Empty \{} 
  | inv_Node : forall x hs Es E,
      Forall2 inv hs Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->   
      inv (Node x hs) E.


(* ******************************************************* *)
(** ** Lemmas and tactics *)

Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => unfold list_union; rew_listx; multiset_eq.
Hint Extern 1 (_ \in (_ : multiset _)) => multiset_in.
Hint Constructors Forall Forall2 list_sub.
Hint Unfold is_ge.

Lemma Forall_foreach_is_ge_inv : forall x y Es,
  Forall (foreach (is_ge x)) Es ->
  y \in list_union Es ->
  x <= y.
Proof using. 
  introv M Hy. unfolds list_union. induction M; rew_listx in *.
  { multiset_in Hy. }
  { multiset_in Hy. { applys* H. } { applys* IHM. } }
Qed.

Lemma foreach_list_union : forall P Es,
  Forall (foreach P) Es ->
  foreach P (list_union Es).
Proof using.
  introv M. induction M.
  { applys foreach_empty. }
  { unfold list_union; rew_listx. applys* foreach_union. }
Qed.

Lemma merge_lemma : forall x1 x2 hs1 hs2 Es1 Es2,
  Forall2 inv hs1 Es1 ->
  Forall2 inv hs2 Es2 ->
  Forall (foreach (is_ge x2)) Es1 ->
  Forall (foreach (is_ge x1)) Es2 ->
  x1 <= x2 ->
  inv (Node x1 (Node x2 hs1 :: hs2)) ('{x1} \u '{x2} \u list_union Es1 \u list_union Es2).
Proof using.
  introv Is1 Is2 Ks1 Ks2 L. applys_eq inv_Node 1. constructor.
  { applys* inv_Node. }
  { eauto. }
  { constructors.
    { applys foreach_union.
      { applys* foreach_single. }
      { applys* foreach_list_union. applys Forall_pred_incl Ks1.
        { intros x Hx. applys* foreach_weaken. { intros y Hy. unfolds* is_ge. } } } }
    { eauto. } }
  { reflexivity. }
  { autos*. }
Qed.


(* ******************************************************* *)
(** ** Verification *)

Lemma empty_spec : 
  inv empty \{}.
Proof using. constructor. Qed.

Lemma is_empty_spec : forall h E,
  inv h E ->
  is_empty h = isTrue (E = \{}).
Proof using.
  introv I. unfold is_empty. destruct h; rew_bool_eq; inverts I.
  { auto. }
  { multiset_inv. }
Qed.

Lemma merge_spec : forall h1 E1 h2 E2,
  inv h1 E1 ->
  inv h2 E2 ->
  inv (merge h1 h2) (E1 \u E2).
Proof using.
  introv I1 I2. unfold merge.
  (destruct h1 as [|x1 hs1]; inverts I1 as; [ intros | intros Is1 Ks1]);
  (destruct h2 as [|x2 hs2]; inverts I2 as; [ intros | intros Is2 Ks2]).
  { applys* inv_Empty. }
  { applys* inv_Node. }
  { applys* inv_Node. }
  { rename Es into Es1, Es0 into Es2. case_if.
    { applys_eq* merge_lemma 1. }
    { applys_eq* merge_lemma 1. } }
Qed.

Lemma insert_spec : forall x h E,
  inv h E ->
  inv (insert h x) (E \u \{x}).
Proof using.
  introv I. unfold insert. applys_eq (>> merge_spec I) 1.
  { applys* inv_Node. } { autos*. } 
Qed.

Lemma merge_pairs_spec : forall hs Es,
  Forall2 inv hs Es ->
  inv (merge_pairs hs) (list_union Es).
Proof using. 
  intros hs. induction_wf IH: (@LibList.length heap) hs; introv Is.
  destruct hs as [|h1 hs'']; simpl.
  { inverts Is. applys inv_Empty. }
  { inverts Is as I1 Is1. destruct hs'' as [|h2 hs']; simpl.
    { inverts Is1. unfold list_union. rew_listx. applys_eq~ I1 1. }
    { inverts Is1 as I2 Is2. rename y into E1, y0 into E2, r0 into Es'.
      unfold list_union. rew_listx.
      applys_eq merge_spec 1.
      { applys* merge_spec. }
      { applys* IH. Search tclosure. hnf; rew_list*. }
      { autos*. } } }
Qed.

Lemma delete_min_spec : forall h E h' x,
  E <> \{} ->
  inv h E ->
  (x,h') = pop_min h ->
     min_of E x
  /\ exists E', inv h' E' /\ E = \{x} \u E'.
Proof using.
  introv N I M. unfolds pop_min.
  destruct h as [|y hs]; inverts I; tryfalse.
  { invert M ;=> <- Eh'. forwards* Is: merge_pairs_spec hs. split.
    { unfold min_of. split.
      { auto. }
      { intros y Hy. multiset_in Hy. { auto. } 
        { applys* Forall_foreach_is_ge_inv Es. } } }
    { eauto. } }
Qed.

End PurePairing.


(* ####################################################### *)

(* LATER: transitive closure of sublist (tclosure (@list_sub heap)) *)
(* FOR TLC
Hint Resolve wf_tclosure : wf.


Lemma Forall_foreach_pred_incl : forall P Q Es,
  Forall (foreach P) Es ->
  pred_incl P Q ->
  Forall (foreach Q) Es.
Proof using.
  introv M N. applys Forall_pred_incl M. intros x Hx.
  applys* foreach_weaken. (* LATER: foreach_pred_incl. *)
Qed.
*)


(**



(*

Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import PairingHeap_ml.

Module PairingHeapSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: HeapSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLHeap := MLPairingHeap O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

(** invariant *)

Definition is_ge (X Y:T) := X <= Y.

Definition list_union (Hs:list (multiset T)) := 
  fold_right union \{} Hs.

Inductive inv : heap -> multiset T -> Prop :=
  | inv_empty : 
      inv Empty \{} 
  | inv_node : forall x X hs Hs E,
      rep x X ->
      Forall2 inv hs Hs ->
      Forall (fun H => H <> \{}) Hs ->
      Forall (foreach (is_ge X)) Hs ->
      E = \{X} \u list_union Hs ->   
      inv (Node x hs) E.

(** model *)

Fixpoint size (t:heap) : nat :=
  match t with
  | Empty => 1%nat
  | Node x hs => (1 + (1 + List.fold_right (fun t x => (x + size t)%nat) 0%nat hs)%nat)%nat 
  end.

Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep inv). intros x. gen_eq n: (size x). gen x.
  induction n using peano_induction; introv N HX HY; 
  subst n; inverts HX; inverts HY; subst. prove_rep.
  fequals. prove_rep. fequals. clear X X0 H0 H2 H3 H6 H8 H9. gen Hs Hs0.
  induction hs; introv K1 K2; inverts K1; inverts K2. prove_rep. fequals.
  applys* H. simpl; math. applys~ IHhs. intros. applys* H. simpls. math. 
Defined.

(** automation *)

Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.
Hint Unfold removed_min.

Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> LibSet.set ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end.

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].

Hint Constructors inv Forall Forall2.

(** useful facts *)

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* le_trans. Qed.

Hint Resolve foreach_ge_trans.

Lemma min_of_prove : forall (X : OS.T) (Hs : list (multiset OS.T)),
  Forall (foreach (is_ge X)) Hs ->
  min_of ('{X} \u list_union Hs) X.
Proof.
  introv H. split~. introv M. destruct (in_union_inv M) as [N|N].
  rewrite (in_single N). apply le_refl.
  clear M. unfolds list_union. induction Hs; simpls.
    false. eapply in_empty. eauto.
    inversions H. destruct (in_union_inv N) as [P|P].
      apply~ H3.
      apply~ IHHs.
Qed.

Hint Resolve min_of_prove.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. apply empty_cf. xret~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).
Proof.
  xcf. intros e E RepE. inverts RepE; xgo. 
  auto. multiset_inv.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ;- heap.
Proof.
  xcf. introv Rep1 Rep2. xmatch.
  xgo. inverts Rep2. equates* 1.
  xgo. inverts Rep1. equates* 1.
  xcleanpat. inverts keep Rep1. inverts keep Rep2. xgo~.
    constructors.
      eauto.
      eauto. 
      constructors~. multiset_inv.
      clear H6 H7 Rep2. constructors. eauto. rew_foreach. splits~.
       applys (@foreach_weaken _ (is_ge X0)).
         unfold list_union. induction Hs0; simpl. auto. inverts~ H8.
         intros_all. applys~ le_trans.
    unfold list_union. simple*.
    lets: (nle_to_sle P_x0). constructors.
      eauto.
      eauto. 
      constructors~. multiset_inv.
      clear H2 H3 Rep1. constructors. eauto. rew_foreach. splits~.
       applys (@foreach_weaken _ (is_ge X)).
         unfold list_union. induction Hs; simpl. auto. inverts~ H4.
         intros_all. applys~ le_trans.
    unfold list_union. simpl. permut_simpl.
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ;- heap.
Proof.
  xcf. introv RepX RepE. xapp~ (>>> \{X} E).
  applys~ (>>> inv_node X (@nil (multiset T))).
  unfolds list_union. simple*.
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma merge_pairs_spec : Spec merge_pairs hs |R>>
  forall Hs, 
  Forall2 inv hs Hs ->
  Forall (fun H => H <> \{}) Hs -> 
  R (list_union Hs ;- heap).
Proof.
  xinduction (@List.length heap). xcf. introv IH RepH NE. xmatch.
  xgo. inverts~ RepH.
  xgo. inverts RepH. inverts H2. unfolds list_union. simpls. equates* 1.
  xcleanpat. inverts RepH. inverts H2. inverts NE. inverts H2.
   xgo~. ximpl. equates* 1.
Qed.

Hint Extern 1 (RegisterSpec merge_pairs) => Provide merge_pairs_spec.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof.
  xcf. intros e E RepE HasE. inverts RepE; xgo*.
Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xcf. intros e E RepE HasE. inverts RepE; xgo~. ximpl. xrep~.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End PairingHeapSpec.





*)

(*


https://sites.google.com/site/progyumming/cpp/pairing-heap

https://github.com/saadtaame/pairing-heap/blob/master/pairing_heap.cc

https://www.sanfoundry.com/cpp-program-implement-pairing-heap/

https://www.techiedelight.com/deletion-from-bst/


module PairingHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
  module Element = Element


  type heap = Empty | Node of Element.t * heap list

  let empty = Empty

  let is_empty = function
     | Empty -> true
     | _ -> false

  let merge h1 h2 = 
     match h1, h2 with
     | _, Empty -> h1
     | Empty, _ -> h2
     | Node (x, hs1), Node (y, hs2) ->
         if Element.leq x y 
            then Node (x, h2 :: hs1)
            else Node (y, h1 :: hs2)

  let insert x h = 
     merge (Node (x, [])) h

  let rec merge_pairs = function
     | [] -> Empty
     | [h] -> h
     | h1::h2::hs -> merge (merge h1 h2) (merge_pairs hs)

  let find_min = function 
     | Empty -> raise EmptyStructure 
     | Node (x, _) -> x

  let delete_min = function 
     | Empty -> raise EmptyStructure 
     | Node (x, hs) -> merge_pairs hs

end



type pairing_heap = ref node

  create() =
    ref null

	let is_empty p =
		return (!p == null)

	let pop_front p =
		if (empty p) fail
    int x = !p.value;
    root = merge_pairs(!p->sub);
		return x

type node = { 
		int value;
		node* parent;
		mlist<node*> sub;
};

let merge(node * a, node * b)  : node* =
		if (a == null) return b;
		if (b == null) return a;
		if (!a.value < !b.value) {
			!a.sub.push_front(b);
			return a;
		} else {
			!b.sub.push_front(a);
			return b;
		}
	}
	node * merge_pairs(list<node*> s) {
    if s.is_empty() return null else
    let a = s.pop_front()
    if s.is_empty() return a else
    let b = s.pop_front()
		return merge(merge(a, b), merge_pairs(s));
	}

*)