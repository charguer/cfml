(**

Formalization of 
- purely functional pairing heaps in Coq
- ephemeral (pointer-based) pairing heaps in CFML2

Author: Arthur Charguéraud.
License: MIT.

*)

(** For simplicity, assume the heap stores integer values.
    It is not hard to generalize everything to any ordered type. *)

Definition elem := int.


(* ####################################################### *)
(** * Purely functional pairing heaps *)

Module PurePairing.


(* ******************************************************* *)
(** ** Code *)

Inductive heap : Type :=
  | Empty : heap
  | Node : elem -> heap -> list heap -> heap.

Definition is_empty (h:heap) : bool :=
  match h with
  | Empty -> true
  | _ -> false
  end.

Definition merge (h1 h2:heap) : heap :=
  match h1, h2 with
   | _, Empty -> h1
   | Empty, _ -> h2
   | Node x hs1, Node y hs2 ->
       if x < y 
          then Node (x, h2::hs1)
          else Node (y, h1::hs2)
   end.

Definition insert x h :=
  merge (Node x nil) h.

Definition merge_pairs (hs:list heap) : heap :=
  match hs with
  | nil -> Empty
  | h::nil -> h
  | h1::h2::hs' -> merge (merge h1 h2) (merge_pairs hs')
  end.

Definition pop_min (h:heap) : elem * heap :=
  match h with
  | Node x hs -> (x, merge_pairs hs)
  | _ -> arbitrary
  end.


(* ******************************************************* *)
(** ** Invariant and lemmas *)

Definition is_ge (x y:elem) : Prop :=
  x <= y.

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



(* ******************************************************* *)
(** ** Verification *)


End PurePairing.



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