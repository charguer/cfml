(**

Formalization of 
- purely functional pairing heaps in Coq
- ephemeral (pointer-based) pairing heaps in CFML2

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import Example.
From Sep Require Import ExampleList.


(* ******************************************************* *)
(** ** Mutable lists extension *)

Module MList.

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Fixpoint MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf R L')
  end.

(*
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists X p', \[v = Cons x p'] \* (x ~> RA X) \* (p' ~> MList L')
  end.
*)

Section Ops.

Context A {EA:Enc A} TA (R:TA->A->hprop).
Implicit Types L : list TA.
Implicit Types p : loc.
Implicit Types x : A.
Implicit Types X : TA.

Parameter is_empty : val.

Parameter Triple_is_empty : forall L p,
  TRIPLE (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).

Parameter push : val.

Parameter Triple_push : forall L p x X,
  TRIPLE (push p ``x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).

Parameter pop : val.

Parameter Triple_pop : forall L p,
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').

End Ops.

End MList.


(* ####################################################### *)

From TLC Require Import LibMultiset.

Tactic Notation "multiset_eq" := (* TODO: move to TLC *)
  check_noevar_goal; permut_simpl.



(** For simplicity, assume the heap stores integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).


(* ####################################################### *)
(** * Data types and invariants *)


(* ******************************************************* *)
(** ** Data types *)

Inductive heap : Type :=
  | Empty : heap
  | Node : elem -> list heap -> heap.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val Empty. Qed.


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

Lemma pop_min_lemma : forall x Es,
  Forall (foreach (is_ge x)) Es ->
  min_of (\{x} \u list_union Es) x.
Proof.
  introv M. split. 
  { auto. }
  { intros y Hy. multiset_in Hy.
    { auto. }  { applys* Forall_foreach_is_ge_inv Es. } }
Qed.


(* ####################################################### *)
(** * Purely functional pairing heaps *)

Module PurePairing.

(* ******************************************************* *)
(** ** Coq code *)

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
      { applys* IH. hnf; rew_list*. }
      { autos*. } } }
Qed.

Lemma pop_min_spec : forall h E h' x,
  E <> \{} ->
  inv h E ->
  (x,h') = pop_min h ->
     min_of E x
  /\ exists E', inv h' E' /\ E = \{x} \u E'.
Proof using.
  introv N I M. unfolds pop_min.
  destruct h as [|y hs]; inverts I; tryfalse.
  { invert M ;=> <- Eh'. forwards* Is: merge_pairs_spec hs. split.
    { applys* pop_min_lemma. } { eauto. } }
Qed.

End PurePairing.





(* ####################################################### *)
(** * Imperative ephemeral pairing heaps *)



Module ImperativePairing.


(* ******************************************************* *)
(** ** OCaml+null code *)

(**
[[

  type heap = ref node  (* [ref null] when empty *)

  type node = {
    value : elem;
    sub : node mlist; }

  let create() =
    ref null

	let is_empty h =
		(!h == null)

  let merge p1 p2 =
		if p1 == null then p1 else
		if p2 == null then p2 else
		if (p1.value < p2.value) then (
			MList.push p1.sub p2;
			p1
		) else (
			MList.push p2.sub p1;
			p2
		)

  let insert h x =
    let p = ref { value = x; sub = MList.create() } in
    h := merge !h p

	let merge_pairs hs =
    if MList.is_empty hs then null else
    let h1 = MList.pop hs in
    if MList.is_empty hs then h1 else
    let h2 = MList.pop hs in
		merge (merge h1 h2) (merge_pairs hs)

	let pop_min p =
    let x = !p.value in
    p := merge_pairs (!p.sub);
		x

]]
*)


(* ******************************************************* *)
(** ** Deeply embedded code *)

Notation "''hs'" := ("hs":var) : var_scope.

Definition value : field := 0%nat.
Definition sub : field := 1%nat.

Definition create : val :=
  VFun 'u := 
    val_ref null.

Definition is_empty : val :=
  VFun 'h := 
    '!'h '= null.

Definition merge : val :=
  VFun 'p1 'p2 := 
		If_ 'p1 '= null Then 'p1 Else
		If_ 'p2 '= null Then 'p2 Else
		If_ ('p1'.value '< 'p2'.value) Then (
			MList.push ('p1'.sub) 'p2 ';
			'p1
		) Else (
			MList.push ('p2'.sub) 'p1 ';
			'p2
		).

Definition merge_pairs : val :=
  VFix 'f 'hs := 
		If_ MList.is_empty 'hs Then null Else
    Let 'h1 := MList.pop 'hs in
    If_ MList.is_empty 'hs Then 'h1 Else
    Let 'h2 := MList.pop 'hs in
		merge (merge 'h1 'h2) ('f 'hs).

Definition pop_min : val :=
  VFun 'p :=
    Let 'x := '!'p'.value in
    'p ':= merge_pairs ('!'p'.sub) ';
		'x.



(* ******************************************************* *)
(** ** Representation predicate *)

(*
Definition Heap (E:elems) (p:loc) : hprop :=
  \exists (v:loc), p ~~> v \*
  If E = \{} then \[v = null] else 
    \exists x hs, v ~> Record`{ value := x; sub := hs } \* .
*)
(*
Inductive tree : Type :=
  | Leaf : tree
  | Node : list tree -> tree.

Fixpoint MListOf' A TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => (p ~> MListOf' R L')
  end.


Fixpoint Repr (t:tree) (p:loc) {struct t} :=
  match t with
  | Leaf => \[p = null]
  | Node ts => (* MListOf' Repr ts p*)
    (fix f R ts p : hprop := match ts with
    | nil => \[p = null]
    | X::L' => (p ~> f R L') \* p ~> R X
    end) Repr ts p
  end.


      Fixpoint MListOf' A TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => (p ~> MListOf' R L')
  end.

Fixpoint MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf R L')
  end.

Fixpoint MListOf' A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | X::L' => \exists (x:A) p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf' R L')
  end.
*)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.



Fixpoint Repr (h:heap) (p:loc) { struct h } : hprop :=
  match h with
  | Empty => \[p = null]
  | Node x hs => 
      \exists q,
       p ~> Record`{ value := x; sub := q } 
      (* \* q ~> MListOf Repr hs *) \*
      (fix MListOf L p : hprop :=
      match L with
      | nil => \[p = null]
      | X::L' => \exists (x:loc) p', p ~> Record`{ head := x; tail := p'} \* (x ~> Repr X) \* (p' ~> MListOf L')
      end) hs q
  end.

Lemma Repr_eq : forall h p,
    Repr h p 
  = match h with
    | Empty => \[p = null]
    | Node x hs => 
        \exists q,
         p ~> Record`{ value := x; sub := q } 
       \* q ~> MList.MListOf Repr hs
   end.
Proof using.
  intros. gen p. induction h; intros.
  auto.
  simpl.
  fequals. applys fun_ext_1.  intros q. fequals. gen q. induction l; intros.
  auto.
  simpl. xrepr_clean.  fequals.   applys fun_ext_1.  intros x. fequals. 
applys fun_ext_1.  intros p'. fequals. fequals.
Admitted. (* generalized induction on trees *)



Definition Heap (E:elems) (p:loc) : hprop :=
  \exists (h:heap), p ~> Repr h \* \[inv h E].



(* ******************************************************* *)
(** ** Verification 


Lemma triple_create :
  triple (val_create val_unit)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MQueue nil p).
Proof using.
  xcf. unfold MQueue.
  xapp triple_alloc_cell as r. intros p v1 v2. intro_subst.
  xapp~. xpull ;=> r x E. xsimpl~.
  { rewrite MListSeg_nil_eq. xsimpl~. }
Qed.

*)

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


(*

https://sites.google.com/site/progyumming/cpp/pairing-heap

https://github.com/saadtaame/pairing-heap/blob/master/pairing_heap.cc

https://www.sanfoundry.com/cpp-program-implement-pairing-heap/

https://www.techiedelight.com/deletion-from-bst/


*)