(**

Formalization of pairing heaps, covering both
- purely functional pairing heaps (in Coq code)
- ephemeral (pointer-based) pairing heaps in CFML2

More information about pairing heaps:
  https://www.cise.ufl.edu/~sahni/dsaaj/enrich/c13/pairing.htm

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example ExampleList ExampleListOf.
From TLC Require Import LibMultiset.
Open Scope comp_scope.

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Representation and lemmas *)

(* ********************************************************************** *)
(** ** Types of elements *)

(** For simplicity, assume the priority queue to store integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).


(* ******************************************************* *)
(** ** Data structure and definitions *)

(** Functional representation of a node in a (nonempty) pairing heap *)

Inductive node : Type :=
  | Node : elem -> list node -> node.

Instance Inhab_node : Inhab node.
Proof using. applys Inhab_of_val (Node arbitrary nil). Qed.

(** Functional representation of a possibly-empty pairing heap *)

Definition heap := option node.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val (@None node). Qed.

(** Auxiliary definition for specifications *)

Definition min_of (E:elems) (x:elem) : Prop :=
  x \in E /\ forall_ y \in E, x <= y.

(** Auxiliary definition for stating invariants follow. *)

(** [is_ge x] is a predicate that characterizes items no less than [x] *)

Definition is_ge (x y:elem) : Prop :=
  x <= y.

(** [list_union Es] computes the iterated union of the multisets in the list [Es] *)

Definition list_union (Es:list elems) : elems :=
  LibList.fold_right union \{} Es.

(** [inv n E] relates a tree node [n] with the multiset [E] made of
    the items that the tree contains *)

Inductive inv : node -> elems -> Prop :=
  | inv_Node : forall x ns Es E,
      Forall2 inv ns Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->
      inv (Node x ns) E.

(** [repr h E] relates a heap representation [h] with the multiset [E] made of the items
    that the heap contains *)

Inductive repr : heap -> elems -> Prop :=
  | repr_None :
      repr None \{}
  | repr_Some : forall n E,
      inv n E ->
      repr (Some n) E.


(* ******************************************************* *)
(** ** Lemmas and tactics *)

(** Implicit Types *)

Implicit Types n : node.
Implicit Types p q l : loc.
Implicit Types x y : elem.
Implicit Types h : heap.
Implicit Types hs : list node.
Implicit Types E : elems.
Implicit Types Es : list elems.

(** Normalization lemmas for [list_union] *)

Lemma list_union_nil :
  list_union (@nil elems) = \{}.
Proof using. auto. Qed.

Lemma list_union_cons : forall E Es,
  list_union (E::Es) = E \u list_union Es.
Proof using. auto. Qed.

(** Hints *)

Hint Rewrite list_union_nil list_union_cons : rew_listx.
Hint Rewrite (@union_empty_r elems _ _ _) (@union_empty_l elems _ _ _) : rew_listx.
Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => rew_listx; multiset_eq.
Hint Extern 1 (_ \in _) => multiset_in.
Hint Constructors Forall Forall2 list_sub.
Hint Unfold is_ge.

(** Lemmas to manipulate the invariant [Forall (foreach (is_ge x)) Es] *)

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

(** Key auxiliary lemmas for the verification proofs
    (both for the functional version and the imperative version) *)

Lemma inv_not_empty : forall n E,
  inv n E ->
  E <> \{}.
Proof using. introv I. inverts I. multiset_inv. Qed.

Lemma merge_lemma : forall x1 x2 ns1 ns2 Es1 Es2,
  Forall2 inv ns1 Es1 ->
  Forall2 inv ns2 Es2 ->
  Forall (foreach (is_ge x2)) Es1 ->
  Forall (foreach (is_ge x1)) Es2 ->
  x1 <= x2 ->
  inv (Node x1 (Node x2 ns1 :: ns2)) ('{x1} \u '{x2} \u list_union Es1 \u list_union Es2).
Proof using.
  introv Is1 Is2 Ks1 Ks2 L. applys_eq inv_Node. constructor.
  { applys* inv_Node. }
  { eauto. }
  { constructors.
    { applys foreach_union.
      { applys* foreach_single. }
      { applys* foreach_list_union. applys Forall_pred_incl Ks1.
        { intros x Hx. applys* foreach_weaken. { intros y Hy. unfolds* is_ge. } } } }
    { eauto. } }
  { autos*. }
Qed.

Lemma pop_min_lemma : forall x Es,
  Forall (foreach (is_ge x)) Es ->
  min_of (\{x} \u list_union Es) x.
Proof.
  introv M. split.
  { auto. }
  { intros y Hy. multiset_in Hy.
    { auto. } { applys* Forall_foreach_is_ge_inv Es. } }
Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Purely functional pairing heaps *)

Module Pure.

(* ******************************************************* *)
(** ** Source code *)

Definition empty : heap :=
  None.

Definition is_empty (h:heap) : bool :=
  match h with
  | None => true
  | _ => false
  end.

Definition merge (n1 n2:node) : node :=
  match n1, n2 with Node x ns1, Node y ns2 =>
     If x < y
        then Node x (n2::ns1)
        else Node y (n1::ns2)
  end.

Definition insert (h:heap) (x:elem) : heap :=
  let n' := Node x nil in
  match h with
  | None => Some n'
  | Some n => Some (merge n n')
  end.

Fixpoint merge_pairs (ns:list node) : node :=
  match ns with
  | nil => arbitrary
  | n::nil => n
  | n1::n2::hs' =>
      let n12 := merge n1 n2 in
      if LibListExec.is_nil hs'
        then n12
        else merge n12 (merge_pairs hs')
  end.

Definition pop_min (h:heap) : elem * heap :=
  match h with
  | Some (Node x ns) =>
      let h' := if LibListExec.is_nil ns
                  then None
                  else Some (merge_pairs ns) in
      (x, h')
  | _ => arbitrary
  end.


(* ******************************************************* *)
(** ** Verification *)

Lemma empty_spec :
  repr empty \{}.
Proof using. constructor. Qed.

Lemma is_empty_spec : forall h E,
  repr h E ->
  is_empty h = isTrue (E = \{}).
Proof using.
  introv I. unfold is_empty. destruct h; rew_bool_eq; inverts I as.
  { introv N. inverts N. multiset_inv. }
  { auto. }
Qed.

Lemma merge_spec : forall n1 E1 n2 E2,
  inv n1 E1 ->
  inv n2 E2 ->
  inv (merge n1 n2) (E1 \u E2).
Proof using.
  introv I1 I2. unfold merge.
  (destruct n1 as [x1 ns1]; inverts I1 as; intros Is1 Ks1);
  (destruct n2 as [x2 ns2]; inverts I2 as; intros Is2 Ks2).
  rename Es into Es1, Es0 into Es2. case_if.
  { applys_eq* merge_lemma. multiset_eq. }
  { applys_eq* merge_lemma. multiset_eq. } (* TODO:  automation should trigger the hint *)
Qed.

Lemma insert_spec : forall x h E,
  repr h E ->
  repr (insert h x) (E \u \{x}).
Proof using.
  introv I. unfold insert.
  destruct h as [n|].
  { inverts I as I. constructor. applys_eq (>> merge_spec I).
    { applys* inv_Node. } }
  { inverts I. constructor. applys* inv_Node. }
Qed.

Lemma merge_pairs_spec : forall ns Es,
  ns <> nil ->
  Forall2 inv ns Es ->
  inv (merge_pairs ns) (list_union Es).
Proof using.
  intros ns. induction_wf IH: (@list_sub node) ns; introv N Is.
  destruct ns as [|n1 ns']; tryfalse. inverts Is as I1 Is.
  rename y into E1. rename r into Es'.
  destruct ns' as [|n2 ns'']; simpl.
  { inverts Is. applys_eq* I1. }
  { inverts Is as I2 Is. rename r into Es, y into E2.
    rewrite LibListExec.is_nil_eq. case_if as C; rew_listx.
    { subst ns''. inverts Is. applys merge_spec.
      { applys I1. } { applys_eq* I2. } }
    { rewrite union_assoc. applys_eq merge_spec.
      { applys* merge_spec. }
      { applys* IH. } } }
Qed.

Lemma pop_min_spec : forall h E h' x,
  E <> \{} ->
  repr h E ->
  (x,h') = pop_min h ->
     min_of E x
  /\ exists E', repr h' E' /\ E = \{x} \u E'.
Proof using.
  introv N I M. unfolds pop_min.
  destruct h as [n|]; inverts I as I; tryfalse.
  destruct n as [y ns]. inverts M. inverts I as I1 Ks. split.
  { applys~ pop_min_lemma. }
  { rewrite LibListExec.is_nil_eq. case_if as C.
    { subst ns. inverts I1. exists \{}. split~. constructor. }
    { forwards~ Is: merge_pairs_spec I1. exists (list_union Es). split~.
      constructor~. } }
Qed.

End Pure.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Imperative pairing heaps *)

Module Imperative.

(* ******************************************************* *)
(** ** Source code in OCaml+null syntax *)

(**
[[

type node = { value : elem; sub : node mlist }
type heap = null OR node

let create () =
  ref null

let is_empty p =
  p == null

let merge q1 q2 =
  if q1.value < q2.value
    then (MList.push q1.sub q2; q1)
    else (MList.push q2.sub q1; q2)

let insert p x =
  let q1 = !p in
  let q2 = { value = x; sub = MList.create() } in
  if q1 == null
    then p := q2
    else p := merge q1 q2

let rec merge_pairs l =
  let q1 = MList.pop l in
  if MList.is_empty l then q else
  let q2 = MList.pop l in
  let q = merge q1 q2 in
  if MList.is_empty l
     then q
     else merge q (merge_pairs l)

let pop_min p =
  let q = !p in
  let x = q.value in
  if MList.is_empty q.sub
    then p := null
    else p := merge_pairs q.sub
]]

*)

(* ******************************************************* *)
(** ** Source code in embedded syntax *)

Definition value : field := 0%nat.
Definition sub : field := 1%nat.

Definition create : val :=
  Fun 'u :=
    val_ref null.

Definition is_empty : val :=
  Fun 'p :=
    '!'p '= null.

Definition merge : val :=
  Fun 'q1 'q2 :=
		If_ ('q1'.value '< 'q2'.value) Then (
			MList.push ('q1'.sub) 'q2 ';
			'q1
		) Else (
			MList.push ('q2'.sub) 'q1 ';
			'q2
		).

Definition insert : val :=
  Fun 'p 'x :=
    Let 'q1 := '!'p in
    Let 'q2 := New`{ value := 'x; sub := MList.create '() } in
    If_ 'q1 '= null
      Then 'p ':= 'q2
      Else 'p ':= merge 'q1 'q2.

Definition merge_pairs : val :=
  Fix 'f 'l :=
    Let 'q1 := MList.pop 'l in
    If_ MList.is_empty 'l Then 'q1 Else
    Let 'q2 := MList.pop 'l in
    Let 'q := merge 'q1 'q2 in
		If_ MList.is_empty 'l Then 'q Else
    merge 'q ('f 'l).

Definition pop_min : val :=
  Fun 'p :=
    Let 'q := '!'p in
    Let 'x := 'q'.value in
    (If_ MList.is_empty ('q'.sub)
      Then 'p ':= null
      Else 'p ':= merge_pairs ('q'.sub) )';
		'x.


(* ******************************************************* *)
(** ** Representation predicates *)

(**

Definition is_ge (x y:elem) : Prop :=
  x <= y.

(** [list_union Es] computes the iterated union of the multisets in the list [Es] *)

Definition list_union (Es:list elems) : elems :=
  LibList.fold_right union \{} Es.

(** [inv n E] relates a tree node [n] with the multiset [E] made of
    the items that the tree contains *)

Inductive inv : node -> elems -> Prop :=
  | inv_Node : forall x ns Es E,
      Forall2 inv ns Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->
      inv (Node x ns) E.

*)


(** [q ~> Tree n] related a pointer [q] with the functional tree structure [n]
    that it represents in memory *)

Fixpoint Tree (n:node) (q:loc) { struct n } : hprop :=
  match n with
  | Node x hs =>
      \exists (q':loc),
         q ~> Record`{ value := x; sub := q' }
      \* q' ~> MListOf Tree hs
  end.


(** [q ~> Repr E] related a non-null pointer [q] with the multiset of items [E]
    that are stored in the tree *)

Definition Repr (E:elems) (q:loc) : hprop :=
  \exists n, q ~> Tree n \* \[inv n E].

(** [q ~> Heap E] relates a possibly-null pointer [q] with the multiset of items [E]
    that are stored in the heap. It uses [Contents E q] as an auxiliary definition. *)

Definition Contents (E:elems) (q:loc) : hprop :=
  If q = null then \[E = \{}] else q ~> Repr E.

Definition Heap (E:elems) (p:loc) : hprop :=
  \exists q, p ~~> q \* Contents E q.


(* ******************************************************* *)
(** ** Lemmas for the representation predicates *)

(** For [Tree] *)

Lemma Tree_Node : forall q x hs,
  q ~> Tree (Node x hs) =
      \exists l, q ~> Record`{ value := x; sub := l }
              \* l ~> MListOf Tree hs.
Proof using. auto. Qed.

(** For [Repr] *)

Lemma Repr_eq : forall q E,
  q ~> Repr E = \exists n, q ~> Tree n \* \[inv n E].
Proof using. auto. Qed.

Lemma Repr_not_empty : forall q E,
  q ~> Repr E ==> \[E <> \{}] \* q ~> Repr E.
Proof using.
  intros. xunfold Repr. xpull ;=> n I. lets: inv_not_empty I. xsimpl*.
Qed.

Lemma Repr_not_null : forall q E,
  q ~> Repr E ==> \[q <> null] \* q ~> Repr E.
Proof using.
  intros. xunfold Repr. xpull ;=> n I. destruct n as [x hs].
  rewrite Tree_Node. xpull ;=> l. xchange* Record_not_null ;=> N.
  xsimpl~ (Node x hs). rewrite Tree_Node. xsimpl.
Qed.

(** For [Contents] *)

Lemma Contents_eq : forall E q,
  Contents E q = (If q = null then \[E = \{}] else q ~> Repr E).
Proof using. auto. Qed.

Lemma Contents_not_empty : forall E q,
  E <> \{} ->
  Contents E q = (q ~> Repr E).
Proof using.
  introv N. unfold Contents. applys himpl_antisym.
  { case_if; xsimpl. }
  { xchange Repr_not_null ;=> N'. case_if*. }
Qed.

Lemma Contents_is_empty : forall q E,
  Contents E q ==> \[q = null <-> E = \{}] \* Contents E q.
Proof using.
  intros. unfold Contents. case_if.
  { xsimpl*. }
  { xchange Repr_not_empty ;=> N. xsimpl*. }
Qed.

Lemma Contents_null :
  \[] ==> Contents \{} null.
Proof using. unfold Contents. case_if. xsimpl*. Qed.

(** For [Heap] *)

Lemma Heap_eq : forall p E,
  p ~> Heap E = \exists q, p ~~> q \* Contents E q.
Proof using. auto. Qed.

Lemma Heap_of_Repr : forall p q E,
  p ~~> q \* q ~> Repr E ==> p ~> Heap E.
Proof using.
  intros. xchanges Repr_not_empty ;=> N. xunfold Heap.
  xsimpl. xchange Repr_not_null ;=> N'. unfold Contents. case_if~.
Qed.

Lemma Heap_of_null : forall p,
  p ~~> null ==> p ~> Heap \{}.
Proof using. intros. xchanges Contents_null. xchange <- Heap_eq. Qed.


(* ******************************************************* *)
(** ** Verification *)

Lemma Triple_create :
  TRIPLE (create tt)
    PRE \[]
    POST (fun p => p ~> Heap \{}).
Proof using.
  xwp. xapp (>> Triple_ref Enc_loc null) ;=> p.
  xunfold Heap. xsimpl. xchanges~ Contents_null.
Qed.

Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.

Lemma Triple_is_empty : forall p E,
  TRIPLE (is_empty p)
    PRE (p ~> Heap E)
    POST (fun b => \[b = isTrue (E = \{})] \* p ~> Heap E).
Proof using.
  xwp. xunfolds Heap ;=> q. xapp. xapp.
  xchanges~ Contents_is_empty.
Qed.

Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.
(**
Definition merge : val :=
  Fun 'q1 'q2 :=
		If_ ('q1'.value '< 'q2'.value) Then (
			MList.push ('q1'.sub) 'q2 ';
			'q1
		) Else (
			MList.push ('q2'.sub) 'q1 ';
			'q2
		).
*)
Lemma Triple_merge : forall q1 q2 E1 E2,
  TRIPLE (merge q1 q2)
    PRE (q1 ~> Repr E1 \* q2 ~> Repr E2)
    POST (fun q => q ~> Repr (E1 \u E2)).
Proof using.
  xwp. xchange (Repr_eq q1) ;=> [x1 hs1] I1. xchange (Repr_eq q2) ;=> [x2 hs2] I2.
  xchange (Tree_Node q1) ;=> l1. xchange (Tree_Node q2) ;=> l2.
  inverts I1 as Is1 Ks1. inverts I2 as Is2 Ks2.
  xapp. xapp. xapp. xif ;=> C.
  { xapp. xchange <- (Tree_Node q2). xapp (>> __ Enc_loc).
    xval. xchange <- Tree_Node. xchange <- Repr_eq.
    applys* merge_lemma. xsimpl*. }
  { xapp. xchange <- (Tree_Node q1). xapp (>> __ Enc_loc).
    xval. xchange <- Tree_Node. xchange <- Repr_eq.
    applys* merge_lemma. xsimpl*. }
Qed.

Hint Extern 1 (Register_Spec (merge)) => Provide @Triple_merge.

Lemma Triple_insert : forall p x E,
  TRIPLE (insert p x)
    PRE (p ~> Heap E)
    POST (fun (_:unit) => p ~> Heap (E \u \{x})).
Proof using.
  xwp. xchange Heap_eq ;=> q. xapp. xapp (>> __ Tree) ;=> l.
  xnew (>> x l) ;=> q2. xchange <- Tree_Node.
  xchange <- Repr_eq. { applys* inv_Node. }
  rew_listx. xapp. unfold Contents. xif ;=> C; case_if.
  { xpull ;=> ->. xapp. xchanges* Heap_of_Repr. }
  { xapp ;=> r. xapp. xchanges* Heap_of_Repr. }
Qed.

Hint Extern 1 (Register_Spec (insert)) => Provide @Triple_insert.
(**
Definition merge_pairs : val :=
  Fix 'f 'l :=
    Let 'q1 := MList.pop 'l in
    If_ MList.is_empty 'l Then 'q1 Else
    Let 'q2 := MList.pop 'l in
    Let 'q := merge 'q1 'q2 in
		If_ MList.is_empty 'l Then 'q Else
    merge 'q ('f 'l).
**)

Lemma Triple_merge_pairs : forall ns l Es,
  ns <> nil ->
  Forall2 inv ns Es ->
  TRIPLE (merge_pairs l)
    PRE (l ~> MListOf Tree ns)
    POST (fun q => q ~> Repr (list_union Es)).
Proof using.
  intros ns. induction_wf IH: (@list_sub node) ns; introv N Is.
  xwp. xapp~ ;=> q1 n1 ns' ->. inverts Is as I1 Is. rename r into Es'.
  xapp (>> __ Tree). xif ;=> C.
  { subst. inverts Is. rew_listx. xval. xchanges* <- Repr_eq. }
  { xapp~ ;=> q2 n2 ns'' ->. inverts Is as I2 Is. rename r into Es''.
    do 2 xchange* <- Repr_eq. xapp ;=> r. xapp (>> __ Tree). xif ;=> C'.
    { subst. inverts Is. rew_listx. xval. xsimpl. }
    { xapp* ;=> r'. xapp ;=> r''. rew_listx. xsimpl*. } }
Qed.

Hint Extern 1 (Register_Spec (merge_pairs)) => Provide @Triple_merge_pairs.

Lemma Triple_pop_min : forall p E,
  E <> \{} ->
  TRIPLE (pop_min p)
    PRE (p ~> Heap E)
    POST (fun x => \exists E', \[min_of E x /\ E = \{x} \u E'] \* p ~> Heap E').
Proof using.
  introv HE. xwp. xchange Heap_eq ;=> q. xapp. xchange~ Contents_not_empty.
  xchange Repr_eq ;=> [x hs] I. invert I ;=> ? ? ? ? Is Ks Eq -> -> ->.
  xchange Tree_Node ;=> l. xapp.
  xseq. xapp. xapp (>> __ Tree).
  xpost (fun (_:unit) => \exists E', \[E = '{x} \u E'] \* p ~> Heap E' \* \GC). xif ;=> C.
  { { subst. inverts Is. inverts Ks. rew_listx.
      xapp (>> Triple_set Enc_loc). xchange <- Tree_Node. xchanges* Heap_of_null. } }
    { xapp. xapp; eauto ;=> r. xapp. xchange Heap_of_Repr. xsimpl*. }
  { intros _. xpull ;=> E' ->. xval. xsimpl. split~.
    { rewrite Eq. applys~ pop_min_lemma. } }
Qed.

Hint Extern 1 (Register_Spec (pop_min)) => Provide @Triple_pop_min.

End Imperative.




