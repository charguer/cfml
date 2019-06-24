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


Definition is_nil A (l:list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Lemma is_nil_eq : forall A (l:list A),
  is_nil l = isTrue (l = nil).
Proof using. intros. destruct l; simpl; rew_bool_eq*. Qed.


Section ListSub.
Variable (A:Type).

(** Sub-list well-founded order *)

Inductive list_sub : list A -> list A -> Prop :=
  | list_sub_cons : forall x l,
      list_sub l (x::l)
  | list_sub_tail : forall x l1 l2,
      list_sub l1 l2 ->
      list_sub l1 (x::l2).

Hint Constructors list_sub.

Lemma list_sub_wf : wf list_sub.
Proof using.
  intros l. induction l; apply Acc_intro; introv H.
  { inverts~ H. }
  { inverts~ H. applys~ IHl. }
Qed.

End ListSub.

Arguments list_sub {A}.
Hint Constructors list_sub.
Hint Resolve list_sub_wf : wf.




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

Lemma MListOf_eq : forall A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc),
  p ~> MListOf R L =
  match L with
  | nil => \[p = null]
  | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} \* (x ~> R X) \* (p' ~> MListOf R L')
  end.
Proof using. intros. xunfold MListOf at 1. destruct~ L. Qed.

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

Parameter create : val.

Parameter Triple_create : 
  TRIPLE (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).

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

Module Export Hints.
Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.
Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.
Hint Extern 1 (Register_Spec (push)) => Provide @Triple_push.
Hint Extern 1 (Register_Spec (pop)) => Provide @Triple_pop.
End Hints.

Global Opaque MList.MListOf.

End MList.


(* ####################################################### *)

From TLC Require Import LibMultiset.

Tactic Notation "multiset_eq" := (* TODO: move to TLC *)
  check_noevar_goal; permut_simpl.



(** For simplicity, assume the heap stores integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).



Inductive node : Type :=
  | Node : elem -> list node -> node.

Implicit Types n : node.

Definition heap := option node.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val (@None node). Qed.

Instance Inhab_node : Inhab node.
Proof using. applys Inhab_of_val (Node arbitrary nil). Qed.



Implicit Types x y : elem.
Implicit Types h : heap.
Implicit Types hs : list node.
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

Inductive inv : node -> elems -> Prop :=
  | inv_Node : forall x ns Es E,
      Forall2 inv ns Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->   
      inv (Node x ns) E.

Inductive repr : heap -> elems -> Prop :=
  | repr_None :
      repr None \{}
  | repr_Some : forall n E,
      inv n E ->
      repr (Some n) E.
  

(* ******************************************************* *)
(** ** Lemmas and tactics *)

Lemma list_union_nil :
  list_union (@nil elems) = \{}.
Proof using. auto. Qed.

Lemma list_union_cons : forall E Es,
  list_union (E::Es) = E \u list_union Es.
Proof using. auto. Qed.

Hint Rewrite list_union_nil list_union_cons : rew_listx.

Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => rew_listx; multiset_eq.
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
    { auto. } { applys* Forall_foreach_is_ge_inv Es. } }
Qed.


(* ******************************************************* *)
(** ** Coq code *)

Module Pure.

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
      if is_nil hs' 
        then n12 
        else merge n12 (merge_pairs hs')
  end.

Definition pop_min (h:heap) : elem * heap :=
  match h with
  | Some (Node x ns) =>
      let h' := if is_nil ns 
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
  { applys_eq* merge_lemma 1. }
  { applys_eq* merge_lemma 1. }
Qed.

Lemma insert_spec : forall x h E,
  repr h E ->
  repr (insert h x) (E \u \{x}).
Proof using.
  introv I. unfold insert.
  destruct h as [n|].
  { inverts I as I. constructor. applys_eq (>> merge_spec I) 1.
    { applys* inv_Node. } { autos*. } } 
  { inverts I. constructor. applys* inv_Node. }
Qed.

Lemma merge_pairs_spec : forall ns Es,
  ns <> nil ->
  Forall2 inv ns Es ->
  inv (merge_pairs ns) (list_union Es).
Proof using.
  intros ns. induction_wf IH: (@list_sub node) ns; introv N Is.
  destruct ns as [|n1 ns'']; tryfalse. inverts Is as I1 Is. 
  destruct ns'' as [|n2 ns']; simpl.
  { inverts Is. rename y into E. applys_eq* I1 1. }
  { inverts Is as I2 Is. rename r0 into Es, y0 into E2.
    rewrite is_nil_eq. case_if as C.
    { subst ns'. inverts Is. applys merge_spec. { applys I1. } { applys_eq* I2 1. } }
    { applys_eq merge_spec 1.
      { applys* merge_spec. }
      { applys* IH. }
      { autos*. } } }
Qed.

Lemma pop_min_spec : forall h E h' x,
  E <> \{} ->
  repr h E ->
  (x,h') = pop_min h ->
     min_of E x
  /\ exists E', repr h' E' /\ E = \{x} \u E'.
Proof using.
  introv N I M. unfolds pop_min.
  destruct h as [|n]; inverts I as I; tryfalse.
  destruct n as [y ns]. inverts M. inverts I as I1 Ks. split. 
  { applys~ pop_min_lemma. }
  { rewrite is_nil_eq. case_if as C.
    { subst ns. inverts I1. exists \{}. split~. constructor. }
    { forwards~ Is: merge_pairs_spec I1. exists (list_union Es). split~.
      constructor~. } }
Qed.

End Pure.

(* ******************************************************* *)
(** ** Deeply embedded code *)

Implicit Types p q l : loc.
Notation "''hs'" := ("hs":var) : var_scope.

Definition value : field := 0%nat.
Definition sub : field := 1%nat.

Definition create : val :=
  VFun 'u := 
    val_ref null.

Definition is_empty : val :=
  VFun 'p := 
    '!'p '= null.

Definition merge : val :=
  VFun 'q1 'q2 := 
		If_ ('q1'.value '< 'q2'.value) Then (
			MList.push ('q1'.sub) 'q2 ';
			'q1
		) Else (
			MList.push ('q2'.sub) 'q1 ';
			'q2
		).

Definition insert : val :=
  VFun 'p 'x :=
    Let 'q := '!'p in
    Let 'q2 := New`{ value := 'x; sub := MList.create '() } in
    If_ 'q '= null
      Then 'p ':= 'q2
      Else 'p ':= merge 'q 'q2.

Definition merge_pairs : val :=
  VFix 'f 'l := 
    Let 'q1 := MList.pop 'l in
    If_ MList.is_empty 'l Then 'q1 Else
    Let 'q2 := MList.pop 'l in
    Let 'q := merge 'q1 'q2 in
		If_ MList.is_empty 'l Then 'q Else
    merge 'q ('f 'l).

Definition pop_min : val :=
  VFun 'p :=
    Let 'q := '!'p in
    Let 'x := 'q'.value in
    (If_ MList.is_empty ('q'.sub)
      Then 'p ':= null
      Else 'p ':= merge_pairs ('q'.sub) )';
		'x.

(**
[[
Fixpoint Repr (h:heap) (q:loc) : hprop :=
  match h with
  | Node x hs => 
      \exists q',
         q ~> Record`{ value := x; sub := q' } 
      \* q' ~> MListOf Repr hs
  end.
]]
*)

Fixpoint Tree (n:node) (q:loc) : hprop :=
  match n with
  | Node x hs => 
      \exists l,
       q ~> Record`{ value := x; sub := l } \*
      (fix MListOf L p : hprop :=
      match L with
      | nil => \[p = null]
      | X::L' => \exists (x:loc) p', 
                    p ~> Record`{ MList.head := x; MList.tail := p'} 
                   \* (x ~> Tree X) \* (p' ~> MListOf L')
      end) hs l
  end.


Definition Repr (E:elems) (q:loc) : hprop :=
  \exists n, q ~> Tree n \* \[inv n E].

Definition Contents (E:elems) (q:loc) : hprop :=
  If q = null then \[E = \{}] else q ~> Repr E.

Definition Heap (E:elems) (p:loc) : hprop :=
  \exists q, p ~~> q \* Contents E q.



Lemma Tree_eq : forall n q,
  q ~> Tree n =
    match n with
    | Node x hs =>
        \exists l, q ~> Record`{ value := x; sub := l }
                \* l ~> MList.MListOf Tree hs
  end.
Proof using.
  intros n. induction n as [x hs]; intros.
  xunfold Tree. fequals; applys fun_ext_1 ;=> l. fequals.
  gen l. induction hs as [|n hs']; intros.
  { auto. }
  { rewrite MList.MListOf_eq. fequals; applys fun_ext_1 ;=> y.
    fequals; applys fun_ext_1 ;=> p'. fequals. fequals.
    rewrite~ <- IHhs'. }
Qed.

Lemma Tree_Node : forall q x hs,
  q ~> Tree (Node x hs) =
      \exists l, q ~> Record`{ value := x; sub := l }
              \* l ~> MList.MListOf Tree hs.
Proof using. intros. rewrite~ Tree_eq. Qed.


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
  xsimpl~ (Node x hs). rewrite Tree_eq. xsimpl.
Qed.

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


Import MList.Hints.


(* ******************************************************* *)


Lemma Triple_create :
  TRIPLE (create tt)
    PRE \[]
    POST (fun p => p ~> Heap \{}).
Proof using.
  xwp. xapp (>> Triple_ref Enc_loc null) ;=> p. (* LATER: spec auto *)
  xunfold Heap. xsimpl. xchanges~ Contents_null.
Qed.

Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.

Lemma Triple_is_empty : forall p E,
  TRIPLE (is_empty p)
    PRE (p ~> Heap E)
    POST (fun b => \[b = isTrue (E = \{})] \* p ~> Heap E).
Proof using.
  xwp. xunfolds Heap ;=> q. xapp. xapp. typeclass. (* LATER: inj by default *)
  xchanges~ Contents_is_empty.
Qed.

Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.

Lemma Triple_merge : forall q1 q2 E1 E2,
  TRIPLE (merge q1 q2)
    PRE (q1 ~> Repr E1 \* q2 ~> Repr E2)
    POST (fun q => q ~> Repr (E1 \u E2)).
Proof using.
admit.
Admitted.

Hint Extern 1 (Register_Spec (merge)) => Provide @Triple_merge.

Lemma Triple_insert : forall p x E,
  TRIPLE (insert p x)
    PRE (p ~> Heap E)
    POST (fun (_:unit) => p ~> Heap (E \u \{x})).
Proof using.
  xwp. xchange Heap_eq ;=> q. xapp. xapp (>> __ Tree) ;=> l.
  xnew (>> x l). skip. (* TODO *) intros q2.
  xchange <- Tree_Node. xchange <- Repr_eq. { applys* inv_Node. }
  rew_listx. xapp. typeclass. unfold Contents. xif ;=> C; case_if.
  { xpull ;=> ->. xapp. xchanges* Heap_of_Repr. }
  { xapp ;=> r. xapp. xchanges* Heap_of_Repr. }
Qed.

Hint Extern 1 (Register_Spec (insert)) => Provide @Triple_insert.

Lemma Triple_merge_pairs : forall l ns Es,
  ns <> nil ->
  Forall2 inv ns Es ->
  TRIPLE (merge_pairs l)
    PRE (l ~> MList.MListOf Tree ns)
    POST (fun q => q ~> Repr (list_union Es)).
Proof using.
skip.
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
  xseq. xapp. xapp (>> __ Tree). (* LATER: no arg *) 
  xpost (fun (_:unit) => \exists E', \[E = '{x} \u E'] \* p ~> Heap E' \* \GC). xif ;=> C.
  { { subst. inverts Is. inverts Ks. rew_listx.
      xapp (>> Triple_set Enc_loc). xchange <- Tree_Node. xchanges* Heap_of_null. } }
    { xapp. xapp; eauto ;=> r. xapp. xchange Heap_of_Repr. xsimpl*. }
  { intros _. xpull ;=> E' ->. xval. xsimpl. split~.
    { rewrite Eq. applys~ pop_min_lemma. } }
Qed.

Hint Extern 1 (Register_Spec (pop_min)) => Provide @Triple_pop_min.





  (* LATER: reimplement merge_pairs using a whilte loop *)