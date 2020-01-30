(**

Separation Logic Foundations

Chapter: "Struct".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SLFDirect SLFExtra.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(*

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(** * Chapter in a rush *)

(** This chapter introduces

    - records
    - arrays
    - n-ary functions

*)


(* ####################################################### *)
(** ** Semantics of the allocation of consecutive cells *)

val_uninitialized

=> restriction on read is possible

Fixpoint nat_seq p k =
  match k with

Fixpoint hfold_list F L =
  match L with

Definition hcells n p =
  hfold_list (fun q => q ~~> val_uninitialized) (seq p k).

Implicit Types n : int


(* ####################################################### *)
(** ** Specification of the allocation of consecutive cells *)

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_alloc. } { xsimpl*. }
Qed.

Lemma triple_dealloc : forall n l,
  n >= 0 ->
  triple (val_dealloc n l)
    (Dealloc (abs n) l)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_dealloc. } { xsimpl*. }
Qed.


Fixpoint Alloc (k:nat) (l:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => l ~~~> val_uninitialized \* (Alloc k' (S l)%nat)
  end.

Lemma Alloc_zero_eq : forall l,
  Alloc O l = \[].
Proof using. auto. Qed.

Lemma Alloc_succ_eq : forall l k,
  Alloc (S k) l = l ~~~> val_uninitialized \* Alloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc.

Hint Rewrite Alloc_zero_eq Alloc_succ_eq : rew_Alloc.

Tactic Notation "rew_Alloc" :=
  autorewrite with rew_Alloc.

Lemma Alloc_split_eq : forall k1 (k:nat) p,
  (k1 <= k)%nat ->
  Alloc k p = Alloc k1 p \* Alloc (k-k1)%nat (p + k1)%nat.
Proof using.
  Transparent loc field. unfold field.
  intros k1 k. gen k1. induction k; introv N.
  {math_rewrite (k1 = 0%nat). rew_Alloc. rew_heap~. }
  { destruct k1 as [|k1']; rew_nat.
    { rew_Alloc. rew_heap~. }
    { rew_Alloc. rewrite (IHk k1'); [|math]. rew_heap~. } }
Qed.

Arguments Alloc_split_eq : clear implicits.

Lemma Alloc_split_inv : forall k1 k2 p,
  Alloc k1 p \* Alloc k2 (p + k1)%nat ==> Alloc (k1+k2)%nat p.
Proof using.
  intros. rewrites (Alloc_split_eq k1 (k1+k2)%nat p); [|math]. rew_nat~.
Qed.




(* ########################################################### *)
(** ** Definition of record fields *)

Definition field : Type := nat.

Definition hfield (l:loc) (k:field) (v:val) : hprop :=
  (l+k)%nat ~~> v \* \[ l <> null ].

Notation "l `. k '~~>' v" := (hfield l k v)
  (at level 32, k at level 0, no associativity,
   format "l `. k  '~~>'  v") : heap_scope.

Lemma hfield_not_null : forall l k v,
  (l`.k ~~> v) ==> (l`.k ~~> v) \* \[l <> null].
Proof using.
  intros. subst. unfold hfield. xchanges~ hsingle_not_null.
Qed.




(* ########################################################### *)
(** ** Specification of record operations *)


Parameter triple_get_field : forall l f v,
  triple ((val_get_field f) l)
    (l`.f ~~> v)
    (fun r => \[r = v] \* (l`.f ~~> v)).

Parameter triple_set_field : forall v1 l f v2,
  triple ((val_set_field f) l v2)
    (l`.f ~~> v1)
    (fun _ => l`.f ~~> v2).

Hint Resolve triple_get_field triple_set_field : triple.




(* ####################################################### *)
(** ** Representation predicate for a record *)


Definition head : field := 0%nat.
Definition tail : field := 1%nat.


Definition MCell (x:val) (q:loc) (p:loc) : hprop :=
  (p`.head ~~> x) \* (p`.tail ~~> q).



(* ####################################################### *)
(** ** Representation predicate for an array *)


(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint Array (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~~> x) \* (Array L' (S p))
  end.

Global Opaque Array.


(* ---------------------------------------------------------------------- *)
(** Array allocation *)

Lemma Array_of_Alloc : forall k l,
  Alloc k l ==>
  \exists (L : list val), \[length L = k] \* Array L l.
Proof using.
  intros. gen l. induction k; intros.
  { rew_Alloc. xsimpl (@nil val). rew_list~. }
  { rew_Alloc. xpull ;=> v. xchange IHk. xpull ;=> L E.
    xsimpl (v::L).
    { rewrite Array_cons_eq. xsimpl~. }
    { rew_list. math. } }
Qed.

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists (p:loc) (L:list val), \[r = val_loc p] \*
              \[length L = n :> int] \* Array L p).
Proof using.
  introv N. xapp. math.
  intros r. xpull ;=> l (E&Nl). subst r.
  xchange Array_of_Alloc. xpull ;=> L HL.
  xsimpl~. rewrite HL. rewrite~ abs_nonneg.
Qed.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)


(* ####################################################### *)
(** ** Proof of operation on list cells *)

(** *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (MList L' q)
  end.

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* MList L' q.
Proof using.  auto. Qed.


(** Next, we consider functions for constructing mutable lists.
    We begin with the function that allocates one cell.
    The function [mcell] takes as arguments the values to be
    stored in the head and the tail fields of the new cell.

[[
    let rec mcell x q =
      { head = x; tail = q }
]]

    In our ad-hoc program syntax, the [New] construct denotes record
    allocation. *)

Definition mcell : val :=
  VFun 'x 'q :=
    New`{ head := 'x ; tail := 'q }.

(** The precondition of [mcell x q] is empty. Its postcondition
    asserts that the return value is a location [p] such that
    two fields are allocated: [p`.head ~~> x] and [p`.tail ~~> q]. *)

Lemma Triple_mcell : forall (x:int) (q:loc),
  TRIPLE (mcell x q)
    PRE \[]
    POST (fun (p:loc) => (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  (* The tactic [xapp] handles the reasoning on the [New] construct. *)
  xwp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mcell) => Provide Triple_mcell.

(** The function [mcons] is an alias for [mcell].

    Whereas [mcell] is intended to allocate a fresh cell on its own,
    [mcons] is intended to extend an existing list by appending to
    it a freshly-allocated cell. *)

Definition mcons : val := mcell.

(** The specification of [mcons] thus requires a list [q ~> MList L]
    in its precondition, and produces a list [p ~> MList (x::L)] in
    its postcondition. *)

Lemma Triple_mcons : forall (x:int) (q:loc) (L:list int),
  TRIPLE (mcons x q)
    PRE (q ~> MList L)
    POST (fun (p:loc) => p ~> MList (x::L)).
Proof using.
  intros. unfold mcons. xtriple. xapp Triple_mcell.
  intros p. xchange <- MList_cons. (* Fold back the list *)
Qed.

Hint Extern 1 (Register_Spec mcons) => Provide Triple_mcons.




(** The operation [mnil()] returns the [null] value.
    The intention is to produce a representation for the empty list.

[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  VFun 'u :=
    null.

(** The precondition of [mnil] is empty. Its postcondition of [mnil]
    asserts that the return value [p] is a pointer such that
    [p ~> MList nil]. *)

Lemma Triple_mnil :
  TRIPLE (mnil '())
    PRE \[]
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  (* The proof requires introducing [null ~> MList nil] from nothing. *)
  xwp. xval. xchange <- (MList_nil null). { auto. }
Qed.

Hint Extern 1 (Register_Spec mnil) => Provide Triple_mnil.

(** Observe that the specification [Triple_mnil] does not mention
    the [null] pointer anywhere. This specification can thus be
    used to specify the behavior of operations on mutable lists
    without having to reveal low-level implementation details. *)

(** Remark: in the proof of [Triple_mnil], the call to
    [xchange <- (MList_nil null)] can be replaced to a simpler
    tactic invokation: [xchange MList_nil_intro], where
    [MList_nil_intro] corresponds to the lemma stated next. *)

Lemma MList_nil_intro :
  \[] ==> (null ~> MList nil).
Proof using. intros. xchange <- (MList_nil null). auto. Qed.

Lemma Triple_mnil' :
  TRIPLE (mnil '())
    PRE \[]
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  xwp. xval. xchange MList_nil_intro.
Qed.



(* ########################################################### *)
(** ** List copy *)

(** Let's put to practice the function [mnil] and [mcons] for
    verifying the function [mcopy], which constructs an independent
    copy of a given linked list.

[[
    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
]]
*)

Definition mcopy : val :=
  VFix 'f 'p :=
    If_ 'p  '= null
      Then mnil '()
      Else mcons ('p'.head) ('f ('p'.tail)).

(** The precondition of [mcopy] requires a linked list [p ~> MList L].
    Its postcondition asserts that the function returns a pointer [p']
    and a list [p' ~> MList L], in addition to the original list
    [p ~> MList L]. The two lists are totally disjoint and independent,
    as captured by the separating conjunction symbol (the star). *)

Lemma Triple_mcopy : forall (p:loc) (L:list int),
  TRIPLE (mcopy p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).

(** The proof script is very similar in structure to the previous ones.
    While playing the script, try to spot the places where:

    - [mnil] produces an empty list of the form [p' ~> MList nil],
    - the recursive call produces a list of the form [q' ~> MList L'],
    - [mcons] produces a list of the form [p' ~> MList (x::L')]. *)

Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchange* <- (MList_nil p). }
  { intros x q L' ->. xapp. xapp. xapp*. intros q'.
    xapp. intros p'. xchange <- MList_cons. }
Qed.

Hint Extern 1 (Register_Spec mcopy) => Provide Triple_mcopy.

(* ########################################################### *)
(** ** Deallocation of a cell: [mfree_cell] *)

(** Separation Logic can be set up to enforce that all allocated data
    eventually gets properly deallocated. In what follows, we describe
    a function for deallocating one cell, and a function for deallocating
    an entire mutable list. *)

(** There is no explicit deallocation in OCaml, which is equipped with
    a garbage collector, but let's pretend that there is a [delete]
    operation for deallocating records.

[[
    let mfree_cell p =
      delete p
]]

    For technical reasons (because our source language is untyped and our
    formal semantics does not keep track of the size of allocated block),
    we require in our ad-hoc program syntax the delete operation to
    be annotated with the names of the fields of the record to be deleted,
    as shown below.
*)

Definition mfree_cell : val :=
  VFun 'p :=
    val_dealloc 2 'p.

Notation "'Delete' n" := (val_dealloc n) : trm_scope.

(** The precondition of [mfree_cell p] describes the two fields
    associated with the cell: [p`.head ~~> x] and [p`.tail ~~> q].
    The postcondition is empty: the fields are destroyed. *)

Lemma Triple_mfree_cell : forall (x:int) (p q:loc),
  TRIPLE (mfree_cell p)
    PRE ((p`.head ~~> x) \* (p`.tail ~~> q))
    POST (fun (r:unit) => \[]).
Proof using.
  (* The tactic [xapp] handles the reasoning on the [Delete] construct. *)
  xwp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mfree_cell) => Provide Triple_mfree_cell.


(** The operation [mfree_list] deallocates all the cells in a given list.
    It can be implemented as the following tail-recursive function.

[[
    let rec mfree_list p =
      if p != null then begin
        let q = p.tail in
        mfree_cell p;
        mfree_list q
      end
]]

*)

Definition mfree_list : val :=
  VFix 'f 'p :=
    If_ 'p '<> null Then
      Let 'q := 'p'.tail in
      mfree_cell 'p ';
      'f 'q
    End.

(** The precondition of [mfree_list p] requires a full list [p ~> MList L].
    The postcondition is empty: the entire list is destroyed. *)

(* EX1! (Triple_mfree_list) *)
(** Verify the function [mfree_list].
    Hint: follow the pattern of the proof of the function [mlength]. *)

Lemma Triple_mfree_list : forall (p:loc) (L: list int),
  TRIPLE (mfree_list p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => \[]).
Proof using. (* ADMITTED *)
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. { auto. } xsimpl. }
  { intros ->. xval. xsimpl. }
Qed. (* /ADMITTED *)

(** [] *)

Hint Extern 1 (Register_Spec mfree_list) => Provide Triple_mfree_list.

(** This concludes our quick tour of functions on mutable lists.
    Additional functions are presented further in the file,
    as exercises. *)


(* ####################################################### *)
(** ** Local reasoning on arrays *)

Lemma Array_nil_eq : forall p,
  Array nil p = \[].
Proof using. auto. Qed.

Lemma Array_cons_eq : forall p x L,
  Array (x::L) p = (p ~~~> x) \* Array L (S p).
Proof using. auto. Qed.

Lemma Array_one_eq : forall p x,
  Array (x::nil) p = (p ~~~> x).
Proof using. intros. rewrite Array_cons_eq, Array_nil_eq. rew_heap~. Qed.

Lemma Array_concat_eq : forall p L1 L2,
  Array (L1++L2) p = Array L1 p \* Array L2 (p + length L1)%nat.
Proof using.
  Transparent loc.
  intros. gen p. induction L1; intros; rew_list.
  { rewrite Array_nil_eq. rew_heap. fequals. unfold loc; math. }
  { do 2 rewrite Array_cons_eq. rewrite IHL1. rew_heap. do 3 fequals.
    unfold loc; math. }
Qed.

Lemma Array_last_eq : forall p x L,
  Array (L&x) p = Array L p \* ((p + length L)%nat ~~~> x).
Proof using. intros. rewrite Array_concat_eq. rewrite~ Array_one_eq. Qed.

Lemma Array_middle_eq : forall n p L,
  0 <= n < length L ->
  Array L p = \exists L1 x L2, \[L = L1++x::L2] \* \[length L1 = n :> int] \*
    Array L1 p \* (abs(p+n) ~~~> x) \* Array L2 (p + length L1 + 1)%nat.
Proof using.
  (* LATER: simplify the Z/nat math, by using a result from LibListZ directly *)
  introv N. applys himpl_antisym.
  { forwards (L1&x&L2&E&HM): list_middle_inv (abs n) L.
    asserts (N1&N2): (0 <= abs n /\ (abs n < length L)%Z).
    { split; rewrite abs_nonneg; math. } math.
    lets M': eq_int_of_eq_nat HM. rewrite abs_nonneg in M'; [|math].
    xsimpl~ (>> L1 x L2). subst L. rewrite Array_concat_eq, Array_cons_eq.
    rew_nat. xsimpl. rewrite HM. rewrite~ abs_nat_plus_nonneg. math. }
  { xpull ;=> L1 x L2 HM E. subst n.
    subst L. rewrite Array_concat_eq, Array_cons_eq.
    rew_nat. xsimpl. applys_eq himpl_refl 1. fequals.
    rewrite abs_nat_plus_nonneg; [|math]. rewrite~ abs_nat. }
Qed.

function count

parallel calls remark


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)


(* ########################################################### *)
(** ** Semantics of the allocation operations *)


  | eval_alloc : forall k n ma mb l,
      mb = Fmap.conseq l (LibList.make k val_uninitialized) ->
      n = nat_to_Z k ->
      l <> null ->
      Fmap.disjoint ma mb ->
      eval ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  | eval_dealloc : forall n vs ma mb l,
      mb = Fmap.conseq l vs ->
      n = LibList.length vs ->
      Fmap.disjoint ma mb ->
      eval (mb \+ ma) (val_dealloc (val_int n) (val_loc l)) ma val_unit.


Lemma Alloc_fmap_conseq : forall l k,
  l <> null ->
  (Alloc k l) (Fmap.conseq l (LibList.make k val_uninitialized)).
Proof using.
  Transparent loc null.
  introv N. gen l. induction k; intros; rew_Alloc.
  { rewrite LibList.make_zero, Fmap.conseq_nil. applys~ hempty_intro. }
  { rewrite LibList.make_succ, Fmap.conseq_cons. applys hstar_intro.
    { split~. }
    { applys IHk. unfolds loc, null. math. }
    { applys~ Fmap.disjoint_single_conseq. } }
Qed.




(* ########################################################### *)
(** ** Definition of record operations using pointer arithmetics *)

Definition val_get_field (k:field) : val :=
  VFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  VFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

End FieldAccessDef.

Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 56, f at level 0, format "t1 ''.' f" ) : trm_scope.

Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2") : trm_scope.

Lemma triple_get_field : forall l f v,
  triple ((val_get_field f) l)
    (l`.f ~~> v)
    (fun r => \[r = v] \* (l`.f ~~> v)).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

Lemma triple_set_field : forall v1 l f v2,
  triple ((val_set_field f) l v2)
    (l`.f ~~> v1)
    (fun _ => l`.f ~~> v2).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.


(* ########################################################### *)
(** ** Definition of array operations using pointer arithmetics *)


(* -------------------------------------------------------------------------- *)
(** Accesses *)

Import LibListZ.
Implicit Types i ofs len : int.


(* ---------------------------------------------------------------------- *)
(** Array get *)

Definition val_array_get : val :=
  ValFun 'p 'i :=
    Let 'n := val_ptr_add 'p 'i in
    val_get 'n.

Lemma triple_array_get : forall p i L,
  index L i ->
  triple (val_array_get p i)
    (Array L p)
    (fun r => \[r = L[i]] \* Array L p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> Array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp. xpull ;=> r. intro_subst.
  xsimpl; auto. { subst. rewrite~ read_middle. }
Qed.

Hint Extern 1 (Register_spec val_array_get) => Provide triple_array_get.

Notation "'Array'' p `[ i ]" := (trm_app (trm_app (trm_val val_array_get) p) i)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]") : charac.


(* ---------------------------------------------------------------------- *)
(** Array set *)

Definition val_array_set : val :=
  ValFun 'p 'i 'x :=
    Let 'n := val_ptr_add 'p 'i in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  index L i ->
  triple (val_array_set p i v)
    (Array L p)
    (fun r => \[r = val_unit] \* Array (L[i:=v]) p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> Array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp triple_set. xpull ;=> r. intro_subst.
  rewrites (>> Array_middle_eq i (L[i := v])).
   { rewrite <- length_eq in *. rew_array. math. }
  xsimpl; auto. { subst. rewrite~ update_middle. rew_list~. }
Qed.

Hint Extern 1 (Register_spec val_array_set) => Provide triple_array_set.

Notation "'Array'' p `[ i ] `<- x" := (trm_app (trm_app (trm_app (trm_val val_array_set) p) i) x)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]  `<-  x") : charac.


(* ---------------------------------------------------------------------- *)
(** Array make *)

Definition val_array_make : val :=
  ValFun 'n 'v :=
    Let 'p := val_alloc 'n in
    Let 'b := 'n '- 1 in
    For 'i := 0 To 'b Do
      Array' 'p`['i] `<- 'v
    Done;;;
    'p.

(* ####################################################### *)
(** ** Grouped representation of record fields *)


(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Bind Scope fields_scope with Record_fields.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r`.f ~~> V) \* (r ~> Record L')
  end.

(* --TODO: currently restricted due to [r `. f ~> V] not ensuring [r<>null] *)
(* --TODO: rename *)
Lemma hRecord_not_null : forall (r:loc) (L:Record_fields),
  (* L <> nil -> *)
  mem (0%nat:field) (List.map fst L) ->
  (r ~> Record L) ==> (r ~> Record L) \* \[r <> null].
Proof using.
  introv M. induction L as [|(f,[A EA v]) L'].
  { inverts M. }
  { xunfold Record. inverts M.
    { xchange~ (Hfield_not_null r). xsimpl~. }
    { xchange~ IHL'. xsimpl~. } }
Qed.

(** Lemmas for unfolding the definition *)

Lemma Record_nil : forall p,
  p ~> Record nil = \[].
Proof using. auto. Qed.

Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.x ~~> ``V \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.

Hint Rewrite Record_nil Record_cons enc_dyn_make : Record_to_HField.


Local Open Scope heap_scope_ext.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,v) L']. { false. }
  rewrite Record_cons. xchanges~ Hfield_not_null.
Qed.



(* ####################################################### *)
(** ** Treatment of uncurried functions *)

  | trm_fixs : var -> list var -> trm -> trm
  | trm_apps : trm -> list trm -> trm


Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t :=
    subst y w t in
  let aux_no_captures xs t :=
    If LibList.mem y xs then t else aux t in
  match t with
  | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                        aux_no_captures xs t1)
  | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
  ...
 end.


Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. simpls. case_var.
  { false* var_fresh_mem_inv. }
  { auto. }
Qed.


  | eval_fixs : forall m f xs t1,
      xs <> nil ->
      eval m (trm_fixs f xs t1) m (val_fixs f xs t1)

  | eval_apps_fixs : forall m1 m2 f xs t3 v0 vs r,
      v0 = val_fixs f xs t3 ->
      var_fixs f (length vs) xs ->
      eval m1 (substn xs vs (subst1 f v0 t3)) m2 r ->
      eval m1 (trm_apps v0 vs) m2 r


Fixpoint var_distinct (xs:vars) : Prop :=
  match xs with
  | nil => True
  | x::xs' => var_fresh x xs' /\ var_distinct xs'
  end.

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.


(** [noduplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive noduplicates A : list A -> Prop :=
  | noduplicates_nil : noduplicates nil
  | noduplicates_cons : forall x l,
      ~ (mem x l) ->
      noduplicates l ->
      noduplicates (x::l).



Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop :=
     var_distinct (f::xs)
  /\ length xs = n
  /\ xs <> nil.

Definition var_fixs_exec (f:bind) (n:nat) (xs:vars) : bool := ..

Lemma var_fixs_exec_eq : forall f (n:nat) xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).


Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* eval_apps_fixs. }
Qed.


Fixpoint trms_to_vals_rec (acc:vals) (ts:trms) : option vals :=
  match ts with
  | nil => Some (List.rev acc)
  | trm_val v :: ts' => trms_to_vals_rec (v::acc) ts'
  | _ => None
  end.

Definition trms_to_vals (ts:trms) : option vals :=
  trms_to_vals_rec nil ts.


Lemma xwp_lemma_fixs : forall F f vs ts xs t H Q,
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f (length vs) xs ->
  H ==> (wpgen (combine (f::xs) (F::vs)) t) Q ->
  triple (trm_apps F ts) H Q.


(* ####################################################### *)
(** ** Coercion for uncurried functions *)

Coercion trm_to_pat : trm >-> pat.

(** Parsing facility: coercions for turning [t1 t2 t3]
    into [trm_apps t1 (t2::t3::nil)] *)

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.



*)