(**

This file formalizes basic examples from standard Separation Logic,
as described in Arthur Charguéraud's lecture notes.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require LibListZ.
From Sep Require Import LambdaCF TLCbuffer.
Export NotationForVariables NotationForTerms.
Open Scope trm_scope.
Open Scope heap_scope.
Open Scope liblist_scope.
Open Scope charac.

Ltac auto_star ::= jauto.


Local Open Scope fmap_scope.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types f : var.
Implicit Types k : field.
Implicit Type l p q : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Derived basic functions *)


(* ---------------------------------------------------------------------- *)
(** Increment function *)

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.

(** Same proof using characteristic formulae with advanced tactics *)

Lemma triple_incr : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_spec val_incr) => Provide triple_incr.


(* ---------------------------------------------------------------------- *)
(** Decrement function *)

Definition val_decr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '- 1 in
    val_set 'p 'm.

Lemma triple_decr : forall p n,
  triple (val_decr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n-1))).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_spec val_decr) => Provide triple_decr.


(* ---------------------------------------------------------------------- *)
(** Negation *)

Definition val_not :=
  ValFun 'n := If_ 'n '= true Then false Else true.

Lemma triple_not : forall (b:bool),
  triple (val_not b)
    \[]
    (fun r => \[r = !b]).
Proof using.
  xcf. xapps. xif; => C.
  { xvals. inverts~ C. }
  { xvals. fequals. destruct b; auto_false. }
Qed.

Hint Extern 1 (Register_spec val_not) => Provide triple_not.


(* ---------------------------------------------------------------------- *)
(** Disequality test *)

Definition val_neq :=
  ValFun 'm 'n :=
    Let 'x := ('m '= 'n) in
    val_not 'x.

Notation "t1 '<> t2" :=
  (val_neq t1 t2)
  (at level 69) : trm_scope.

Lemma triple_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 <> v2)]).
Proof using.
  xcf. xapps. xapps. hsimpl ;=> ? ->. rew_isTrue~.
Qed.

Hint Extern 1 (Register_spec val_neq) => Provide triple_neq.


(* ********************************************************************** *)
(* * Formalisation of records *)

(* ---------------------------------------------------------------------- *)
(** Read to a record field *)

Definition val_get_field (k:field) :=
  ValFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Lemma triple_get_field : forall l k v,
  triple ((val_get_field k) l)
    (l `.` k ~~~> v)
    (fun r => \[r = v] \* (l `.` k ~~~> v)).
Proof using.
  intros. unfold val_get_field. xcf.
  xapp triple_ptr_add_nat.
  intros r ->.
  rewrite hfield_eq_fun_hsingle. xpull ;=> N.
  xapps triple_get. intros ? ->. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Write to a record field *)

Definition val_set_field (k:field) :=
  ValFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Lemma triple_set_field : forall v' l k v,
  triple ((val_set_field k) l v)
    (l `.` k ~~~> v')
    (fun r => \[r = val_unit] \* (l `.` k ~~~> v)).
Proof using.
  intros. unfold val_set_field. xcf.
  xapp triple_ptr_add_nat.
  intros r ->.
  rewrite hfield_eq_fun_hsingle. xpull ;=> N.
  xapps triple_set. intros ? ->. hsimpl~.
Qed.

Arguments triple_set_field : clear implicits.


(* ********************************************************************** *)
(* * Formalisation of arrays *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint Array (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~~> x) \* (Array L' (S p))
  end.

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
    hsimpl~ (>> L1 x L2). subst L. rewrite Array_concat_eq, Array_cons_eq.
    rew_nat. hsimpl. rewrite HM. rewrite~ abs_nat_plus_nonneg. math. }
  { hpull ;=> L1 x L2 HM E. subst n.
    subst L. rewrite Array_concat_eq, Array_cons_eq.
    rew_nat. hsimpl. applys_eq himpl_refl 1. fequals.
    rewrite abs_nat_plus_nonneg; [|math]. rewrite~ abs_nat. }
Qed.

Global Opaque Array.


(* ---------------------------------------------------------------------- *)
(** Array allocation *)

Lemma Array_of_Alloc : forall k l,
  Alloc k l ==>
  \exists (L : list val), \[length L = k] \* Array L l.
Proof using.
  intros. gen l. induction k; intros.
  { rew_Alloc. hsimpl (@nil val). rew_list~. }
  { rew_Alloc. hpull ;=> v. hchange IHk. hpull ;=> L E.
    hsimpl (v::L).
    { rewrite Array_cons_eq. hsimpl~. }
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
  intros r. hpull ;=> l (E&Nl). subst r.
  hchange Array_of_Alloc. hpull ;=> L HL.
  hsimpl~. rewrite HL. rewrite~ abs_nonneg.
Qed.


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
  xpull ;=> L1 x L2 EL HL.
  xapp. hpull ;=> r. intro_subst.
  hsimpl; auto. { subst. rewrite~ read_middle. }
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
  xpull ;=> L1 x L2 EL HL.
  xapp triple_set. hpull ;=> r. intro_subst.
  rewrites (>> Array_middle_eq i (L[i := v])).
   { rewrite <- length_eq in *. rew_array. math. }
  hsimpl; auto. { subst. rewrite~ update_middle. rew_list~. }
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

Lemma triple_array_make : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (fun r => \exists p L, \[r = val_loc p] \* \[L = make n v] \* Array L p).
Proof using.
  introv N. xcf. xapp~ triple_alloc_array ;=> r p L Er EL. subst r.
  xapps. xseq.
  { (* LATER: xfor tactic *)
    applys local_erase. esplit; esplit; splits; [reflexivity|reflexivity|].
    intros S LS EF M. subst EF. simpl in M.
    cuts G: (forall i L', i >= 0 -> length L' = n-i ->
       S i (Array ((make i v)++L') p) (fun r => (Array (make n v) p))).
    { applys_eq (>> G L) 2. math. math. rewrite make_zero. rew_list~. }
    intros i. induction_wf IH: (upto n) i. intros L' Ei EL'.
    applys (rm M). case_if.
    { xseq. (* later: remove *)
      xapp~. { rewrite index_eq_inbound. rew_list. rewrite length_make; math. }
      intros r. hsimpl.
      destruct L' as [|x L']. { false. rew_list in EL'. math. }
      rewrite~ update_middle; [| rewrite length_make; math ].
      rew_list. xapplys (>> IH L').
      { auto with maths. }
      { rew_list; math. }
      { rew_list in *; math. }
      { applys LS. }
      { rewrite make_succ_r; [|math]. rew_list. hsimpl~. } }
    { xval. math E: (i = LibList.length L).
      asserts: (L' = nil). { applys length_zero_inv. math. }
      subst. rew_list. hsimpl~. } }
  { simpl ;=> _. xval. subst n. hsimpl~. }
Qed.

Hint Extern 1 (Register_spec val_array_make) => Provide triple_array_make.


(* ---------------------------------------------------------------------- *)
(** Array init *)
