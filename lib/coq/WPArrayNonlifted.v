(**

Formalization of arrays, without lifting.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require LibListZ.
From CFML Require Export WPTactics.
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
(* * Formalisation of arrays *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint array (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~~> x) \* (array L' (S p))
  end.

Lemma array_nil_eq : forall p,
  array nil p = \[].
Proof using. auto. Qed.

Lemma array_cons_eq : forall p x L,
  array (x::L) p = (p ~~~> x) \* array L (S p).
Proof using. auto. Qed.

Lemma array_one_eq : forall p x,
  array (x::nil) p = (p ~~~> x).
Proof using. intros. rewrite array_cons_eq, array_nil_eq. rew_heap~. Qed.

Lemma array_concat_eq : forall p L1 L2,
  array (L1++L2) p = array L1 p \* array L2 (p + length L1)%nat.
Proof using.
  Transparent loc.
  intros. gen p. induction L1; intros; rew_list.
  { rewrite array_nil_eq. rew_heap. fequals. unfold loc; math. }
  { do 2 rewrite array_cons_eq. rewrite IHL1. rew_heap. do 3 fequals.
    unfold loc; math. }
Qed.

Lemma array_last_eq : forall p x L,
  array (L&x) p = array L p \* ((p + length L)%nat ~~~> x).
Proof using. intros. rewrite array_concat_eq. rewrite~ array_one_eq. Qed.

Lemma array_middle_eq : forall n p L,
  0 <= n < length L ->
  array L p = \exists L1 x L2, \[L = L1++x::L2] \* \[length L1 = n :> int] \*
    array L1 p \* (abs(p+n) ~~~> x) \* array L2 (p + length L1 + 1)%nat.
Proof using.
  (* LATER: simplify the Z/nat math, by using a result from LibListZ directly *)
  introv N. applys himpl_antisym.
  { forwards (L1&x&L2&E&HM): list_middle_inv (abs n) L.
    asserts (N1&N2): (0 <= abs n /\ (abs n < length L)%Z).
    { split; rewrite abs_nonneg; math. } math.
    lets M': eq_int_of_eq_nat HM. rewrite abs_nonneg in M'; [|math].
    xsimpl~ (>> L1 x L2). subst L. rewrite array_concat_eq, array_cons_eq.
    rew_nat. xsimpl. rewrite HM. rewrite~ abs_nat_plus_nonneg. math. }
  { xpull ;=> L1 x L2 HM E. subst n.
    subst L. rewrite array_concat_eq, array_cons_eq.
    rew_nat. xsimpl. applys_eq himpl_refl. fequals.
    rewrite abs_nat_plus_nonneg; [|math]. rewrite~ abs_nat. }
Qed.

(* ---------------------------------------------------------------------- *)
(** array allocation *)

(* TODO: later
Lemma array_of_Alloc : forall k l,
  Alloc k l ==>
  \exists (L : list val), \[length L = k] \* array L l.
Proof using.
  intros. gen l. induction k; intros.
  { rew_Alloc. xsimpl (@nil val). rew_list~. simple*. }
  { rew_Alloc. xchange IHk. intros L E.
    xsimpl (val_uninitialized::L).
    { rew_list. math. } 
    { rewrite array_cons_eq. xsimpl~. } }
Qed.

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists (p:loc) (L:list val), \[r = val_loc p] \*
              \[length L = n :> int] \* array L p).
Proof using.
  introv N. xapp. math.
  intros r. xpull ;=> l (E&Nl). subst r.
  xchange array_of_Alloc. xpull ;=> L HL.
  xsimpl~. rewrite HL. rewrite~ abs_nonneg.
Qed.
TODO
*)



Global Opaque array.


(* -------------------------------------------------------------------------- *)
(** Accesses *)

(* TODO: not there?
 
Import LibListZ.
Implicit Types i ofs len : int.


(* ---------------------------------------------------------------------- *)
(** array get *)

Definition val_array_get : val :=
  ValFun 'p 'i :=
    Let 'n := val_ptr_add 'p 'i in
    val_get 'n.

Lemma triple_array_get : forall p i L,
  index L i ->
  triple (val_array_get p i)
    (array L p)
    (fun r => \[r = L[i]] \* array L p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp. xpull ;=> r. intro_subst.
  xsimpl; auto. { subst. rewrite~ read_middle. }
Qed.

Hint Extern 1 (Register_spec val_array_get) => Provide triple_array_get.

Notation "'array'' p `[ i ]" := (trm_app (trm_app (trm_val val_array_get) p) i)
  (at level 69, p at level 0, no associativity,
   format "'array''  p `[ i ]") : charac.


(* ---------------------------------------------------------------------- *)
(** array set *)

Definition val_array_set : val :=
  ValFun 'p 'i 'x :=
    Let 'n := val_ptr_add 'p 'i in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  index L i ->
  triple (val_array_set p i v)
    (array L p)
    (fun r => \[r = val_unit] \* array (L[i:=v]) p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp triple_set. xpull ;=> r. intro_subst.
  rewrites (>> array_middle_eq i (L[i := v])).
   { rewrite <- length_eq in *. rew_array. math. }
  xsimpl; auto. { subst. rewrite~ update_middle. rew_list~. }
Qed.

Hint Extern 1 (Register_spec val_array_set) => Provide triple_array_set.

Notation "'array'' p `[ i ] `<- x" := (trm_app (trm_app (trm_app (trm_val val_array_set) p) i) x)
  (at level 69, p at level 0, no associativity,
   format "'array''  p `[ i ]  `<-  x") : charac.


(* ---------------------------------------------------------------------- *)
(** array make *)

Definition val_array_make : val :=
  ValFun 'n 'v :=
    Let 'p := val_alloc 'n in
    Let 'b := 'n '- 1 in
    For 'i := 0 To 'b Do
      array' 'p`['i] `<- 'v
    Done;;;
    'p.

Lemma triple_array_make : forall n v,
  n >= 0 ->
  triple (val_array_make n v)
    \[]
    (fun r => \exists p L, \[r = val_loc p] \* \[L = make n v] \* array L p).
Proof using.
  introv N. xcf. xapp~ triple_alloc_array ;=> r p L Er EL. subst r.
  xapps. xseq.
  { (* LATER: xfor tactic *)
    applys mklocal_erase. esplit; esplit; splits; [reflexivity|reflexivity|].
    intros S LS EF M. subst EF. simpl in M.
    cuts G: (forall i L', i >= 0 -> length L' = n-i ->
       S i (array ((make i v)++L') p) (fun r => (array (make n v) p))).
    { applys_eq (>> G L). math. math. rewrite make_zero. rew_list~. }
    intros i. induction_wf IH: (upto n) i. intros L' Ei EL'.
    applys (rm M). case_if.
    { xseq. (* later: remove *)
      xapp~. { rewrite index_eq_inbound. rew_list. rewrite length_make; math. }
      intros r. xsimpl.
      destruct L' as [|x L']. { false. rew_list in EL'. math. }
      rewrite~ update_middle; [| rewrite length_make; math ].
      rew_list. xapplys (>> IH L').
      { auto with maths. }
      { rew_list; math. }
      { rew_list in *; math. }
      { applys LS. }
      { rewrite make_succ_r; [|math]. rew_list. xsimpl~. } }
    { xval. math E: (i = LibList.length L).
      asserts: (L' = nil). { applys length_zero_inv. math. }
      subst. rew_list. xsimpl~. } }
  { simpl ;=> _. xval. subst n. xsimpl~. }
Qed.

Hint Extern 1 (Register_spec val_array_make) => Provide triple_array_make.



*)