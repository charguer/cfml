Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import MList_ml.
From TLC Require Import LibListZ.


(* TODO MOVE *)

Lemma heq_hexists : forall A (J1 J2:A->hprop),
  (forall (x:A), J1 x = J2 x) ->
  hexists J1 = hexists J2.
Proof using. introv M. fequals. applys* fun_ext_1. Qed.

Lemma heq_hstar_hpure : forall H1 H2 P,
  (P -> H1 = H2) ->
  H1 \* \[P] = H2 \* \[P].
Proof using. introv M. xsimpl*; intros; rewrite* M. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Representation predicates *)

(** [p ~> MList L] asserts that at location [p] one finds a mutable list
    whose values are described by the list [L]. These values are not associated
    with any ownership, unlike with [MListOf]. *)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists (v:contents_ A), p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Definition MList_contents A `{EA:Enc A} (v:contents_ A) (L:list A) : hprop :=
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Lemma MList_contents_iff : forall A (EA:Enc A) v (L:list A),
  (MList_contents v L) ==> (MList_contents v L) \* \[v = Nil <-> L = nil].
Proof using.
  intros. unfold MList_contents. destruct L; xsimpl; auto_false.
Qed.

Lemma MList_eq : forall (p:loc) A (EA:Enc A) (L:list A),
  p ~> MList L = (\exists (v:contents_ A), p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

Lemma MList_nil : forall (p:loc) A (EA:Enc A),
  (p ~> MList (@nil A)) = (p ~~> (@Nil A)).
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> ? ->. auto. }
  { xsimpl~. }
Qed.

Lemma MList_cons : forall (p:loc) A `{EA:Enc A} x (L':list A),
    p ~> MList (x::L')
  = \exists p', p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. intros. xunfold MList at 1. xsimpl~. Qed.

Lemma MList_not_nil : forall (p:loc) A `{EA:Enc A} (L:list A),
  L <> nil ->
  p ~> MList L ==> \exists x L' p', \[L = x::L'] \*
                      p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. introv N. destruct L as [|x L']; tryfalse. xchanges* MList_cons. Qed.

Lemma haffine_MList : forall A `{EA:Enc A}  (L:list A) (p:loc),
  haffine (p ~> MList L).
Proof using.
  intros. gen p. induction L; intros; xunfold MList; xaffine.
Qed.

Hint Resolve haffine_MList : haffine.


(* ---------------------------------------------------------------------- *)
(** ** Specifications for stack operations w.r.t. [MList] *)

Section Ops.

Context A {EA:Enc A}.
Implicit Types L : list A.
Implicit Types x : A.

Lemma Triple_is_empty : forall L p,
  SPEC (is_empty p)
    PRE (p ~> MList (L:list A))
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> MList L).
Proof using.
  xcf. xchange MList_eq ;=> v. xchange MList_contents_iff ;=> HL. xmatch.
  { xvals*. xchanges <- MList_eq. }
  { xvals. { auto_false*. } xchanges <- MList_eq. }
Qed.

Lemma Triple_create :
  SPEC (create tt)
    PRE \[]
    POST (fun p => p ~> MList (@nil A)).
Proof using.
  xcf. xapp ;=> p. xchanges <- MList_nil.
Qed.

Lemma Triple_push : forall L p x,
  SPEC (push p x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (x::L)).
Proof using.
  xcf. xchange MList_eq ;=> v. xapp. xapp ;=> q. xapp.
  xchanges <- (@MList_eq q). xchanges <- (@MList_cons p).
Qed.

Lemma Triple_pop : forall L p,
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> MList L)
    POST (fun x =>
      \exists L', \[L = x::L'] \* p ~> MList L').
Proof using.
  xcf. xchange MList_eq ;=> v. xchange MList_contents_iff ;=> HL.
  xmatch; destruct L as [|x' L']; auto_false*.
  unfold MList_contents. xpull ;=> q' E. inverts E.
  xchange MList_eq ;=> v'. xapp. xapp. xval. xchanges* <- (@MList_eq p).
Qed.

End Ops.

Global Opaque MList.

Module Import SpecMList.
Hint Extern 1 (RegisterSpec create) => Provide Triple_create.
Hint Extern 1 (RegisterSpec is_empty) => Provide Triple_is_empty.
Hint Extern 1 (RegisterSpec push) => Provide Triple_push.
Hint Extern 1 (RegisterSpec pop) => Provide Triple_pop.
End SpecMList.



(* ---------------------------------------------------------------------- *)
(** ** Derived specifications for stack operations w.r.t. [MListOf] *)

(** [p ~> MListOf R L] asserts that at location [p] one finds a mutable list
    whose values are described by the list [L], where an item [x] from the list
    is related to an logical value [X] from the list [L], via the representation
    predicate [R]. *)

Definition MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  \exists (l:list A), \[length l = length L] \* p ~> MList l
                      \* hfold_list2 (fun X x => x ~> R X) L l.


Lemma MListOf_nil : forall p A `{EA:Enc A} TA (R:TA->A->hprop),
  (p ~> MListOf R (@nil TA)) = (p ~~> (@Nil A)).
Proof using.
  intros. xunfold MListOf. applys himpl_antisym.
  { xpull ;=> l Hl. rewrites (>> length_zero_inv Hl). xchange MList_nil. simpl. xsimpl. }
  { xchange <- MList_nil. xsimpl*. }
Qed.

Lemma MListOf_cons : forall p A `{EA:Enc A} TA (R:TA->A->hprop) X L,
  (p ~> MListOf R (X::L)) = \exists x p', p ~~> (Cons x p') \* (x ~> R X) \* (p' ~> MListOf R L).
Proof using.
  intros. xunfold MListOf. applys himpl_antisym.
  { xpull ;=> l Hl. rew_list in *. lets (x&l'&->): length_pos_inv_cons l. { math. }
    xchange MList_cons. intros p'. simpl. xsimpl. { rew_list in *. math. } }
  { xpull ;=> x p' l EQ. xchange <- MList_cons. xsimpl*. { rew_list. math. } }
Qed.

Lemma MListOfCongr : forall p a A `{EA:Enc a} (R1 R2:A->a->hprop) (L:list A),
  (forall (x:a) (X:A), mem X L -> R1 X x = R2 X x) ->
  p ~> MListOf R1 L = p ~> MListOf R2 L.
Proof using.
  introv EQ. gen p. induction L; intros.
  { do 2 rewrite MListOf_nil. auto. }
  { do 2 rewrite MListOf_cons.
    applys heq_hexists. intros x.
    applys heq_hexists. intros p'.
    fequals. fequals. { applys* EQ. } { applys* IHL. } }
Qed.

Lemma haffine_MListOf : forall A (EA:Enc A) TA (R:TA->A->hprop) (L:list TA) (p:loc),
  (forall x X, mem X L -> haffine (x ~> R X)) ->
  haffine (p ~> MListOf R L).
Proof using.
  intros. xunfold MListOf. xaffine. do 2 rewrite length_eq in *.
  applys* haffine_hfold_list2. math.
Qed.

Hint Resolve haffine_MListOf : haffine.

Section OfOps.

Context A {EA:Enc A} TA (R:TA->A->hprop).
Implicit Types L : list TA.
Implicit Types x : A.
Implicit Types X : TA.

Lemma Triple_create' :
  SPEC (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).
Proof using.
  xtriple. xapp (>> Triple_create EA) ;=> p. xunfold MListOf. xsimpl*.
  { rew_heapx. xsimpl. }
Qed.

(**
Ltac applys_base E ::=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ eapply E  | rapply E  | applys_build E ]
  end; fast_rm_inside E.
*)

Lemma Triple_is_empty' : forall L p,
  SPEC (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp. xsimpl*.
  { applys* LibSepTLCbuffer.list_same_length_inv_nil. }
Qed.

Lemma Triple_push' : forall L p x X,
  SPEC (push p x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  xsimpl (x::l). { rew_list. math. } { rew_heapx. xsimpl. }
Qed.

Lemma Triple_pop' : forall L p,
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  { rewrites~ (>> LibSepTLCbuffer.list_same_length_inv_nil L). }
  intros x l' ->. destruct L as [|X L']; rew_listx in *; tryfalse.
  rew_heapx. xsimpl*. math.
Qed.

End OfOps.

Global Opaque MListOf.

Module Import SpecMListOf.
Hint Extern 1 (RegisterSpec create) => Provide Triple_create'.
Hint Extern 1 (RegisterSpec is_empty) => Provide Triple_is_empty'.
Hint Extern 1 (RegisterSpec push) => Provide Triple_push'.
Hint Extern 1 (RegisterSpec pop) => Provide Triple_pop'.
End SpecMListOf.
