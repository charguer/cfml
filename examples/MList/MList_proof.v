Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import MList_ml.
From TLC Require Import LibListZ.

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

Lemma Triple_copy : forall L p,
    SPEC (copy p)
      PRE (p ~> MList L)
      POST (fun q => p ~> MList L \* q ~> MList L).
Proof using.
  intro L. induction_wf IH : list_sub L.
  xcf. xchange* MList_eq ;=> v.
  xapp. destruct L as [|x' L']; xmatch.
  { xchange* MList_contents_iff; =>.
    xapp ;=> x.
    xchange* <- (MList_nil x).
    xchange* <- MList_eq. xsimpl*. }
  { unfold MList_contents; xpull*. }
  { unfold MList_contents; xpull*. }
  { unfold MList_contents; xpull*; =>.
    inversion H; subst.
    xapp; auto; =>. xapp; =>.
    xchange* <- MList_cons.
    xchange* <- MList_cons.
    xsimpl*. }
Qed.

Lemma Triple_rev_aux : forall L1 L2 p1 p2,
    SPEC (rev_aux p1 p2)
      PRE (p1 ~> MList L1 \* p2 ~> MList L2)
      POST (fun q => q ~> MList (rev L2 ++ L1)).
Proof using.
  intros. gen p1 p2 L1. induction_wf IH : list_sub L2. intros.
  xcf. xchange MList_eq ;=> v2. xchange MList_eq ;=> v1.
  xapp. xmatch.
  { xval. xchanges MList_contents_iff ;=> HL.
    destruct HL. cuts G : (L2 = nil); auto.
    subst. xchange* MList_contents_iff ;=>. rew_list*.
    xchange* <- MList_eq. unfold MList_contents. xsimpl*. }
  { destruct L2 as [|x2' L2'].
    { unfold MList_contents. xpull*. }
    { xchange* <- MList_eq. unfold MList_contents.
      xpull*. intros. inverts H.
      xchange* MList_eq. intros. xapp.
      xchange* MList_eq. intros. xapp.
      xapp. xapp. intros.
      xchange* <- (MList_eq x2).
      xchange* <- (MList_eq x0).
      xchange* <- (MList_cons p2).
      xapp; auto.
      rew_list*. xsimpl*. } }
Qed.

Lemma Triple_rev : forall L p,
    SPEC (rev_main p)
      PRE (p ~> MList L)
      POST (fun q => q ~> MList (rev L)).
Proof using.
  xcf. xapp ;=>.
  xchange* <- MList_nil. xapp Triple_rev_aux ;=>.
  xsimpl*. rew_list*.
Qed.

Lemma Triple_is_null : forall L p,
    SPEC (is_null p)
      PRE (p ~> MList L)
      POST (fun b => \[b = isTrue (L = nil)]).
Proof using.
  xcf. xchange* MList_eq; =>v.
  xapp. destruct L as [|x' L']; xmatch; xval*.
  { xchange* <- MList_eq. xsimpl*. }
  { assert (v <> Nil) by auto. xchange* MList_contents_iff. }
  { unfold MList_contents; xpull. }
  { xchange* <- MList_eq. xsimpl*. intros false. inversion false. }
Qed.

Lemma Triple_cmp : forall L1 L2 p1 p2 eq,
  (forall x1 x2,
    SPEC (eq x1 x2)
      PRE \[]
      POST (fun b => \[b = isTrue (x1 = x2)])) ->
  SPEC (cmp eq p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun b => \[b = isTrue (L1 = L2)] \*
                  p1 ~> MList L1 \* p2 ~> MList L2).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH : list_sub L1.
  xcf. xchange* MList_eq ;=>. xchange* MList_eq ;=>.
  xapp. xapp. xmatch.
  { xchange* MList_contents_iff ;=>.
    xchange* MList_contents_iff ;=>.
    xval*. xchange* <- MList_eq. xchange* <- MList_eq.
    xsimpl*.
    destruct H0. destruct H1.
    destruct H0; auto. }
  { xchange* MList_contents_iff ;=>.
    xchange* MList_contents_iff ;=>.
    xval*. xchange* <- MList_eq. xchange* <- MList_eq.
    xsimpl*. intros false. destruct H1.
    cuts G : (L2 = nil).
    { subst. destruct H2; auto. }
    { destruct H0; auto. } }
  { xchange* MList_contents_iff ;=>.
    xchange* MList_contents_iff ;=>.
    cuts G : (L1 = nil).
    { xval*. xchange* <- MList_eq. xchange* <- MList_eq.
      xsimpl*. intros false. destruct H0. subst.
      destruct H2; auto. }
    { destruct H1; auto. } }
  { rename H into triple_eq.
    xapp (triple_eq x1 x2).
    destruct L1 as [|x' L1']; xif ;=>.
    { unfold MList_contents. xpull*. }
    { unfold MList_contents. xpull*. }
    { unfold MList_contents; xpull* ;=>.
      destruct L2 as [|y' L2']; xpull* ;=>.
      inversion H0; subst. inversion H1; subst.
      xapp; try constructor.
      xchange* <- MList_cons. xchange* <- MList_cons.
      xsimpl*. split; intros; subst; auto.
      inversion H; auto. }
    { unfold MList_contents. xpull* ;=>.
      destruct L2 as [|y' L2']; xpull* ;=>.
      inversion H0; subst. inversion H1; subst.
      xval*. xchange* <- MList_cons. xchange* <- MList_cons.
      xsimpl*. intros false. inversion false. contradiction. } }
Qed.

Lemma Triple_iter : forall (I: list A -> hprop) L (f: val) p,
    (forall x L1 L2, L = L1++x::L2 ->
                SPEC (f x)
                  PRE (I L1)
                  POSTUNIT (I (L1&x))) ->
    SPEC (iter f p)
      PRE (p ~> MList L \* I nil)
      POSTUNIT (p ~> MList L \* I L).
Proof using.
  introv Hf.
  cuts G : (forall L1 L2, L = L1 ++ L2 ->
              SPEC (iter f p)
                PRE (p ~> MList L2 \* I L1)
                POSTUNIT (p ~> MList L2 \* I L)).
  { xapp G; rew_list*. xsimpl*. }
  intros. gen L1 H p. induction_wf IH : list_sub L2.
  xcf. xchange* MList_eq ;=> vL2. xapp. xchange* MList_contents_iff ;=> ; xmatch.
  { destruct H0. assert (L2 = nil) by auto. subst.
    xval. rew_list. xchange* <- MList_eq. xsimpl*. }
  { unfold MList_contents. destruct L2 as [| x2' L2']; xpull*; =>.
    inversion H1. subst x. xapp (Hf x2'); eauto.
    xapp; auto. { rew_list*. } { xchange* <- MList_cons. xsimpl*. } }
Qed.

Lemma Triple_test_iter : forall L p,
    SPEC (test_iter p)
      PRE (p ~> MList L)
      POST (fun n => p ~> MList L \* \[n = length L]).
Proof using.
  xcf. xapp ;=> c. xlet_fun.
  xapp (Triple_iter (fun (K: list A) => c ~~> length K)).
  { intros. xapp. xapp. xapp. xsimpl*. rew_list*. math. }
  { xapp. xsimpl*. }
Qed.

Inductive prefix {A} : list A -> list A -> Prop :=
| PrefixZero:
    forall xs,
    prefix xs xs
| PrefixSucc:
    forall (xs: list A) (x: A) (zs: list A),
    prefix (xs ++ (x::nil)) zs ->
    prefix xs zs.

Definition permitted (V: list A) L : Prop :=
  exists L', V ++ L' = L.

Definition complete (V: list A) L : Prop :=
  V = L.

Lemma aux : forall L L',
    L = L ++ L' -> L' = nil.
Proof using.
  induction L; auto.
  intros. rew_list in H. inversion H.
  destruct (IHL L'); auto.
Qed.

Lemma Triple_iter_alt : forall (I: list A -> hprop) L (f: val) p,
    (forall x V,
        SPEC (f x)
          PRE (\[permitted (V&x) L] \* \[complete V L -> False] \* I V )
          POSTUNIT (I (V&x))) ->
    SPEC (iter f p)
      PRE (p ~> MList L \* I nil)
      POSTUNIT (p ~> MList L \* I L).
Proof using.
  introv Hf.
  cuts G : (forall L1 L2, L = L1 ++ L2 ->
              SPEC (iter f p)
                PRE (p ~> MList L2 \* I L1)
                POSTUNIT (p ~> MList L2 \* I L)).
  { xapp G. rew_list*. xsimpl*. }
  intros. gen L1 H p. induction_wf IH : list_sub L2.
  xcf. xchange* MList_eq ;=> v.
  xapp. xmatch.
  { xval. xchange* MList_contents_iff ;=>. destruct H0.
    assert (L2 = nil) by auto. subst.
    rew_list*. xchange* <- MList_eq. xsimpl*. }
  { unfold MList_contents. destruct L2 as [| x' L2']; xpull* ;=>.
    inversion H0; subst. xapp (Hf x').
    { assert (L1 ++ x' :: L2' = L1 & x' ++ L2'). { apply app_cons_r. }
      rewrite H. exists L2'. auto. }
    { intros. inversion H. apply aux in H1. inversion H1. }
    { xapp; auto; rew_list*.
      xchange* <- MList_cons. xsimpl*. } }
Qed.

(* Section Fold. *)

  (* Context {Acc: Type}. *)

  (* Lemma Triple_mfold_left : forall B (I: A -> list B -> hprop) (L: list B) acc0 (f: val) p, *)
  (*     (forall acc (x: B) (L1 L2: list B), L = L1++x::L2 -> *)
  (*                     SPEC (f acc x) *)
  (*                       PRE (I acc L1) *)
  (*                       POST (fun nacc => I nacc (L1&x))) -> *)
  (*     SPEC (fold_mleft acc0 f p) *)
  (*       PRE (p ~> MList L \* I acc0 nil) *)
  (*       POST (fun r => p ~> MList L \* I r L). *)
  (* Proof using. *)
  (*   introv Hf. *)
  (*   cuts G : (forall a (L1 L2: list B), L = L1 ++ L2 -> *)
  (*               SPEC (fold_mleft a f p) *)
  (*                 PRE (p ~> MList L2 \* I a L1) *)
  (*                 POST (fun r => p ~> MList L2 \* I r L)). *)
  (*   { xapp; rew_list*. xsimpl*. } *)
  (*   intros. gen L1 H p a. induction_wf IH : list_sub L2. *)
  (*   intros. xcf. *)

End Ops.

Global Opaque MList.

Module Import SpecMList.
Hint Extern 1 (RegisterSpec create) => Provide Triple_create.
Hint Extern 1 (RegisterSpec is_empty) => Provide Triple_is_empty.
Hint Extern 1 (RegisterSpec push) => Provide Triple_push.
Hint Extern 1 (RegisterSpec pop) => Provide Triple_pop.
Hint Extern 1 (RegisterSpec rev_main) => Provide Triple_rev.
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
