Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Queue_OCaml_ml.
From TLC Require Import LibListZ.

Definition Cell A `{EA: Enc A} (v: A) (n c: cell_ A) : hprop :=
  \exists cf,
      \[c = Cons cf] \* (cf ~~~> `{ content' := v; next' := n }).

Fixpoint Cell_Seg A `{EA: Enc A} (L: list A) (to from: cell_ A) : hprop :=
  match L with
  | nil => \[to = from]
  | x :: L' => \exists n, (from ~> Cell x n) \* (n ~> Cell_Seg L' to)
  end.

Definition Queue A `{EA: Enc A} (L: list A) (q: loc) : hprop :=
  \exists (cf cl: cell_ A),
      (q ~~~> `{ length' := length L; first' := cf; last' := cl }) \*
        If L = nil then \[cf = Nil] \* \[cl = Nil]
        else
          \exists x L', \[L = L' & x] \* (cf ~> Cell_Seg L' cl) \*
                     (cl ~> Cell_Seg (x::nil) Nil).

(* Definition Queue A `{EA: Enc A} (L: list A) (q: loc) : hprop := *)
(*   \exists (cf cl: cell_ A), *)
(*       (q ~~~> `{ length' := length L; first' := cf; last' := cl }) \* *)
(*         If cl = Nil then \[cf = Nil] \* \[L = nil] *)
(*         else *)
(*           \exists x L', \[L = L' & x] \* (cf ~> Cell_Seg L' cl) \* *)
(*                      (cl ~> Cell x Nil). *)

Lemma Cell_Seg_nil : forall A (EA: Enc A) (to from: cell_ A),
    from ~> Cell_Seg (@nil A) to = \[to = from].
Proof using. auto. Qed.

Lemma Cell_Seg_Nil : forall A (EA: Enc A),
    Nil ~> Cell_Seg (@nil A) Nil = \[].
Proof using.
  intros.
  (* FIXME? How come I cannot use here [xchange Cell_Seg_nil] ? *)
  xunfold Cell_Seg. xsimpl*.
Qed.

Lemma Cell_Seg_cons : forall A (EA: Enc A) (x: A) (L: list A) (to from: cell_ A),
    from ~> Cell_Seg (x :: L) to
  = \exists n, (from ~> Cell x n) \* (n ~> Cell_Seg L to).
Proof using. auto. Qed.

Lemma Cell_Seg_Nil2 : forall A (EA: Enc A) (c: cell_ A) (L: list A),
    Nil ~> Cell_Seg L c ==> \[L = nil] \* \[c = Nil].
Proof using.
  intros. destruct L as [|x L'].
  { xchange* Cell_Seg_nil ;=> ->. xsimpl*. }
  { xchange* Cell_Seg_cons ;=>. xunfold Cell ;=>. xpull*. }
Qed.

Lemma Queue_if : forall A (EA: Enc A) (L: list A) (q: loc),
    q ~> Queue L =
      \exists cf cl,
          (q ~~~> `{ length' := length L; first' := cf; last' := cl }) \*
            (If cl = Nil then
               \[L = nil] \* \[cf = Nil]
             else \exists x L', \[L = L' & x] \* (cf ~> Cell_Seg L' cl) \*
                             (cl ~> Cell_Seg (x::nil) Nil)).
(* TODO: really simplify this proof *)
Proof using.
  intros. xunfold* Queue. xpull* ;=>.
  { case_if*.
    { xsimpl* ;=> -> ->. case_if*. xsimpl*. }
    { xpull* ;=>. xsimpl*. case_if*.
      { subst. xchange* Cell_Seg_cons ;=>.
        xunfold Cell. xpull*. }
      { xsimpl*. } } }
  { case_if*.
    { xpull* ;=> -> ->. xsimpl*.
      case_if*. xsimpl*. }
    { xpull* ;=>. xsimpl*.
      case_if*.
      { subst. apply last_eq_nil_inv in C0. contradiction. }
      { xsimpl*. } } }
Qed.

Lemma Queue_if_first : forall A (EA: Enc A) (L: list A) (q: loc),
    q ~> Queue L =
      \exists cf cl,
          (q ~~~> `{ length' := length L; first' := cf; last' := cl }) \*
            (If cf = Nil then
               \[L = nil] \* \[cl = Nil]
             else \exists x L', \[L = L' & x] \* (cf ~> Cell_Seg L' cl) \*
                             (cl ~> Cell_Seg (x::nil) Nil)).
(* TODO: I really need to clean up and simplify this and the previous proof. *)
Proof using.
  intros. xunfold* Queue. xpull* ;=>.
  { case_if*.
    { xsimpl* ;=> -> ->. case_if*; xsimpl*. }
    { xpull* ;=>. xsimpl*. case_if*.
      { subst. xchange* Cell_Seg_Nil2. intros. subst.
        xchange* Cell_Seg_cons ;=>. xunfold Cell. xpull*. }
      { xsimpl*. } } }
  { case_if*.
    { xpull* ;=> -> ->. xsimpl*.
      case_if*. xsimpl*. }
    { xpull* ;=>. xsimpl*.
      case_if*.
      { subst. apply last_eq_nil_inv in C0. contradiction. }
      { xsimpl*. } } }
Qed.

Lemma Queue_nil : forall (q: loc) A `{EA: Enc A},
    q ~> Queue (@nil A)
  = \exists (cf cl: cell_ A),
        (q ~~~> `{ length' := 0; first' := cf; last' := cl }) \*
        \[cl = Nil] \* \[cf = Nil].
Proof using.
  intros. xunfold Queue. xpull* ;=>; case_if; xsimpl*.
Qed.

Lemma Queue_last : forall (q: loc) A `{EA: Enc A} (x: A) (L: list A),
    q ~> Queue (L & x)
==> \exists cf cl,
      q ~~~> `{ length' := length (L & x); first' := cf; last' := cl } \*
        cf ~> Cell_Seg L cl \* cl ~> Cell_Seg (x::nil) Nil.
Proof using.
  intros. xunfold Queue. xsimpl* ;=>.
  case_if*; xpull*.
  { apply last_eq_nil_inv in C. auto_false. }
  { introv HLx. apply last_eq_last_inv in HLx.
    destruct HLx. subst. xsimpl*. }
Qed.

Lemma Queue_last_close :
  forall (q: loc) A `{EA: Enc A} (x: A) (L: list A) (cf cl: cell_ A),
    q ~~~> `{ length' := length (L & x); first' := cf; last' := cl } \*
      cf ~> Cell_Seg L cl \* cl ~> Cell_Seg (x::nil) Nil
==> q ~> Queue (L & x).
Proof using.
  intros. xunfold Queue. xsimpl*. case_if*.
  { apply last_eq_nil_inv in C. auto_false. }
  { xsimpl*. }
Qed.

(* Lemma Queue_nil_alt: forall (q: loc) A `{EA: Enc A}, *)
(*     q ~~~> `{ length' := 0; first' := Nil; last' := Nil } *)
(*       ==> q ~> Queue (@nil A). *)

Lemma Cell_eq : forall A `{EA: Enc A} (c: cell_ A) (x: A) (n: cell_ A),
    c ~> Cell x n
  = \exists cf, \[c = Cons cf] \* cf ~~~> `{ content' := x; next' := n }.
Proof using. auto. Qed.

Lemma Cell_of_Cell_Seg : forall A `{EA: Enc A} (x: A) (c: cell_ A),
    c ~> Cell_Seg (x :: nil) Nil ==> c ~> Cell x Nil.
Proof using.
  intros. xchange* Cell_Seg_cons ;=> x0. xchanges* Cell_Seg_nil ;=> ->.
Qed.

Lemma Cell_Seg_of_Cell : forall A `{EA: Enc A} (x: A) (c: cell_ A),
    c ~> Cell x Nil ==> c ~> Cell_Seg (x :: nil) Nil.
Proof using.
  intros. xunfold Cell_Seg. xsimpl*.
  xchange* <- Cell_Seg_Nil.
  Unshelve. auto. (* FIXME? *)
Qed.

Lemma Cell_Seg_of_Cell_singleton : forall A `{EA: Enc A} (x: A) (c1 c2: cell_ A),
    c1 ~> Cell x c2 ==> c1 ~> Cell_Seg (x :: nil) c2.
Proof using.
  intros. xunfold Cell_Seg. xsimpl*.
  xchanges* <- Cell_Seg_nil.
  Unshelve. auto.
Qed.

Lemma Queue_singleton_close :
  forall (q: loc) A `{EA: Enc A} (x: A) (c: cell_ A),
    q ~~~> `{ length' := 1; first' := c; last' := c } \* c ~> Cell x Nil
==> q ~> Queue (x::nil).
Proof using.
  intros. xunfold Queue. xsimpl*. case_if*. xsimpl*.
  { assert (x :: nil = nil & x) by auto. eauto. }
  { xchange* Cell_Seg_of_Cell. xunfold Cell_Seg at 2. xsimpl*. }
Qed.

Lemma Cell_Seg_trans : forall A `{EA: Enc A} (c1 c2 c3: cell_ A) (L1 L2 L3: list A),
    c1 ~> Cell_Seg L1 c2 \* c2 ~> Cell_Seg L2 c3 \* c3 ~> Cell_Seg L3 Nil
==> c1 ~> Cell_Seg (L1 ++ L2) c3 \* c3 ~> Cell_Seg L3 Nil.
Proof using.
  intros. gen L2 L3 c2 c3 c1. induction_wf IH : list_sub L1.
  intros. destruct L1 as [| x1 L1']; rew_list*.
  { xchanges* Cell_Seg_nil ;=> ->. xsimpl*. }
  { xchange* Cell_Seg_cons ;=> next.
    xchange* (IH L1'). xchange* <- Cell_Seg_cons. }
Qed.

Lemma Cell_Seg_last : forall A `{EA: Enc A} (from: cell_ A) (L: list A) (x: A) (to: cell_ A),
    from ~> Cell_Seg (L & x) to
==> \exists n, from ~> Cell_Seg L n \* n ~> Cell_Seg (x :: nil) to.
Proof using.
  intros. gen x to from. induction_wf IH : list_sub L.
  intros x to from. destruct L as [| x' L'].
  { rew_list*. xunfold Cell_Seg. xsimpl*. }
  { rew_list*. xchange* Cell_Seg_cons ;=> next.
    xchange IH. { constructor. }
    intros. xchange* <- Cell_Seg_cons. xsimpl*. }
Qed.

Lemma haffine_Cell_Seg : forall A `{EA: Enc A} (L: list A) (cl cf: cell_ A),
    haffine (cf ~> Cell_Seg L cl).
Proof using.
  intros. gen cl cf. induction L; intros.
  { xunfold Cell_Seg. xaffine. }
  { xunfold Cell_Seg. xaffine.
    xunfold Cell. xaffine. }
Qed.

Section Ops.

  Context A {EA: Enc A}.
  Implicit Types L: list A.
  Implicit Types q: loc.

  Lemma Triple_create :
    SPEC (create tt)
      PRE \[]
      POST (fun (q: loc) => q ~> Queue (@nil A)).
  Proof using.
    xcf. xapp ;=> q. xchanges* <- Queue_nil.
  Qed.

  (* Lemma Triple_clear : forall q L, *)
  (*   SPEC (clear q) *)
  (*     PRE (q ~> Queue L) *)
  (*     POSTUNIT (q ~> Queue (@nil A)). *)
  (* Proof using. *)
  (*   xcf. xunfold Queue. xpull* ;=> cf cl. *)
  (*   case_if*; xpull*. *)
  (*   { intros -> ->. case_if*. do 3 xapp. *)
  (*     xsimpl*. } *)
  (*   { intros x x0 ->. case_if*. xchange* Cell_Seg_cons ;=>. *)
  (*     xchange* Cell_Seg_nil. intros ->. do 3 xapp. *)
  (*     xsimpl*. *)
  (*     { applys haffine_Cell_Seg. } *)
  (*     { xunfold * Cell. xaffine. } } *)
  (* Qed. *)

  Lemma Triple_clear_alt : forall (q: loc) (L: list A) (cf cl: cell_ A),
      SPEC (clear q)
        PRE (q ~~~> `{ length' := length L; first' := cf; last' := cl })
        POSTUNIT (q ~> Queue (@nil A)).
  Proof using.
    xcf. xapp. xapp. xapp. xchanges* <- Queue_nil.
  Qed.

  Lemma Triple_add : forall L q x,
      SPEC (add x q)
        PRE (q ~> Queue L)
        POSTUNIT (q ~> Queue (L & x)).
  Proof using.
    xcf. xapp ;=> cell. xlet. xchange Queue_if ;=> cf cl.
    case_if*.
    { xpull* ;=> -> ->. xapp. xmatch.
      do 3 xapp. rew_list*. xunfold Queue.
      case_if*. xsimpl*.
      { rewrite last_nil. eauto. }
      { inversion Pcell0; subst.
        xchange* <- Cell_eq. xchange* Cell_Seg_of_Cell.
        xunfold Cell_Seg. xsimpl*. } }
    { xpull*; introv Hv. xchange* Cell_Seg_cons ;=>.
      xchange* Cell_Seg_nil ;=>. xapp. xmatch.
      { xapp. xapp. xchange* Cell_eq ;=>. inversion H0; subst.
        xapp. xapp. xchange* <- Cell_eq. xchange* <- Cell_eq.
        xchange* Cell_Seg_of_Cell.
        xchange* Cell_Seg_of_Cell_singleton.
        xchange* Cell_Seg_trans. xunfold Queue.
        case_if*. { apply last_eq_nil_inv in C1. auto_false. }
        xsimpl*. rew_list*. math. } }
  Qed.

  Lemma Triple_push : forall L q x,
      SPEC (push x q)
        PRE (q ~> Queue L)
        POSTUNIT (q ~> Queue (L & x)).
  Proof using. xcf. xapp* Triple_add. xsimpl*. Qed.

  Lemma Triple_take : forall L q,
      L <> nil ->
      SPEC (Queue_OCaml_ml.take q)
        PRE (q ~> Queue L)
        POST (fun (x: A) => \exists L', q ~> Queue L' \* \[L = x :: L']).
  Proof using.
    xcf. xchange* Queue_if_first ;=> cf cl. case_if*; xpull ;=> ? ? ->.
    xchange* Cell_of_Cell_Seg. xapp. xmatch.
    destruct x0 as [| x' L'].
    { (* queue contains a single element *)
      xchange* Cell_Seg_nil ;=> ->. xchange* Cell_eq ;=> ?.
      introv Hcx0. inversion Hcx0; subst. xapp. xapp.
      xif; introv ?; tryfalse *. xapp Triple_clear_alt. xapp.
      xsimpl*. }
    { (* queue contains at least two elements *)
      xchange* Cell_Seg_cons ;=> x1n. xchange* Cell_eq (Cons c) ;=> ?.
      introv Hcx0. inversion Hcx0; subst. xapp. xapp.
      (* TODO: it would be nice to get rid of this sub-case; maybe an
         auxiliary lemma to show that [q.first.next] is, under these
         hypotheses, provably not [Nil]. *)
      destruct L' as [| x'' L''].
      { (* q.first.next == q.last *)
        xchange* Cell_Seg_nil ;=> ->. xchange* Cell_eq ;=> ? ->.
        xif ;=> ; tryfalse*. repeat xapp.
        rew_list*. xsimpl*. xchange* <- Cell_eq.
        xchange* Queue_singleton_close. xsimpl*. }
      { (* q.first.next != q.last *)
        (* the queue provably contains more than two elements *)
        xchange* Cell_Seg_cons ;=>. xchange* Cell_eq x1n ;=> ? ->.
        xif; intros; tryfalse*. repeat xapp. rew_list*.
        xsimpl*. xchange* <- Cell_eq. xchange* <- Cell_Seg_cons x''.
        xchange* Cell_Seg_of_Cell. xchange* Queue_last_close q.
        { rew_list*. math. }
        { xsimpl*. } } }
  Qed.

  Lemma Triple_pop : forall L q,
      L <> nil ->
      SPEC (pop q)
        PRE (q ~> Queue L)
        POST (fun (x: A) => \exists L', q ~> Queue L' \* \[L = x :: L']).
  Proof using. xcf. xapp Triple_take; eauto. xsimpl*. Qed.

  Lemma Triple_transfer : forall (L1 L2: list A) (q1 q2: loc),
      SPEC (transfer q1 q2)
        PRE (q1 ~> Queue L1 \* q2 ~> Queue L2)
        POSTUNIT (q1 ~> Queue (@nil A) \* q2 ~> Queue (L2 ++ L1)).
  Proof using.
    xcf. xunfold Queue at 1. xpull*; => cf cl. case_if*; xpull*.
    { intros -> ->. xapp. xif.
      { introv Hlength. rewrite C in Hlength. math. }
      { introv Hlength. xval. subst. rew_list*.
        xchanges* <- Queue_nil. } }
    { intros x x0 ->. xchange* Cell_Seg_cons ;=> n.
      xchange* Cell_Seg_nil ;=>. xapp. xif.
      { intros Hgt. xchange Queue_if. intros cf_q2 cl_q2.
        case_if*.
        { subst. xpull* ;=> -> ->. xapp. xmatch.
          xapp. xapp. xapp. xapp. xapp. xapp.
          xchange* Cell_Seg_of_Cell.
          xapp Triple_clear_alt. xchange* Queue_last_close.
          rew_list*. xsimpl*. }
        { xpull* ;=> x1 x2 ->. xchange* Cell_Seg_cons ;=> cx1.
          xchange* Cell_Seg_nil ;=>.
          xapp. xchange* (Cell_eq cl_q2) ;=> cx3 ->.
          xmatch. repeat xapp. subst. xchange* Cell_Seg_of_Cell.
          xapp Triple_clear_alt. xchange* <- Cell_eq .
          xchange Cell_Seg_of_Cell_singleton.
          xchange (Cell_Seg_trans (Cons cx3) cf cl).
          xchange Cell_Seg_trans. rew_list*.
          asserts* -> : (1 + length x2 + (1 + length x0) = length ((x2 ++ x1 :: x0) & x)).
          { rew_list*. math. }
          xchange Queue_last_close. rew_list*. xsimpl*. } }
      { intros Hfalse. destruct Hfalse. rew_list*. math. } }
  Qed.

  Lemma Triple_copy_aux_simpl : forall (cl: cell_ A) (n: int) (cf: cell_ A) (L2 L3: list A)
                            (q_res: loc) (prev cell: cell_ A),
      SPEC (copy_aux q_res prev cell)
        PRE (q_res ~~~> `{ length' := n; first' := cf; last' := cl }
               \* prev ~> Cell_Seg L2 Nil
               \* cell ~> Cell_Seg L3 Nil)
        POST (fun (q_res: loc) =>
                cell ~> Cell_Seg L3 Nil).
  Proof using.
    intros. gen n cf L2 q_res prev cell.
    induction_wf IH : list_sub L3.
    xcf. destruct L3 as [| x3 L3'].
    { xchange* Cell_Seg_nil ;=> ->.
      xmatch. xunfold Cell_Seg at 2. xapp.
      xval. xsimpl*. applys haffine_Cell_Seg. }
    { xchange* Cell_Seg_cons ;=> x. xchange* Cell_eq ;=> x0 ->.
      xmatch. xunfold Cell_Seg at 3. xapp. xapp ;=> r. xlet.
      destruct L2 as [| x2 L2'].
      { xchange* Cell_Seg_nil ;=>. xmatch. xapp.
        xapp. subst res. xchange* <- Cell_eq.
        xchange* Cell_Seg_of_Cell. xapp; eauto.
        intros. xchange* <- Cell_eq. xsimpl*. }
      { xchange* Cell_Seg_cons ;=> x1. xchange* Cell_eq ;=> x4 Hprev.
        xmatch. inversion TEMP; subst. xapp. xapp.
        xchange* <- Cell_eq. xchange* Cell_Seg_of_Cell.
        xapp; eauto.
        intros. xsimpl*. xchange* <- Cell_eq. xchange* <- Cell_eq.
        xsimpl*. { applys haffine_Cell_Seg. }
        { xunfold Cell. xaffine. } } }
  Qed.

  Lemma Triple_copy_aux : forall (n: int) (cf cl: cell_ A) (L2 L3 L4: list A)
                            (q_res: loc) (prev cell: cell_ A),
      SPEC (copy_aux q_res prev cell)
        PRE (q_res ~~~> `{ length' := n; first' := cf; last' := (@Nil A) }
               \* prev ~> Cell_Seg L2 Nil
               \* cell ~> Cell_Seg L3 cl
               \* cl ~> Cell_Seg L4 Nil
               \* \[L4 = nil \/ exists x, L4 = (x::nil)])
        POST (fun (q_res: loc) =>
                cell ~> Cell_Seg L3 cl \* cl ~> Cell_Seg L4 Nil).
  Proof using.
    intros. gen n cf cl L2 q_res prev cell.
    assert (exists L, L = L3 ++ L4) by eauto.
    destruct H as [L]. gen L3 L4.
    induction_wf IH : list_sub L.
    xcf. destruct L3 as [| xc L3'] eqn:HL3.
    { xchange Cell_Seg_nil ;=>. xmatch.
      { xunfold Cell_Seg at 3. xapp. xval.
        xsimpl*; applys haffine_Cell_Seg. }
      { destruct L4 as [| x4 L4'].
        { xchange* Cell_Seg_nil. }
        { destruct H0. { inversion H0. }
          destruct H0. inversion H0; subst.
          xchange* Cell_Seg_cons ;=>. xchange* Cell_Seg_nil ;=>.
          xchange* Cell_eq ;=> x1 Hv. inversion Hv; subst.
          xunfold Cell_Seg at 2. xunfold Cell_Seg at 2.
          xapp. xapp ;=> tmp. xlet.
          destruct L2 as [| x2 L2'].
          { xchange* Cell_Seg_nil ;=>. xmatch.
            xapp. xapp. xchange* <- Cell_eq. rewrite <- Pres.
            xchange* Cell_Seg_of_Cell_singleton.
            xchange* <- Cell_Seg_Nil. xchange* <- Cell_Seg_Nil.
            xapp (IH nil); auto.
            { rew_list*. }
            { intros. xsimpl*. xchange* Cell_Seg_Nil.
              xchange* <- Cell_eq. xsimpl*. } }
          { xchange* Cell_Seg_cons ;=> prev_next.
            xchange* Cell_eq ;=>. xmatch.
            { inversion TEMP; subst. xapp. xapp.
              xchange* <- Cell_Seg_Nil. xchange* <- Cell_Seg_Nil.
              xchange* <- Cell_eq. xchange* Cell_Seg_of_Cell.
              xapp (IH nil); try rew_list*.
              intros. do 2 xchange* <- Cell_eq. xsimpl*.
              { applys haffine_Cell_Seg. }
              { applys haffine_Cell_Seg. }
              { xunfold Cell. xaffine. } } } } } }
    { (* L3 = xc :: L3' *)
      xpull*. introv HL4. xchange* Cell_Seg_cons ;=> x0.
      xmatch.
      { xunfold Cell_Seg at 4. xapp. xval. xsimpl*;
          applys haffine_Cell_Seg. }
      { xchange* Cell_eq ;=>. inversion H0; subst.
        xunfold Cell_Seg at 4. xapp. xapp ;=> tmp. xlet.
        destruct L2 as [| x2 L2'].
        { xchange* Cell_Seg_nil ;=>. xmatch. xapp.
          xapp. xchange* <- Cell_eq. rewrite <- Pres.
          xchange* Cell_Seg_of_Cell. xapp (IH (L3' ++ L4)); rew_list*.
          intros. xsimpl*. xchange* <- Cell_eq. xsimpl*. }
        { xchange* Cell_Seg_cons ;=>. xchange* Cell_eq ;=>.
          xmatch. inversion TEMP; subst.
          xapp. xapp. xchange* <- Cell_eq. xchange* Cell_Seg_of_Cell.
          xapp (IH (L3' ++ L4)); try rew_list*.
          intros. xsimpl*. xchange* <- Cell_eq. xchange* <- Cell_eq.
          xsimpl*. { applys haffine_Cell_Seg. }
          { xunfold Cell. xaffine. } } } }
  Qed.

  Lemma Triple_copy : forall (L: list A) (q: loc),
      SPEC (copy q)
        PRE (q ~> Queue L)
        POST (fun (q_res: loc) => q ~> Queue L).
  Proof using.
    xcf. xchange* Queue_if ;=> cf cl. case_if*.
    { xpull* ;=> -> ->. xapp. xapp. xapp ;=> tmp.
      do 3 xchange <- Cell_Seg_Nil. (* TODO pay attention here to shelved goal *)
      xapp* Triple_copy_aux ;=>. xchange* <- Queue_nil.
      xsimpl*; applys haffine_Cell_Seg. }
    { xpull* ;=> x x0 ->. xchange* Cell_Seg_cons ;=>.
      xchange* Cell_Seg_nil ;=>. xapp. xapp.
      xapp ;=> tmp. xchange* <- Cell_Seg_Nil.
      xchange* Cell_Seg_of_Cell_singleton.
      subst x1. xchange* Cell_Seg_trans.
      xapp* Triple_copy_aux_simpl. intros.
      xchange* Cell_Seg_last ;=>. gen cl.
      xchange* Queue_last_close. xsimpl*. }
  Qed.

End Ops.
