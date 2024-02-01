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

Lemma Queue_nil : forall (q: loc) A `{EA: Enc A},
    q ~> Queue (@nil A)
  = \exists (cf cl: cell_ A),
        (q ~~~> `{ length' := 0; first' := cf; last' := cl }) \*
        \[cl = Nil] \* \[cf = Nil].
Proof using.
  intros. xunfold Queue. xpull* ;=>; case_if; xsimpl*.
Qed.

Lemma Cell_eq : forall A `{EA: Enc A} (x: A) (c n: cell_ A),
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

Lemma Cell_Seg_trans : forall A `{EA: Enc A} (L1 L2 L3: list A) (c1 c2 c3: cell_ A),
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

  Lemma Triple_clear : forall q L,
    SPEC (clear q)
      PRE (q ~> Queue L)
      POSTUNIT (q ~> Queue (@nil A)).
  Proof using.
    xcf. xunfold Queue. xpull* ;=> cf cl.
    case_if*; xpull*.
    { intros -> ->. case_if*. do 3 xapp.
      xsimpl*. }
    { intros x x0 ->. case_if*. xchange* Cell_Seg_cons ;=>.
      xchange* Cell_Seg_nil. intros ->. do 3 xapp.
      xsimpl*.
      { applys haffine_Cell_Seg. }
      { xunfold * Cell. xaffine. } }
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

End Ops.
