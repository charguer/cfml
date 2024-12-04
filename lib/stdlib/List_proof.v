Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import WPDisplay WPRecord.
Require Import Pervasives_ml Pervasives_proof.
From TLC Require Export LibListZ.  (* TODO: needed? *)
Require Import List_ml.
Generalizable Variables A.
(*
Open Scope cf_scope.
*)

Ltac auto_tilde ::= unfold measure; rew_list in *; try math; auto.
  (* Restored to default at the end of the file *)

(* TODO: find a nicer way to write [@TLC.LibList] *)

(************************************************************)
(** Functions treated directly by CFML *)

Lemma length_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (length l)
    PRE \[]
    POST \[= (@TLC.LibListZ.length _) l].
Proof using.
  xcf. xlet.
  asserts ? : (forall (xs:list A) j, SPEC (aux j xs) PRE \[] POST \[=j + @TLC.LibListZ.length _ xs]).
  { induction xs; intros.
    { xgo. rew_list. math. }
    { xapp Spec_aux. xgo.
      rew_list. math. } }
  xgo. math.
Qed.

Hint Extern 1 (RegisterSpec length) => Provide length_spec.

(* Remark: details of the script for length:

  xcf. xfun_no_simpl (fun f => forall n (l:list A),
    app f [n l] \[] \[= n + LibListZ.length l]).
  intros n. induction_wf IH: (downto 0) n.
  intros. apply (proj2 Saux). clear Saux.
  { xmatch.
    { xrets~. }
    { xapp~. xsimpl~. } }
  { xapp~. }
*)

Lemma rev_append_spec : forall A `{EA:Enc A} (l1 l2:list A),
  SPEC (rev_append l1 l2)
    PRE \[]
    POST \[= LibList.rev l1 ++ l2].
Proof using.
  intros. gen l2. induction_wf IH: (@list_sub A) l1. xcf_go*.
  rew_list*.
Qed.

Hint Extern 1 (RegisterSpec rev_append) => Provide rev_append_spec.

Lemma rev_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (rev l)
    PRE \[]
    POST \[= (@TLC.LibList.rev _) l].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec rev) => Provide rev_spec.

Lemma append_spec : forall A `{EA:Enc A} (l1 l2:list A),
  SPEC (append l1 l2)
    PRE \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using.
  xcf. xlet.
  asserts ? : (forall l, SPEC (aux l) PRE \[] POST \[=(@TLC.LibList.app _) l l2]).
  { induction l; xapp Spec_aux; xgo*. }
  xgo*.
Qed.

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Lemma infix_at_spec : forall A `{EA:Enc A}(l1 l2:list A),
  SPEC (infix_at__ l1 l2)
    PRE \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec infix_at__) => Provide infix_at_spec.

Lemma concat_spec : forall A `{EA:Enc A} (l:list (list A)),
  SPEC (concat l)
    PRE \[]
    POST \[= (@TLC.LibList.concat _) l].
Proof using.
  intros. induction_wf IH: (@list_sub (list A)) l. xcf_go*.
Qed.

Hint Extern 1 (RegisterSpec concat) => Provide concat_spec.


(************************************************************)
(** Iterators *)

Lemma iter_spec : forall A `{EA:Enc A} (l:list A) (f:func),
  forall (I:list A->hprop),
  (forall x t r, (l = t++x::r) ->
     SPEC (f x) PRE (I t) POSTUNIT (I (t&x))) ->
  SPEC (iter f l)
    PRE (I nil)
    POSTUNIT (I l).
Proof using.
  =>> M. cuts G: (forall r t, l = t++r ->
    SPEC (iter f r) PRE (I t) POSTUNIT (I l)). { xapp~. xsimpl. }
  => r. induction_wf IH: (@LibList.length A) r. =>> E.
  xcf. xmatch; rew_list in E; inverts E; xgo~.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.

(** Alternative spec for [iter], with an invariant that
    depends on the remaining items, rather than depending
    on the processed items. *)

Lemma iter_spec_rest : forall A `{EA:Enc A} (l:list A) (f:func),
  forall (I:list A->hprop),
  (forall x t, SPEC (f x) PRE (I (x::t)) POSTUNIT (I t)) ->
  SPEC (iter f l) PRE (I l) POSTUNIT (I nil).
Proof using.
  introv M. xapp~ (>> iter_spec (fun k => \exists r, \[l = k ++ r] \* I r)).
  { introv E. xtriple. xpull. intros r' E'.
    subst l. lets: app_cancel_l E'. subst r'. xapp. xsimpl~. }
  { xpull; introv E. rewrites (>> self_eq_app_l_inv E). xsimpl~. }
Qed. (* TODO: beautify this proof *)


(************************************************************)
(** ListOf *)

Fixpoint ListOf A B (R:A -> B -> hprop) (LS:list A) (xs:list B) :=
  match LS,xs with
  | nil,nil => \[]
  | L::LS,x::xs => x ~> R L \* xs ~> ListOf R LS
  | _,_ => \[False]
  end.

Lemma ListOf_eq A B : forall (R:A -> B -> hprop) (LS:list A) (xs:list B),
    xs ~> ListOf R LS =
    match LS,xs with
    | nil,nil => \[]
    | L::LS,x::xs => x ~> R L \* xs ~> ListOf R LS
    | _,_ => \[False] end.
Proof. intros R LS xs; now destruct LS. Qed.

(* TODO use haffine_repr *)
Lemma haffine_ListOf : forall A B (R:A -> B -> hprop) (LS:list A) (xs:list B),
  (forall x X, haffine (x ~> R X)) ->
  haffine (xs ~> ListOf R LS).
Proof.
  intros. revert LS.
  induction xs; destruct LS; xunfold ListOf; xaffine.
Qed.

Hint Resolve haffine_ListOf : haffine.

Definition ListOf_nil : forall A B R,
    (@nil B) ~> ListOf R (@nil A) = \[].
Proof. auto. Qed.

Definition ListOf_nil_r : forall A B R (L:list A),
    (@nil B) ~> ListOf R L ==> \[L = (@nil A)].
Proof.
  intros.
  destruct L as [|x].
  { xsimpl*. }
  { xchange* ListOf_eq. }
Qed.

Definition ListOf_nil_l : forall A B R (xs:list B),
    xs ~> ListOf R (@nil A) ==> \[xs = nil].
Proof.
  intros.
  destruct xs as [|x].
  { xsimpl*. }
  { xchange* ListOf_eq. }
Qed.

Definition ListOf_cons_r : forall A B R (L:list A) (x:B) (xs:list B),
    (x::xs) ~> ListOf R L ==> \exists LF LS, x ~> R LF \* xs ~> ListOf R LS \* \[L = LF::LS].
Proof.
  intros.
  destruct L as [|LF].
  { xchange* ListOf_eq. }
  { xsimpl*. }
Qed.

Definition ListOf_cons_l : forall A B R LF (LS:list A) (xs:list B),
    xs ~> ListOf R (LF::LS)  ==> \exists y ys, y ~> R LF \* ys ~> ListOf R LS \* \[xs = y::ys].
Proof.
  intros.
  destruct xs as [|xs].
  { xchange* ListOf_eq. }
  { xsimpl*. }
Qed.

(** Restore the default [auto_tilde] behavior *)

Ltac auto_tilde ::= auto_tilde_default.



(************************************************************)
(************************************************************)
(************************************************************)
(* FUTURE: ListOf

  Fixpoint List A a (T:A->a->hprop) (L:list A) (l:list a) : hprop :=
    match L,l with
    | nil, nil => \[l = nil]
    | X::L', x::l' => x ~> T X \* l' ~> List T L'
    | _,_=> \[False]
    end.

  Lemma focus_nil : forall A a (T:A->a->hprop),
    \[] ==> nil ~> List T nil.
  Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

  Lemma unfocus_nil : forall a (l:list a) A (T:A->a->hprop),
    l ~> List T nil ==> \[l = nil].
  Proof. intros. simpl. hdata_simpl. destruct l. auto. hsimpl. Qed.

  Lemma unfocus_nil' : forall A (L:list A) a (T:A->a->hprop),
    nil ~> List T L ==> \[L = nil].
  Proof.
    intros. destruct L.
    simpl. hdata_simpl. hsimpl~.
    simpl. hdata_simpl. hsimpl.
  Qed.

  Lemma focus_cons : forall a (l:list a) A (X:A) (L':list A) (T:A->a->hprop),
    (l ~> List T (X::L')) ==>
    Hexists x l', (x ~> T X) \* (l' ~> List T L') \* \[l = x::l'].
  Proof.
    intros. simpl. hdata_simpl. destruct l as [|x l'].
    hsimpl.
    hsimpl~ x l'.
  Qed.

  Lemma focus_cons' : forall a (x:a) (l:list a) A (L:list A) (T:A->a->hprop),
    (x::l) ~> List T L ==>
    Hexists X L', \[L = X::L'] \* (x ~> T X) \* (l ~> List T L').
  Proof. intros. destruct L; simpl; hdata_simpl; hsimpl~. Qed.

  Lemma unfocus_cons : forall a (x:a) (l:list a) A (X:A) (L:list A) (T:A->a->hprop),
    (x ~> T X) \* (l ~> List T L) ==>
    ((x::l) ~> List T (X::L)).
  Proof. intros. simpl. hdata_simpl. hsimpl. Qed.

  Global Opaque List.

*)
