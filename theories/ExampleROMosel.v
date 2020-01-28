(**

This file formalizes example in Separation Logic with read-only predicates

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SepRO SepROMosel.
Import NotationForTerms NotationForVariables.
Import ProofMode.
Generalizable Variables A B.
Open Scope trm_scope.

Ltac auto_star ::= jauto.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types r : val.


(* ********************************************************************** *)
(* * Tactics to help in the proofs *)

(** Tactic to reason about [let y = f x in t],
    where [M] is the specification lemma for [f]. *)

Tactic Notation "xletapp" constr(M) :=
  ram_apply_let M;
  [ solve [ auto 20 with iFrame ]
  | unlock; xtpull; simpl ].

(** Tactic to reason about [let f x = t1 in t2] *)

Tactic Notation "xletfun" :=
  applys triple_letfun; simpl; xtpull.

(** Tactic to reason about [triple (f x) H Q], by unfolding
    the definition of [f]. *)

Tactic Notation "xdef" :=
  rew_nary; rew_trms_vals;
  match goal with |- triple (trm_apps (trm_val ?f) _) _ _ =>
   match goal with
   | H: f =_ |- _ =>
     rew_nary in H;
     applys triple_apps_funs;
     [ applys H | auto | simpl ]
   | |- _ =>
     applys triple_apps_funs;
     [ unfold f; rew_nary; reflexivity | auto | simpl ]
  end
 end.

(** Patch to call [unlock] automatically before [xtpull] *)

Ltac xtpull_main tt ::=
  unlock;
  xtpull_setup tt;
  (repeat (xtpull_step tt));
  xtpull_cleanup tt.


(* ********************************************************************** *)
(* * Formalisation of higher-order iterator on a reference *)

(* ---------------------------------------------------------------------- *)
(** Apply a function to the contents of a reference *)

Definition val_ref_apply :=
  ValFun 'f 'p :=
    Let 'x := val_get 'p in
    'f 'x.

Lemma triple_ref_apply : forall (f:val) (p:loc) (v:val) (H:hprop) (Q:val->hprop),
  (triple (f v)
    PRE (RO(p ~~~> v) \* H)
    POST Q)
  ->
  (triple (val_ref_apply f p)
    PRE (RO(p ~~~> v) \* H)
    POST Q).
Proof using.
  introv M. xdef. ram_apply_let triple_get_ro. { auto with iFrame. }
  move=>X /=. xtpull=>->. done.
Qed.


(* ---------------------------------------------------------------------- *)
(** In-place update of a reference by applying a function *)

Definition val_ref_update :=
  ValFun 'f 'p :=
    Let 'x := val_get 'p in
    Let 'y := 'f 'x in
    val_set 'p 'y.

Lemma triple_ref_update : forall (f:val) (p:loc) (v:val) (H:hprop) (Q:val->hprop),
  Normal_post Q -> (* todo: this might not be needed if using "normally" *)
  (triple (f v)
    PRE (RO(p ~~~> v) \* H)
    POST Q)
  ->
  (triple (val_ref_update f p)
    PRE (p ~~~> v \* H)
    POST (fun r => \exists w, (p ~~~> w) \* (Q w))).
Proof using.
  introv N M. xdef. ram_apply_let triple_get_ro. { auto with iFrame. }
  unlock. move=>x /=. xtpull=>->. ram_apply_let M. { auto with iFrame. }
  unlock. move=>y /=. ram_apply triple_set. { auto 10 with iFrame. }
Qed.


(* ********************************************************************** *)
(* * Formalisation of the box data structure : a reference on a reference *)

(* ---------------------------------------------------------------------- *)
(** Representation predicate and its properties *)

Definition Box (n:int) (p:loc) :=
  \exists (q:loc), (p ~~~> q) \* (q ~~~> n).

Lemma Box_unfold : forall p n,
  (p ~> Box n) ==> \exists (q:loc), (p ~~~> q) \* (q ~~~> n).
Proof using. xunfold Box. auto. Qed.

Lemma Box_fold : forall p q n,
  (p ~~~> q) \* (q ~~~> n) ==> (p ~> Box n).
Proof using. xunfold Box. auto. Qed.

Lemma RO_Box_unfold : forall p n,
  RO (p ~> Box n) ==> RO (p ~> Box n) \* \exists (q:loc), RO (p ~~~> q) \* RO (q ~~~> n).
Proof using.
  iIntros (p n) "H". iDestruct (RO_duplicatable with "H") as "[$ H]". xunfold Box.
  iDestruct "H" as (q) "[??]". auto with iFrame.
Qed.

Lemma RO_Box_fold : forall p q n,
  RO (p ~~~> q \* q ~~~> n) ==> RO (p ~> Box n).
Proof using. iIntros (???) "?". xunfold Box. by iExists _. Qed.

Instance Box_normal : forall p n, Normal (p ~> Box n).
Proof. xunfold Box. apply _. Qed.

Arguments Box_fold : clear implicits.
Arguments Box_unfold : clear implicits.
Arguments RO_Box_unfold : clear implicits.
Arguments RO_Box_fold : clear implicits.


(* ---------------------------------------------------------------------- *)
(** Get operation *)

(*
  let get p =
     ! (!p)
*)

Definition val_box_get :=
  ValFun 'p :=
    Let 'q := val_get 'p in
    val_get 'q.

Lemma triple_box_get : forall p n,
  triple (val_box_get p)
    PRE (RO (p ~> Box n))
    POST (fun r => \[r = val_int n]).
Proof using.
  intros. xdef. xtchanges (RO_Box_unfold p) ;=> q.
  xletapp triple_get_ro => ? ->.
  ram_apply triple_get_ro. auto 10 with iFrame.
Qed.


(* ---------------------------------------------------------------------- *)
(** Box up2 operation *)

(*
  let up2 f p =
    let q = !p in
    q := f !q + f !q
*)

Definition val_box_up2 :=
  ValFun 'f 'p :=
    Let 'q := val_get 'p in
    Let 'n1 := val_get 'q in
    Let 'a1 := 'f 'n1 in
    Let 'n2 := val_get 'q in
    Let 'a2 := 'f 'n2 in
    Let 'm := 'a1 '+ 'a2 in
    val_set 'q 'm.

Lemma triple_box_up2 : forall (F:int->int) n (f:val) p,
  (forall (x:int), triple (f x)
      PRE (RO(p ~> Box n))
      POST (fun r => \[r = val_int (F x)])) ->
  triple (val_box_up2 f p)
    PRE (p ~> Box n)
    POST (fun r => p ~> Box (2 * F n)).
Proof using.
  introv M. xdef. xtchange (Box_unfold p). xtpull ;=> q.
  xletapp triple_get_ro => ? ->.
  xletapp triple_get_ro => ? ->.
  ram_apply_let M.
  { rewrite -RO_Box_fold. iIntros "Hq Hp". iCombine "Hp Hq" as "H".
    auto with iFrame. }
  unlock. xtpull => /= a1 ->.
  xletapp triple_get_ro => ? ->.
  ram_apply_let M.
  { rewrite -RO_Box_fold. iIntros "Hq Hp". iCombine "Hp Hq" as "H".
    auto with iFrame. }
  unlock. xtpull => /= a2 ->.
  xletapp triple_add => ? ->.
  ram_apply triple_set.
  iIntros "Hp $ !>!> % -> Hq". iApply Box_fold. iFrame.
  by math_rewrite (2 * F n = F n + F n)%Z.
Qed.

Arguments triple_box_up2 : clear implicits.


(* ---------------------------------------------------------------------- *)
(** Box demo program *)

Definition val_box_demo :=
  ValFun 'n :=
    Let 'q := val_ref 'n in
    Let 'p := val_ref 'q in
    LetFun 'f 'x :=
      Let 'a := val_box_get 'p in
      'x '+ 'a in
    Let 'u := val_box_up2 'f 'p in
    val_box_get 'p.

Lemma triple_box_demo : forall (n:int),
  triple (val_box_demo n)
    PRE \[]
    POST (fun r => \[r = val_int (4*n)]).
Proof using.
  intros. xdef.
  xletapp triple_ref => ? q ->.
  xletapp triple_ref => ? p ->.
  xletfun => F HF.
  ram_apply_let (triple_box_up2 (fun (x:int) => (x + n)%Z) n).
  { intros. xdef. xletapp triple_box_get => m ->.
    ram_apply triple_add. { auto 10 with iFrame. } }
  { iIntros "Hq Hp". iDestruct (Box_fold with "[$Hq $Hp]") as "$".
    auto with iFrame. }
  unlock. xtpull=> u. apply triple_htop_post. ram_apply triple_box_get.
  math_rewrite (2 * (n + n) = 4 * n)%Z. auto 10 with iFrame.
Qed.
