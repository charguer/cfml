(**

This file formalizes example in Separation Logic with read-only predicates

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SepRO.
Generalizable Variables A B.
Export NotationForVariables NotationForTerms.
Open Scope trm_scope.
Ltac auto_star ::= jauto.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types v : val.


(*------------------------------------------------------------------*)
(** Auxiliary *)

Lemma triple_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs xs (length Vs) ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h1 h2 D H1.
  forwards~ (h1'&v&N1&N2&N3&N4): (rm M) h2 H1.
  exists h1' v. splits~. { subst. applys* eval_app_funs_val. }
Qed.

Lemma var_funs_exec_elim : forall (n:nat) xs,
  var_funs_exec xs n ->
  var_funs n xs.
Proof using. introv M. rewrite var_funs_exec_eq in M. rew_istrue~ in M. Qed.

Hint Resolve var_funs_exec_elim.

Lemma RO_himpl_RO_hstar_RO : forall H,
  RO H ==> (RO H \* RO H).
Proof using. intros. applys RO_duplicatable. Qed.

Lemma triple_xtchange : forall (H1 H1':hprop), H1 ==> H1' ->
  forall t H H2 Q,
  H ==> H1 \* H2 ->
  triple t (H1' \* H2) Q ->
  triple t H Q.
Proof using.
  introv M1 M2 M. applys~ triple_conseq M2.
  applys* triple_conseq (H1' \* H2). xsimpl~.
Qed.

Lemma triple_frame_read_only_conseq : forall t H1 Q1 H2 H Q,
  H ==> (H1 \* H2) ->
  Normal H1 ->
  triple t (RO H1 \* H2) Q1 ->
  (Q1 \*+ H1) ===> Q ->
  triple t H Q.
Proof using.
  introv WP M N WQ. applys* triple_conseq (rm WP) (rm WQ).
  forwards~ R: triple_frame_read_only t H2 Q1 H1.
  { rewrite~ hstar_comm. } { rewrite~ hstar_comm. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* l ~~~> v).
Proof using.
  intros. applys triple_frame_read_only_conseq (l ~~~> v).
  { xsimpl. } { apply _. }
  { rew_heap. applys triple_get_ro. }
  { auto. }
Qed.

Lemma triple_let' : forall z t1 t2 H2 H1 H Q Q1,
  H ==> (H1 \* H2) ->
  triple t1 H1 Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X \* H2) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using. introv WP M1 M2. applys* triple_conseq WP. applys* triple_let. Qed.

Lemma triple_frame : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. applys~ triple_frame_read_only.
  applys~ triple_conseq (H1 \* \Top). xsimpl.
  applys* triple_htop_pre.
Qed.

Lemma triple_frame_conseq : forall t H1 Q1 H2 H Q,
  H ==> H2 \* H1 ->
  Normal H1 ->
  triple t H2 Q1 ->
  Q1 \*+ H1 ===> Q ->
  triple t H Q.
Proof using. intros. applys* triple_conseq. applys* triple_frame. Qed.

Hint Resolve Normal_hsingle.


(* ********************************************************************** *)
(* * Formalisation of higher-order iterator on a reference *)

Tactic Notation "xdef" :=
  rew_nary; rew_trms_vals;
  match goal with |- triple (trm_apps (trm_val ?f) _) _ _ =>
   applys triple_apps_funs;
   [unfold f; rew_nary; reflexivity | auto | simpl]
  end.

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
  introv M. xdef. xtchange (@RO_himpl_RO_hstar_RO (p ~~~> v)).
  rew_heap. applys triple_let (RO (p ~~~> v)).
  { applys triple_get_ro. }
  { intros x; simpl. xtpull ;=> E. subst x.
    applys triple_conseq M; xsimpl. }
Qed.

(* Note: this specification allows [f] to call [val_get] on [r],
   as illustrated next

  Definition val_demo_1 :=
    ValFun 'n :=
      Let 'p := val_ref 'n in
      LetFun 'f 'x :=
        Let 'y := val_get 'p in
        val_add 'x 'y in
      val_ref_apply 'f 'p.

  Lemma triple_demo_1 : forall (n:int),
    triple (val_demo_1 n)
      PRE \[]
      POST (fun r => \[r = val_int (2*n)]).
  Proof using.

  Qed.

*)



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
  introv N M. xdef.
  applys triple_let.
  { applys triple_get. }
  { intros x; simpl. xtpull ;=> E. subst x.
    applys triple_let' \[]. { xsimpl. }
    applys~ triple_frame_read_only_conseq (p ~~~> v).
    { applys triple_conseq M; xsimpl. }
    { xsimpl. }
    { clear M. intros y; simpl. xtpull.
      applys~ triple_frame_conseq (Q y).
      { applys triple_set. }
      { xsimpl~. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** In-place update of a reference by invoking a function, with representation predicate  *)

Hint Rewrite RO_hexists RO_pure : rew_RO.
 (* todo : rename to RO_hpure , RO_hstar. *)

Tactic Notation "rew_RO" :=
  autorewrite with rew_RO.

Lemma triple_htop_pre' : forall H2 H1 t H Q,
  H ==> H1 \* H2 ->
  triple t H1 Q ->
  triple t H Q.
Proof using.
  introv W M. applys triple_conseq; [| applys triple_htop_pre M |].
  { xchange W. xsimpl. } { auto. }
Qed.


(*---*)



Definition Box (n:int) (p:loc) :=
  \exists (q:loc), (p ~~~> q) \* (q ~~~> n).

Lemma Box_unfold : forall p n,
  (p ~> Box n) ==> \exists (q:loc), (p ~~~> q) \* (q ~~~> n).
Proof using. intros. xunfold Box. xsimpl. Qed.

Lemma Box_fold : forall p q n,
  (p ~~~> q) \* (q ~~~> n) ==> (p ~> Box n).
Proof using. intros. xunfold Box. xsimpl. Qed.

Lemma RO_Box_unfold : forall p n,
  RO (p ~> Box n) ==> RO (p ~> Box n) \* \exists (q:loc), RO (p ~~~> q) \* RO (q ~~~> n).
Proof using.
  intros. xchange RO_duplicatable. xunfold Box at 1.
  rew_RO. xpull ;=> q. xchanges (RO_star (p ~~~> q) (q ~~~> n)).
Qed.

Arguments Box_fold : clear implicits.
Arguments Box_unfold : clear implicits.
Arguments RO_Box_unfold : clear implicits.


(*---*)

Definition val_box_get :=
  ValFun 'p :=
    Let 'q := val_get 'p in
    val_get 'q.

Lemma triple_box_get : forall p n,
  triple (val_box_get p)
    PRE (RO (p ~> Box n))
    POST (fun r => \[r = val_int n]).
Proof using.
  intros. xdef. xtchange (RO_Box_unfold p). xtpull ;=> q.
  applys triple_htop_pre' (RO (p ~> Box n)). xsimpl. (* not need, ideally *)
  rew_heap. applys triple_let' __ (RO (p ~~~> q)).
  { xsimpl. }
  { applys triple_get_ro. }
  { intros x; simpl; xtpull ;=> E; subst x. applys triple_get_ro. }
Qed.



(* ---------------------------------------------------------------------- *)

(*--- Under development

(* let box_twice f p =
      let q = !p in
      q := f !q + f !q
*)

Definition val_box_twice :=
  ValFun 'f 'p :=
    Let 'q := val_get 'p in
    Let 'n1 := val_get 'q in
    Let 'a1 := 'f 'n1 in
    Let 'n2 := val_get 'q in
    Let 'a2 := 'f 'n2 in
    Let 'm := 'a1 '+ 'a2 in
    val_set 'q 'm.

Lemma triple_box_twice : forall (f:val) p n (F:int->int),
  (forall (x:int) H, triple (val_box_twice f x)
      PRE (RO(p ~> Box n) \* H)
      POST (fun r => \[r = val_int (F x)] \* H)) ->
  triple (val_box_twice f p)
    PRE (p ~> Box n)
    POST (fun r => p ~> Box (2 * F n)).
Proof using.
  introv M. xdef. xtchange (Box_unfold p). xtpull ;=> q.
  applys triple_let' __ (p ~~~> q).
  { xsimpl. }
  { rew_heap. applys triple_get. }
  { intros x; simpl; xtpull ;=> E; subst x.
  applys triple_let' __ (q ~~~> n).
  { xsimpl. }
  { rew_heap. applys triple_get. }
  { intros x; simpl; xtpull ;=> E; subst x.
Abort.



*)