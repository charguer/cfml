(**

Foundations of Separation Logic

Chapter: "Extra".

This file provides formalization of additional reasoning rules
expressed using Separation Logic triples.

This file serves as a reference, there is no need to read through it.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Export SLFDirect.

(** Implicit Types *)

Implicit Types k : nat.
Implicit Types n i : int.
Implicit Types v : val.
Implicit Types w : hval.
Implicit Types p : loc.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional Hoare Triples *)

(** There additional extraction rules are not needed in weakest
    precondition style because they are subsumed by corresponding
    rules on entailment. *)

Section Hoare.

Lemma hoare_hforall : forall t (A:Type) (J:A->hprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using.
  introv (x&M) Hh. applys* hoare_conseq (hforall J) Q M.
  applys* himpl_hforall_l.
Qed.

Lemma hoare_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using. introv HP M. rewrite* hwand_hpure_l. Qed.

End Hoare.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Separation Logic Triples *)


(* ########################################################### *)
(** ** Structural rules *)

(** Consequence and frame rule *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HF. applys hoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF. applys hoare_conseq (M (HF \* H')); xsimpl.
Qed.

(** Details of the frame rule proof. *)

Lemma triple_frame' : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold triple in *. rename H' into H1. intros H2.
  applys hoare_conseq. applys M (H1 \* H2).
  { rewrite hstar_assoc. auto. }
  { intros v. rewrite hstar_assoc. auto. }
Qed.

(** Extraction rules *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_hpure. intros. applys* M.
Qed. (* Note: can also be proved from [triple_hexists] *)

Lemma triple_hforall : forall A (x:A) t (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using.
  introv M. applys* triple_conseq M. applys hforall_specialize.
Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using.
  introv HP M. applys* triple_conseq M. rewrite* hwand_hpure_l.
Qed.

(** Combined and ramified rules *)

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_conseq WH WQ. applys triple_frame M.
Qed.

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M W.
  { rewrite~ <- qwand_equiv. }
Qed.

(** Named heaps *)

Lemma hexists_named_eq : forall H,
  H = (\exists h, \[H h] \* (= h)).
Proof using.
  intros. apply himpl_antisym.
  { intros h K. applys hexists_intro h.
    rewrite* hstar_hpure. }
  { xpull. intros h K. intros ? ->. auto. }
Qed.

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using.
  introv M. rewrite (hexists_named_eq H).
  applys triple_hexists. intros h.
  applys* triple_hpure.
Qed.


(* ########################################################### *)
(** ** Rules for terms *)

Lemma triple_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv E M1. intros H'. applys hoare_eval_like E. applys M1.
Qed.

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { xchanges M. }
Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. intros HF. applys~ hoare_fun. { xchanges M. }
Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF. applys~ hoare_fix. { xchanges M. }
Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_seq.
  { applys M1. }
  { applys hoare_conseq M2; xsimpl. }
Qed.

Lemma triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst x X t2) (Q1 X) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq M2; xsimpl. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if. applys M1.
Qed.

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  (* can also be proved using [triple_eval_like] *)
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fun E. applys M1.
Qed.

Lemma triple_app_fun_direct : forall x v2 t1 H Q,
  triple (subst x v2 t1) H Q ->
  triple (trm_app (val_fun x t1) v2) H Q.
Proof using. introv M. applys* triple_app_fun. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  (* can also be proved using [triple_eval_like] *)
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fix E. applys M1.
Qed.

Lemma triple_app_fix_direct : forall v2 f x t1 H Q,
  triple (subst x v2 (subst f (val_fix f x t1) t1)) H Q ->
  triple (trm_app (val_fix f x t1) v2) H Q.
Proof using. introv M. applys* triple_app_fix. Qed.


(* ########################################################### *)
(** ** Rules for primitives *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros H'. applys hoare_conseq hoare_add; xsimpl~.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_ref; xsimpl~.
Qed.

Lemma triple_get : forall v p,
  triple (val_get (val_loc p))
    (p ~~> v)
    (fun x => \[x = v] \* (p ~~> v)).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_get; xsimpl~.
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun _ => p ~~> v).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_set; xsimpl~.
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_free; xsimpl~.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** Disjunction and conjunction *)


(* ################################################ *)
(** ** Definition and properties of [hor] *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

Lemma hor_sym : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using.
  intros. unfold hor. applys himpl_antisym.
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_l : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using.
  introv M1 M2. unfold hor. applys triple_hexists.
  intros b. destruct* b.
Qed.


(* ################################################ *)
(** ** Definition and properties of [hand] *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

Lemma hand_sym : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using.
  intros. unfold hand. applys himpl_antisym.
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
Qed.

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H1 ==> H2 ->
  H1 ==> H3 ->
  H1 ==> hand H2 H3.
Proof using.
  introv M1 M2. unfold hand. applys himpl_hforall_r. intros b. case_if*.
Qed.

Lemma triple_hand_l : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t (hand H1 H2) Q.
Proof using. introv M1. unfold hand. applys~ triple_hforall true. Qed.

Lemma triple_hand_r : forall t H1 H2 Q,
  triple t H2 Q ->
  triple t (hand H1 H2) Q.
Proof using. introv M1. unfold hand. applys~ triple_hforall false. Qed.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties of [haffine] *)

Lemma haffine_hempty :
  haffine \[].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hstar_hpure : forall (P:Prop) H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. intros. applys haffine_hany. Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using. intros. applys haffine_hany. Qed.

Ltac xaffine_core tt ::= (* configure [xaffine] *)
  repeat match goal with |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  end.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional primitive operations *)

(* ################################################ *)
(** ** Syntax *)

(** Notation for the additional primitive operations. *)

Notation "'not t" :=
  (val_neg t)
  (at level 57) : trm_scope.

Notation "'- t" :=
  (val_opp t)
  (at level 57) : trm_scope.

Notation "t1 '- t2" :=
  (val_sub t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '* t2" :=
  (val_mul t1 t2)
  (at level 57) : trm_scope.

Notation "t1 '/ t2" :=
  (val_div t1 t2)
  (at level 57) : trm_scope.

Notation "t1 'mod t2" :=
  (val_div t1 t2)
  (at level 57) : trm_scope.

Notation "t1 '= t2" :=
  (val_eq t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '<> t2" :=
  (val_neq t1 t2)
  (at level 58) : trm_scope.

Notation "t1 '<= t2" :=
  (val_le t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '< t2" :=
  (val_lt t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '>= t2" :=
  (val_ge t1 t2)
  (at level 60) : trm_scope.

Notation "t1 '> t2" :=
  (val_gt t1 t2)
  (at level 60) : trm_scope.


(* ################################################ *)
(** ** Specification of [unop] and [binop] in general *)

(** Hoare specifications *)

Lemma hoare_unop : forall v H op v1,
  evalunop op v1 v ->
  hoare (op v1)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval_unop. }
  { himpl_fold. xsimpl*. }
Qed.

Lemma hoare_binop : forall v H op v1 v2,
  evalbinop op v1 v2 v ->
  hoare (op v1 v2)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval_binop. }
  { himpl_fold. xsimpl*. }
Qed.

(** Separation Logic specifications *)

Lemma triple_unop : forall v op v1,
  evalunop op v1 v ->
  triple (op v1) \[] (fun r => \[r = v]).
Proof using.
  introv R. unfold triple. intros H'.
  applys* hoare_conseq hoare_unop. xsimpl*.
Qed.

Lemma triple_binop : forall v op v1 v2,
  evalbinop op v1 v2 v ->
  triple (op v1 v2) \[] (fun r => \[r = v]).
Proof using.
  introv R. unfold triple. intros H'.
  applys* hoare_conseq hoare_binop. xsimpl*.
Qed.


(* ################################################ *)
(** ** Specification of primitive operations *)

(** Remark: [triple_add] and [triple_div] are proved in [SLFDirect]. *)

Lemma triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = val_bool (neg b1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_neg. Qed.

Lemma triple_opp : forall n1,
  triple (val_opp n1)
    \[]
    (fun r => \[r = val_int (- n1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_opp. Qed.

Lemma triple_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_eq. Qed.

Lemma triple_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 <> v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_neq. Qed.

Lemma triple_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_sub. Qed.

Lemma triple_mul : forall n1 n2,
  triple (val_mul n1 n2)
    \[]
    (fun r => \[r = val_int (n1 * n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mul. Qed.

Lemma triple_mod : forall n1 n2,
  n2 <> 0 ->
  triple (val_mod n1 n2)
    \[]
    (fun r => \[r = val_int (Z.rem n1 n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mod. Qed.

Lemma triple_le : forall n1 n2,
  triple (val_le n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 <= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_le. Qed.

Lemma triple_lt : forall n1 n2,
  triple (val_lt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 < n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_lt. Qed.

Lemma triple_ge : forall n1 n2,
  triple (val_ge n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 >= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_ge. Qed.

Lemma triple_gt : forall n1 n2,
  triple (val_gt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 > n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_gt. Qed.

Lemma triple_ptr_add : forall p n,
  p + n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (abs (p + n))]).
Proof using.
  intros. applys* triple_binop. applys* evalbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

Lemma triple_ptr_add_nat : forall p (f:nat),
  triple (val_ptr_add p f)
    \[]
    (fun r => \[r = val_loc (p+f)%nat]).
Proof using.
  intros. applys triple_conseq triple_ptr_add. { math. } { xsimpl. }
  { xsimpl. intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

Hint Resolve triple_neg triple_opp triple_eq triple_neq
   triple_sub triple_mul triple_mod triple_le triple_lt
   triple_ge triple_gt triple_ptr_add triple_ptr_add_nat : triple.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Treatment of functions of 2 and 3 arguments *)

(** As explained in chapter [SLFStruct], there are different ways to
    support functions of several arguments: curried functions, n-ary
    functions, or functions expecting a tuple as argument.

    For simplicity, we here follow the approach based on curried
    function, specialized for arity 2 and 3. It is possible to state
    arity-generic definitions and lemmas, but the definitions become
    much more technical.

    From an engineering point of view, it is easier and more efficient
    to follow the approach using n-ary functions, as the CFML tool does. *)


(* ################################################ *)
(** ** Syntax for functions of 2 or 3 arguments *)

Notation "'Fun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1, x2 at level 0, format "'Fun'  x1  x2  ':='  t") : val_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f, x1, x2 at level 0, format "'Fix'  f  x1  x2  ':='  t") : val_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1, x2, x3 at level 0, format "'Fun'  x1  x2  x3  ':='  t") : val_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f, x1, x2, x3 at level 0, format "'Fix'  f  x1  x2  x3  ':='  t") : val_scope.


(* ################################################ *)
(** ** Evaluation rules for applications to 2 or 3 arguments. *)

(** [eval_like] judgment for applications to several arguments. *)

Lemma eval_like_app_fun2 : forall v0 v1 v2 x1 x2 t1,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  x1 <> x2 ->
  eval_like (subst x2 v2 (subst x1 v1 t1)) (v0 v1 v2).
Proof using.
  introv E N. introv R. applys* eval_app_args.
  { applys eval_app_fun E. simpl. rewrite var_eq_spec. case_if. applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma eval_like_app_fix2 : forall v0 v1 v2 f x1 x2 t1,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst f v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R. applys* eval_app_args.
  { applys eval_app_fix E. simpl. do 2 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma eval_like_app_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t1,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) (v0 v1 v2 v3).
Proof using.
  introv E (N1&N2&N3). introv R. applys* eval_app_args.
  { applys* eval_like_app_fun2 E. simpl. do 2 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma eval_like_app_fix3 : forall v0 v1 v2 v3 f x1 x2 x3 t1,
  v0 = val_fix f x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ f <> x2 /\ f <> x3 /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 (subst f v0 t1)))) (v0 v1 v2 v3).
Proof using.
  introv E (N1&N2&N3&N4&N5). introv R. applys* eval_app_args.
  { applys* eval_like_app_fix2 E. simpl. do 3 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed.


(* ################################################ *)
(** ** Reasoning rules for applications to 2 or 3 arguments *)

(** Weakest preconditions for applications to several arguments. *)

Lemma wp_app_fun2 : forall x1 x2 v0 v1 v2 t1 Q,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  x1 <> x2 ->
  wp (subst x2 v2 (subst x1 v1 t1)) Q ==> wp (trm_app v0 v1 v2) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fun2. Qed.

Lemma wp_app_fix2 : forall f x1 x2 v0 v1 v2 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  wp (subst x2 v2 (subst x1 v1 (subst f v0 t1))) Q ==> wp (trm_app v0 v1 v2) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix2. Qed.

Lemma wp_app_fun3 : forall x1 x2 x3 v0 v1 v2 v3 t1 Q,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ x1 <> x3 /\ x2 <> x3) ->
  wp (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) Q ==> wp (trm_app v0 v1 v2 v3) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fun3. Qed.

Lemma wp_app_fix3 : forall f x1 x2 x3 v0 v1 v2 v3 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2 /\ f <> x2 /\ f <> x3 /\ x1 <> x3 /\ x2 <> x3) ->
  wp (subst x3 v3 (subst x2 v2 (subst x1 v1 (subst f v0 t1)))) Q ==> wp (trm_app v0 v1 v2 v3) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix3. Qed.


(* ################################################ *)
(** ** Generaliation of [xwp] to handle functions of two arguments *)

Lemma xwp_lemma_fun2 : forall v0 v1 v2 x1 x2 t H Q,
  v0 = val_fun x1 (trm_fun x2 t) ->
  var_eq x1 x2 = false ->
  H ==> wpgen ((x1,v1)::(x2,v2)::nil) t Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv M1 N M2. rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((x1,v1)::nil) ++ ((x2,v2)::nil)) t Q).
  rewrite isubst_app. do 2 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fun2.
Qed.

Lemma xwp_lemma_fix2 : forall f v0 v1 v2 x1 x2 t H Q,
  v0 = val_fix f x1 (trm_fun x2 t) ->
  (var_eq x1 x2 = false /\ var_eq f x2 = false) ->
  H ==> wpgen ((f,v0)::(x1,v1)::(x2,v2)::nil) t Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((f,v0)::nil) ++ ((x1,v1)::nil) ++ ((x2,v2)::nil)) t Q).
  do 2 rewrite isubst_app. do 3 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix2.
Qed.

Lemma xwp_lemma_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t H Q,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t)) ->
  (var_eq x1 x2 = false /\ var_eq x1 x3 = false /\ var_eq x2 x3 = false) ->
  H ==> wpgen ((x1,v1)::(x2,v2)::(x3,v3)::nil) t Q ->
  triple (v0 v1 v2 v3) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((x1,v1)::nil) ++ ((x2,v2)::nil) ++ ((x3,v3)::nil)) t Q).
  do 2 rewrite isubst_app. do 3 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fun3.
Qed.

Lemma xwp_lemma_fix3 : forall f v0 v1 v2 v3 x1 x2 x3 t H Q,
  v0 = val_fix f x1 (trm_fun x2 (trm_fun x3 t)) ->
  (   var_eq x1 x2 = false /\ var_eq f x2 = false /\ var_eq f x3 = false
   /\ var_eq x1 x3 = false /\ var_eq x2 x3 = false) ->
  H ==> wpgen ((f,v0)::(x1,v1)::(x2,v2)::(x3,v3)::nil) t Q ->
  triple (v0 v1 v2 v3) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((f,v0)::nil) ++ ((x1,v1)::nil) ++ ((x2,v2)::nil) ++ ((x3,v3)::nil)) t Q).
  do 3 rewrite isubst_app. do 4 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix3.
Qed.

(** Generalization of [xwp] to handle functions of arity 2 *)

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ]
        | applys xwp_lemma_fun2; [ reflexivity | reflexivity | ]
        | applys xwp_lemma_fix2; [ reflexivity | splits; reflexivity | ]
        | applys xwp_lemma_fun3; [ reflexivity | splits; reflexivity | ]
        | applys xwp_lemma_fix3; [ reflexivity | splits; reflexivity | ] ];
  xwp_simpl.


(* ################################################ *)
(** ** Bonus: Triples for applications to several arguments *)

(** Triples for applications to 2 arguments.
    Similar rules can be stated and proved for 3 arguments.
    These rules are not needed for the verification framework. *)

Lemma triple_app_fun2 : forall v0 v1 v2 x1 x2 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  x1 <> x2 ->
  triple (subst x2 v2 (subst x1 v1 t1)) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fun2.
Qed.

Lemma triple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Specification of operations on arrays and records *)

(** The chapter [SLFStruct] shows how to these specifications
    may be realized. *)


(* ########################################################### *)
(** ** Predicate [hcells] *)

Definition hvals : Type := list hval.

Fixpoint hcells (L:hvals) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | w::L' => (p ~~> w) \* (hcells L' (S p))
  end.

Lemma hcells_intro : forall L p,
  p <> null ->
  hcells L p (Fmap.conseq L p).
Proof using.
  intros L. induction L as [|L']; introv N; simpl.
  { applys hempty_intro. }
  { applys hstar_intro.
    { applys* hsingle_intro. }
    { applys IHL. unfolds loc, null. math. }
    { applys Fmap.disjoint_single_conseq. left. math. } }
Qed.

Lemma hcells_inv : forall p L h,
  hcells L p h ->
  h = Fmap.conseq L p.
Proof using.
  introv N. gen p h. induction L as [|x L']; simpl; intros.
  { applys hempty_inv N. }
  { lets (h1&h2&N1&N2&N3&->): hstar_inv N. fequal.
    { applys hsingle_inv N1. }
    { applys IHL' N2. } }
Qed.

Lemma hcells_nil_eq : forall p,
  hcells nil p = \[].
Proof using. auto. Qed.

Lemma hcells_cons_eq : forall p w L,
  hcells (w::L) p = (p ~~> w) \* hcells L (S p).
Proof using. intros. simpl. xsimpl*. Qed.

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. }
  { rewrite IHL1. math_rewrite (length L1 + S p = S (length L1 + p))%nat.
    xsimpl. }
Qed.

Lemma hcells_focus : forall k p (L:hvals),
  k < length L ->
  hcells L p ==>
       ((p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~~> w) \-* hcells (LibList.update k w L) p).
Proof using.
  introv E. gen k p. induction L as [|w L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case. case_if.
    { subst. math_rewrite (p + 0 = p)%nat. xsimpl. intros w'.
       rewrite LibList.update_zero. rewrite hcells_cons_eq. xsimpl*. }
    { forwards R: IHL' (k-1)%nat (S p). { math. }
      math_rewrite (S p + (k - 1) = p + k)%nat in R. xchange R.
      xsimpl. intros w'. xchange (hforall_specialize w').
      rewrite update_cons_pos; [|math]. rewrite hcells_cons_eq. xsimpl. } }
Qed.

Arguments hcells_focus : clear implicits.


(* ########################################################### *)
(** ** Predicate [harray] *)

Definition header (k:nat) (p:loc) : hprop :=
  p ~~> hval_header k \* \[p <> null].

Lemma header_intro : forall k p,
  p <> null ->
  (header k p) (Fmap.single p (hval_header k)).
Proof using.
  introv N. unfolds header. rewrite hstar_comm, hstar_hpure.
  split*. applys hsingle_intro.
Qed.

Lemma header_inv : forall k p h,
  (header k p) h ->
  h = Fmap.single p (hval_header k) /\ p <> null.
Proof using.
  introv M. unfolds header. rewrite hstar_comm, hstar_hpure in M.
  destruct M as (N&M). lets E: hsingle_inv M. split*.
Qed.

Definition harray (L:hvals) (p:loc) : hprop :=
  header (length L) p \* hcells L (S p).

Lemma harray_not_null : forall p L,
  harray L p ==> harray L p \* \[p <> null].
Proof using. intros. unfold harray, header. xsimpl*. Qed.

Lemma harray_focus : forall k p L,
  k < length L ->
  harray L p ==>
       ((S p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((S p+k)%nat ~~> w) \-* harray (LibList.update k w L) p).
Proof using.
  introv E. unfold harray. xchange* (hcells_focus k).
  xsimpl. intros w. xchange (hforall_specialize w).
  rewrite LibList.length_update. xsimpl.
Qed.


(* ########################################################### *)
(** ** Predicate [harray_uninit] *)

Definition harray_uninit (k:nat) (p:loc) : hprop :=
  harray (LibList.make k hval_uninit) p.

Lemma harray_uninit_intro : forall p k,
  p <> null ->
  harray_uninit k p (Fmap.conseq (hval_header k :: LibList.make k hval_uninit) p).
Proof using.
  introv N. unfold harray_uninit, harray. rewrite conseq_cons.
  applys hstar_intro.
  { unfold header. rewrite hstar_comm, hstar_hpure. split*.
    rewrite LibList.length_make. applys* hsingle_intro. }
  { applys* hcells_intro. }
  { applys disjoint_single_conseq. left*. }
Qed.


(* ########################################################### *)
(** ** Predicate [hcells_any] *)

Fixpoint hcells_any (k:nat) (p:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => (\exists w, p ~~> w) \* (hcells_any k' (S p))
  end.

Definition harray_any (k:nat) (p:loc) : hprop :=
  header k p \* hcells_any k (S p).

Lemma himpl_hcells_any_hcells : forall p k,
  hcells_any k p ==> \exists L, \[length L = k] \* hcells L p.
Proof using.
  intros. gen p. induction k as [|k']; simpl; intros.
  { xsimpl (@nil hval). { auto. } { simpl. xsimpl. } }
  { xpull. intros w. xchange IHk'. intros L' EL'.
    xsimpl (w::L'). { rew_list. math. } { simpl. xsimpl. } }
Qed.

Lemma himpl_harray_any_harray : forall p k,
  harray_any k p ==> \exists L, \[length L = k] \* harray L p.
Proof using.
  intros. unfold harray, harray_any.
  xchange himpl_hcells_any_hcells. intros L EL. subst k. xsimpl*.
Qed.


(* ########################################################### *)
(** ** Specification of [val_alloc] *)

Lemma hoare_alloc_nat : forall H k,
  hoare (val_alloc k)
    H
    (funloc p => harray_uninit k p \* H).
Proof using.
  intros. intros h Hh.
  forwards~ (p&Dp&Np): (Fmap.conseq_fresh null h
                         (hval_header k :: LibList.make k hval_uninit)).
  match type of Dp with Fmap.disjoint ?hc _ => sets h1': hc end.
  exists (h1' \u h) (val_loc p). split.
  { applys~ (eval_alloc k). }
  { applys hexists_intro p. rewrite hstar_hpure. split*.
    { applys* hstar_intro. applys* harray_uninit_intro. } }
Qed.

Lemma triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (funloc p => harray_uninit k p).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_alloc_nat H'. } { xsimpl. } { xsimpl*. }
Qed.

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray_uninit (abs n) p).
Proof using.
  introv N. rewrite <- (@abs_nonneg n) at 1; [|auto].
  xtriple. xapp triple_alloc_nat. xsimpl*.
Qed.

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).
Proof using.
  introv N. xtriple. xapp triple_alloc. { auto. }
  { xpull. intros p. unfold harray_uninit. xsimpl*.
    { rewrite length_make. rewrite* abs_nonneg. } }
Qed.


(* ########################################################### *)
(** ** Specification of [val_dealloc] *)

Lemma hoare_dealloc : forall H L p,
  hoare (val_dealloc p)
    (harray L p \* H)
    (fun _ => H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4).
  unfolds harray. destruct N1 as (h11&h12&N5&N6&N7&N8).
  lets (E11&Np): header_inv N5. lets E12: hcells_inv N6. subst h h1 h11 h12.
  exists h2 val_unit. split; [|auto]. applys* eval_dealloc.
Qed.

Lemma triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_dealloc H'. } { xsimpl. } { xsimpl. }
Qed.

Lemma triple_dealloc_any : forall p k,
  triple (val_dealloc p)
    (harray_any k p)
    (fun _ => \[]).
Proof using.
  intros. xtriple. xchange himpl_harray_any_harray. intros L EL.
  xapp triple_dealloc. { xsimpl. }
Qed.


(* ########################################################### *)
(** ** Specification of [val_get_header] and [val_array_length] *)

Lemma eval_get_header_sep : forall s s2 p k,
  s = Fmap.union (Fmap.single p (hval_header k)) s2 ->
  eval s (val_get_header (val_loc p)) s (val_int k).
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p (hval_header k).
  applys eval_get_header.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma hoare_get_header : forall H k p,
  hoare (val_get_header p)
    ((p ~~> hval_header k) \* H)
    (fun r => \[r = k] \* (p ~~> hval_header k) \* H).
Proof using.
  intros. intros s K0. exists s (val_int k). split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets E1: hsingle_inv P1. subst s1. applys eval_get_header_sep U. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma triple_get_header' : forall H k p,
  triple (val_get_header p)
    ((p ~~> hval_header k) \* H)
    (fun r => \[r = k] \* (p ~~> hval_header k) \* H).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_get_header; xsimpl~.
Qed.

Lemma triple_get_header : forall k p,
  triple (val_get_header p)
    (header k p)
    (fun r => \[r = k] \* header k p).
Proof using.
  intros. unfold header. rewrite hstar_comm. applys triple_hpure. intros N.
  applys triple_conseq triple_get_header'. { xsimpl. } { xsimpl; auto. }
Qed.

Definition val_array_length : val := val_get_header.

Lemma triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).
Proof using.
  intros. unfold harray. applys triple_conseq_frame triple_get_header.
  { xsimpl. } { xsimpl. auto. }
Qed.


(* ########################################################### *)
(** ** Encoding of [val_array_get] and [val_array_set] *)

Module Export ArrayAccessDef.
Import SLFProgramSyntax.
Open Scope wp_scope.

Lemma abs_lt_inbound : forall i k,
  0 <= i < nat_to_Z k ->
  (abs i < k).
Proof using.
  introv N. apply lt_nat_of_lt_int. rewrite abs_nonneg; math.
Qed.

Lemma succ_int_plus_abs : forall p i,
  i >= 0 ->
  (S (p + abs i) = abs (nat_to_Z p + (i + 1)))%nat.
Proof using.
  introv N. rewrite abs_nat_plus_nonneg; [|math].
  math_rewrite (i+1 = 1 + i).
  rewrite <- succ_abs_eq_abs_one_plus; math.
Qed.

Definition val_array_get : val :=
  Fun 'p 'i :=
    Let 'j := 'i '+ 1 in
    Let 'n := val_ptr_add 'p 'j in
    val_get 'n.

Lemma triple_array_get : forall p i v (L:hvals),
  0 <= i < length L ->
  LibList.nth (abs i) L = hval_val v ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = v] \* harray L p).
Proof using.
  introv N E. xwp. xapp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L).
  { rew_listx. applys* abs_lt_inbound. }
  sets w: (LibList.nth (abs i) L). rewrite succ_int_plus_abs; [|math].
  xapp triple_get. { applys E. }
  xchange (hforall_specialize w). subst w.
  rewrite update_nth_same. rewrite <- E. xsimpl*.
  { rew_listx. applys* abs_lt_inbound. }
Qed.

Definition val_array_set : val :=
  Fun 'p 'i 'x :=
    Let 'j := 'i '+ 1 in
    Let 'n := val_ptr_add 'p 'j in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) (hval_val v) L) p).
Proof using.
  introv N. xwp. xapp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_inbound. }
  rewrite succ_int_plus_abs; [|math].
  xapp triple_set. xchange (hforall_specialize (hval_val v)).
Qed.

End ArrayAccessDef.


(* ########################################################### *)
(** ** Predicates on list of values *)

Definition vals : Type := list val.

Coercion vals_to_hvals (L:vals) : hvals :=
  LibList.map hval_val L.

Lemma length_vals_to_hvals : forall L,
  length (vals_to_hvals L) = length L.
Proof using. intros. unfold vals_to_hvals. rewrite* LibList.length_map. Qed.

Hint Rewrite length_vals_to_hvals : rew_listx.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Treatment of records *)

(* ########################################################### *)
(** ** Definition of record fields *)

Definition field : Type := nat.

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+k)%nat ~~> v.

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v") : hprop_scope.

Lemma hfield_eq : forall p k v,
  hfield p k v = ((k+p)%nat ~~> v).
Proof using. intros. math_rewrite (k+p = p+k)%nat. auto. Qed.


(* ########################################################### *)
(** ** Definition of record operations *)

Module Export FieldAccessDef.
Import SLFProgramSyntax.
Open Scope wp_scope.

Definition val_get_field (k:field) : val :=
  Fun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Lemma triple_get_field : forall p k v,
  triple ((val_get_field k) p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).
Proof using.
  xwp. xapp. unfold hfield. xapp. xsimpl*.
Qed.

Definition val_set_field (k:field) : val :=
  Fun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Lemma triple_set_field : forall v1 p k v2,
  triple ((val_set_field k) p v2)
    (p`.k ~~> v1)
    (fun _ => p`.k ~~> v2).
Proof using.
  xwp. xapp. unfold hfield. xapp. xsimpl*.
Qed.

Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 56, f at level 0, format "t1 ''.' f" ) : trm_scope.

Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set'  t1 ''.' f  '':='  t2") : trm_scope.

End FieldAccessDef.

Global Opaque hfield.

Hint Resolve triple_get_field triple_set_field : triple.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Extra demo programs *)

Module ExtraDemoPrograms.
Export SLFProgramSyntax.


(* ########################################################### *)
(** ** The decrement function *)

(*
[[
   let decr p =
       let n = !p in
       let m = n - 1 in
       p := m
]]
*)

Definition decr : val :=
  Fun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '- 1 in
    'p ':= 'm.

Lemma triple_decr : forall (p:loc) (n:int),
  triple (trm_app decr p)
    (p ~~> n)
    (fun _ => p ~~> (n-1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl*.
Qed.

Hint Resolve triple_decr : triple.


(* ################################################ *)
(** *** Definition and verification of [mysucc]. *)

(** Here is another example, the function:
[[
   let mysucc n =
      let r = ref n in
      incr r;
      let x = !r in
      free r;
      x
]]

  Note that this function has the same behavior as [succ],
  but its implementation makes use of the [incr] function
  from above. *)

Definition mysucc : val :=
  Fun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    Let 'x := '! 'r in
    val_free 'r ';
    'x.

Lemma triple_mysucc : forall n,
  TRIPLE (trm_app mysucc n)
    PRE \[]
    POST (fun v => \[v = n+1]).
Proof using.
  xwp. xapp. intros r. xapp. xapp. xapp. xval. xsimpl*.
Qed.


(* ################################################ *)
(** *** Definition and verification of [myfun]. *)

(** Here is an example of a function involving a local function definition.

[[
   let myfun p =
      let f = (fun () => incr p) in
      f();
      f()
]]

*)

Definition myfun : val :=
  Fun 'p :=
    Let 'f := (Fun_ 'u := incr 'p) in
    'f '() ';
    'f '().

Lemma triple_myfun : forall (p:loc) (n:int),
  TRIPLE (trm_app myfun p)
    PRE (p ~~> n)
    POST (fun _ => p ~~> (n+2)).
Proof using.
  xwp.
  xfun (fun (f:val) => forall (m:int),
    TRIPLE (f '())
      PRE (p ~~> m)
      POST (fun _ => p ~~> (m+1))); intros f Hf.
  { intros. applys Hf. clear Hf. xapp. xsimpl. }
  xapp.
  xapp.
  replace (n+1+1) with (n+2); [|math]. xsimpl.
Qed.


End ExtraDemoPrograms.
