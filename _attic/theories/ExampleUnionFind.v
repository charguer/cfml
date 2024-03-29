(**

This file formalizes Union-Find in plain Separation Logic,
using characteristic formulae.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From Sep Require Import LambdaCF LambdaStruct.
From TLC Require Import LibList.
Generalizable Variables A B.

Ltac auto_star ::= jauto.

Implicit Type p q : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Union find *)

From TLC Require Import LibListZ.

(* ---------------------------------------------------------------------- *)
(** Invariants *)

Implicit Type L : list int.
Implicit Type R : int->int.
Implicit Type x y z : int.

(** [repr L x z] asserts that [z] is the end of the
    path that starts from [x]. *)

Inductive repr L : int->int->Prop :=
  | repr_root : forall x,
      index L x ->
      x = L[x] ->
      repr L x x
  | repr_next : forall x y z,
      index L x ->
      y = L[x] ->
      x <> y ->
      repr L y z ->
      repr L x z.

(** [roots L R] captures the fact that [R] is the function
    that computes the roots described by the table [L]. *)

Definition roots L R :=
  forall x, index L x -> repr L x (R x).

(** [UF B] is a heap predicate that corresponds to a set of
    cells describing the union-find structure associated with
    the PER [R], which is a binary relation over locations. *)

Definition UF (n:int) (R:int->int) (p:loc) : hprop :=
  \exists (L:list int),
     Array (map val_int L) p
  \* \[n = length L /\ roots L R].


(* ---------------------------------------------------------------------- *)
(** Induction principle on the height of a [repr] derivation *)

(** Ideally, would be automatically generated by Coq *)

Section Reprn.
Implicit Type d : nat.

(** Copy-paste of the definition of [repr], plus a bound on the depth *)

Inductive reprn L : nat->int->int->Prop :=
  | reprn_root : forall d x,
      index L x ->
      x = L[x] ->
      reprn L d x x
  | reprn_next : forall d x y z,
      index L x ->
      y = L[x] ->
      x <> y ->
      reprn L d y z ->
      reprn L (S d) x z.

Hint Constructors repr reprn.
Hint Extern 1 (_ < _) => math.

Lemma reprn_lt : forall d d' L x z,
  reprn L d x z ->
  d < d' ->
  reprn L d' x z.
Proof.
  introv H. gen d'. induction H; introv N;
   (destruct d' as [|d']; [ false; math | autos* ]).
Qed.

Lemma reprn_of_repr : forall L x z,
  repr L x z ->
  exists d, reprn L d x z.
Proof.
  hint reprn_lt. introv H. induction H; try induct_height.
Qed.

Lemma repr_of_reprn : forall L d x z,
  reprn L d x z ->
  repr L x z.
Proof. introv H. induction* H. Qed.

End Reprn.

Hint Resolve repr_of_reprn.


(* ---------------------------------------------------------------------- *)
(** Basic lemmas about [repr] *)

Lemma repr_inj : forall z1 z2 L x,
  repr L x z1 ->
  repr L x z2 ->
  z1 = z2.
Proof using.
  introv H1 H2. gen z2.
  induction H1 as [x1 HI1 HE1 | x1 y1 z1 HI1 HE1 HN1 IH]; intros.
  { inverts H2; auto_false. }
  { inverts H2; auto_false. subst y1. applys* IHIH. }
Qed.

Arguments repr_inj : clear implicits.

Lemma repr_functional : forall L x z1 z2,
  repr L x z1 ->
  repr L x z2 ->
  z1 = z2.
Proof using.
  introv H1 H2. induction H1; inverts H2; try subst; auto_false.
Qed.

Lemma repr_inv_index_l : forall L x z,
  repr L x z ->
  index L x.
Proof using. introv H. inverts* H. Qed.

Lemma repr_inv_index_r : forall L x z,
  repr L x z ->
  index L z.
Proof using. introv H. induction* H. Qed.

Lemma repr_inv_L : forall L x z,
  repr L x z ->
  L[z] = z.
Proof using. introv H. induction~ H. Qed.

Lemma index_L : forall L R x,
  index L x ->
  roots L R ->
  index L (L[x]).
Proof using.
  introv HI HR. forwards M: HR HI. inverts M as.
  { congruence. }
  { intros. applys* repr_inv_index_l. }
Qed.

Hint Resolve repr_inv_index_l repr_inv_index_r index_L.

Lemma roots_inv_L : forall x L R,
  roots L R ->
  R x = x ->
  index L x ->
  L[x] = x.
Proof using.
  introv HR E Ix. forwards~ Hx: HR x.
  lets Ex: repr_inv_L Hx. congruence.
Qed.

Lemma roots_inv_L_root : forall x L R,
  roots L R ->
  index L x ->
  L[R x] = R x.
Proof using.
  introv HR Ix. forwards~ Hx: HR x. applys* repr_inv_L.
Qed.

Lemma roots_inv_R : forall x z L R,
  roots L R ->
  repr L x z ->
  R x = z.
Proof using.
  introv HR Hx. forwards* Hx': HR x.
  forwards~: repr_functional Hx Hx'.
Qed.

(* not used? *)
Lemma roots_inv_R_root : forall x L R,
  roots L R ->
  L[x] = x ->
  index L x ->
  R x = x.
Proof using.
  introv HR Lx Ix. forwards* Hx': HR x.
  inverts Hx'; congruence.
Qed.


(* ---------------------------------------------------------------------- *)
(** Lemmas for specifying and justifying the operations *)

Ltac auto_tilde ::=
  try solve [ jauto_set; solve [ eauto | congruence | math ] ].

(** Result of a link operation between [x] and [y] that results
    in establishing a link between the roots of [x] and [y]. *)

Definition link R x y :=
  fun i => If (R i = R x \/ R i = R y) then R y else R i.

Lemma link_related : forall R x y,
  R x = R y ->
  link R x y = R.
Proof using.
  introv E. applys fun_ext_1 ;=> i. unfold link. case_if as C.
  { destruct~ C. }
  { auto. }
Qed.

(* TODO: not used? *)
Lemma link_inv_related : forall R x y,
  R x = R y ->
  link R x y = R.
Proof using.
  introv E. extens ;=> i. unfold link. case_if as C.
  { rewrite E in C. destruct~ C. }
  { auto. }
Qed.

Lemma udpate_inv : forall L' L a b,
  L' = L[a:=b] ->
     (forall i, index L i -> index L' i)
  /\ (forall i, index L' i -> index L i)
  /\ (forall i, index L i -> i <> a -> L'[i] = L[i])
  /\ (index L a -> L'[a] = b).
Proof using.
  intros. subst. splits; intros.
  { rewrite~ @index_update_eq. }
  { rewrite~ @index_update_eq in H. }
  { rewrite~ @read_update_neq. }
  { rewrite~ @read_update_same. }
Qed.

Lemma repr_update_neq : forall L a b L' x z,
  repr L x z ->
  L' = L[a:=b] ->
  L[a] = a ->
  z <> a ->
  repr L' x z.
Proof using.
  introv M E R N. lets (I1&_&K1&_): udpate_inv (rm E).
  induction M.
  { applys~ repr_root. rewrite~ K1. }
  { applys~ repr_next y. rewrite~ K1. }
Qed.

Lemma repr_update_eq : forall L a b L' x,
  repr L x a ->
  L' = L[a:=b] ->
  index L b ->
  L[b] = b ->
  a <> b ->
  repr L' x b.
Proof using.
  introv M E Ib Rb N. lets (I1&_&K1&K2): udpate_inv (rm E).
  lets Ra: repr_inv_L M.
  gen_eq a': a. induction M; intros E.
  { subst x. applys~ repr_next b. rewrite~ K2.
    applys* repr_root. rewrite~ K1. }
  { applys~ repr_next y. rewrite~ K1. }
Qed.

Lemma roots_link : forall L R x y L' R',
  R' = link R x y ->
  roots L R ->
  L' = L [R x := R y] ->
  R x <> R y ->
  index L x ->
  index L y ->
  roots L' R'.
Proof using. (* Note: this proof uses hint [repr_inv_L] *)
  introv M HR E N Dx Dy. intros u Du.
  forwards~ Hx: roots_inv_L_root x HR.
  forwards~ Hy: roots_inv_L_root y HR.
  lets (I1&I2&_&_): udpate_inv E.
  rewrites (rm M). unfold link. case_if as C.
  { destruct C as [C|C].
    { rewrite <- C in E. applys~ repr_update_eq E. }
    { rewrite <- C. applys~ repr_update_neq E. } }
  { rew_logic in C. destruct C as [C1 C2]. applys~ repr_update_neq E. }
Qed.

Lemma roots_compress' : forall d L R a L' x,
  roots L R ->
  reprn L d x (R x) ->
  L' = L [a := R a] ->
  index L x ->
  index L a ->
  reprn L' d x (R x).
Proof using.
  introv HR M E Dx Da.
  forwards~ Ha: HR a. lets Ra: repr_inv_L Ha.
  lets (I1&I2&K1&K2): udpate_inv E.
  gen_eq z: (R x). induction M; introv Ez.
  { applys~ reprn_root. tests C: (x = a).
    { rewrite~ K2. }
    { rewrite~ K1. } }
  { tests C: (x = a).
    { subst z. asserts~ Na: (a <> R a).
      applys~ reprn_next (R a).
      { rewrite~ K2. }
      { applys~ reprn_root. rewrite~ K1. } }
    { forwards~ Ez': roots_inv_R y z HR.
      applys~ reprn_next y. { rewrite~ K1. } } }
Qed.

(* derivable from above *)
Lemma roots_compress : forall L R a L',
  roots L R ->
  L' = L [a := R a] ->
  index L a ->
  roots L' R.
Proof using.
  introv HR E Da. intros x Dx.
  forwards~ Ha: HR a. lets Ra: repr_inv_L Ha.
  lets (I1&I2&K1&K2): udpate_inv E. forwards~ M: HR x.
  gen_eq z: (R x). induction M; introv Ez.
  { applys~ repr_root. tests C: (x = a).
    { rewrite~ K2. }
    { rewrite~ K1. } }
  { tests C: (x = a).
    { subst z. asserts~ Na: (a <> R a).
      applys~ repr_next (R a).
      { rewrite~ K2. }
      { applys~ repr_root. rewrite~ K1. } }
    { forwards~ Ez': roots_inv_R y z HR.
      applys~ repr_next y. { rewrite~ K1. } } }
Qed.



(* ---------------------------------------------------------------------- *)
(** Function to get the root *)

Definition val_root :=
  ValFun 'p 'x :=
    LetFix 'f 'x :=
      Let 'y := val_array_get 'p 'x in
      If_ val_eq 'x 'y
        Then 'x
        Else 'f 'y
      in
    'f 'x.

Hint Rewrite @index_map_eq : rew_array. (*--TODO  move *)


Lemma triple_root : forall n R p x,
  index n x ->
  triple (val_root p x)
    (UF n R p)
    (fun r => \[r = R x] \* UF n R p).
Proof using.
  introv Dx. xcf. xval as F ;=> EF.
  unfold UF. xtpull ;=> L (Hn&HR).
  forwards~ Ix: index_of_index_length' (rm Dx) Hn.
  forwards~ Hx: HR x.
  forwards (d&Hx'): reprn_of_repr Hx.
  applys mklocal_erase.
  gen x. induction_wf IH: lt_wf d. hide IH. intros.
  rewrite EF. xcf. rewrite <- EF.
  xapp as vy. rew_array~. rewrite (@read_map int _ val _); auto.
  (* --todo: should be rewrite read_map. *)
  intros Evy. subst vy.
  xapps. xif ;=> C; inverts Hx' as; try solve [ intros; false ].
  { introv _ _ Ex. xvals~. }
  { rename d0 into d. introv _ _ Nx. sets y: (L[x]).
    forwards~ ER: roots_inv_R y (R x) HR.
    xapp~ (>> IH d). xsimpl~. }
Qed.

Hint Extern 1 (Register_spec val_root) => Provide triple_root.


(* ---------------------------------------------------------------------- *)
(** Compression function *)

Definition val_compress :=
  ValFun 'p 'x 'z :=
    LetFix 'f 'x :=
      If_ 'x '<> 'z Then
        Let 'y := val_array_get 'p 'x in
        val_array_set 'p 'x 'z ;;;
        'f 'y
      End in
    'f 'x.

Hint Resolve index_map.

Lemma triple_compress : forall n R p x z,
  index n x ->
  z = R x ->
  triple (val_compress p x z)
    (UF n R p)
    (fun r => UF n R p).
Proof using.
  introv Dx Ez. xcf. xval as F ;=> EF.
  unfold UF. xtpull ;=> L (Hn&HR).
  forwards~ Ix: index_of_index_length' (rm Dx) Hn.
  forwards~ Hx: HR x.
  applys mklocal_erase. (* TODO: avoid *)
  forwards (d&Hx'): reprn_of_repr Hx.
  gen L x. induction_wf IH: lt_wf d. hide IH. intros.
  rewrite EF. xcf. rewrite <- EF.
  xapps. xif ;=> C.
  { xapps~. xapp~ ;=> ? ->. rewrite (@read_map int _ val _); auto.
    (* --todo: should be rewrite read_map. *)
    inverts Hx' as; try solve [ intros; false ].
    introv _ Nx Ry. sets y: (L[x]). rename d0 into d.
    forwards~ ER: roots_inv_R y (R x) HR.
    rewrite <- map_update; auto.
    sets_eq L': (L[x:=z]).
    forwards~ (I1&I2&K1&K2): udpate_inv L' L x z.
    subst z. forwards~ HR': roots_compress L' HR.
    forwards~ Hy: HR' y.
    xapp~ (>> IH d).
    { subst L'. rew_array~. }
    { applys~ roots_compress' HR. }
    { xsimpl~. } }
  { xvals~. }
Qed.

Hint Extern 1 (Register_spec val_compress) => Provide triple_compress.


(** TODO: compress and find revisited using a loop *)

(* ---------------------------------------------------------------------- *)
(** Find function, with path compression *)

Definition val_find :=
  ValFun 'p 'x :=
    Let 'r := val_root 'p 'x in
    val_compress 'p 'x 'r ;;;
    'r.

Lemma triple_find : forall n R p x,
  index n x ->
  triple (val_find p x)
    (UF n R p)
    (fun r => \[r = R x] \* UF n R p).
Proof using.
  introv Ix. xcf. xapps~. xapps~. intros _. xvals~.
Qed.

Hint Extern 1 (Register_spec val_find) => Provide triple_find.


(* ---------------------------------------------------------------------- *)
(** Union function, with naive linking strategy *)

Definition val_union :=
  ValFun 'p 'x 'y :=
    Let 'r := val_find 'p 'x in
    Let 's := val_find 'p 'y in
    If_ 'r '<> 's Then
      val_array_set 'p 'r 's
    End.

Lemma triple_union : forall n R p x y,
  index n x ->
  index n y ->
  triple (val_union p x y)
    (UF n R p)
    (fun r => \exists R', UF n R' p \* \[R' = link R x y]).
Proof using.
  introv Dx Dy. xcf. xapps~. xapps~. xapps. xif ;=> C.
  { unfold UF. xtpull ;=> L (Hn&HR).
    forwards~ Ix: index_of_index_length' (rm Dx) Hn.
    forwards~ Iy: index_of_index_length' (rm Dy) Hn.
    xapp~. (* todo: xapps does not do the right thing *)
    { xpull ;=> r Er. rewrite~ <- map_update; auto.
      xsimpl~. rew_array~. split~.
      { applys~ roots_link L R x y. } } }
  { xvals~. rewrite~ link_related. }
Qed.

Hint Extern 1 (Register_spec val_union) => Provide triple_union.





(* ---------------------------------------------------------------------- *)
(** Initialization function *)

(* LATER

  let val_create =
    Vars N, I in
    Fun_ N :=
      val_array_init (Fun_ I := I) N.

Parameter val_create : val.

Parameter triple_create : forall n,
  n >= 0 ->
  triple (val_create n)
    \[]
    (fun r => \exists p R, \[r = val_loc p] \*
              UF R p \* \[forall i, index n i -> R i = i]).

*)
