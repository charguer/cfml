Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListSub LibListZ.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

(*******************************************)
(** Tactics *)

Ltac typeclass_only_if_class tt :=
  match goal with |- Inhab (list _) =>
    apply Inhab_list
    (* equivalent: typeclasses eauto with typeclass_instances *)
  end.

Hint Resolve Inhab_unit Inhab_list : haffine.

Ltac auto_star ::=
  try solve [
		autounfold in *; subst; rew_list; rew_int;
             try math_only_if_arith;
             try typeclass_only_if_class tt; jauto].

Module Import HintArith.
Hint Extern 1 => (try math_only_if_arith).
End HintArith.

(*******************************************)
(** About lists *)

Hint Rewrite length_drop : rew_list.
Hint Rewrite length_update drop_at_length : rew_list.
(* Note: TLC only exports these lemmas in [rew_listx] *)

(***************************************)
(** ** [list_cases] for bruteforcing case analyses on list read operations *)

Ltac list_cases_step tt :=
  first [ rewrite read_app
        | rewrite read_take | rewrite read_drop
        | rewrite read_cons_case
        | rewrite read_update_case
        | rewrite read_make ];
  repeat case_if; try math.

Ltac list_cases_core tt :=
  repeat (list_cases_step tt).

Tactic Notation "list_cases" :=
  autorewrite with rew_index in *; (* Some indexes can hide case_if. *)
  list_cases_core tt;
  rew_listx in *;
  autorewrite with rew_listp in *; try math.

Tactic Notation "list_cases" "*" :=
  list_cases; auto_star.

(**************************************)
(** Sums *)

Lemma sum_pos : forall (l:list int),
  Forall (fun x => 0 <= x) l ->
  0 <= sum l.
Proof using.
  introv Hl.
  unfold sum. induction l; rew_listx* in *; intros; unfold sum.
  destruct Hl as (?&Hl2).
  apply IHl in Hl2. math.
Qed.

Lemma length_concat_nonempty : forall A (L:list (list A)),
  Forall (<> nil) L ->
  length L <= length (concat L).
Proof using.
  intros A L.
  rewrite length_concat_eq_sum.
  induction L as [|a ?]; rew_listx*. intros (?&HL).
  asserts : (length a <> 0).
  { now destruct a. }
  rew_listx*. apply IHL in HL. math.
Qed.


(**************************************)
(* Update *)

Lemma update_nil : forall A (IA:Inhab A) (i:int) z,
  (@nil A)[i:=z] = nil.
Proof using.
  intros.
  now rewrite <- length_zero_eq_eq_nil, length_update, length_zero_eq_eq_nil.
Qed.

Hint Rewrite update_nil : rew_listx.

Lemma update_cons_case : forall A (IA:Inhab A) x (xs:list A) (i:int) z,
  0 <= i -> (* replaced in TLC with index (x::xs) i *)
  (x::xs)[i:=z] = If i = 0 then z::xs else x::xs[i-1:=z].
Proof using.
  intros.
  case_if as C.
  { rewrite C. rewrite* update_zero. }
  { destruct i; try easy.
    rewrite* update_cons_pos. }
Qed.

(* TODO Forall_update : l'ordre des deux arguments à changé *)

(***************************************)
(** Suffixes *)

Definition Suffix (A:Type) (xs ys:list A) : Prop :=
  exists n, xs = drop n ys /\ 0 <= n <= length ys.
  (* TODO consider: exists zs, ys = zs ++ xs
     or consider: prefix (rev xs) (rev ys)
       to reuse proofs on prefixes *)

Lemma Suffix_refl : forall A (xs:list A),
  Suffix xs xs.
Proof using.
  exists 0. rew_list*.
Qed.

Lemma Suffix_trans : forall A (xs ys zs:list A),
  Suffix xs ys ->
  Suffix ys zs ->
  Suffix xs zs.
Proof using.
  introv (n,(?,?)) (m,(?,?)).
  exists (n+m). subst. rewrite length_drop in *; try math.  (* NB: rew_listp does not handle length_drop *)
  split*; rew_listp*.
Qed.

Lemma Suffix_cons : forall (A:Type) (x:A) (xs:list A),
    Suffix xs (x::xs).
Proof using.
  exists 1. rew_listx*.
Qed.

Create HintDb suffix.
Hint Resolve Suffix_refl Suffix_trans Suffix_cons : suffix.

Lemma Suffix_length : forall A (l1 l2:list A),
  Suffix l1 l2 ->
  length l1 <= length l2.
Proof using.
  unfolds Suffix.
  introv (?,(?&?)).
  subst. rew_listp*.
Qed.

Lemma Suffix_mem : forall A (l1 l2:list A) x,
  Suffix l1 l2 ->
  mem x l1 ->
  mem x l2.
Proof using.
  introv (?,(?&?)) ?.
  subst. applys* mem_drop_inv.
Qed.

Lemma drop_eq_cons_inv : forall A (IA:Inhab A) x (xs L:list A) i,
   0 <= i <= length L ->
   drop i L = x :: xs ->
   L[i] = x /\ drop (1+i) L = xs.
Proof using.
  introv Hi Hd.
  lets* (l',(?,->)): (drop_spec i L).
  rewrite Hd. rewrite* read_middle.
  rewrite* drop_app_r. subst.
  math_rewrite (1 + length l' - length l' = 1).
  rew_listx*.
Qed.

Lemma Suffix_cons2_inv : forall A (x1 x2:A) (l1 l2: list A),
  Suffix (x1::l1) (x2::l2) ->
  Suffix l1 l2.
Proof using.
  introv (i,(E&?)).
  asserts ? : (i <> length (x2::l2)).
  { intros ?. subst.
    rewrite drop_at_length in E. congruence. }
  symmetry in E.
  apply drop_eq_cons_inv in E; try easy.
  math_rewrite (1+i = i + 1) in E.
  rew_listx* in E. rew_list in *.
  exists i. split*.
Qed.

Lemma Suffix_cons_inv : forall A (x1:A) (l1 l2: list A),
  Suffix (x1::l1) (l2) ->
  Suffix l1 l2.
Proof using.
  introv (i,(E&?)).
  asserts ? : (i <> length l2).
  { intros ?. subst.
    rewrite drop_at_length in E. congruence. }
  symmetry in E.
  apply drop_eq_cons_inv in E; try easy.
  exists (1+i). split*.
Qed.

Lemma Suffix_inv_split : forall A (l1 l2: list A),
  Suffix l1 l2 ->
  exists l, l2 = l ++ l1.
Proof using.
  introv (i,(E&?)).
  exists (take i l2). rewrite E.
  symmetry. applys* list_eq_take_app_drop.
Qed.

Lemma Suffix_read : forall A (IA:Inhab A) (l1 l2:list A) i,
  length l2 - length l1 <= i < length l2 ->
  Suffix l1 l2 ->
  l2[i] = l1[i - (length l2 - length l1)].
Proof using.
  intros A IA l1 l2 i Hi (n,(Hs1&Hs2)). subst.
  rewrite* length_drop in Hi.
  rewrite* read_drop; rewrite* length_drop.
  fequal. math.
Qed.

Lemma Suffix_Forall : forall A (l1 l2 : list A) P,
  Suffix l1 l2 ->
  Forall P l2 ->
  Forall P l1.
Proof using.
  introv Hs HL. rewrite Forall_eq_forall_mem.
  intros x Hx.
  apply* Forall_mem_inv. apply* Suffix_mem.
Qed.

(* NB: Using app_cancel_same_length_l from LibList generates
   a goal with LibList.length *)
Lemma app_cancel_same_length_l : forall A (l1 l2 t1 t2: list A),
  l1 ++ l2 = t1 ++ t2 ->
  length l1 = length t1 ->
  l1 = t1 /\ l2 = t2.
Proof using.
  intros.
  apply* app_cancel_same_length_l.
Qed.
