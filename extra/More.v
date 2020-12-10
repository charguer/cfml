



(* ########################################################### *)
(* DO NOT DELETE ;: application of for loops *)

(*---*)
(** The example of [factorec] was a warmup. Let's now tackle a recursive
    function involving mutable state.

    The function [repeat_incr p m] makes [m] times a call to [incr p].
    Here, [m] is assumed to be a nonnegative value.

OCaml:
[[
    let rec repeat_incr p m =
      if m > 0 then (
        incr p;
        repeat_incr p (m - 1)
      )
]]
*)

Module ForExample.
Open Scope trm_scope.
Import SLFProgramSyntax DemoPrograms ExtraDemoPrograms.

Definition repeat_incr_using_for : val :=
  Fun 'p 'm :=
    For 'i = 0 To 'm Do
      incr 'p
    Done.

Lemma triple_repeat_incr_using_for : forall (m n:int) (p:loc),
  m >= 0 ->
  triple (repeat_incr_using_for p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).

(* EX2! (triple_repeat_incr) *)
(** Prove the function [triple_repeat_incr]. *)

Proof using. (* ADMITTED *)
  intros. applys triple_app_fun2. { reflexivity. }
skip.
simpl.
simpl.
  applys triple_let.
  { apply triple_ref. }
  intros r. simpl.
  apply triple_hexists. intros p.
  apply triple_hpure. intros ->.
  applys triple_seq.
  { applys triple_conseq_frame.
    { applys triple_incr. }
    { xsimpl. }
    { xsimpl. } }
  applys triple_let.
  { apply triple_get. }
  intros x. simpl.
  apply triple_hpure. intros ->.
  applys triple_seq.
  { applys triple_conseq_frame.
    { applys triple_free. }
    { xsimpl. }
    { xsimpl. } }
  applys triple_val.
  xsimpl. auto.


  introv Hm. xwp. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros n p Hm. xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. math. }
Qed. (* /ADMITTED *)

End ForExample.
(*---*)




(* ########################################################### *)
(* DO NOT DELETE : general spec for higher order repeat *)

(** Recall from the previous chapter, [SLFBasic], how the operation [repeat_incr]
    was specified using a [max] operator, allowing to remove the unnecessary
    assumption [n >= 0]. *)

(** The proof scripts exploits two properties of the [min] function. *)

Lemma min_r : forall n m,
  n >= m ->
  min n m = m.
Proof using. introv M. unfold min. case_if; math. Qed.

Lemma min_l : forall n m,
  n <= m ->
  min n m = n.
Proof using. introv M. unfold min. case_if; math. Qed.

Lemma min_eq_neg_max : forall n,
  min 0 n = n - (max 0 n).
Proof using.
  intros. tests C: (n >= 0).
  { rewrite min_l; [|math]. rewrite max_r; [|math]. math. }
  { rewrite min_r; [|math]. rewrite max_l; [|math]. math. }
Qed.

(* EX4? (triple_repeat') *)
(** State and prove a refined specification for [repeat] that does not require
    the hypothesis [n >= 0]. Hint: for reasoning about the [max] operator, exploit
    lemmas [max_l] and [max_r] stated in [SLFBasic]. *)

Lemma triple_repeat' : forall (I:int->hprop) (f:val) (n:int),
  (forall i, 0 <= i < n ->
    triple (f '())
      (I i)
      (fun u => I (i+1))) ->
  triple (repeat f n)
    (I (min 0 n))
    (fun u => I n).
Proof using. (* ADMITTED *)
  introv Hf.
  cuts G: (forall m, m <= n ->
    triple (repeat f m)
      (I (n - (max 0 m)))
      (fun u => I n)).
  { applys_eq G. { fequals. applys min_eq_neg_max. } }
  intros m. induction_wf IH: (downto 0) m. intros Hm.
  xwp. xapp. xif; intros C.
  { xapp. { rewrite max_r; math. } xapp. xapp. { math. } { math. }
    math_rewrite ((n - (max 0 m)) + 1 = n - (max 0 (m - 1))).
    { rewrite max_r; [|math]. rewrite max_r; [|math]. math. }
    xsimpl. }
  { xval. math_rewrite (n - (max 0 m) = n). { rewrite max_l; math. }
    xsimpl. }
Qed. (* /ADMITTED *)

(* [] *)

(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)









(** Inhabited type *)

Instance tree_Inhab : Inhab tree.
Proof using. apply (Inhab_of_val Leaf). Qed.



(* ########################################################### *)
(** ** Specification of a Higher-Order Fold on Mutable Lists *)

(** The operation [mfold_right] is the counterpart of [List.fold_right], for
    mutable lists.

[[
    let rec mfold_right f p a =
      if p = null
        then a
        else f p.head (mfold_right f p.tail a)
]]
*)

Definition mfold_right : val :=
  Fix 'g 'f 'p :=
    Let 'b := ('p '<> null) in
    If_ 'b Then
      Let 'x := 'p'.head in
      'f 'x ';
      Let 'q := 'p'.tail in
      'g 'f 'q
    End.


let rec fold_left f a l =
match l with
| [] -> a
| x::k -> fold_left f (f a x) k

let rec fold_right f l a =
match l with
| [] -> a
| x::k -> f x (fold_right f k a)




(** It is useful for folding and unfolding the definition of [Stack] to exploit
    the following reformulation of the definition. *)

Lemma Stack_eq : forall s L,
  Stack L s = (\exists p, s ~~~>`{ data := p; size := length L } \* (MList L p)).
Proof using. auto. Qed.



(**

Definition alloc : val :=
  .

Lemma triple_alloc : forall p n,
  triple (alloc p n)
    \[]
    (funloc s => s ~~~> `{ data := p ; size := n }).
*)






    However,
    developing and justifying the soundness of a higher-order Separation Logic
    for a higher-order programming language was a challenge tacked by Biering,
    Birkedal and Torp-Smith, and Yang (2005, 2006), using advanced mathematical
    constructions.

    The Ynot tool presents

Ni and Shao [2006] presented the XCAP framework


    By contrast, the use of a shallow embedding of Separation Logic in Coq,
    applied
    to the deep embedding of a higher-order imperative programming language,
    provides a direct construction of a higher-order logic.

Nanevski, Morrisett, Shinnar, Govereau, Birkedal (2008)
Chlipala, Malecha, Morrisett, Shinnar, Wisnesky (2009).


*)

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | xwp_simpl ]
        | applys xwp_lemma_fix; [ reflexivity | xwp_simpl ]
        | applys xwp_lemma_fun2; [ reflexivity | reflexivity | xwp_simpl ]
        | applys xwp_lemma_fix2; [ reflexivity | splits; reflexivity | xwp_simpl ]
        | applys xwp_lemma_fun3; [ reflexivity | splits; reflexivity | xwp_simpl ]
        | applys xwp_lemma_fix3; [ reflexivity | splits; reflexivity | xwp_simpl ]
        | applys xtriple_lemma ].
