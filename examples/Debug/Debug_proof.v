Set Implicit Arguments.
From CFML Require Import WPLib WPValid.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Debug_ml.

(*Close Scope wp_scope.

Notation "'LetX' x ':=' F1 'in' F2" :=
 ( (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  only printing,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetX'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'").
*)

Notation "'int'" := (Z%type).








(********************************************************************)
(** ** RB Tree *)

(**)

Lemma balance_cf_def : balance_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { unfold Wpgen_negpat. intros. lets R : (@Enc_neq_inv _ (@Enc_tuple4 color_ _ rbtree_  _ int _ rbtree_  _)).
 eapply R. rew_enc. simpl.

    eapply __MatchHyp. }
  {  }
  { cf_val. }
  { cf_case.
    { cf_val. }
    { cf_match_fail. } }
Qed.



  


(********************************************************************)
(** ** CF proof for size and lookup *)

(*
(*

let size = function
  | Leaf x -> 1
  | Node (w, _, _) -> w

let rec lookup_tree i = function
  | Leaf x -> if i = 0 then x else raise OutOfBound
  | Node (w, t1, t2) ->
      if i < w/2
        then lookup_tree i t1
        else lookup_tree (i - w/2) t2

let rec lookup i = function
  | [] -> raise OutOfBound
  | Zero :: ts -> lookup i ts
  | One t :: ts ->
     if i < size t
        then lookup_tree i t
        else lookup (i - size t) ts

*)

Lemma size_cf_def : size_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_val. }
  { cf_case.
    { cf_val. }
    { cf_match_fail. } }
Qed.

Lemma lookup_tree_cf_def : lookup_tree_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_letval. intros x. cf_if. { cf_val. } { cf_match_fail. } }
  { cf_case.
(* cf_inlined_if_needed. cf_if.
    { cf_val. }
    { cf_match_fail. } }
Qed.
*)
Abort.

Lemma lookup_cf_def : lookup_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_fail. }
  { cf_case.
    { destruct d; tryfalse. cf_case_eq_end.
      cf_app. }
    { cf_case.
      { destruct d; tryfalse; inverts H1. cf_case_eq_end.
        cf_let.
        { cf_app. }
        { intros x. cf_if.
          { cf_app. }
          { cf_let.
            { cf_app. }
            { intros y. cf_app. } } } }
     { cf_match_fail. destruct d; tryfalse. } } }
Qed.
*)


(********************************************************************)
(** ** CF proof for prim *)


Lemma prim_cf_def : prim_cf_def__.
Proof using.
  cf_main.
  cf_if.
  { cf_val. }
  { cf_val. }
Qed.

Lemma prim_cf_def' : prim_cf_def__.
Proof using.
  cf_main.
  cf_inlined_if_needed. cf_if.
  { cf_inlined_if_needed. cf_val. }
  { cf_inlined_if_needed. cf_val. }
Qed.

Lemma prim_cf_def'' : prim_cf_def__.
Proof using.
  cf_main.
  eapply Lifted_let_inlined; [ applys structural_mkstruct | | ].
  { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
    { applys himpl_wpgen_app. applys triple_not. }
    { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
      { applys himpl_wpgen_app. applys triple_infix_bar_bar__. }
      { applys himpl_wpgen_app. applys triple_infix_amp_amp__. } } }
  { cf_if.
    { eapply Lifted_let_inlined; [ applys structural_mkstruct | | ].
      { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
        { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
          { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
Abort.


(********************************************************************)
(** ** CF proof for polydepth *)



(*
let rec polydepth : 'a. 'a poly -> int = fun s ->
  match s with
  | Empty _ -> 0
  | Pair s2 -> 1 + polydepth s2
*)


Lemma polydepth_cf_def : polydepth_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_val. }
  { cf_case.
    { cf_let.
      { cf_app. }
      { intros n. cf_inlined_app. cf_val. } }
    { cf_match_fail. } }
Qed.


Lemma polydepth_cf_def' : polydepth_cf_def__.
Proof using.
  cf_main.
  applys Lifted_case.
  { intros HN. unfold Wpgen_negpat. intros. applys Enc_neq_inv. applys HN. }
  { unfold Lifted. intros A EA Q.
    xsimpl. introv E. destruct s; tryfalse.
    applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ]. simpls. inverts E.
    applys Lifted_val; [ reflexivity ]. }
  { intros N1. unfold Lifted. intros A EA Q.
    applys Lifted_case.
    { intros HN. hnf. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Lifted. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct s as [|s2]. 1:{ false. }
      rew_enc in E. inverts E.
      applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Lifted_let; [ | | applys structural_mkstruct ].
      { applys Lifted_app; [ reflexivity ]. }
      { intros n. applys Lifted_inlined_fun; [ applys triple_infix_plus__ |  ].
        applys Lifted_val; [ reflexivity ]. } }
    { intros N2. applys Lifted_fail_false.
      destruct s; try false*. } }
Qed.


(********************************************************************)
(** ** CF proof for bools *)

(*
let bools b =

  if true then b || false else b && true
*)

Lemma bools_cf_def : bools_cf_def__.
Proof using.
  cf_main.
  applys Lifted_if; [ reflexivity | | ].
  { applys Lifted_inlined_fun; [ applys triple_infix_bar_bar__ | ].
    applys Lifted_val; [ reflexivity ]. }
  { applys Lifted_inlined_fun; [ applys triple_infix_amp_amp__ | ].
    applys Lifted_val; [ reflexivity ]. }
Qed.

Lemma bools_cf_def' : bools_cf_def__.
Proof using.
  cf_main. cf_if.
  { cf_inlined_app. cf_val. }
  { cf_inlined_app. cf_val. }
Qed.



(********************************************************************)
(** ** CF proof for pair_swap *)

(*
let pair_swap (x,y) =
  (y,x)
*)

Lemma pair_swap_cf_def : pair_swap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Lifted_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Lifted. intros A EA Q.
    xsimpl. intros x y E.
    destruct x0__ as [X Y]. rew_enc in E. inverts E.
    do 2 applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Lifted_val; [ reflexivity ]. }
  { intros N. applys Lifted_fail_false.
    destruct x0__. false N. reflexivity. }
Qed.



(********************************************************************)
(** ** CF proof for list map *)

(*
let rec listmap f l =
  match l with
  | [] -> []
  | x::t -> f x :: listmap f t
*)


Lemma listmap_cf_def : listmap_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_val. }
  { cf_case. cf_let.
    { cf_app. }
    { intros n. cf_let.
       { cf_app. }
       { intros m. cf_val. } }
    { cf_match_fail. } }
Qed.

(* not maintained
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Lifted_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Lifted. intros A EA Q.
    xsimpl. introv HN. destruct x0__. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Lifted_val; [ reflexivity ]. }
  { intros N1. unfold Lifted. intros A EA Q.
   applys Lifted_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Lifted. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Lifted_let; [ | | applys structural_mkstruct ].
      { applys Lifted_app; [ reflexivity ]. }
      { intros t2.
        applys Lifted_let; [ | | applys structural_mkstruct ].
        { applys Lifted_app; [ reflexivity ]. }
        { intros r. applys Lifted_val; [ reflexivity ]. } } }
    { intros N2. applys Lifted_fail_false.
      destruct l; try false*. } }
Qed.
*)


(********************************************************************)
(** ** CF proof for custom list map *)

(*
type 'a mylist = Nil | Cons of 'a * 'a mylist

let rec mymap f l =
  match l with
  | Nil -> Nil
  | Cons(x,t) -> Cons (f x, mymap f t)
*)

Lemma mymap_cf_def : mymap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Lifted_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Lifted. intros A EA Q.
    xsimpl. intros HN. destruct l. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Lifted_val; [ reflexivity ]. }
  { intros N1.
    unfold Lifted. intros A EA Q.
   applys Lifted_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Lifted. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Lifted_let; [ | | applys structural_mkstruct ].
      { applys Lifted_app; [ reflexivity ]. }
      { intros t2.
        applys Lifted_let; [ | | applys structural_mkstruct ].
        { applys Lifted_app; [ reflexivity ]. }
        { intros r. applys Lifted_val; [ reflexivity ]. } } }
    { intros N2. applys Lifted_fail_false.
      destruct l; try false*. } }
Qed.


(********************************************************************)
(** ** CF proof for id *)

(*
let id x = x
*)

Lemma id_cf_def : id_cf_def__.
Proof using.
  cf_main.
  applys Lifted_val; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for apply *)

(*
let apply f x = f x
*)

Lemma apply_cf_def : apply_cf_def__.
Proof using.
  cf_main.
  applys Lifted_app; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for idapp *)

(*
let idapp =
  let a = id 1 in
  let b = id true in
  2
*)

Lemma idapp_cf_def : idapp_cf_def__.
Proof using.
  cf_main.
  (* hnf. introv CF. applys Triple_of_CF_and_Lifted (rm CF); try reflexivity.
  unfold Wptag, dyn_to_val; simpl. xwpgen_simpl. *)
  applys Lifted_let; [ | | applys structural_mkstruct ].
  { applys Lifted_app; [ reflexivity ]. }
  { intros a.
    applys Lifted_let; [ | | applys structural_mkstruct ].
    { applys Lifted_app; [ reflexivity ]. }
    { intros b.
      applys Lifted_val; [ reflexivity ]. } }
Qed.


(********************************************************************)
(** ** CF proof for f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)

Lemma f_cf_def : f_cf_def__.
Proof using.
  cf_main.
  applys Lifted_let; [ | | applys structural_mkstruct ].
  { applys Lifted_app; [ reflexivity ]. }
  { intros X. cf_inlined.
    applys Lifted_app; [ reflexivity ]. }
Qed.



(********************************************************************)
(** ** Verification of f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)


Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.


(*

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)








