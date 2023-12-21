

(* ########################################################### *)
(** ** A Fixed-Point Combinator *)

(*
untyped OCaml:
 h is a functional, that is, a function that expects as first argument
 a function for performing recursive calls.

 let landin h =
   let p = ref () in
   let g x = (!p) x in
   let f x = h g x in
   set p f;
   f

*)

Definition landin : val :=
  Fun 'h :=
    Let 'p := 'ref '() in
    Let 'g := (Fun_ 'x :=
      Let 'f := '! 'p in
      'f 'x) in
    Let 'f := (Fun_ 'x :=
      'h 'g 'x) in
    'p ':= 'f ';
    'f.

(** Simplified specification where the well-founded relation is over the argument only,
    and not also over the state *)

Lemma triple_landin : forall A (C:A->val) (R:binary A) (JI:A->hprop) (JO:A->val->hprop) (h:val),
  wf R ->
  (forall H (g:val) i,
     (forall i', R i' i -> triple (g (C i')) (H \* JI i') (fun r => H \* JO i' r)) ->
     triple (h g (C i)) (H \* JI i) (fun r => H \* JO i r)) ->
  triple (landin h)
    \[]
    (fun f => \exists H, H \*
        \[forall i, triple (f (C i)) (H \* JI i) (fun r => H \* JO i r)]).
Proof.
  introv WR Hh. xwp. xapp. intros p.
  xfun. intros g Hg. xfun. intros f Hf.
  xapp. xval. sets H: (p ~~> f). xsimpl.
  intros x. induction_wf IH: WR x.
  xwp. xapp. xapp (Hh H).
  { intros x' Hx'. xwp. xapp. xapp. xapp IH. { auto. } xsimpl. }
  xsimpl.
Qed.

Arguments triple_landin [ A ]. (*  : clear implicits.*)
(* Need to invoke [xapp (triple_landin R (fun x => ..) (fun x y => ..))]
    where R is eg [downto 0]. *)

(* same def as repeat, but not recursive *)
Definition repeat' : val :=
  Fun 'f 'n :=
    Let 'h := (Fun_ 'g 'x :=
      Let 'b := ('x '> 0) in
      If_ 'b Then
        'f '() ';
        Let 'x2 := 'x '- 1 in
        'g 'f 'x2
      End) in
    Let 'f := landin 'h in
    'f 'n.

(** Proof: needs hiding of invariants to match [triple_repeat] *)
