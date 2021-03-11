Set Implicit Arguments.
From CFML Require Import WPLib.
Require Import Pervasives_ml Pervasives_proof.
From TLC Require Export LibListZ.  (* TODO: needed? *)
Require Import List_ml.
Generalizable Variables A.


Ltac auto_tilde ::= unfold measure; rew_list in *; try math; auto.
  (* Restored to default at the end of the file *)

(* TODO: find a nicer way to write [@TLC.LibList] *)

(************************************************************)
(** Functions treated directly by CFML *)

Lemma length_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (length l)
    PREC \[]
    POST \[= (@TLC.LibListZ.length _) l].
Proof using.
(* TODO: revive xfun_ind
  xcf. xfun_ind (@list_sub A) (fun f => forall (r:list A) n,
    app f [n r] \[] \[= n + LibListZ.length r]); xgo~.
*) skip.
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



(** Custom grammar for the display of characteristic formulae. *)

Declare Custom Entry wp.

Notation "<[ e ]>" :=
 e
 (at level 0, e custom wp at level 99) : wp_scope.

Notation "( x )" :=
 x
 (in custom wp,
  x at level 99) : wp_scope.

Notation "{ x }" :=
 x
 (in custom wp at level 0,
  x constr,
  only parsing) : wp_scope.

Notation "x" :=
 x
 (in custom wp at level 0,
  x constr at level 0) : wp_scope.

Notation "'Fail'" :=
 ((Wpgen_fail))
 (in custom wp at level 69) : wp_scope.

Notation "'Done'" :=
 ((Wpgen_done))
 (in custom wp at level 69) : wp_scope.

Notation "'Match' F" :=
 ((Wpgen_match F))
 (in custom wp at level 69,
  F custom wp at level 99) : wp_scope.

Notation "'Assert' F" :=
 ((Wpgen_assert F))
 (in custom wp at level 69,
  F custom wp at level 99) : wp_scope.

Notation "'Val' v" :=
 ((Wpgen_Val v))
 (in custom wp at level 69) : wp_scope.

Notation "'Let?' x ':=' F1 'in' F2" :=
 ((Wpgen_let F1 (fun x => F2)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'Let?'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.
 (* TODO: improve notation or deprecate it *)

Notation "'Let' x ':=' F1 'in' F2" :=
 ((Wpgen_let_typed F1 (fun x => F2)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetVal' x ':=' V 'in' F1" :=
 ((Wpgen_let_Val V (fun x => F1)))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'LetVal'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Alias' x ':=' V 'in' F1" :=
 ((Wpgen_alias V (fun x => F1)))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Alias'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Seq' F1 ; F2" :=
 ((Wpgen_seq F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' f x1 x2 .. xn" := (Wpgen_App_typed _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..)))
  (in custom wp at level 68,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.
(* DEPRECATED
Notation "'App' f v1 v2" :=
 ((wp (trm_app (trm_app f v1) v2)))
 (in custom wp at level 68, f, v1, v2 at level 0) : wp_scope.
*)

Notation "'If_' v 'Then' F1 'Else' F2" :=
 ((Wpgen_if_bool v F1 F2))
 (in custom wp at level 69,
  v constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
 ((Wpgen_while F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  format "'[v' '[' 'While'  F1  'Do'  ']' '/' '['   F2 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'To' n2 'Do' F1 'Done'" :=
 ((Wpgen_for_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'To'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'Downto' n2 'Do' F1 'Done'" :=
 ((Wpgen_for_downto_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'Downto'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.


(* DEPRECATED
Notation "'Fun' x '=>' F1" :=
 ((wpgen_fun (fun x => F1)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

Notation "'Fix' f x '=>' F1" :=
 ((wpgen_fix (fun f x => F1)))
 (in custom wp at level 69,
  f ident, x ident,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'Fix'  f  x  '=>'  F1  ']' ']'") : wp_scope.
*)

Notation "'LetFun' f ':=' B1 'in' F1" :=
 (Wpgen_let_fun (fun _ _ Q => \forall f1, \[B1] \-* (^F1 Q)))
 (in custom wp at level 69,
  f ident,
  B1 constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'LetFun'  f  ':='  B1  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.



(* TODO: generalize let-fun to recursive functions *)


(* Notation for Case is not reversible, but that's fine because we know that
   the argument P is always in practice the negation of a test that is visible in F1. *)

(* generic notation for arities that are not supported *)
Notation "'Case' F1 'Else' F2" :=
 ((Wpgen_case F1 _ F2))
 (in custom wp at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity, (* TODO: could be right? *)
  format "'[v' '[' 'Case' ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p 'Then' F1 'Else' F2" :=
 ((Wpgen_case (fun _ _ Q => \[v = p] \-* ^F1 Q) _ F2))
 (in custom wp at level 69,
  v constr at level 69,
  p constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

(* PRINTING FOR F1 in case pattern  -- TODO
Notation "v 'is' p { x1 x2 .. xn } 'Then' F1" :=
 (fun _ _ Q => hforall (fun x1 => hforall (fun x2 => .. (hforall (fun xn => \[v = p] \-* ^F1 Q)) ..)))
 (in custom wp at level 69,
  v constr at level 69,
  p constr at level 69,
  x1 binder,
  x2 binder,
  xn binder,
  F1 custom wp at level 99,
  left associativity
(*
  format "'[v' '[' 'Case'   v  'is'  p  { x1 .. xn }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'"*) ) : wp_scope.
*)

(*
Notation "'Case' v 'is' p { x1 } 'Then' F1 'Else' F2" :=
 ((Wpgen_case (fun _ _ Q => \forall x1, \[v = p] \-* ^F1 Q) _ F2))
 (in custom wp at level 69,
  v constr at level 69,
  p constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'   v  'is'  p  { x1 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.
DEPRECATED *)

(* FAILS, why?
Notation "'Case' v 'is' p { x1 x2 .. xn } 'Then' F1 'Else' F2" :=
 (Wpgen_case (fun _ _ Q => hforall (fun x1 => hforall (fun x2 => .. (hforall (fun xn => \[v = p] \-* ^F1 Q) _ F2) ..))))
 (in custom wp at level 69,
  v constr at level 69,
  p constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity
(*
  format "'[v' '[' 'Case'   v  'is'  p  { x1 .. xn }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'"*) ) : wp_scope.
*)

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.


(Wpgen_App_typed _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..)))
  (in custom wp at level 68,


(* TODO: generalize arity, and add support for when clauses
   TODO: do not attempt to currify the assumption associated with the when clause?
    this could simplify the tactic that handles the case *)



(* in [xcase_post H], H is either an equality [v = p], or a conjunction [v = p /\ istrue b]
   in case the hypothesis comes from testing a when-clause. *)

Ltac xcase_post_old H :=
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).

Ltac xcase_post H :=
  let aux1 tt := try solve [ discriminate | false; congruence ] in
  let aux2 E := symmetry in E; inverts E; xclean_trivial_eq tt in
  match type of H with
  | |- _ /\ _ => 
      try (
        let E := fresh "E" H in 
        destruct H as [H E];
        aux1 tt;
        aux2 E (* if inverts E, then keep the original conjunction *)
      )
  | |- _ -> 
      aux1 tt;
      try (aux2 H)
  end.

Ltac xcase_extract_hyps tt ::=
  pose ltac_mark;
  repeat (apply himpl_hforall_r; intro);
  apply hwand_hpure_r_intro; intro;
  gen_until_mark.


Lemma rev_append_spec : forall A `{EA:Enc A} (l1 l2:list A),
  SPEC (rev_append l1 l2)
    PREC \[]
    POST \[= LibList.rev l1 ++ l2].
Proof using.
  intros. gen l2. induction_wf IH: (@list_sub A) l1. xcf. xcf_go~.
Qed.

Hint Extern 1 (RegisterSpec rev_append) => Provide rev_append_spec.

Lemma rev_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (rev l)
    PREC \[]
    POST \[= (@TLC.LibList.rev _) l].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec rev) => Provide rev_spec.

Lemma append_spec : forall A `{EA:Enc A} (l1 l2:list A),
  SPEC (append l1 l2)
    PREC \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using.
Admitted. (*
  xcf. xfun_ind (@list_sub A) (fun f => forall (r:list A),
    app f [r] \[] \[= r ++ l2]); xgo*.
Qed. *)

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Lemma infix_at_spec : forall A `{EA:Enc A}(l1 l2:list A),
  SPEC (infix_at__ l1 l2)
    PREC \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec infix_at__) => Provide infix_at_spec.

Lemma concat_spec : forall A `{EA:Enc A} (l:list (list A)),
  SPEC (concat l)
    PREC \[]
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
     SPEC (f x) PREC (I t) POSTUNIT (I (t&x))) ->
  SPEC (iter f l)
    PREC (I nil)
    POSTUNIT (I l).
Proof using.
  =>> M. cuts G: (forall r t, l = t++r ->
    SPEC (iter f r) PREC (I t) POSTUNIT (I l)). { xapp~. xsimpl. }
  => r. induction_wf IH: (@LibList.length A) r. =>> E.
  xcf. xmatch; rew_list in E; inverts E; xgo~.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.

(** Alternative spec for [iter], with an invariant that
    depends on the remaining items, rather than depending
    on the processed items. *)

Lemma iter_spec_rest : forall A `{EA:Enc A} (l:list A) (f:func),
  forall (I:list A->hprop),
  (forall x t, SPEC (f x) PREC (I (x::t)) POSTUNIT (I t)) ->
  SPEC (iter f l) PREC (I l) POSTUNIT (I nil).
Proof using.
  introv M. xapp~ (>> __ (fun k => \exists r, \[l = k ++ r] \* I r)).
  { introv E. xtriple. xpull. intros r' E'. subst l.
    lets: app_cancel_l E'. subst r'.
    xapp. xsimpl~. }
  { xpull; introv E. rewrites (>> self_eq_app_l_inv E). xsimpl~. }
Qed. (* TODO: beautify this proof *)

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