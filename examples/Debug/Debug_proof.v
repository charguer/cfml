Set Implicit Arguments.
From CFML Require Import WPLib.
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
(** ** Function calls: [xapp] *)

Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.

(*
Axiom triple_app_fix_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
*)

Lemma triple_apps_funs : forall F vs ts xs t H (Q:val->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (length vs) ->
  H ==> (wpgen (LibListExec.combine xs vs) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Admitted.

Lemma f_cf_def_proof : f_cf_def__.
Proof using.
  hnf. introv CF.
Transparent Triple.
  unfold Triple.
  unfold Trm_apps. rew_listx. rew_enc.
  eapply triple_apps_funs; try reflexivity. simpl.
  xchange (rm CF). unfold Wptag.


Qed.



(*
let f r n =
  let x = !r in
  r := x + n

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)

