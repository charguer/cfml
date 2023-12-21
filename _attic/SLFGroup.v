

(* EX1! (setsucc) *)
(** . 

[[
   let setsucc p q =
      q := !p + 1
]]
*)


Definition setsucc : val :=
  Fun 'p 'q :=
    Let 'n := '!'p in
    Let 'm := 'n '+ 1 in
    'q ':= 'm.

(* SOLUTION *)
Lemma triple_setsucc_distinct : forall (p q:loc) (n m:int),
  triple (setsucc p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl. 
Qed.

Lemma triple_setsucc_aliased : forall (p:loc) (n:int),
  triple (setsucc p p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl. 
Qed.

Lemma triple_setsucc_common : forall (p q:loc) (n m:int),
  triple (setsucc p q)
    (p ~~> n \* If p = q then \[] else q ~~> m)
    (fun _ => q ~~> (n+1) \* If p = q then \[] else p ~~> n).
Proof using.
  xwp. xapp. xapp. case_if.
  { subst. xapp. xsimpl. }
  { xapp. xsimpl. } 
Qed.

From TLC Require Import LibMonoid LibContainer LibSet LibMap.

Definition sep_monoid := 
  monoid_make hstar hempty.

Definition RefIntGroup (M:map loc int) : hprop :=
     fold sep_monoid (fun p n => p ~~> val_int n) M
  \* \[LibMap.finite M].

Implicit Types M : map loc int.
Implicit Types v : val.

Parameter triple_get_group : forall M p,
  p \indom M ->
  triple (val_get p)
    (RefIntGroup M)
    (fun v => \[v = val_int (M[p])] \* RefIntGroup M).

Parameter triple_set_group : forall M p n,
  p \indom M ->
  triple (val_set p n)
    (RefIntGroup M)
    (fun _ => RefIntGroup (M[p:=n])).


Lemma triple_setsucc_group : forall M p q,
  p \indom M ->
  q \indom M ->
  triple (setsucc p q)
    (RefIntGroup M)
    (fun _ => RefIntGroup (M[q:=M[p]+1])).
Proof using.
  introv Hp Hq. xwp. xapp triple_get_group. auto.
  xapp. xapp triple_set_group. auto. xsimpl.
Qed.

(* /SOLUTION *)

(** [] *)
