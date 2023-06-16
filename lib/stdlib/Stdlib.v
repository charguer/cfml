From CFML Require Import WPLib.
From CFML Require Import WPDisplay WPRecord.
Require Export Pervasives_ml Pervasives_proof.
(* TODO: error without the require wplib, custom wp is undeclared *)
Require Array_ml Array_proof.
Require List_ml List_proof.
Require Sys_ml Sys_proof.


(* TEMPORARY: USE FOR CF VALIDATION ONLY *)


(* TODO : relate to Pervasives_proof.ml *)

Axiom triple_infix_plus__ : forall (n1 n2:int),
  triple (infix_plus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).

Axiom triple_infix_amp_amp__ : forall (b1 b2:bool),
  triple (infix_amp_amp__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 && b2)]).

Axiom triple_infix_bar_bar__ : forall (b1 b2:bool),
  triple (infix_bar_bar__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 || b2)]).


Axiom triple_not : forall (b:bool),
  triple (not b)
    \[]
    (fun r => \[r = val_bool (!b)]).

Hint Resolve triple_not
 : triple_builtin.

Axiom triple_infix_minus__ : forall (n1 n2:int),
  triple (infix_minus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).

Axiom triple_ignore : forall (v:val),
  triple (val_ignore v)
    \[]
    (fun r => \[r = val_unit]).

Axiom triple_and : forall (b1 b2:bool),
  triple (val_and b1 b2)
    \[]
    (fun r => \[r = (b1 && b2)]).

Axiom triple_or : forall (b1 b2:bool),
  triple (val_or b1 b2)
    \[]
    (fun r => \[r = (b1 || b2)]).

Axiom triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = (negb b1)]).

(* TODO: use infix__ names? *)

Axiom triple_infix_lt__ : forall (n1 n2:int),
  triple (infix_lt__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 < n2)]).

Axiom triple_infix_lt_eq__ : forall (n1 n2:int),
  triple (infix_lt_eq__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 <= n2)]).

Axiom triple_infix_gt__ : forall (n1 n2:int),
  triple (infix_gt__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 > n2)]).

Axiom triple_infix_gt_eq__ : forall (n1 n2:int),
  triple (infix_gt_eq__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 >= n2)]).

(* TODO: triples
Definition val_abs : val :=
  Fun 'x :=
    If_ 'x '< 0 Then '- 'x Else 'x.

Definition val_min : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'x Else 'y.

Definition val_max : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'y Else 'x.
*)

Axiom triple_infix_eq__ : forall (n1 n2:int),
  triple (infix_eq__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 = n2)]).


Hint Resolve
  triple_infix_plus__ triple_infix_bar_bar__ triple_infix_amp_amp__
  triple_infix_minus__ triple_ignore triple_and triple_or
  triple_neg triple_infix_lt__ triple_infix_lt_eq__
  triple_infix_gt__ triple_infix_gt_eq__
  triple_infix_eq__ : triple_builtin.
