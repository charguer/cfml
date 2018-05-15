(**

This file describes the syntax and semantics of a lambda calculus
with mutable heap. The language includes recursive functions, and a
couple of primitive functions. Records and arrays operations are
encoded using pointer arithmetics, and using the [alloc] operation
which allocates at once a requested number of consecutive memory cells.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibString LibList LibCore.
From Sep Require Export Fmap TLCbuffer.
Open Scope string_scope.


(* ********************************************************************** *)
(* * Source language syntax *)

(* ---------------------------------------------------------------------- *)
(** Representation of variables *)

Definition name := string.

Inductive var : Type :=
  | var_anon : var
  | var_name : name -> var.

Definition eq_name_dec := String.string_dec.

Definition name_eq (s1 s2:name) : bool :=
  if eq_name_dec s1 s2 then true else false.

Lemma name_eq_spec : forall s1 s2,
  name_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold name_eq. case_if; rew_bool_eq~.
Qed.

Definition var_eq (x1 x2:var) : bool :=
  match x1, x2 with
  | var_anon, var_anon => true
  | var_name s1, var_name s2 => name_eq s1 s2
  | _, _ => false
  end.

Lemma var_eq_spec : forall x1 x2,
  var_eq x1 x2 = isTrue (x1 = x2).
Proof using.
  intros. unfold var_eq. destruct x1; destruct x2; 
   try rewrite name_eq_spec; rew_bool_eq; auto_false*.
  { iff; congruence. } (* LATER:simplify*)
Qed.

Global Opaque name.


(* ---------------------------------------------------------------------- *)
(** Representation of locations and fields *)

Definition loc := nat.

Definition null : loc := 0%nat.

Definition field := nat.

Global Opaque field loc.


(* ---------------------------------------------------------------------- *)
(** Syntax of the source language *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_alloc : prim
  | val_eq : prim
  | val_sub : prim
  | val_add : prim
  | val_ptr_add : prim.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : var -> var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm.

(** The type of values is inhabited *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** Encoded constructs *)

(*
Definition trm_seq (t1:trm) (t2:trm) :=
  trm_let var_anon t1 t2.

Definition trm_fun (x:var) (t1:trm) :=
  trm_fix var_anon x t1.

Definition val_fun (x:var) (t1:trm) :=
  val_fix var_anon x t1.
*)

Notation "'trm_seq' t1 t2" := (trm_let var_anon t1 t2) 
  (at level 69, t1 at level 0, t2 at level 0).

Notation "'trm_fun' x t1" := (trm_fix var_anon x t1) 
  (at level 69, x at level 0, t1 at level 0).

Notation "'val_fun' x t1" := (val_fix var_anon x t1) 
  (at level 69, x at level 0, t1 at level 0).


(* ---------------------------------------------------------------------- *)
(** Coercions *)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.
Coercion var_name : name >-> var.


(* ********************************************************************** *)
(* * Source language semantics *)

(* ---------------------------------------------------------------------- *)
(** Definition of capture-avoiding substitution *)

Definition var_match (x1:var) (x2:var) : bool :=
  match x1,x2 with
  | var_name s1, var_name s2 => name_eq s1 s2
  | _,_ => false
  end.

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let aux_no_capture x t := if var_match x y then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if var_match x y then trm_val w else t
  | trm_fix f x t1 => trm_fix f x (if var_match f y then t1 else
                                   aux_no_capture x t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capture x t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  end.


(* ---------------------------------------------------------------------- *)
(** Characterization of values *)

Definition trm_is_val (t:trm) : Prop :=
  match t with
  | trm_val v => True
  | _ => False
  end.


(* ---------------------------------------------------------------------- *)
(** Big-step evaluation *)

Section Red.

Definition state := fmap loc val.

Local Open Scope fmap_scope.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types i : field.
Implicit Types b : bool.
Implicit Types n : int.

Inductive red : state -> trm -> state -> val -> Prop :=
  | red_val : forall m v,
      red m v m v
  | red_fix : forall m f x t1,
      red m (trm_fix f x t1) m (val_fix f x t1)
  | red_if : forall m1 m2 m3 b r t0 t1 t2,
      red m1 t0 m2 (val_bool b) ->
      red m2 (if b then t1 else t2) m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r
  | red_let : forall m1 m2 m3 x t1 t2 v1 r,
      red m1 t1 m2 v1 ->
      red m2 (subst x v1 t2) m3 r ->
      red m1 (trm_let x t1 t2) m3 r
  | red_app_arg : forall m1 m2 m3 m4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_app v1 v2) m4 r ->
      red m1 (trm_app t1 t2) m4 r
  | red_app_fun : forall m1 m2 v1 v2 x t r,
      v1 = val_fun x t ->
      red m1 (subst x v2 t) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_app_fix : forall m1 m2 v1 v2 f x t r,
      v1 = val_fix f x t ->
      red m1 (subst f v1 (subst x v2 t)) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_ref : forall ma mb v l,
      mb = (fmap_single l v) ->
      l <> null ->
      \# ma mb ->
      red ma (val_ref v) (mb \+ ma) (val_loc l)
  | red_get : forall m l v,
      fmap_data m l = Some v ->
      red m (val_get (val_loc l)) m v
  | red_set : forall m m' l v,
      m' = fmap_update m l v ->
      red m (val_set (val_loc l) v) m' val_unit
  | red_alloc : forall k n ma mb l,
      mb = fmap_conseq l k val_unit ->
      n = nat_to_Z k ->
      l <> null ->
      \# ma mb ->
      red ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  | red_add : forall m n1 n2 n',
      n' = n1 + n2 ->
      red m (val_add (val_int n1) (val_int n2)) m (val_int n')
  | red_sub : forall m n1 n2 n',
      n' = n1 - n2 ->
      red m (val_sub (val_int n1) (val_int n2)) m (val_int n')
  | red_ptr_add : forall l' m l n,
      (l':nat) = (l:nat) + n :> int ->
      red m (val_ptr_add (val_loc l) (val_int n)) m (val_loc l')
  | red_eq : forall m v1 v2,
      red m (val_eq v1 v2) m (val_bool (isTrue (v1 = v2)))
  | red_while : forall m1 m2 t1 t2 r,
      red m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      red m1 (trm_while t1 t2) m2 r
  | red_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (* LATER: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_for x v1 v2 t3) m4 r ->
      red m1 (trm_for x t1 t2 t3) m4 r
  | red_for : forall m1 m2 x n1 n2 t3 r,
      red m1 (
        If (n1 <= n2)
          then (trm_seq (subst x n1 t3) (trm_for x (n1+1) n2 t3))
          else val_unit) m2 r ->
      red m1 (trm_for x n1 n2 t3) m2 r.

  (* Remark: alternative for red_for rules.
    | red_for : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
        red m1 (
          (trm_seq (trm_let x n1 t3) (trm_for x (n1+1) n2 t3))
          val_unit) m2 r ->
        red m1 (trm_for x n1 n2 t3) m2 r
  *)


(* ---------------------------------------------------------------------- *)
(* ** Properties of variable matching *)

Lemma var_match_anon : forall x,
  var_match x var_anon = false.
Proof using. intros. destruct~ x. Qed.

Lemma var_match_true_inv : forall x1 x2,
  var_match x1 x2 = true ->
  x1 = x2.
Proof using. 
  introv M. destruct x1; destruct x2; simpls; auto_false.
  { rewrite name_eq_spec in M. rew_bool_eq in *. inverts* M. }
Qed.

Lemma var_match_false_inv : forall x1 x2,
  var_match x1 x2 = false ->
  x1 <> x2 \/ x1 = var_anon \/ x2 = var_anon.
Proof using. 
  introv M. destruct x1; destruct x2; simpls; auto_false.
  { rewrite name_eq_spec in M. rew_bool_eq in *. left. intros E. inverts* E. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of anonymous substitution *)

Lemma subst_anon : forall v t,
  subst var_anon v t = t.
Proof using.
  intros. induction t; simpl; 
   try solve [ repeat rewrite var_match_anon; fequals ].
Qed.



(* ---------------------------------------------------------------------- *)
(* ** Derived rules *)

Lemma red_fun : forall m x t1,
  red m (trm_fun x t1) m (val_fun x t1).
Proof using. intros. applys red_fix. Qed.

Lemma red_seq : forall m1 m2 m3 t1 t2 r1 r,
  red m1 t1 m2 r1 ->
  red m2 t2 m3 r ->
  red m1 (trm_seq t1 t2) m3 r.
Proof using. introv M1 M2. applys* red_let. rewrite* subst_anon. Qed.

Lemma red_ptr_add_nat : forall m l (f : nat),
  red m (val_ptr_add (val_loc l) (val_int f)) m (val_loc (l+f)%nat).
Proof using. intros. applys* red_ptr_add. math. Qed.

Lemma red_if_bool : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using. introv M1. applys* red_if. applys red_val. Qed.

Lemma red_for_le : forall m1 m2 m3 x n1 n2 t3 r,
  n1 <= n2 ->
  red m1 (subst x n1 t3) m2 val_unit ->
  red m2 (trm_for x (n1+1) n2 t3) m3 r ->
  red m1 (trm_for x n1 n2 t3) m3 r.
Proof using.
  introv N M1 M2. applys red_for. case_if.
  { applys red_seq. applys M1. applys M2. }
  { false; math. }
Qed.

Lemma red_for_gt : forall m x n1 n2 t3,
  n1 > n2 ->
  red m (trm_for x n1 n2 t3) m val_unit.
Proof using.
  introv N. applys red_for. case_if.
  { false; math. }
  { applys red_val. }
Qed.

End Red.


(* ********************************************************************** *)
(* * Notation for terms *)

(* ---------------------------------------------------------------------- *)
(** Notation for program variables *)

Notation "''a'" := ("a":var) : var_scope.
Notation "''b'" := ("b":var) : var_scope.
Notation "''c'" := ("c":var) : var_scope.
Notation "''d'" := ("d":var) : var_scope.
Notation "''e'" := ("e":var) : var_scope.
Notation "''f'" := ("f":var) : var_scope.
Notation "''g'" := ("g":var) : var_scope.
Notation "''h'" := ("h":var) : var_scope.
Notation "''i'" := ("i":var) : var_scope.
Notation "''j'" := ("j":var) : var_scope.
Notation "''k'" := ("k":var) : var_scope.
Notation "''l'" := ("l":var) : var_scope.
Notation "''m'" := ("m":var) : var_scope.
Notation "''n'" := ("n":var) : var_scope.
Notation "''o'" := ("o":var) : var_scope.
Notation "''p'" := ("p":var) : var_scope.
Notation "''q'" := ("q":var) : var_scope.
Notation "''r'" := ("r":var) : var_scope.
Notation "''s'" := ("s":var) : var_scope.
Notation "''t'" := ("t":var) : var_scope.
Notation "''u'" := ("u":var) : var_scope.
Notation "''v'" := ("v":var) : var_scope.
Notation "''w'" := ("w":var) : var_scope.
Notation "''x'" := ("x":var) : var_scope.
Notation "''y'" := ("y":var) : var_scope.
Notation "''z'" := ("z":var) : var_scope.

Notation "''a1'" := ("a1":var) : var_scope.
Notation "''b1'" := ("b1":var) : var_scope.
Notation "''c1'" := ("c1":var) : var_scope.
Notation "''d1'" := ("d1":var) : var_scope.
Notation "''e1'" := ("e1":var) : var_scope.
Notation "''f1'" := ("f1":var) : var_scope.
Notation "''g1'" := ("g1":var) : var_scope.
Notation "''h1'" := ("h1":var) : var_scope.
Notation "''i1'" := ("i1":var) : var_scope.
Notation "''j1'" := ("j1":var) : var_scope.
Notation "''k1'" := ("k1":var) : var_scope.
Notation "''l1'" := ("l1":var) : var_scope.
Notation "''m1'" := ("m1":var) : var_scope.
Notation "''n1'" := ("n1":var) : var_scope.
Notation "''o1'" := ("o1":var) : var_scope.
Notation "''p1'" := ("p1":var) : var_scope.
Notation "''q1'" := ("q1":var) : var_scope.
Notation "''r1'" := ("r1":var) : var_scope.
Notation "''s1'" := ("s1":var) : var_scope.
Notation "''t1'" := ("t1":var) : var_scope.
Notation "''u1'" := ("u1":var) : var_scope.
Notation "''v1'" := ("v1":var) : var_scope.
Notation "''w1'" := ("w1":var) : var_scope.
Notation "''x1'" := ("x1":var) : var_scope.
Notation "''y1'" := ("y1":var) : var_scope.
Notation "''z1'" := ("z1":var) : var_scope.

Notation "''a2'" := ("a2":var) : var_scope.
Notation "''b2'" := ("b2":var) : var_scope.
Notation "''c2'" := ("c2":var) : var_scope.
Notation "''d2'" := ("d2":var) : var_scope.
Notation "''e2'" := ("e2":var) : var_scope.
Notation "''f2'" := ("f2":var) : var_scope.
Notation "''g2'" := ("g2":var) : var_scope.
Notation "''h2'" := ("h2":var) : var_scope.
Notation "''i2'" := ("i2":var) : var_scope.
Notation "''j2'" := ("j2":var) : var_scope.
Notation "''k2'" := ("k2":var) : var_scope.
Notation "''l2'" := ("l2":var) : var_scope.
Notation "''m2'" := ("m2":var) : var_scope.
Notation "''n2'" := ("n2":var) : var_scope.
Notation "''o2'" := ("o2":var) : var_scope.
Notation "''p2'" := ("p2":var) : var_scope.
Notation "''q2'" := ("q2":var) : var_scope.
Notation "''r2'" := ("r2":var) : var_scope.
Notation "''s2'" := ("s2":var) : var_scope.
Notation "''t2'" := ("t2":var) : var_scope.
Notation "''u2'" := ("u2":var) : var_scope.
Notation "''v2'" := ("v2":var) : var_scope.
Notation "''w2'" := ("w2":var) : var_scope.
Notation "''x2'" := ("x2":var) : var_scope.
Notation "''y2'" := ("y2":var) : var_scope.
Notation "''z2'" := ("z2":var) : var_scope.

Notation "''a3'" := ("a3":var) : var_scope.
Notation "''b3'" := ("b3":var) : var_scope.
Notation "''c3'" := ("c3":var) : var_scope.
Notation "''d3'" := ("d3":var) : var_scope.
Notation "''e3'" := ("e3":var) : var_scope.
Notation "''f3'" := ("f3":var) : var_scope.
Notation "''g3'" := ("g3":var) : var_scope.
Notation "''h3'" := ("h3":var) : var_scope.
Notation "''i3'" := ("i3":var) : var_scope.
Notation "''j3'" := ("j3":var) : var_scope.
Notation "''k3'" := ("k3":var) : var_scope.
Notation "''l3'" := ("l3":var) : var_scope.
Notation "''m3'" := ("m3":var) : var_scope.
Notation "''n3'" := ("n3":var) : var_scope.
Notation "''o3'" := ("o3":var) : var_scope.
Notation "''p3'" := ("p3":var) : var_scope.
Notation "''q3'" := ("q3":var) : var_scope.
Notation "''r3'" := ("r3":var) : var_scope.
Notation "''s3'" := ("s3":var) : var_scope.
Notation "''t3'" := ("t3":var) : var_scope.
Notation "''u3'" := ("u3":var) : var_scope.
Notation "''v3'" := ("v3":var) : var_scope.
Notation "''w3'" := ("w3":var) : var_scope.
Notation "''x3'" := ("x3":var) : var_scope.
Notation "''y3'" := ("y3":var) : var_scope.
Notation "''z3'" := ("z3":var) : var_scope.

Open Scope var_scope.

(* Note: for variable names with several letters, add your own definition *)


(* ---------------------------------------------------------------------- *)
(** Notation for concrete programs *)

Notation "'()" := val_unit : trm_scope.

Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Let' 'Rec' f x ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x t1) t2)
  (at level 69, f at level 0, x at level 0, right associativity,
  format "'[v' '[' 'Let'  'Rec'  f  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 ;;; t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity, only parsing,
   format "'[v' '[' t1 ']'  ;;;  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x ':=' t" :=
  (trm_fix f x t)
  (at level 69, f at level 0, x at level 0) : trm_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'ValFix' f x ':=' t" :=
  (val_fix f x t)
  (at level 69, f at level 0, x at level 0) : trm_scope.

Notation "'ValFix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'ValFix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'ValFun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'ValFun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'ValFun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'LetFun' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

Notation "'LetFun' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 t1)) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'LetFun' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'LetFix' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

Notation "'LetFix' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 t1)) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'LetFix' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'While' t1 'Do' t2 'Done'" :=
  (trm_while t1 t2)
  (at level 69, t2 at level 68,
   format "'[v' 'While'  t1  'Do'  '/' '[' t2 ']' '/'  'Done' ']'")
   : trm_scope.

Notation "'For' x ':=' t1 'To' t2 'Do' t3 'Done'" :=
  (trm_for x t1 t2 t3)
  (at level 69, x at level 0, (* t1 at level 0, t2 at level 0, *)
   format "'[v' 'For'  x  ':='  t1  'To'  t2  'Do'  '/' '[' t3 ']' '/'  'Done' ']'")
  : trm_scope.

Notation "'ref t" :=
  (val_ref t)
  (at level 67) : trm_scope.

Notation "'! t" :=
  (val_get t)
  (at level 67) : trm_scope.

Notation "t1 ':= t2" :=
  (val_set t1 t2)
  (at level 67) : trm_scope.

Notation "t1 '+ t2" :=
  (val_add t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '- t2" :=
  (val_sub t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '= t2" :=
  (val_eq t1 t2)
  (at level 69) : trm_scope.




(* ********************************************************************** *)
(* * More on substitutions *)

(* ---------------------------------------------------------------------- *)
(** Properties of substitution *)

(** Substitutions for two distinct variables commute. *)

Lemma subst_subst_neq : forall x1 x2 v1 v2 t,
  x1 <> x2 ->
  subst x2 v2 (subst x1 v1 t) = subst x1 v1 (subst x2 v2 t).
Proof using.
  introv N. induction t; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  repeat case_if; simpl; repeat case_if~.
  { false. destruct v; destruct x1; destruct x2; false. simpls.
    rewrite name_eq_spec in *. rew_bool_eq in *. false. }
Qed. (* LATER: simplify *)

(** Substituting for a variable that has just been substituted
    does not further modify the term. *)

Lemma subst_subst_same : forall x v1 v2 t,
  subst x v2 (subst x v1 t) = subst x v1 t.
Proof using.
  intros. induction t; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
Qed.


(* ---------------------------------------------------------------------- *)
(** Distinct variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.

(** [var_distinct xs] asserts that [xs] consists of a list of distinct variables. *)

Fixpoint var_distinct (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => var_fresh x xs' && var_distinct xs'
  end.


(* ---------------------------------------------------------------------- *)
(** Iterated substitution *)

(** [ctx] describes a list of bindings *)

Definition ctx := list (var*val).

(** [ctx_empty] describes the empty context *)

Definition ctx_empty : ctx :=
  nil.

(** [ctx_add x v E] extends [E] with a binding from [x] to [v] *)

Definition ctx_add (x:var) (v:val) (E:ctx) :=
  (x,v)::E.

(** [ctx_rem x E] removes all bindings on [x] stored in [E] *)

Fixpoint ctx_rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E' =>
    let E'' := ctx_rem x E' in
    if var_eq x y then E'' else (y,v)::E''
  end.

(** [ctx_lookup x E] returns
    - [None] if [x] is not bound in [E]
    - [Some v] if [x] is bound to [v] in [E]. *)

Fixpoint ctx_lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E' => if var_match x y
                   then Some v
                   else ctx_lookup x E'
  end.

(** [ctx_fresh x E] asserts that [x] is not bound in [E] *)

Fixpoint ctx_fresh (x:var) (E:ctx) : bool :=
  match E with
  | nil => true
  | (y,v)::E' => if var_eq x y then false else ctx_fresh x E'
  end.

(* todo: deprecated
Definition ctx_fresh (x:var) (E:ctx) : Prop :=
  ctx_lookup x E = None.
*)

(** [substs E t] substitutes all the bindings from [E] inside [t] *)

Fixpoint substs (E:ctx) (t:trm) :=
  match E with
  | nil => t
  | (x,v)::E' => substs E' (subst x v t)
  end.


(* ---------------------------------------------------------------------- *)
(** Properties of iterated substitution *)

(** Simplification equalities for [ctx_rem] *)

Lemma ctx_rem_same : forall x v E,
  ctx_rem x ((x,v)::E) = ctx_rem x E.
Proof using. intros. simpl. rewrite var_eq_spec. case_if~. Qed.

Lemma ctx_rem_neq : forall x y v E,
  x <> y ->
  ctx_rem x ((y,v)::E) = (y,v)::(ctx_rem x E).
Proof using. intros. simpl. rewrite var_eq_spec. case_if~. Qed.

(** Auxiliary results *)

Lemma ctx_rem_fresh : forall x E,
  ctx_fresh x E ->
  ctx_rem x E = E.
Proof using.
  introv M. induction E as [|(y,v) E'].
  { auto. } 
  { simpls. rewrite var_eq_spec in *. case_if. fequals. rewrite~ IHE'. }
Qed.

(** Substituting for [E] without [x] then substituting for [x]
    is equivalent to substituting for [x] then for [E]
    (even if [x] is bound in [E]). *)

Lemma subst_substs_ctx_rem_same : forall E x v t,
    subst x v (substs (ctx_rem x E) t)
  = substs E (subst x v t).
Proof using.
  intros E. induction E as [|(y,w) E']; simpl; intros.
  { auto. }
  { rewrite var_eq_spec. case_if.
    { subst. rewrite IHE'. rewrite~ subst_subst_same. }
    { simpl. rewrite IHE'. rewrite~ subst_subst_neq. } }
Qed.

Lemma subst_substs : forall x v E t,
  ctx_fresh x E ->
  subst x v (substs E t) = substs E (subst x v t).
Proof using.
  introv M. forwards N: subst_substs_ctx_rem_same E x v t.
  rewrite~ ctx_rem_fresh in N.
Qed.

(** The following lemmas describe how iterated substitution
    distributes over the construction of the language *)

Ltac substs_simpl_proof :=
  let x := fresh "x" in let w := fresh "w" in
  let E := fresh "E" in let E' := fresh "E'" in
  let IH := fresh "IH" in
  intros E; induction E as [|(x,w) E' IH]; intros; simpl;
  [ | try rewrite IH ]; auto.

Lemma substs_val : forall E v,
  substs E (trm_val v) = v.
Proof using. substs_simpl_proof. Qed.

Lemma substs_var : forall E x,
    substs E (trm_var x)
  = match ctx_lookup x E with
    | None => trm_var x
    | Some v => v end.
Proof using.
  substs_simpl_proof.
  { case_if.
    { rewrite~ substs_val. }
    { auto. } }
Qed.

Lemma substs_fun : forall E x t,
  substs E (trm_fun x t) = trm_fun x (substs (ctx_rem x E) t).
Proof using. 
  substs_simpl_proof. 
  { fequals. rewrite var_eq_spec.
    case_eq (var_match x0 x); introv M.
    { lets: var_match_true_inv M. subst. case_if~. }
    { lets [N|[N|N]]: var_match_false_inv M.
      { case_if~. }
      { case_if~. subst. rewrite~ subst_anon. }
      { case_if~. subst. rewrite~ subst_anon. } } }
Qed.

Lemma substs_fix : forall E f x t,
  substs E (trm_fix f x t) = trm_fix f x (substs (ctx_rem x (ctx_rem f E)) t).
Proof using.
  substs_simpl_proof.
  { fequals. rewrite var_eq_spec.
    case_eq (var_match f x); introv M1.
    { lets: var_match_true_inv M1. subst. case_if~. }
    { lets [N1|[N1|N1]]: var_match_false_inv M1.
      { case_eq (var_match x0 x); introv M2.
        { lets: var_match_true_inv M2. subst. case_if~. rewrite~ ctx_rem_same. }
        { lets [N2|[N2|N2]]: var_match_false_inv M2.
          { case_if. { rewrite~ ctx_rem_neq. } }
          { subst. case_if~. admit. (*todo *) } 
          { subst. case_if~. rewrite subst_anon. (* todo: same as later *) admit. } } }
      { subst. case_eq (var_match x0 x); introv M2.
        { lets: var_match_true_inv M2. subst. case_if~. rewrite~ ctx_rem_same. }
        { lets [N2|[N2|N2]]: var_match_false_inv M2.
          { case_if. { subst. rewrite~ subst_anon. } { rewrite~ ctx_rem_neq. } }
          { subst. case_if~.
            { subst. rewrite~ subst_anon. } 
            { rewrite~ ctx_rem_neq. } } 
          { subst. case_if~.
            { subst. rewrite~ subst_anon. } } } }
      { subst. rewrite var_match_anon. rewrite subst_anon.
        case_if~.  (* todo: substs  with var_anon  in ctx  is irrelevant *) admit. } } }
Qed.

Lemma substs_if : forall E t1 t2 t3,
   substs E (trm_if t1 t2 t3)
 = trm_if (substs E t1) (substs E t2) (substs E t3).
Proof using. substs_simpl_proof. Qed.

Lemma substs_app : forall E t1 t2,
   substs E (trm_app t1 t2)
 = trm_app (substs E t1) (substs E t2).
Proof using. substs_simpl_proof. Qed.

Lemma substs_seq : forall E t1 t2,
   substs E (trm_seq t1 t2)
 = trm_seq (substs E t1) (substs E t2).
Proof using. substs_simpl_proof. Qed.

Lemma substs_let : forall E x t1 t2,
   substs E (trm_let x t1 t2)
 = trm_let x (substs E t1) (substs (ctx_rem x E) t2).
Proof using. substs_simpl_proof. { fequals. case_if~. } Qed.

Lemma substs_while : forall E t1 t2,
   substs E (trm_while t1 t2)
 = trm_while (substs E t1) (substs E t2).
Proof using. substs_simpl_proof. Qed.



(* ---------------------------------------------------------------------- *)
(** N-ary substitution *)

(** Shorthand [names], [vals] and [trms] for lists of items. *)

Definition names := list name.
Definition vals : Type := list val.
Definition trms : Type := list trm.

(** Coercion from list of names to list of variables *)

Coercion names_to_vars (xs:names) :=
  List.map var_name xs.

(** [substn xs vs t] is a shorthand for [substs (List.combine xs vs) t].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Definition substn (xs:vars) (vs:vals) (t:trm) : trm :=
  substs (LibList.combine xs vs) t.

(** Distribution of [substn] on [nil] and [cons] lists *)

Lemma substn_nil : forall t,
  substn nil nil t = t.
Proof using. auto. Qed.

Lemma substn_cons : forall x xs v vs t,
  substn (x::xs) (v::vs) t = substn xs vs (subst x v t).
Proof using. auto. Qed.

(** Auxiliary results for freshness of bindings w.r.t. combine *)

Lemma ctx_fresh_combine : forall x ys vs,
  var_fresh x ys ->
  length ys = length vs ->
  ctx_fresh x (LibList.combine ys vs).
Proof using.
  intros x ys. unfold ctx_fresh.
  induction ys as [|y ys']; simpl; intros [|v vs] M L;
   rew_list in *; try solve [ false; math ].
  { auto. }
  { simpl. do 2 case_if. rewrite~ IHys'. }
Qed.

(* Permutation lemma for substitution and n-ary substitution *)

Lemma subst_substn : forall x v ys ws t,
  var_fresh x ys ->
  length ys = length ws ->
  subst x v (substn ys ws t) = substn ys ws (subst x v t).
Proof using.
  introv M L. unfold substn. rewrite~ subst_substs.
  applys~ ctx_fresh_combine.
Qed.


(* ********************************************************************** *)
(* * N-ary functions and applications *)

(** [trm_apps t ts] denotes a n-ary application of [t] to the
    arguments from the list [ts].

    [trm_funs xs t] denotes a n-ary function with arguments [xs]
    and body [t].

    [trm_fixs f xs t] denotes a n-ary recursive function [f]
    with arguments [xs] and body [t].

  The tactic [rew_nary] can be used to convert terms in the goal
  to using the nary constructs wherever possible.

  The operation [substn xs vs t] substitutes the variables [xs]
  with the values [vs] inside the term [t].
*)


(* ---------------------------------------------------------------------- *)
(** Coercions from values to terms *)

Coercion vals_to_trms (vs:vals) : trms :=
  List.map trm_val vs.

(** Tactic [rew_vals_to_trms] to fold the coercion where possible *)

Lemma vals_to_trms_fold_start : forall v,
  (trm_val v)::nil = vals_to_trms (v::nil).
Proof using. auto. Qed.

Lemma vals_to_trms_fold_next : forall v vs,
  (trm_val v)::(vals_to_trms vs) = vals_to_trms (v::vs).
Proof using. auto. Qed.

Hint Rewrite vals_to_trms_fold_start vals_to_trms_fold_next
  : rew_vals_to_trms.

Tactic Notation "rew_vals_to_trms" :=
  autorewrite with rew_vals_to_trms.


(* ---------------------------------------------------------------------- *)
(** N-ary applications and N-ary functions *)

Fixpoint trm_apps (tf:trm) (ts:trms) : trm :=
  match ts with
  | nil => tf
  | t::ts' => trm_apps (trm_app tf t) ts'
  end.

Fixpoint trm_funs (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fun x (trm_funs xs' t)
  end.

Definition val_funs (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fun x (trm_funs xs' t)
  end.

Definition trm_fixs (f:var) (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fix f x (trm_funs xs' t)
  end.

Definition val_fixs (f:var) (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fix f x (trm_funs xs' t)
  end.


(* ---------------------------------------------------------------------- *)
(** Nonempty list of distinct variables *)

Definition var_funs (n:nat) (xs:vars) : Prop :=
     var_distinct xs
  /\ length xs = n
  /\ xs <> nil.

(** Computable version of the above definition
    LATER use TLC exec *)

Definition var_funs_exec (n:nat) (xs:vars) : bool :=
     nat_compare n (List.length xs)
  && is_not_nil xs
  && var_distinct xs.

Lemma var_funs_exec_eq : forall n xs,
  var_funs_exec n xs = isTrue (var_funs n xs).
Proof using.
  intros. unfold var_funs_exec, var_funs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.

Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop :=
     var_distinct (f::xs)
  /\ length xs = n
  /\ xs <> nil.

Definition var_fixs_exec (f:var) (n:nat) (xs:vars) : bool :=
     nat_compare n (List.length xs)
  && is_not_nil xs
  && var_distinct (f::xs).

Lemma var_fixs_exec_eq : forall f n xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).
Proof using.
  intros. unfold var_fixs_exec, var_fixs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary functions *)

Lemma red_funs : forall m xs t,
  xs <> nil ->
  red m (trm_funs xs t) m (val_funs xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fun.
Qed.

Lemma subst_trm_funs : forall y w xs t,
  var_fresh y xs ->
  subst y w (trm_funs xs t) = trm_funs xs (subst y w t).
Proof using.
  introv N. induction xs as [|x xs']; simpls; fequals.
  { case_if. rewrite~ IHxs'. }
Qed.

Lemma red_app_funs_val_ind : forall xs vs m1 m2 tf t r,
  red m1 tf m1 (val_funs xs t) ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  hint red_val.
  intros xs. induction xs as [|x xs']; introv R M (N&L&P).
  { false. } clear P.
  { destruct vs as [|v vs']; rew_list in *. { false; math. }
    simpls. tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys~ red_app_arg R. applys~ red_app_fun. }
    { rew_istrue in N. destruct N as [F N']. applys~ IHxs' M.
      applys~ red_app_arg R. applys~ red_app_fun.
      rewrite~ subst_trm_funs. applys~ red_funs. splits~. } }
Qed.

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv R M N. applys* red_app_funs_val_ind.
  { subst. apply~ red_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary recursive functions *)

Lemma red_fixs : forall m f xs t,
  xs <> nil ->
  red m (trm_fixs f xs t) m (val_fixs f xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fix.
Qed.

Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst y w (trm_fixs f xs t) = trm_fixs f xs (subst y w t).
Proof using.
  introv N. unfold trm_fixs. destruct xs as [|x xs'].
  { auto. }
  { simpls. do 2 case_if in N. rewrite~ subst_trm_funs. }
Qed.

Lemma red_app_fixs_val : forall xs vs m1 m2 vf f t r,
  vf = val_fixs f xs t ->
  red m1 (subst f vf (substn xs vs t)) m2 r ->
  var_fixs f (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv E M (N&L&P). destruct xs as [|x xs']. { false. }
  { destruct vs as [|v vs']; rew_list in *. { false; math. } clear P.
    simpls. case_if*. rew_istrue in *. destruct N as (N1&N2&N3).
    tests C':(xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys* red_app_fix. }
    { applys~ red_app_funs_val_ind.
      { applys* red_app_fix. do 2 rewrite~ subst_trm_funs. applys~ red_funs. }
      { rewrite~ subst_substn in M. { rewrite~ substn_cons in M.
        rewrite~ subst_subst_neq. } { simpl. case_if~. } }
      { splits*. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Folding of n-ary functions *)

Lemma trm_apps_fold_start : forall t1 t2,
  trm_app t1 t2 = trm_apps t1 (t2::nil).
Proof using. auto. Qed.

Lemma trm_apps_fold_next : forall t1 t2 t3s,
  trm_apps (trm_app t1 t2) t3s = trm_apps t1 (t2::t3s).
Proof using. auto. Qed.

Lemma trm_apps_fold_concat : forall t1 t2s t3s,
  trm_apps (trm_apps t1 t2s) t3s = trm_apps t1 (List.app t2s t3s).
Proof using.
  intros. gen t1; induction t2s; intros. { auto. }
  { rewrite <- trm_apps_fold_next. simpl. congruence. }
Qed.

Lemma trm_funs_fold_start : forall x t,
  trm_fun x t = trm_funs (x::nil) t.
Proof using. auto. Qed.

Lemma trm_funs_fold_next : forall x xs t,
  trm_funs (x::nil) (trm_funs xs t) = trm_funs (x::xs) t.
Proof using. auto. Qed.

Lemma trm_fixs_fold_start : forall f x t,
  trm_fix f x t = trm_fixs f (x::nil) t.
Proof using. auto. Qed.

(* subsumed by iteration of trm_funs_fold_next *)
Lemma trm_funs_fold_app : forall xs ys t,
  trm_funs xs (trm_funs ys t) = trm_funs (List.app xs ys) t.
Proof using.
  intros. induction xs. { auto. } { simpl. congruence. }
Qed.

(* for innermost first rewriting strategy
Lemma trm_fixs_fold_next : forall f x xs t,
  trm_fixs f (x::nil) (trm_funs xs t) = trm_fixs f (x::xs) t.
Proof using. auto. Qed.
*)

Lemma trm_fixs_fold_app : forall f x xs ys t,
  trm_fixs f (x::xs) (trm_funs ys t) = trm_fixs f (x :: List.app xs ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_start : forall x t,
  val_fun x t = val_funs (x::nil) t.
Proof using. auto. Qed.

Lemma val_funs_fold_app : forall x xs ys t,
  val_funs (x::xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_app' : forall x xs ys t,
  val_funs (List.app (x::nil) xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_start : forall f x t,
  val_fix f x t = val_fixs f (x::nil) t.
Proof using. auto. Qed.

Lemma val_fixs_fold_app : forall f x xs ys t,
  val_fixs f (x::xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_app' : forall f x xs ys t,
  val_fixs f (List.app (x::nil) xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Hint Rewrite
  trm_apps_fold_start trm_apps_fold_next trm_apps_fold_concat
  trm_funs_fold_start trm_funs_fold_next
  trm_fixs_fold_start trm_fixs_fold_app
  val_funs_fold_start val_funs_fold_app val_funs_fold_app'
  val_fixs_fold_start val_fixs_fold_app val_fixs_fold_app' : rew_nary.

Tactic Notation "rew_nary" :=
  autorewrite with rew_nary; simpl List.app.
Tactic Notation "rew_nary" "in" hyp(H) :=
  autorewrite with rew_nary in H; simpl List.app in H.
Tactic Notation "rew_nary" "in" "*" :=
  autorewrite with rew_nary in *; simpl List.app in *.
  (* rewrite_strat (any (innermost (hints rew_nary))).
     => way too slow! *)

Lemma rew_nary_demo_1 : forall f x y z t1 t2 t,
  val_fix f x (trm_fun y (trm_fun z (f t1 x y t2))) = t.
Proof using. intros. rew_nary. Abort.

Lemma rew_nary_demo_2 : forall f x y t,
  val_fun f (trm_fun x (trm_fun y (x y))) = t.
Proof using. intros. rew_nary. Abort.


(* ---------------------------------------------------------------------- *)
(* ** Sequence of consecutive variables *)

(** [nat_to_name n] converts [nat] values into distinct
    [name] values.
    Warning: the current implementation is inefficient. *)

Definition dummy_char := Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_name (n:nat) : name :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_name n')
  end.

Lemma injective_nat_to_name : injective nat_to_name.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (var_name (nat_to_name start)) :: var_seq (S start) nb'
  end.

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall x start nb,
  (x < start)%nat ->
  var_fresh (nat_to_name x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_if.
    { lets: injective_nat_to_name C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall x start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_name x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_if.
    { lets: injective_nat_to_name C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_distinct_var_seq : forall start nb,
  var_distinct (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. rew_istrue. split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

Lemma var_funs_var_seq : forall start nb,
  (nb > 0%nat)%nat ->
  var_funs nb (var_seq start nb).
Proof using.
  introv E. splits.
  { applys var_distinct_var_seq. }
  { applys length_var_seq. }
  { destruct nb. { false. math. } { simpl. auto_false. } }
Qed.

End Var_seq.



(* ********************************************************************** *)
(* * Tactics  *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red] for proving [red] goals modulo
      equalities between states *)

Ltac fmap_red_base tt ::=
  match goal with H: red _ ?t _ _ |- red _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [var_neq] for proving two concrete variables distinct;
      also registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var =>
    solve [ let E := fresh in
            destruct (eq_var_dec x y) as [E|E];
              [ false | apply E ] ] end.

Hint Extern 1 (?x <> ?y) => var_neq.
