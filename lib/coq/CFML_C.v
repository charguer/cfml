Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap.
Import LibListNotation.

From compcert Require Import Coqlib Maps Integers Floats Values Errors.

(** * Formalizing CFML's fragment resulting from the parsing of C programs *)

(* We compile CFML's language down to CLight.
   In practice, we only compile a subset of CFML, although we do not reflect this subset statically.
   The subset corresponds to C programs parsed into CFML. It can be roughly described by the following BNF,
   obtained after a preprocessing phase (to be written as of now):

   (program)  p ::= list f
   (function) f ::= { name ; rettype: τ; params: list (var * τ); vars: σ; temps: σ; body: t }
   (env_var)  σ ::=
   (prims)    ρ ::= free (heap x) | alloc e
   (fun)      φ ::= name f | ρ
   (terms)    t ::= | e

                    | let const x = φ t* in t
                    | let const x = e in t
                    | let stack x = undef in t
                    | let heap  p = var const x in t

                    | let _       = t in t   *
                    | stack x := e
                    | heap  x := e

                    | let _       = t in t
                    | if e then t else t
                    | while e do t

   (expr)     e ::= v | var flag x | get x | e + e | e < e
   (values)   v ::= undef | i | f | loc i
   (types)    τ ::= long | double | ref τ

Note: get x   == trm_apps (val_prim val_get) [x]
Note: x ::= v == trm_apps (val_prim val_set) [x;v]

 *)



(** CFML types *)

(* Definition program := list toplevel_fundef
   fundef := {name, rettype, list (var*type), trm}

   Clight.program -> main : "main"

   Definition tr_program (p : program) : mon Clight.program

   Definition gather_vars (t : trm_r) : list (ident*type)
   Definition gather_temps (t : trm_r) : list (ident*type)

   Definition tr_trm_stmt (E : env_var) (t: trm_r) : mon Clight.statement
   Definition tr_trm_expr (E : env_var) (t: trm_r) : mon Clight.expr

   Definiton env_var := Ptree.t var_descr

   Inductive var_descr :=
    | var_stack
    | var_heap
    | var_const


   Definition trm_get_var_heap_inv (E : env_var) (t : trm) :
                                       option (ident*type) :=
      match t with
      | trm_app trm_get (trm_var x :: nil) =>
                       match Ptree.get E x with
                       | Some (var_heap) => Some x
                       | _ => None
      | _ => None

 *)

Unset Elimination Schemes.

Section CFML_TYPES.

Inductive type : Type :=
| type_long : type
| type_double : type
| type_ref : type -> type.

Variant var_descr : Type :=
  | stack : var_descr
  | heap : var_descr
  | const : var_descr.

Global Instance Inhab_var_descr_type : Inhab (var_descr * type).
Proof using. apply (Inhab_of_val (stack,type_long)). Qed.


Definition var' : Type := var * (option AST.ident).
Coercion var_to_var' (x : var) : var' := (x, None).


Definition var'_eq (x y : var') : bool :=
  match x, y with
  | (xv, Some xi), (yv, Some yi) =>
      if (eq_var_dec xv yv) then (Pos.eqb xi yi) else false
  | _, _ => false
  end.


Definition get_ident (x : var') : res AST.ident :=
  match x with
  | (v, Some i) => OK i
  | (v, None) => Error (msg "get_ident: no set ident" ++ msg v)
  end.

(* Redefiniton of LibSepBind.bind to be typed, and with var descr *)
Inductive binding : Type :=
| binding_anon : binding
| binding_var : var' -> type -> var_descr -> binding.

Definition numtype := type.

Variant prim : Type :=
  | val_ptr_add : prim
  | val_add : numtype -> prim
  (* | val_cast : numtype -> numtype -> prim
      (en pratique, juste besoin de (val_cast type_long type_double))*)
  | val_lt : numtype -> prim
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_alloc : prim
  | val_dealloc : prim.


Definition is_binop (op : prim) : bool :=
  match op with
  | val_add _
  | val_lt _
    => true
  | _ => false
  end.

Inductive val : Type :=
| val_uninitialized : val
| val_unit : val
| val_int : int -> val
| val_loc : loc -> val
| val_prim : prim -> val

with trm : Type :=
| trm_val : val -> trm
| trm_var : var' -> trm
| trm_apps : trm -> list trm -> trm
| trm_let : binding -> trm -> trm -> trm
| trm_while : trm -> trm -> trm
| trm_ite : trm -> trm -> trm -> trm.


Definition trm_seq (t1 t2 : trm) : trm :=
  trm_let binding_anon t1 t2.

Definition env_var := PTree.t (var_descr*type).

Definition env_var_join (E1 E2 : env_var) : env_var :=
  PTree.fold (fun t k elt => PTree.set k elt t) E1 E2.

(* Definition env_var := fmap var (var_descr*type). *)

Record fundef : Type :=
  mkfundef {
      name: var';
      rettype: type;
      params: list (var' * type);
      vars: env_var;
      temps: env_var;
      body: trm
  }.


(* The choice is made here that function paramenters are temporaries (const in cfml),
   do not reside in memory, and thus their address cannot be referenced. This choice
   corresponds to the semantic [function_entry2] of Clight. (read Clight.v:547,713)*)

Definition program := list fundef.

End CFML_TYPES.

Coercion val_prim : prim >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_var : var' >-> trm.
Coercion trm_val : val >-> trm.

Definition state : Type := fmap loc val.

Implicit Types v : val.
Implicit Types x : var'.
Implicit Type l : loc.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types op : prim.
Implicit Types P : state -> trm -> Prop.

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.

Section Trm_induct.

  Variables (P : trm -> Prop)
    (Q : list trm -> Prop)
    (Q1 : Q nil)
    (Q2 : forall t (l : list trm), P t -> Q l -> Q (t::l))
    (f : forall (v : val), P v)
    (f0 : forall (v : var'), P v)
    (f3 : forall (t : trm), P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_ite t t0 t1))
    (f4 : forall (b : binding) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0))
    (f5 : forall (t : trm), P t -> forall (l : list trm), Q l -> P (trm_apps t l))
    (f6 : forall (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_while t t0)).

  Definition trm_induct_gen := fix F (t : trm) : P t :=
      let trm_list_induct := fix f (l : list trm) : Q l :=
          match l as x return Q x with
          | nil   => Q1
          | t::l' => Q2 (F t) (f l')
          end in
      match t as t0 return (P t0) with
      | trm_val v => @f v
      | trm_var v => @f0 v
      | trm_ite t0 t1 t2 => @f3 t0 (F t0) t1 (F t1) t2 (F t2)
      | trm_let b t0 t1 => @f4 b t0 (F t0) t1 (F t1)
      | trm_apps t0 l => @f5 t0 (F t0) l (trm_list_induct l)
      | trm_while t0 t1 => @f6 t0 (F t0) t1 (F t1)
      end.

End Trm_induct.

Lemma trm_ind : forall P : trm -> Prop,
  (forall v : val, P v) ->
  (forall v : var', P v) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> forall t1 : trm, P t1 -> P (trm_ite t t0 t1)) ->
  (forall (b : binding) (t : trm), P t -> forall t0 : trm, P t0 -> P (trm_let b t t0)) ->
  (forall t : trm, P t -> forall (l : list trm), (forall t, mem t l -> P t) -> P (trm_apps t l)) ->
  (forall t : trm, P t -> forall t0 : trm, P t0 -> P (trm_while t t0)) ->
  forall t : trm, P t.
Proof using.
  hint mem_map'.
  intros. gen t. eapply trm_induct_gen with
    (Q := fun (l : list trm) => forall t, mem t l -> P t); eauto.
  { introv M. inverts M. }
  { introv M1 M2 M3. inverts~ M3. }
Qed.



  (** ** int * (const) p = malloc ?     ->  w: *p = v;    r: *p     + free(p);
    cfml   => let p = val_alloc(1) in
           w=> (set p v)
           r=> (get p)
           free=> (free p)

    clight =>
           decla d'un `type * p` au début, puis
              Sbuiltin (Some p) malloc [sizeof(int)];
           w=> Sassign (Ederef (Evar p)) v
           r=> Ederef (Evar p)
           free=> Sbuiltin None free (Evar p)
   *)

  (** ** int x;         ->   w:   x = v;    r: x
    cfml   => let p (décoration : stack allocated) = valloc(1) in
           ... pareil

    clight => ramener au début de la déclaration de la fonction
              compile_fun => analyse prog, sort liste des variabels
           w=> Sassign (Evar x) v
           r=> Evar x
   *)

  (** ** tempvar = v;
        => Sset tempvar v / let tempvar = v
        => clight : decla d'un `register void *$42;` au début
                      -> pour tout appel de fonction du coup
   *)




(** * Surface syntax for CFML_C *)

(* Custom Syntax (from SLF) *)

Declare Custom Entry trm.
(* Import LibListNotation. *)

Declare Scope type_scope.

Notation "'long'" := type_long (at level 0, only parsing) : type_scope.
Notation "'double'" := type_double (at level 0, only parsing) : type_scope.
Notation "ty 'ref'" :=
  (type_ref ty) (at level 0, only parsing) : type_scope.


Declare Scope trm_scope.

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
   x constr at level 0) : trm_scope.


Notation "t1 '(' t2 , .. , tn ')'" :=
  (trm_apps t1 (@cons trm t2 .. (@cons trm tn nil) .. ))
    (in custom trm at level 30,
        t2 custom trm at level 99,
        tn custom trm at level 99,
      format "t1 '[   ' '(' t2 ',' .. ',' tn ')' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_ite t0 t1 t2)
  (in custom trm at level 69,
   t0 custom trm at level 99,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'while' t1 'do' t2 'done'" :=
  (trm_while t1 t2)
  (in custom trm at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   format "'[v' 'while'  t1  'do'  '/' '['   t2 ']' '/'  'done' ']'")
   : trm_scope.

Notation "t1 ';' t2" :=
  (trm_let binding_anon t1 t2)
  (in custom trm at level 68,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' '(' x ':' ty '#' desc ')' '=' t1 'in' t2" :=
  (trm_let (binding_var x ty desc) t1 t2)
  (in custom trm at level 69,
      x at level 0,
      ty at level 0,
      desc at level 0,
      t1 custom trm at level 100,
      t2 custom trm at level 100,
      right associativity,
      format "'[v' '[' 'let'  '(' x  ':'  ty '#' desc ')'  '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'()'" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "'()'" :=
  (val_unit)
  (at level 0) : val_scope.


Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0) : trm_scope.


Notation "'!' t" :=
  (val_get t)
  (in custom trm at level 0,
      t custom trm at level 1,
      format "'!' t") : trm_scope.

(* Notation "'free'" := *)
(*   (trm_val (val_prim val_free)) *)
(*   (in custom trm at level 0) : trm_scope. *)

Notation "'alloc'" :=
  (trm_val (val_prim val_alloc))
  (in custom trm at level 0) : trm_scope.

Notation "t1 ':=' t2" :=
  (val_set t1 t2)
  (in custom trm at level 67, format "t1  ':='  t2") : trm_scope.

Notation "t1 + t2" :=
  ((val_add type_long) t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 < t2" :=
  ((val_lt type_long) t1 t2)
    (in custom trm at level 60) : trm_scope.


Module CFMLSyntax.

  Open Scope type_scope.
  Open Scope trm_scope.
  Open Scope val_scope.
  Open Scope string_scope.

  Coercion string_to_var (x:string) : var := x.
  Coercion int_to_trm (n:int) : trm := (trm_val (val_int n)).

End CFMLSyntax.




Section Semantics.

  Import CFMLSyntax.

  Global Instance Inhab_val : Inhab val.
  Proof using. apply (Inhab_of_val val_unit). Qed.


(*   Fixpoint subst (y:var') (w:val) (t:trm) : trm := *)
(*     let aux t := *)
(*       subst y w t in *)
(*     let aux_no_capture z t := *)
(*       match z with *)
(*       | binding_anon => aux t *)
(*       | binding_var x _ _ => if (var'_eq x y) then t else aux t *)
(*       end in *)
(*     (* If z = binding_var y then t else aux t in *) *)
(*     let aux_no_captures xs t := *)
(*       If LibList.mem y xs then t else aux t in *)
(*   match t with *)
(*   | trm_val v => trm_val v *)
(*   | trm_var x => If x = y then trm_val w else t *)
(* | trm_ite t0 t1 t2 => trm_ite (aux t0) (aux t1) (aux t2) *)
(* | trm_let z t1 t2 => trm_let z (aux t1) (aux_no_capture z t2) *)
(* | trm_apps t0 ts => trm_apps (aux t0) (LibListExec.map aux ts) *)
(* | trm_while t1 t2 => trm_while (aux t1) (aux t2) *)
(*   end. *)


(*   Definition subst1 (z:binding) (v:val) (t:trm) := *)
(*     match z with *)
(*     | binding_anon => t *)
(*     | binding_var x _ _ => subst x v t *)
(*     end. *)



  (* variable environments *)
  Definition env := PTree.t (val * var_descr * type).


  Definition postcond : Type := state -> trm -> Prop.


  (* NOTE: substition-based, will need to bridge the gap with the environment-based one on CLight's side *)
  (* NOTE: missing constructs *)
  Reserved Notation "G '/' t '/' s '-->e' P"
    (at level 40, t, s at level 30).

  Inductive cfml_omnistep_expr : env -> state -> trm -> postcond -> Prop :=
  | cfml_omnistep_expr_val : forall G v s P,
      P s (trm_val v) ->
      G / (trm_val v) / s -->e P
  | cfml_omnistep_expr_var : forall G i x v d ty s P,
      snd x = Some i ->
      G ! i = Some (v, d, ty) ->
      P s (trm_val v) ->
      G / trm_var x / s -->e P
  (* [get] *)
  | cfml_omnistep_expr_get_t : forall G t s P1 P,
      G / t / s -->e P1 ->
      (forall s' t', P1 s' t' -> G / (val_get t') / s' -->e P) ->
      G / (val_get t) / s -->e P
  | cfml_omnistep_expr_get_v : forall G l s P,
      Fmap.indom s l ->
      P s (trm_val (Fmap.read s l)) ->
      G / (val_get l) / s -->e P
  (* [+] *)
  | cfml_omnistep_expr_add_l : forall G t1 t2 s P1 P,
      G / t1 / s -->e P1 ->
      (forall s' t1', P1 s' t1' -> G / <{t1' + t2}> / s' -->e P) ->
      G / <{t1 + t2}> / s -->e P
  | cfml_omnistep_expr_add_r : forall G v1 t2 s P2 P,
      G / t2 / s -->e P2 ->
      (forall s' t2', P2 s' t2' -> G / <{v1 + t2'}> / s' -->e P) ->
      G / <{v1 + t2}> / s -->e P
  | cfml_omnistep_expr_add_val : forall G n1 n2 s P,
      P s (val_int (n1 + n2)) ->
      G / <{n1 + n2}> / s -->e P
  (* [<] *)
  | cfml_omnistep_expr_lt_l : forall G t1 t2 s P1 P,
      G / t1 / s -->e P1 ->
      (forall s' t1', P1 s' t1' -> G / <{t1' < t2}> / s' -->e P) ->
      G / <{t1 < t2}> / s -->e P
  | cfml_omnistep_expr_lt_r : forall G v1 t2 s P2 P,
      G / t2 / s -->e P2 ->
      (forall s' t2', P2 s' t2' -> G / <{v1 < t2'}> / s' -->e P) ->
      G / <{v1 < t2}> / s -->e P
  | cfml_omnistep_expr_lt_val : forall G (n1 n2 : int) s P,
      P s (val_int (if (n1 <? n2)%Z then 1 else 0)) ->
      G / <{n1 < n2}> / s -->e P

  where "G '/' t '/' s '-->e' P" := (cfml_omnistep_expr G s t P).



  Reserved Notation "G '/' t '/' s '-->' P"
    (at level 40, t, s at level 30).

  Inductive cfml_step : env -> state -> trm -> (state->trm->Prop) -> Prop :=
  | cfml_step_seq : forall v1 t2 s P,
      P s t2 ->
      G / (trm_seq (trm_val v1) t2) / s --> P

  | cfml_step_seq_l : forall t1 t2 s P P1,
      t1 / s --> P1 ->
      (forall t1' s', P1 s' t1' -> (trm_seq t1' t2) / s' --> P) ->
      (trm_seq t1 t2) / s --> P

  | cfml_step_set : forall s l v P,
      Fmap.indom s l ->
      P (Fmap.update s l v) val_unit ->
      (val_set l v) / s --> P

  | cfml_step_let : forall s x t2 v1 P,
      P s (subst1 x v1 t2) ->
      (trm_let x v1 t2) / s --> P

  | cfml_step_ref : forall v s P,
      (forall l, ~Fmap.indom s l ->
            l <> null ->
            P (Fmap.update s l v) (val_loc l)) ->
      (exists l, ~Fmap.indom s l /\ l <> null) ->
      (val_ref v)/ s --> P

  | cfml_step_get : forall s l P,
      Fmap.indom s l ->
      P s (Fmap.read s l) ->
      (val_get l) / s --> P

  | cfml_step_ite : forall s b t1 t2 P,
      P s (if (b =? 0) then t2 else t1) ->
      (trm_ite (val_int b) t1 t2) / s --> P

  | cfml_step_free : forall s l P,
      Fmap.indom s l ->
      P (Fmap.remove s l) val_unit ->
      (val_free l) / s --> P

  | cfml_step_ptr_add : forall l l' n s P,
      (l':nat) = (l:nat) + n :> int ->
      P s (val_loc l') ->
      (val_ptr_add l (val_int n)) / s --> P
  | cfml_step_add : forall s n1 n2 P,
      P s (val_int (n1 + n2)) ->
      ((val_add type_long) (val_int n1) (val_int n2)) / s --> P

  | cfml_step_lt : forall s n1 n2 P,
      P s (if (n1 <? n2) then val_int 1 else val_int 0) ->
      ((val_lt type_long) (val_int n1) (val_int n2)) / s --> P

  | cfml_step_alloc : forall n sa P,
      (forall l k sb, sb = Fmap.conseq (LibList.make k val_uninitialized) l ->
                 n = nat_to_Z k ->
                 l <> null ->
                 Fmap.disjoint sa sb ->
                 P (sb \+ sa) (val_loc l)) ->
      (exists l k sb, sb = Fmap.conseq (LibList.make k val_uninitialized) l
                 /\ n = nat_to_Z k
                 /\ l <> null
                 /\ Fmap.disjoint sa sb) ->
      (val_alloc (val_int n)) / sa --> P
  | cfml_step_dealloc : forall (n:int) s l P,
      (forall vs sa sb, s = sb \+ sa ->
                   sb = Fmap.conseq vs l ->
                   n = LibList.length vs ->
                   Fmap.disjoint sa sb ->
                   P sa val_unit) ->
      (exists vs sa sb, s = sb \+ sa
                   /\ sb = Fmap.conseq vs l
                   /\ n = LibList.length vs
                   /\ Fmap.disjoint sa sb) ->
      (val_dealloc (val_int n) l) / s --> P

  where "G / t / s --> P" := (cfml_step G s t P).
  (* TODO à compléter *)

End Semantics.
