Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap.
Import LibListNotation.

From compcert Require Integers.
From compcert Require Import Coqlib Maps Floats Values Errors.

From TLC Require Import LibCore LibInt.

(** * Formalizing CFML's fragment resulting from the parsing of C programs *)

(* We compile CFML's language down to CLight.
   In practice, we only compile a subset of CFML, although we do not reflect this subset statically.
   The subset corresponds to C programs parsed into CFML. It can be roughly described by the following BNF,
   obtained after a preprocessing phase (to be written as of now):

   (program)  p ::= list f
   (function) f ::= { name ; rettype: τ; params: list (var * τ); vars: σ; temps: σ; body: t }
   (env_var)  σ ::= PTree.t (var_descr*type)
   (var)      x ::= (string * option ident)
   (prims)    ρ ::= dealloc (e, e) | alloc (e)
   (fun)      φ ::= name f | ρ
   (terms)    t ::= | e

                    | let const x : τ = φ(t,..t) in t
                    | let const x : τ = e in t
                    | let stack x : τ = undef in t
                    | let heap  p : τ = const x in t

                    | x := e

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

Definition var'_ident (x : var') := snd x.


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
  | val_ptr_add
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

Definition vals : Type := list val.
Definition trms : Type := list trm.

Definition trm_is_val (t:trm) : Prop :=
  exists v, t = trm_val v.

Coercion trms_vals (vs:vals) : list trm :=
  LibListExec.map trm_val vs.

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


(** potential block memory model : block index -> offset -> value *)
Definition state' : Type := fmap positive (fmap int val).

Definition state : Type := fmap loc val.

Implicit Types v : val.
Implicit Types x : var.
Implicit Type l : loc.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types op : prim.

(* Inductive combiner := *)
(*   | combiner_nil : trm -> trm -> combiner *)
(*   | combiner_cons : combiner -> trm -> combiner. *)

(* Coercion combiner_nil : trm >-> Funclass. *)
(* Coercion combiner_cons : combiner >-> Funclass. *)

(* Fixpoint combiner_to_trm (c:combiner) : trm := *)
(*   match c with *)
(*   | combiner_nil t1 t2 => trm_apps t1 (t2::nil) *)
(*   | combiner_cons c1 t2 => *)
(*       match combiner_to_trm c1 with *)
(*       | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil)) *)
(*       | t1 => trm_apps t1 (t2::nil) *)
(*       end *)
(*   end. *)

(* Coercion combiner_to_trm : combiner >-> trm. *)



Fixpoint is_expr (t : trm) : bool :=
  match t with
  | trm_val _ => true
  | trm_var _ => true
  | trm_apps val_get [t'] => is_expr t'
  | trm_apps (val_prim op) [t1; t2] =>
      is_binop op && is_expr t1 && is_expr t2
  | _ => false
  end.



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

Lemma trm_induct : forall P : trm -> Prop,
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

Declare Scope cfml_type_scope.

Notation "'long'" := type_long (at level 0, only parsing) : cfml_type_scope.
Notation "'double'" := type_double (at level 0, only parsing) : cfml_type_scope.
Notation "ty 'ref'" :=
  (type_ref ty) (at level 0, only parsing) : cfml_type_scope.


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
  (trm_apps val_get [(t : trm)])
  (in custom trm at level 0,
      t custom trm at level 1,
      format "'!' t") : trm_scope.

(* Notation "'free'" := *)
(*   (trm_val (val_prim val_free)) *)
(*   (in custom trm at level 0) : trm_scope. *)

Notation "'alloc'" :=
  (trm_val (val_prim val_alloc))
  (in custom trm at level 0) : trm_scope.

Notation "'dealloc'" :=
  (trm_val (val_prim val_dealloc))
  (in custom trm at level 0) : trm_scope.

Notation "t1 ':=' t2" :=
  (trm_apps val_set [(t1 : trm); (t2 : trm)])
  (in custom trm at level 67, format "t1  ':='  t2") : trm_scope.

Notation "t1 + t2" :=
  (trm_apps (val_add type_long) [(t1 : trm); (t2 : trm)])
    (in custom trm at level 58) : trm_scope.

Notation "t1 '+p' t2" :=
  (trm_apps val_ptr_add [(t1 : trm); (t2 : trm)])
  (in custom trm at level 58) : trm_scope.

Notation "t1 < t2" :=
  (trm_apps (val_lt type_long) [(t1 : trm); (t2 : trm)])
    (in custom trm at level 60) : trm_scope.


Module CFMLSyntax.

  Open Scope cfml_type_scope.
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


  (* Notation int := Z. *)


  (* variable environments *)
  Definition val_env := PTree.t (val * var_descr * type).
  Definition fundef_env := PTree.t fundef.
  Definition funtypes_env := PTree.t (list type * type).

  Definition funtypes_from_fundef_env (F : fundef_env) :=
    PTree.map (fun i f => (List.map (fun '(x,ty) => ty) f.(params), f.(rettype))) F.


  Definition postcond : Type := state -> val_env -> trm -> Prop.

  (* Implicit Type P : postcond. *)
  Implicit Type G : val_env.


  (** *** Bind contexts for expressions *)
  Inductive evalctx_expr : (trm -> trm) -> Prop :=
  | evalctx_expr_add_l : forall t2,
      evalctx_expr (fun t1 => <{t1 + t2}>)
  | evalctx_expr_add_r : forall v1,
      evalctx_expr (fun t2 => <{v1 + t2}>)
  | evalctx_expr_ptr_add_l : forall t2,
      evalctx_expr (fun t1 => <{t1 +p t2}>)
  | evalctx_expr_ptr_add_r : forall l1,
      evalctx_expr (fun t2 => <{l1 +p t2}>)
  | evalctx_expr_lt_l : forall t2,
      evalctx_expr (fun t1 => <{t1 < t2}>)
  | evalctx_expr_lt_r : forall v1,
      evalctx_expr (fun t2 => <{v1 < t2}>)
  | evalctx_expr_get : evalctx_expr (fun t => <{ !t }>).


  (** ** Omni-big step judgement, for pure expressions (see grammar) *)

  Definition val_pc := val -> Prop.
  Implicit Type Q : val_pc.

  Reserved Notation "G '/' s '/' t '⇓' Q"
    (at level 40, t, s at level 30).

  Inductive cfml_omnibig_expr (G : val_env) (s :state) : trm -> val_pc -> Prop :=
  (* bind *)
  | cfml_omnibig_expr_bind : forall C t Q1 Q,
      evalctx_expr C ->
      ~ trm_is_val t ->
      G / s / t ⇓ Q1 ->
      (forall v1, Q1 v1 -> G / s / (C v1) ⇓ Q) -> (* FIXME maybe *)
      G / s / (C t) ⇓ Q
  (* values *)
  | cfml_omnibig_expr_val : forall v Q,
      Q v ->
      G / s / (trm_val v) ⇓ Q
  (* variables *)
  | cfml_omnibig_expr_var : forall i (x : var) v d ty Q,
      G ! i = Some (v, d, ty) ->
      Q v ->
      G / s / trm_var (x, Some i) ⇓ Q
  (* [get] *)
  | cfml_omnibig_expr_get : forall v l Q,
      Fmap.indom s l ->
      v = Fmap.read s l ->
      Q v ->
      G / s / <{! l}> ⇓ Q
  (* [+] *)
  | cfml_omnibig_expr_add : forall n1 n2 Q,
      Q (val_int (n1 + n2)) ->
      G / s / <{n1 + n2}> ⇓ Q
  (* [<] *)
  | cfml_omnibig_expr_lt : forall (n1 n2 : int) Q,
      (* C-style boolean values *)
      Q (val_int (if (n1 <? n2)%Z then 1 else 0)) ->
      G / s / <{n1 < n2}> ⇓ Q
  (* pointer arithmetic *)
  | cfml_omnibig_expr_ptr_add : forall (l l' : loc) (n : Z) Q,
      (l' : nat) = (l : nat) + n :> int ->
      Q (val_loc l') ->
      G / s / <{ l +p n }> ⇓ Q

  where "G '/' s '/' t '⇓' Q" := (cfml_omnibig_expr G s t Q).


  (** eval a list of expressions to a list of postconditions *)
  Inductive cfml_omnibig_expr_list (G : val_env) (s : state) :
    list trm -> list val_pc -> Prop :=
  | cfml_omnibig_expr_list_nil :
    cfml_omnibig_expr_list G s nil nil
  | cfml_omnibig_expr_list_cons : forall e Q ts Qs,
      G / s / e ⇓ Q ->
      cfml_omnibig_expr_list G s ts Qs ->
      cfml_omnibig_expr_list G s (e :: ts) (Q :: Qs).

  (** [val_list_sat_pc_list [Q1..Qn] [v1..vn]] := Q1 v1 /\ .. Qn vn *)
  Definition val_list_sat_pc_list (Qs : list val_pc) (vs : list val) :=
    length Qs = length vs /\
    fold_right (fun '(Q, v) p => p /\ Q v) True (combine Qs vs).

  (* (** ** Eventually judgment for exprs *) *)

  (* Reserved Notation "G '/' t '/' s '-->e⋄' P" (at level 40, t, s at level 30). *)

  (* Inductive eventually_expr : val_env -> state -> trm -> postcond -> Prop := *)
  (* | eventually_expr_here : forall s G t P, *)
  (*     P s G t -> *)
  (*     G / t / s -->e⋄ P *)
  (* | eventually_expr_step : forall G s t P1 P, *)
  (*     G / t / s -->e P1 -> *)
  (*     (forall s' G' t', P1 s' G' t' -> *)
  (*                  G' / t' / s' -->e⋄ P) -> *)
  (*     G / t / s -->e⋄ P *)

  (* where "G '/' t '/' s '-->e⋄' P" := (eventually_expr G s t P). *)



  (** *** Bind contexts where arguments are restricted to pure expressions *)
  Inductive eval_expr_ctx : (trm -> trm) -> Prop :=
  | eval_expr_ctx_ite : forall t2 t3,
      eval_expr_ctx (fun e1 => <{if e1 then t2 else t3}>)
  | eval_expr_ctx_apps_arg : forall v0 vs ts,
      eval_expr_ctx (fun e1 => trm_apps v0 ((trms_vals vs)++e1::ts))
  | eval_expr_ctx_let_expr : forall z t,
      eval_expr_ctx (fun e => trm_let z e t).

  (** *** The other bind contexts *)
  Inductive eval_trm_ctx : (trm -> trm) -> Prop :=
  | eval_trm_ctx_seq : forall t2,
      eval_trm_ctx (fun t1 => <{ t1 ; t2 }>)
  (* let const : only during reduction can t1 be anything other than a funcall *)
  | eval_trm_ctx_let_const : forall x ty t2,
      eval_trm_ctx (fun t1 => <{ let (x : ty#const) = t1 in t2 }>).
  (* FIXME, remove, funcall is a special case *)


  (** ** Omni-small step for terms *)

  Inductive call_stack : Type :=
  | Ctop : call_stack           (* top level *)
  | Ccall : fundef ->            (* caller *)
            val_env ->           (* outer environment *)
            call_stack ->
            call_stack.

  Implicit Type k : call_stack.

  Definition config : Type := (fundef * val_env * state * trm * call_stack).
  Implicit Type c : config.

  (* TODO: refactor *)
  Definition stmt_pc := config -> Prop.
  Implicit Type P : stmt_pc.


  (** relates the parameters of a fundef to a list of idents and types *)
  Definition R_params
    (fun_par_list : list (var' * type))
    (id_ty_list : list (AST.ident * type)) : Prop :=
    length fun_par_list = length id_ty_list
    /\ (fold_right (fun '((x, ty), (i, ty')) p =>
                     p /\ ty = ty' /\ var'_ident x = Some i)
         True (combine fun_par_list id_ty_list)).


  Reserved Notation "F '/' c '-->' P"
    (at level 40, c at level 30).

  Inductive cfml_omnistep (F : fundef_env) : config -> stmt_pc -> Prop :=
  (* (* when a subterm can only be an expression *) *)
  (* | cfml_omnistep_expr_ctx : forall F G C e s P1 P, *)
  (*     is_expr e -> *)
  (*     eval_expr_ctx C -> *)
  (*     ~ trm_is_val e -> *)
  (*     G / e / s -->e P1 -> *)
  (*     (forall s1 G1 e1, P1 s1 G1 e1 -> P s1 G (C e1)) -> (* we do not pass the env to the outer context *) *)
  (*     F / G / (C e) / s --> P *)
  (* the rest of the contexts *)
  | cfml_omnistep_trm_ctx : forall f G C t s k P1 P,
      eval_trm_ctx C ->
      ~ trm_is_val t ->
      F / (f, G, s, t, k) --> P1 ->
      (forall f1 s1 G1 t1 k1, P1 (f1, G1, s1, t1, k1) -> P (f1, G1, s1, (C t1), k1)) ->
      F / (f, G, s, (C t), k) --> P

  (* let bindings *)
  | cfml_omnistep_let_fun_call : forall f f' xf i_f G G' s x ty es Qs prms t k P,
      F ! i_f = Some f ->
      R_params f.(params) prms ->
      ty = f.(rettype) ->

      length es = length prms ->
      cfml_omnibig_expr_list G s es Qs ->

      (forall vs, length vs = length Qs ->
             val_list_sat_pc_list Qs vs ->
             G' = fold_right (fun '(i, ty, v) G =>
                                PTree.set i (v, const, ty) G)
                    G (combine prms vs) ->
             P (f, G', s,
                 <{ let (x : ty#const) = {f.(body)} in t }>,
                    Ccall f' G k)) ->

      F / (f', G, s, <{let (x : ty#const) =
                            {trm_apps (trm_var (xf, Some i_f)) es} in t}>, k) --> P


  (* | cfml_omnistep_apps : forall (f f1 : fundef) t G G' x i ts Qs s P, *)
  (*     F ! i = Some f1 -> *)
  (*     f1.(body) = t -> *)
  (*     length ts = length f1.(params) -> *)
  (*     cfml_omnibig_expr_list G s ts Qs -> *)
  (*     (forall vs, fold_right (fun '(Q, v) p => p /\ Q v) True (combine Qs vs) -> *)
  (*            G' = fold_right *)
  (*                   (fun '(x,ty,v) G => *)
  (*                      match snd x with *)
  (*                      | Some i => PTree.set i (v, const, ty) G *)
  (*                      | None => G (* never happens (see CompilationTest.make_function) *) *)
  (*                      end) *)
  (*                   G (combine f.(params) vs) -> *)
  (*            (* TODO better = relation that takes f.(params) and *)
  (*               return list (ident * type) *) *)
  (*            P (f1, G', s, t)) -> *)
  (*     F / (f, G, s, trm_apps (trm_var (x, Some i)) ts) --> P *)

  | cfml_omnistep_let_fun_ret : forall f f' G G' s x i ty t e k Q P,
      G / s / e ⇓ Q ->
      (forall v, Q v ->
            P (f', PTree.set i (v, const, ty) G', s, t, k)) ->
      F / (f, G, s,
          <{ let ({(x, Some i)} : ty#const) = e in t }>,
             Ccall f' G' k) --> P

  | cfml_omnistep_let_expr : forall f G s x i ty d e t k Q P,
      G / s / e ⇓ Q ->
      (forall v, Q v -> P (f, PTree.set i (v, const, ty) G, s, t, k)) ->
      F / (f, G, s, <{let ({(x, Some i)} : ty#d) = e in t}>, k) --> P

  (* only an expression left: return *)
  | cfml_omnistep_is_return : forall x f f' G G' s e k Q P,
      is_expr e ->
      G / s / e ⇓ Q ->
      (forall v, Q v -> P (f', G', s, trm_val v, k)) ->
      F / (f, G, s, e, k) --> P

  (* sequence *)
  | cfml_omnistep_seq : forall f G v1 t2 s k P,
      P (f, G, s, t2, k) ->
      F / (f, G, s, <{v1 ; t2}>, k) --> P


  (* prims *)
  | cfml_omnistep_set : forall f G s l v k P,
      Fmap.indom s l ->
      P (f, G, (Fmap.update s l v), trm_val val_unit, k) ->
      F / (f, G, s, <{l := v }>, k) --> P


  | cfml_omnistep_alloc : forall f G n sa k P,
      (forall l i sb, sb = Fmap.conseq (LibList.make i val_uninitialized) l ->
                 n = nat_to_Z i ->
                 l <> null ->
                 Fmap.disjoint sa sb ->
                 P (f, G, (sb \+ sa), trm_val (val_loc l), k)) ->
      (exists l i sb, sb = Fmap.conseq (LibList.make i val_uninitialized) l
                 /\ n = nat_to_Z i
                 /\ l <> null
                 /\ Fmap.disjoint sa sb) ->
      F / (f, G, sa, <{alloc(n)}>, k) --> P

  | cfml_step_dealloc : forall f G (n:int) s l k P,
      (forall vs sa sb, s = sb \+ sa ->
                   sb = Fmap.conseq vs l ->
                   n = LibList.length vs ->
                   Fmap.disjoint sa sb ->
                   P (f, G, sa, trm_val val_unit, k)) ->
      (exists vs sa sb, s = sb \+ sa
                   /\ sb = Fmap.conseq vs l
                   /\ n = LibList.length vs
                   /\ Fmap.disjoint sa sb) ->
      F / (f, G, s, <{dealloc(n, l)}>, k) --> P

  | cfml_omnistep_ite : forall f G e (n : int) t1 t2 s k Q P,
      (* C-style boolean values *)
      G / s / e ⇓ Q ->
      (forall n, Q (val_int n) -> P (f, G, s, (if (n =? 0)%Z then t2 else t1), k)) ->
      F / (f, G, s, <{if e then t1 else t2}>, k) --> P

  | cfml_omnistep_while : forall f G e t s P1 k P,
      P (f, G, s, <{if e then (t; while e do t done)
                    else val_unit}>, k) ->
      F / (f, G, s, <{while e do t done}>, k) --> P


  (* | cfml_step_free : forall s l P, *)
  (*     Fmap.indom s l -> *)
  (*     P (Fmap.remove s l) val_unit -> *)
  (*     (val_free l) / s --> P *)

  where "F / c --> P" := (cfml_omnistep F c P).
  (* TODO à compléter : DONE? *)



  (** ** Eventually judgment *)

  Reserved Notation "F '/' c '-->⋄' P" (at level 40, c at level 30).

  Inductive eventually (F : fundef_env) : config -> stmt_pc -> Prop :=
  | eventually_here : forall c P,
      P c ->
      F / c -->⋄ P
  | eventually_step : forall c P1 P,
      F / c --> P1 ->
      (forall c', P1 c' -> F / c' -->⋄ P) ->
      F / c -->⋄ P

  where "F / c -->⋄ P" := (eventually F c P).


  Definition final_config : Type :=
    fundef * val_env * state * val * call_stack.

  Definition apply_ctx_cfg (C : (trm -> trm)) : final_config -> config :=
    fun '(f, G, s, v, k) => (f, G, s, C v, k).


  Definition big_pc := final_config -> Prop.

  Implicit Type Qb : big_pc.


  Reserved Notation "F '/' c '==>' Q" (at level 40, c at level 30).

  Inductive cfml_omnibig_stmt (F : fundef_env) :
    config -> big_pc -> Prop :=
  | cfml_omnibig_stmt_ctx : forall C f G s t k Qb1 Qb,
      eval_trm_ctx C ->
      ~ trm_is_val t ->
      F / (f, G, s, t, k) ==> Qb1 ->
      (forall (c1 : final_config), Qb1 c1 -> F / (apply_ctx_cfg C c1) ==> Qb) ->
      F / (f, G, s, (C t), k) ==> Qb

  (* | cfml_omnibig_let_fun_call : forall f f' xf i_f G s x ty es Qs prms t k Q1 Q, *)
  (*     F ! i_f = Some f -> *)
  (*     R_params f.(params) prms -> *)
  (*     ty = f.(rettype) -> *)

  (*     cfml_omnibig_expr_list G s es Qs -> *)

  (*     (exists vs G', val_list_sat_pc_list Qs vs *)
  (*                  /\ G' = fold_right (fun '(i, ty, v) G => *)
  (*                                       PTree.set i (v, const, ty) G) *)
  (*                           G (combine prms vs) *)
  (*                  /\ F / (f, G', s, f.(body), Ccall f' G k) ==> Q1) -> *)

  (*     (forall vs G', *)
  (*         val_list_sat_pc_list Qs vs -> *)
  (*         G' = fold_right (fun '(i, ty, v) G => *)
  (*                            PTree.set i (v, const, ty) G) *)
  (*                G (combine prms vs) -> *)
  (*         F / (f, G', s, f.(body), Ccall f' G k) ==> Q1 -> *)
  (*         forall v1, Q1 v1 -> *)
  (*               F / (f', G, s, <{let (x : ty#const) = v1 in t}>, *)
  (*                                 k) ==> Q *)
  (*     ) -> *)

  (*     F / (f', G, s, <{let (x : ty#const) = *)
  (*                           {trm_apps (trm_var (xf, Some i_f)) es} in t}>, k) ==> Q *)

  | cfml_omnibig_let_expr : forall f G s x i ty d e t k Qe Qb,
      G / s / e ⇓ Qe ->
      (forall v, Qe v -> F / (f, PTree.set i (v, const, ty) G, s, t, k) ==> Qb) ->
      F / (f, G, s, <{let ({(x, Some i)} : ty#d) = e in t}>, k) ==> Qb

  | cfml_omnibig_is_return : forall x f G s e k Qe Qb,
      is_expr e ->
      G / s / e ⇓ Qe ->
      (forall v, Qe v -> Qb (f, G, s, v, k)) ->
      F / (f, G, s, e, k) ==> Qb


  | cfml_omnibig_seq : forall f G v1 t2 s k Qb,
      F / (f, G, s, t2, k) ==> Qb ->
      F / (f, G, s, <{v1 ; t2}>, k) ==> Qb

  (* prims *)
  | cfml_omnibig_set : forall f G s l v k Qb,
      Fmap.indom s l ->
      Qb (f, G, (Fmap.update s l v), val_unit, k) ->
      F / (f, G, s, <{l := v }>, k) ==> Qb

  | cfml_omnibig_alloc : forall f G n sa k Qb,
      (forall l i sb, sb = Fmap.conseq (LibList.make i val_uninitialized) l ->
                 n = nat_to_Z i ->
                 l <> null ->
                 Fmap.disjoint sa sb ->
                 Qb (f, G, (sb \+ sa), (val_loc l), k)) ->
      (exists l i sb, sb = Fmap.conseq (LibList.make i val_uninitialized) l
                 /\ n = nat_to_Z i
                 /\ l <> null
                 /\ Fmap.disjoint sa sb) ->
      F / (f, G, sa, <{alloc(n)}>, k) ==> Qb

  | cfml_omnibig_dealloc : forall f G (n:int) s l k Qb,
      (forall vs sa sb, s = sb \+ sa ->
                   sb = Fmap.conseq vs l ->
                   n = LibList.length vs ->
                   Fmap.disjoint sa sb ->
                   Qb (f, G, sa, val_unit, k)) ->
      (exists vs sa sb, s = sb \+ sa
                   /\ sb = Fmap.conseq vs l
                   /\ n = LibList.length vs
                   /\ Fmap.disjoint sa sb) ->
      F / (f, G, s, <{dealloc(n, l)}>, k) ==> Qb

  | cfml_omnibig_ite : forall f G e (n : int) t1 t2 s k Qe Qb,
      (* C-style boolean values *)
      G / s / e ⇓ Qe ->
      (forall n, Qe (val_int n) -> F / (f, G, s, (if (n =? 0)%Z then t2 else t1), k) ==> Qb) ->
      F / (f, G, s, <{if e then t1 else t2}>, k) ==> Qb

  | cfml_omnibig_while : forall f G e t s k Qb,
      F / (f, G, s, <{if e then (t; while e do t done)
                    else val_unit}>, k) ==> Qb ->
      F / (f, G, s, <{while e do t done}>, k) ==> Qb

  where "F / c ==> Q" := (cfml_omnibig_stmt F c Q).


End Semantics.

(* t / s --> P => t / Kstop / s -->⋄ [P]


   t / k / s ----> compcert
 *)
