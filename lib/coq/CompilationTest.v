Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap.

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




Variant prim_r : Type :=
| val_r_ptr_add : prim_r
| val_r_ref : prim_r
| val_r_get : prim_r
| val_r_set : prim_r
| val_r_free : prim_r
| val_r_alloc : prim_r
| val_r_dealloc : prim_r.


Inductive val_r : Type :=
| val_r_uninitialized : val_r
| val_r_unit : val_r
| val_r_bool : bool -> val_r
| val_r_int : int -> val_r
| val_r_double : double -> val_r
| val_r_loc : loc -> val_r
| val_r_prim : prim_r -> val_r
| val_r_header : nat -> val_r
                     
with trm_r : Type :=
| trm_r_val : val_r -> trm_r
| trm_r_var : var -> trm_r
| trm_r_apps : trm_r -> list trm_r -> trm_r
| trm_r_seq : trm_r -> trm_r -> trm_r
| trm_r_let : bind -> trm_r -> trm_r -> trm_r
| trm_r_while : trm_r -> trm_r -> trm_r
| trm_r_ite : trm_r -> trm_r -> trm_r -> trm_r.
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

Coercion val_r_prim : prim_r >-> val_r.
Coercion val_r_loc : loc >-> val_r.
Coercion trm_r_var : var >-> trm_r.
Coercion trm_r_val : val_r >-> trm_r.

Definition state_r : Type := fmap loc val_r.

Implicit Types v : val_r.
Implicit Type l : loc.
Implicit Types t : trm_r.
Implicit Types s : state_r.
Implicit Types op : prim_r.
Implicit Types P : state_r -> trm_r -> Prop.

Inductive combiner :=
  | combiner_nil : trm_r -> trm_r -> combiner
  | combiner_cons : combiner -> trm_r -> combiner.

Coercion combiner_nil : trm_r >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm_r :=
  match c with
  | combiner_nil t1 t2 => trm_r_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_r_apps t1 ts => trm_r_apps t1 (List.app ts (t2::nil))
      | t1 => trm_r_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm_r.

Reserved Notation "t '/' s '-->' P"
  (at level 40, s at level 30).

Global Instance Inhab_val_r : Inhab val_r.
Proof using. apply (Inhab_of_val val_r_unit). Qed.


Inductive cfml_step : state_r -> trm_r -> (state_r->trm_r->Prop) -> Prop :=
| cfml_step_val : forall v s P,
    P s (trm_r_val v) ->
    (trm_r_val v) / s --> P
| cfml_step_seq_r : forall v1 t2 s P,
    P s t2 ->
    (trm_r_seq (trm_r_val v1) t2) / s --> P
| cfml_step_seq_l : forall t1 t2 s P P1,
    t1 / s --> P1 ->
    (forall t1' s', P1 s' t1' -> (trm_r_seq t1' t2) / s' --> P) ->
    (trm_r_seq t1 t2) / s --> P
| cfml_step_ref : forall v s P,
      (forall l, ~Fmap.indom s l ->
            l <> null ->
            P (Fmap.update s l v) (val_r_loc l)) ->
      (exists l, ~Fmap.indom s l /\ l <> null) ->
       (val_r_ref v)/ s --> P
| cfml_step_get : forall s l P,
    Fmap.indom s l ->
    P s (Fmap.read s l) ->
    (val_r_get l) / s --> P
| cfml_step_set : forall s l v P,
    Fmap.indom s l ->
    P (Fmap.update s l v) val_r_unit ->
    (val_r_set l v) / s --> P
| cfml_step_free : forall s l P,
    Fmap.indom s l ->
    P (Fmap.remove s l) val_r_unit ->
    (val_r_free l) / s --> P
| cfml_step_ptr_add : forall l l' n s P,
    (l':nat) = (l:nat) + n :> int ->
    P s (val_r_loc l') ->
    (val_r_ptr_add l (val_r_int n)) / s --> P
| cfml_step_alloc : forall n sa P,
    (forall l k sb, sb = Fmap.conseq (LibList.make k val_r_uninitialized) l ->
               n = nat_to_Z k ->
               l <> null ->
               Fmap.disjoint sa sb ->
               P (sb \+ sa) (val_r_loc l)) ->
    (exists l k sb, sb = Fmap.conseq (LibList.make k val_r_uninitialized) l
               /\ n = nat_to_Z k
               /\ l <> null
               /\ Fmap.disjoint sa sb) ->
     (val_r_alloc (val_r_int n)) / sa --> P
| cfml_step_dealloc : forall (n:int) s l P,
    (forall vs sa sb, s = sb \+ sa ->
                 sb = Fmap.conseq vs l ->
                 n = LibList.length vs ->
                 Fmap.disjoint sa sb ->
                 P sa val_r_unit) ->
    (exists vs sa sb, s = sb \+ sa
                 /\ sb = Fmap.conseq vs l
                 /\ n = LibList.length vs
                 /\ Fmap.disjoint sa sb) ->
    (val_r_dealloc (val_r_int n) l) / s --> P

where "t / s --> P" := (cfml_step s t P).

(** Preprocessing *)


(** CompCert types *)



(* Fmap.update --> assign_loc *)

(** ** Important!! *)
(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state.

  (in [[../../../CompCert/cfrontend/Clight.v:223]])

  -> meaning each loc can be mapped to a block, at least for refs
 *)

Add Rec LoadPath "../../../CompCert" as compcert.
Add Rec LoadPath "../../../CompCert/flocq" as Flocq.
From compcert Require Import Coqlib Maps Integers Floats Values AST Ctypes.



Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
.



Definition label := ident.



Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
.



