(** * Syntax and semantics *)

(** In order to give a formal presentation of assertions (a.k.a.
    heap predicates) and triples, we need to introduce the syntax
    and semantics of the source language used throughout this course. *)

(** ** Syntax of the source language *)

(** To begin with, we load appropriate definitions from the TLC library. *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Close Scope fmap_scope.

(** Program variables are represented using natural numbers. *)

Definition var := nat.

(** Locations are also represented as natural numbers. The [null] pointer
    corresponds to the address zero. *)

Definition loc := nat.
Definition null : loc := 0%nat.

(** The language includes a number of basic primitive functions.
    The list of such builtin functions appears next. *)

Inductive prim : Type :=
  | val_get : prim      (* read in a memory cell *)
  | val_set : prim      (* write in a memory cell *)
  | val_ref : prim      (* allocate a single memory cell *)
  | val_alloc : prim    (* allocate a range of cells *)
  | val_eq : prim       (* comparison *)
  | val_add : prim      (* addition *)
  | val_sub : prim      (* substraction *)
  | val_mul : prim      (* multiplication *)
  | val_div : prim      (* division *)
  | val_ptr_add : prim. (* pointer addition *)

(** Values of the programming language include:
    - the unit value (like in OCaml, similar to [void] type in C);
    - the boolean values (true and false);
    - integer values, which are assumed for simplicity to be idealized
      (unbounded) integers, without arithmetic overflow---the [int] type
      is provided by the TLC library, as an alias for the type [Z], which
      is the integer type provided by Coq's standard library;
    - locations, a.k.a. pointer values,
    - primitive functions, whose grammar was shown above,
    - functions, of the form [val_fun x t], with argument [x] and body [t],
    - and recursive functions, of the form [val_fix f x t], where [f]
      denotes the name of the function in recursive calls.

    Due to the presence of functions, the grammars of values is mutually
    recursive with the grammar of terms. A term may be:
    - a value, i.e. one object from the above grammar of values;
    - a program variable, i.e. a token that may get replaced by a value
      during a substitution operation;
    - a function definition, of the form [trm_fun x t]; such functions
      are intended to become values of the form [val_fun x t], once
      substitutions of the free variables of the function have been performed;
    - a recursive function definition, of the form [trm_fix f x t];
    - a conditional, of the form [trm_if t1 t2 t3], written in concrete
      syntax as [If t1 Then t2 Else t3];
    - a sequence, of the form [trm_seq t1 t2], also written [t1 ;; t2];
    - a let-binding, of the form [trm_let x t1 t2], also written
      [Let x := t1 in t2];
    - an application, of the form [trm_app t1 t2], which may be written
      simply as [t1 t2], thanks to the coercion mechanism introduced further;
    - a while loop, of the form [trm_while t1 t2], also written
      [While t1 Do t2 Done];
    - a for loop, of the form [trm_for x t1 t2 t3], also written
      [For x := t1 To t2 Do t3 Done].


    The corresponding grammar appears next.
*)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm.


(** ** Coercions for terms and values *)

(** _Coercions_ help writing concrete terms more succinctly.
    For example, thanks to the coercions defined further below,
    instead of writing:
[[
  trm_app (trm_val (val_prim val_ref)) (trm_val (val_int 3))
]]
    it suffices to write:
[[
  val_ref 3
]]
    Coq is able to automatically insert the appropriate constructors where
    required for the term to type-check correctly.

    The list of coercions in use appears next.
*)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(** Given an expression, we may ask Coq to display the coercions that it
    has automatically inferred. For example, consider the definition
    shown below. Activate the [Set Printing Coercions] option, and observe
    the result of making the query [Print coercion_example]. *)

Example coercion_example : trm :=
  val_ref 3.


(** ** Representation of the heap *)

(** The mutable state of a program is represented as a finite map from location
    to values. *)

Definition state := fmap loc val.

(** The details of the implementation of finite maps (type [fmap]) is not
    relevant to the present course. The curious reader may find the definition
    in the file [Fmap.v]. In this chapter, we only need to know about the
    main operations for manipulating finite maps.

    - [state_empty] describes the empty finite map.

    - [state_single l v] describes a finite map with a single entry
      that binds location [l] to value [v].

    - [state_union h1 h2] describes the union of two finite maps;
      in case of overlap, bindings from the first argument are kept.

    - [state_disjoint h1 h2] asserts that two finite maps have disjoint
      domains, i.e. that they do not overlap.

*)

(** ** Evaluation predicate *)

(** The evaluation rules are standard. They define an evaluation
    judgment, written [red h t h' v], which asserts that the
    evaluation of the term [t] starting in memory state [h] does
    terminate and produces the value [v] in the final state [h'].
    Note that the arguments [h] and [h'] of [red] describe the full
    memory state. *)

Parameter red : state -> trm -> state -> val -> Prop.

(** Rather than reproducing here pages of standard definitions, we will
    present the evaluation rules as we need them. Details may be found in
    the file [Semantics.v], which contains the recursive definition of
    capture-avoiding substitution and the inductive definition of the
    evaluation rules. *)


(** * From Hoare triples to Separation Logic triples *)

(** ** Hoare triples for terms with an output value **)

(** In what follows, we adapt Hoare triples to terms, which, unlike
    commands, always produce an output value.

    Recall the grammar of assertions: *)

Definition assertion := state -> Prop.

(** Recall the definition of a partial correctness Hoare triple for a
    programming language based on commands (i.e. with statements that
    do not return an output value) from Volume 2. It asserts that if the
    precondition is satisfied, and if the program terminates, then the
    postcondition holds:

[[
  Definition Hoare_triple_com_partial (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h h', H h -> ceval h c h' -> Q h'.
]]

    In this course, we focus on total correctness, which brings stronger
    guarantees, as it enforces termination. The definition of Hoare triple
    may be easily adapted to total correctness, to assert the following:
    if the precondition is satisfied, then the program terminates, and
    the postcondition holds. In the formal definition below, observe
    that the output heap [h'] now gets quantified existentially in the
    conclusion.

[[
  Definition Hoare_triple_com_total (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h, H h ->
    exists h', ceval h c h' /\ Q h'.
]]

   The definition above assumes a language of commands, in which terms do not
   produce any output value. How should the definition of Hoare triple be adapted
   to handle terms that produce an output value?

   The output value, call it [v], needs to be quantified existentially
   like the output heap. The evaluation predicate becomes [red h t h' v].
   The postcondition [Q h'] also needs to be extended, so that Hoare triple
   may be used to specify the output value of the term [t]. We achieve this
   by passing [v] as first argument to the postcondition [Q]. In other words,
   we update the type of the postcondition from [assertion] to
   [val -> assertion].

   In summary, the definition of Hoare triples gets adapted as follows.

*)

Definition Hoare_triple (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall h, H h ->
  exists v h', red h t h' v /\ Q v h'.

