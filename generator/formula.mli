open Coq


(** This module contains a data structure for representing characteristic
    formulae. Such data is constructed in file [characteristic.ml] from
    the typed abstract syntax tree, and is converted into a Coq expression
    (as described in [coq.ml]), using an algorithm contained in this file. *)


(** For loop direction *)

type for_loop_dir = For_loop_up | For_loop_down

type record_items = (var * coq * coq) list

(** Characteristic formulae for terms *)

type cf =
  | Cf_val of coq
    (* Val v *)
  | Cf_fail
    (* Fail *)
  | Cf_assert of cf
    (* Assert Q *)
  | Cf_done
    (* Done *)
  | Cf_record_new of var * record_items
    (* AppNew [.. (fi, @dyn Ai xi) .. ] *) (* TODO: the first var is for recursive records *)
  | Cf_record_with of coq * record_items * coqs
     (* stores both { p with f2 := v2 }  and also [f1;f2;f3] the list of fields *)
  | Cf_app of coqs * coq * coq * coqs
    (* App f [.. (@dyn Ai xi) .. ] (B:=B) *)
  | Cf_body of var * vars * typed_vars * coq * cf
    (* Body f Ai xi => Q *)
  | Cf_let of typed_var * cf * cf
    (* Let x := Q1 in Q2 *)
  | Cf_let_poly of var * vars * vars * coq * cf * cf
    (* Let x [Ai,Bi] := Q1 in Q2  // where x : forall Ai.T *)
  | Cf_let_val of var * vars * coq * coq * cf
    (* Let x [Ai] := v in Q2  // where x : forall Ai.T *)
  | Cf_let_fun of (var * cf) list * cf
    (* Let fi := Qi in Q *)
  | Cf_if of coq * cf * cf
    (* If v Then Q1 else Q2 *)
  | Cf_case of coq * typed_vars * coq * coq option * (typed_var*coq) list * cf * cf
    (* Case v [xi] p [When c] Then (Alias yk = vk in Q1) else Q2 *)
  | Cf_match of var * coq * int * cf
    (* Match lab v n Q    where n is the number of branches *)
  | Cf_seq of cf * cf
    (* Q1 ;; Q2 *)
  | Cf_for of for_loop_dir * var * coq * coq * cf
    (* for i = v1 to v2 do Q done *)
  | Cf_while of cf * cf
    (* while Q1 do Q2 done *)
  | Cf_manual of coq
    (* Q *)
  | Cf_pay of cf
    (* Pay; Q *)

      (* not currently used:
        | Cf_caseif of cf * cf * cf
          (* If Q0 Then Q1 else Q2 *)
      *)

(** Characteristic formulae for top-level declarations *)

type cftop =
    Cftop_val of typed_var * coq option
    (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t.
       Definition x : t := tdef. *)
  | Cftop_heap of var
    (* Parameter h : heap. *)
  | Cftop_val_cf of var * vars * vars * coq
    (* Parameter x_cf: forall Ai, x = V *)
  | Cftop_let_cf of var * var * var * cf
    (* Parameter x_cf : forall H Q, H h -> F H Q -> Q x h' *)
  | Cftop_fun_cf of var * cf
    (* Parameter f_cf : Val := H *)
  | Cftop_coqs of coqtops
    (* arbitrary coq top-level commands *)

and cftops = cftop list

(** Shorthand *)

type coq = Coq.coq

(*#########################################################################*)


(** Abstract datatype for dynamic values *)

val coq_dyn : coq

val coq_dyn_at : coq

val coq_dyn_of : coq -> coq -> coq

(** Encoder *)

val enc_type : coq -> coq

val enc : coq

val coq_injective : coq

val enc_make : coq

val enc_of : coq -> coq

val enc_of_typed : coq -> coq -> coq

val enc_arg : var -> var * coq

val enc_args : vars -> (var * coq) list

val coq_forall_enc_types : var list -> coq -> coq

val coq_fun_enc_types : var list -> coq -> coq

(** Applications *)

val trm_apps : coq -> coq list -> coq

val trm_apps_lifted : coq -> coq list -> coq

(** Abstract datatype for functions (func) *)

val func_type : coq

(** Abstract data type for locations (loc) *)

val loc_type : coq

(** Type for fields *)

val field_type : coq

(** Abstract data type for heaps *)

val heap : coq

(** Type of proposition on heaps, [hprop], a shorthand for [heap->Prop] *)

val hprop : coq

(** Constructor for [htype A a], used for representation predicates *)

val htype : coq -> coq -> coq

(** The identity representation predicate *)

val id_repr : coq

(** constructor for [hdata X x], printed as [x ~> X] in Coq *)

val hdata : coq -> coq -> coq

(** Type of pure post-conditions [_ -> Prop] *)

val wild_to_prop : coq

(** Type of imperative post-conditions [_ -> hrop] *)

val wild_to_hprop : coq

(** Precise type of formulae [hprop->(T->hprop)->Prop] *)

val formula_type_of : coq -> coq

(** Generic type of formulae [hprop->(_->hprop)->Prop] *)

val formula_type : coq

(** Hprop entailment [H1 ==> H2] *)

val himpl : coq -> coq -> coq

(** Specialized Hprop entailment [H1 ==> Q2 tt] *)

val himpl_unit : coq -> coq -> coq

(** Postcondition entailment [Q1 ===> Q2] *)

val qimpl : coq -> coq -> coq

(** Specialized post-conditions [fun (_:unit) => H], i.e. [# H] *)

val post_unit : coq -> coq

(** Separating conjunction [H1 * H2] *)

val hstar : coq -> coq -> coq

(** Separating conjunction [Q1 * H2] *)

val qstar : coq -> coq -> coq

(** Base data *)

val hsingle : coq -> coq -> coq

(** Empty heap predicate [[]] *)

val hempty : coq

(** Iterated separating conjunction [H1 * .. * HN] *)

val hstars : coq list -> coq

(** Lifted existentials [\exists x, H] *)

val hexists : Coq.var -> coq -> coq -> coq

(** Lifted existentials [\exists x, H], alternative presentation *)

val hexists_one : Coq.var * coq -> coq -> coq

(** Iteration of lifted existentials [\exists x1, .. \exists xn, H] *)

val hexistss : (Coq.var * coq) list -> coq -> coq

(** Lifted existentials [\exists x, H] *)

val hforall : Coq.var -> coq -> coq -> coq

(** Lifted existentials [\forall x, H], alternative presentation *)

val hforall_one : Coq.var * coq -> coq -> coq

(** Iteration of lifted existentials [\forall x1, .. \forall xn, H] *)

val hforalls : (Coq.var * coq) list -> coq -> coq

(** Lifted propositions [ [P] ] *)

val hpure : coq -> coq

(** Garbage collection [ [\GC] ] *)

val hgc : coq

(** Magic wand [H1 \-* H2] *)

val hwand : coq -> coq -> coq

(** Magic wand [Q1 \--* Q2] *)

val qwand : coq -> coq -> coq

(** Magic wand with pure left hand side [\[P] \-* H] *)

val hwand_hpure : coq -> coq -> coq

val hwand_hpures : coq list -> coq -> coq

val formula_app : coq -> coq -> coq

val himpl_formula_app : coq -> coq -> coq -> coq

val formula_def : var -> var -> coq -> coq

val forall_prepost : var -> var -> var -> coq -> coq
