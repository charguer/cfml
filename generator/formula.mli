open Coq


(** This module contains a data structure for representing characteristic
    formulae. Such data is constructed in file [characteristic.ml] from
    the typed abstract syntax tree, and is converted into a Coq expression
    (as described in [coq.ml]), using an algorithm contained in this file. *)


(** For loop direction *)

type for_loop_dir = For_loop_up | For_loop_down

(** Characteristic formulae for terms *)

type cf =
  | Cf_ret of coq 
    (* Ret v *)
  | Cf_fail
    (* Fail *)
  | Cf_assert of cf
    (* Assert Q *)
  | Cf_done
    (* Done *)
  | Cf_record_new of coq
    (* AppNew [.. (fi, @dyn Ai xi) .. ] *)
  | Cf_app of coqs * coq * coq * coqs  
    (* App f [.. (@dyn Ai xi) .. ] (B:=B) *)
  | Cf_body of var * vars * typed_vars * coq * cf
    (* Body f Ai xi => Q *)
  | Cf_let of typed_var * cf * cf 
    (* Let x := Q1 in Q2 *)
  | Cf_let_poly of var * vars * vars * coq * cf * cf 
    (* Let x [Ai,Bi] := Q1 in Q2  // where x : forall Ai.T *)
  | Cf_val of var * vars * coq * coq * cf 
    (* Let x [Ai] := v in Q2  // where x : forall Ai.T *)
  | Cf_fun of (var * cf) list * cf 
    (* Let fi := Qi in Q *)
  | Cf_caseif of coq * cf * cf 
    (* If v Then Q1 else Q2 *)
  | Cf_case of coq * typed_vars * coq * coq option * (typed_var*coq) list * cf * cf 
    (* Case v [xi] p [When c] Then (Alias yk = vk in Q1) else Q2 *)
  | Cf_match of var * int * cf
    (* Match ?lab n Q *)
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
  | Cftop_val of typed_var
    (* Lemma x_safe : Inhab t. Proof. typeclass. Qed.
       Parameter x : t. *)
  | Cftop_heap of var
    (* Parameter h : heap. *)
  | Cftop_pure_cf of var * vars * vars * cf 
    (* Parameter x_cf : forall Ai Bi P, F (P Ai) -> P Ai (x Ai) *)
  | Cftop_val_cf of var * vars * vars * coq 
    (* Parameter x_cf: forall Ai, x = V *)
  | Cftop_let_cf of var * var * var * cf 
    (* Parameter x_cf : forall H Q, H h -> F H Q -> Q x h' *)
  | Cftop_fun_cf of var * cf
    (* Parameter f_cf : Val := H *)
  | Cftop_coqs of coqtops
    (* arbitrary coq top-level commands *)

and cftops = cftop list


(*#########################################################################*)


(** Abstract datatype for dynamic values *)

val coq_dyn_at : Coq.coq

(** Abstract datatype for functions (func) *)

val func_type : Coq.coq

(** Abstract data type for locations (loc) *)

val loc_type : Coq.coq

(** Abstract data type for heaps *)

val heap : Coq.coq

(** Type of proposition on heaps, [hprop], a shorthand for [heap->Prop] *)

val hprop : Coq.coq

(** Constructor for [htype A a], used for representation predicates *)

val htype : Coq.coq -> Coq.coq -> Coq.coq

(** The identity representation predicate *)

val id_repr : Coq.coq

(** constructor for [hdata X x], printed as [x ~> X] in Coq *)

val hdata : Coq.coq -> Coq.coq -> Coq.coq

(** Type of pure post-conditions [_ -> Prop] *)

val wild_to_prop : Coq.coq

(** Type of imperative post-conditions [_ -> hrop] *)

val wild_to_hprop : Coq.coq

(** Precise type of formulae [hprop->(T->hprop)->Prop] *)

val formula_type_of : Coq.coq -> Coq.coq

(** Generic type of formulae [hprop->(_->hprop)->Prop] *)

val formula_type : Coq.coq

(** Hprop entailment [H1 ==> H2] *)

val heap_impl : Coq.coq -> Coq.coq -> Coq.coq

(** Specialized Hprop entailment [H1 ==> Q2 tt] *)

val heap_impl_unit : Coq.coq -> Coq.coq -> Coq.coq

(** Postcondition entailment [Q1 ===> Q2] *)

val post_impl : Coq.coq -> Coq.coq -> Coq.coq

(** Specialized post-conditions [fun (_:unit) => H], i.e. [# H] *)

val post_unit : Coq.coq -> Coq.coq

(** Separating conjunction [H1 * H2] *)

val heap_star : Coq.coq -> Coq.coq -> Coq.coq

(** Base data [heap_is_single c1 c2] *)

val heap_is_single : Coq.coq -> Coq.coq -> Coq.coq

(** Empty heap predicate [[]] *)

val heap_empty : Coq.coq

(** Iterated separating conjunction [H1 * .. * HN] *)

val heap_stars : Coq.coq list -> Coq.coq

(** Lifted existentials [Hexists x, H] *)

val heap_exists : Coq.var -> Coq.coq -> Coq.coq -> Coq.coq

(** Lifted existentials [Hexists x, H], alternative presentation *)

val heap_exists_one : Coq.var * Coq.coq -> Coq.coq -> Coq.coq

(** Iteration of lifted existentials [Hexists x1, .. Hexists xn, H] *)

val heap_existss : (Coq.var * Coq.coq) list -> Coq.coq -> Coq.coq

(** Lifted propositions [ [P] ] *)

val heap_pred : Coq.coq -> Coq.coq
