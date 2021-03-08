open Coq
open Mytools


(*#########################################################################*)
(* ** Syntax of characteristic formulae *)

type for_loop_dir = For_loop_up | For_loop_down

type cf =
    Cf_ret of coq
  | Cf_fail
  | Cf_assert of cf
  | Cf_done
  | Cf_record_new of coq
  | Cf_app of coqs * coq * coq * coqs
  | Cf_body of var * vars * typed_vars * coq * cf
  | Cf_let of typed_var * cf * cf
  | Cf_let_poly of var * vars * vars * coq * cf * cf
  | Cf_val of var * vars * coq * coq * cf
  | Cf_fun of (var * cf) list * cf
  | Cf_caseif of coq * cf * cf
  | Cf_case of coq * typed_vars * coq * coq option *
      (typed_var * coq) list * cf * cf
  | Cf_match of var * int * cf
  | Cf_seq of cf * cf
  | Cf_for of for_loop_dir * var * coq * coq * cf
  | Cf_while of cf * cf
  | Cf_manual of coq
  | Cf_pay of cf

type cftop =
    Cftop_val of typed_var
  | Cftop_heap of var
  | Cftop_pure_cf of var * vars * vars * cf
  | Cftop_val_cf of var * vars * vars * coq
  | Cftop_let_cf of var * var * var * cf
  | Cftop_fun_cf of var * cf
  | Cftop_coqs of coqtops

and cftops = cftop list




(*#########################################################################*)
(* ** Shared functions *)

(** Abstract datatype for dynamic values *)

let coq_dyn_at = coq_var_at "CFML.CFHeaps.dyn" 

(** Abstract datatype for functions *)

let func_type = Coq_var "CFML.CFApp.func"   

(** Abstract data type for locations *)

let loc_type =
  Coq_var "CFML.CFHeaps.loc"

(** Abstract data type for heaps *)

let heap =
   Coq_var "CFML.CFHeaps.heap"

(** Type of proposition on heaps, [hprop], a shorthand for [heap->Prop] *)

let hprop =
   Coq_var "CFML.CFHeaps.hprop"

(** Type of representation predicates *)

let htype c_abstract c_concrete =
   coq_apps (Coq_var "CFML.CFHeaps.htype") [c_abstract; c_concrete]

(** The identity representation predicate *)

let id_repr =
   Coq_var "CFML.CFHeaps.Id" 

(** Representation predicate tag *)

let hdata c_concrete c_abstract =
   coq_apps (Coq_var "CFML.CFHeaps.hdata") [c_abstract; c_concrete]

(** Type of pure post-conditions [_ -> Prop] *)

let wild_to_prop =
   coq_pred Coq_wild

(** Type of imperative post-conditions [_ -> hrop] *)

let wild_to_hprop =
   Coq_impl (Coq_wild, hprop)

(** Precise type of formulae [hprop->(T->hprop)->Prop] *)

let formula_type_of c =
   coq_impls [hprop; Coq_impl (c, hprop)] Coq_prop

(** Generic type of formulae [hprop->(_->hprop)->Prop] *)

let formula_type =
   formula_type_of Coq_wild

(** Hprop entailment [H1 ==> H2] *)

let heap_impl h1 h2 =
  coq_apps (Coq_var "TLC.LibLogic.pred_incl") [h1;h2]

(** Specialized Hprop entailment [H1 ==> Q2 tt] *)

let heap_impl_unit h1 q2 =
  heap_impl h1 (Coq_app (q2, coq_tt))

(** Postcondition entailment [Q1 ===> Q2] *)

let post_impl q1 q2 =
  coq_apps (Coq_var "TLC.LibRelation.rel_incl'") [q1;q2]

(** Specialized post-conditions [fun (_:unit) => H], i.e. [# H] *)

let post_unit h =
  Coq_fun (("_",coq_unit), h)

(** Separating conjunction [H1 * H2] *)

let heap_star h1 h2 = 
  coq_apps (Coq_var "CFML.CFHeaps.heap_is_star") [h1;h2]

(** Base data [heap_is_single c1 c2] *)

let heap_is_single c1 c2 = 
  coq_apps (coq_var_at "CFML.CFHeaps.heap_is_single") [c1;Coq_wild;c2]

(** Empty heap predicate [[]] *)

let heap_empty =
   Coq_var "CFML.CFHeaps.heap_is_empty"

(** Iterated separating conjunction [H1 * .. * HN] *)

let heap_stars hs = 
   match (List.rev hs) with
   | [] -> heap_empty
   | hn::hs' -> List.fold_left (fun acc x -> heap_star x acc) hn hs' 

(** Lifted existentials [Hexists x, H] *)

let heap_exists xname xtype h =
   Coq_app (Coq_var "CFML.CFHeaps.heap_is_pack", Coq_fun ((xname, xtype), h))

(** Lifted existentials [Hexists x, H], alternative *)

let heap_exists_one (xname, xtype) h =
   heap_exists xname xtype h

(** Iteration of lifted existentials [Hexists x1, .. Hexists xn, H] *)

let heap_existss x_names_types h =
  List.fold_right (fun (xname,xtype) acc -> heap_exists xname xtype acc) x_names_types h

(** Lifted propositions [ [P] ] *)

let heap_pred c =
   Coq_app (Coq_var "CFML.CFHeaps.heap_is_empty_st", c)
