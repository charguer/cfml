open Coq
open Mytools


(*#########################################################################*)
(* ** Syntax of characteristic formulae *)

type for_loop_dir = For_loop_up | For_loop_down

type cf =
    Cf_val of coq
  | Cf_fail
  | Cf_assert of cf
  | Cf_done
  | Cf_record_new of (var * coq * coq) list
  | Cf_app of coqs * coq * coq * coqs
  | Cf_body of var * vars * typed_vars * coq * cf
  | Cf_let of typed_var * cf * cf
  | Cf_let_poly of var * vars * vars * coq * cf * cf
  | Cf_let_val of var * vars * coq * coq * cf
  | Cf_let_fun of (var * cf) list * cf
  | Cf_if of coq * cf * cf
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

let coq_dyn_at = coq_var_at "CFML.SepLifted.dyn"

(** Encoder type *)

let enc_type t =
  coq_app (coq_var "CFMF.SepLifted.Enc") t

(** Encoder function *)

let enc = coq_var "CFML.SepLifted.enc"

let enc_of c =
  coq_apps enc [c]

let enc_of_typed typ c =
  coq_apps (coq_at enc) [typ; coq_wild; c]

(** Syntax of application *)

let trm_apps cf cvs =
  coq_apps (coq_var "CFML.Semantics.trm_apps") [cf; coq_list cvs]

(** Encoder function for a specific type*)

let enc_at = coq_var "CFML.SepLifted.enc"

(** Abstract datatype for functions *)

let func_type = coq_var "CFML.CFLib.func"

(** Abstract data type for fields *)

let field_type =
  coq_var "CFML.Semantics.field"

(** Abstract data type for locations *)

let loc_type =
  coq_var "CFML.Semantics.loc"

(** Abstract data type for heaps *)

let heap =
  coq_var "CFML.SepBase.heap"

(** Type of proposition on heaps, [hprop], a shorthand for [heap->Prop] *)

let hprop =
   coq_var "CFML.SepBase.hprop"

(** Type of representation predicates *)

let htype c_abstract c_concrete =
   coq_apps (coq_var "CFML.CFHeaps.htype") [c_abstract; c_concrete]

(** Predicate transformer for Separation Logic *)

let mkstruct =
  coq_var "CFML.WPLifted.MkStruct"

(** The identity representation predicate *)

let id_repr =
   coq_var "CFML.SepBase.Id"

(** Representation predicate tag *)

let hdata c_concrete c_abstract =
   coq_apps (coq_var "CFML.SepBase.repr") [c_abstract; c_concrete]

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

let himpl h1 h2 =
  coq_apps (coq_var "CFML.SepBase.himpl") [h1;h2]

(** Specialized Hprop entailment [H1 ==> Q2 tt] *)

let himpl_unit h1 q2 =
  himpl h1 (Coq_app (q2, coq_tt))

(** Postcondition entailment [Q1 ===> Q2] *)

let qimpl q1 q2 =
  coq_apps (coq_var "CFML.SepBase.qimpl") [q1;q2]

(** Specialized post-conditions [fun (_:unit) => H], i.e. [# H] *)

let post_unit h =
  Coq_fun (("_",coq_unit), h)

(** Separating conjunction [H1 * H2] *)

let hstar h1 h2 =
  coq_apps (coq_var "CFML.SepBase.hstar") [h1;h2]

(** Magic wand [H1 \-* H2] *)

let hstar h1 h2 =
  coq_apps (coq_var "CFML.SepBase.hwand") [h1;h2]

(** Magic wand for postconditions [Q1 \--* Q2] *)

let hstar q1 q2 =
  coq_apps (coq_var "CFML.SepBase.qwand") [q1;q2]

(** Base data [hsingle c1 c2] *)

let hsingle c1 c2 =
  coq_apps (coq_var_at "CFML.SepBase.hsingle") [c1;Coq_wild;c2]

(** Empty heap predicate [[]] *)

let hempty =
   coq_var "CFML.SepBase.hempty"

(** Iterated separating conjunction [H1 * .. * HN] *)

let hstars hs =
   match (List.rev hs) with
   | [] -> hempty
   | hn::hs' -> List.fold_left (fun acc x -> hstar x acc) hn hs'

(** Lifted existentials [\exists x, H] *)

let heap_exists xname xtype h =
   Coq_app (coq_var "CFML.SepBase.hexists", Coq_fun ((xname, xtype), h))

(** Lifted existentials [\exists x, H], alternative *)

let heap_exists_one (xname, xtype) h =
   heap_exists xname xtype h

(** Iteration of lifted existentials [\exists x1, .. \exists xn, H] *)

let heap_existss x_names_types h =
  List.fold_right (fun (xname,xtype) acc -> heap_exists xname xtype acc) x_names_types h

(** Lifted propositions [ \[P] ] *)

let hpure c =
   coq_app (coq_var "CFML.SepBase.hpure") c

(** Construction of a formula of the form [fun A (EA:enc a) (Q:A->hprop) => CF] *)

let formula_def a q c =
  let typ_a = Coq_type in
  let ea = "E" ^ a in
  let typ_ea = enc_type a in
  let typ_q = coq_impl a hprop in
  coq_funs [(a,typ_a); (ea,typ_ea); (q,typ_q)] c


(* TODO: check which of these bindings are actually needed *)