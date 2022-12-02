open Coq


(*#########################################################################*)
(* ** Syntax of characteristic formulae *)

type for_loop_dir = For_loop_up | For_loop_down

type record_items = (var * coq * coq) list

type cf =
    Cf_val of coq
  | Cf_fail
  | Cf_assert of cf
  | Cf_done
  | Cf_record_new of var * record_items
  | Cf_record_with of coq * record_items * coqs
  | Cf_app of coqs * coq * coq * coqs
  | Cf_body of var * vars * typed_vars * coq * cf
  | Cf_let of typed_var * cf * cf
  | Cf_let_poly of var * vars * vars * coq * cf * cf
  | Cf_let_val of var * vars * coq * coq * cf
  | Cf_let_fun of (var * cf) list * cf
  | Cf_if of coq * cf * cf
  | Cf_case of coq * typed_vars * coq * coq option *
      (typed_var * coq) list * cf * cf
  | Cf_match of var * coq * int * cf
  | Cf_seq of cf * cf
  | Cf_for of for_loop_dir * var * coq * coq * cf
  | Cf_while of cf * cf
  | Cf_manual of coq
  | Cf_pay of cf

type cftop =
    Cftop_val of typed_var * coq option
  | Cftop_heap of var
  | Cftop_val_cf of var * vars * vars * coq
  | Cftop_let_cf of var * var * var * cf
  | Cftop_fun_cf of var * cf
  | Cftop_coqs of coqtops

and cftops = cftop list

(** Shorthand *)

type coq = Coq.coq

(*#########################################################################*)
(* ** Shared functions *)

(** Abstract datatype for dynamic values *)

let coq_dyn = coq_cfml_var "SepLifted.dyn_make"

let coq_dyn_at = coq_at coq_dyn

let coq_dyn_of t v =
  coq_apps coq_dyn_at [t; coq_wild; v]

(** Encoder type *)

let enc_type t =
  coq_app (coq_cfml_var "SepLifted.Enc") t

(** Injectivity property *)

let coq_injective =
  coq_var "TLC.LibOperation.injective"

(** Encoder constructor *)

let enc_make =
  coq_cfml_var "SepLifted.make_Enc"

(** Encoder function *)

let enc = coq_cfml_var "SepLifted.enc"

let enc_of c =
  coq_apps enc [c]

let enc_of_typed typ c =
  coq_apps (coq_at enc) [typ; coq_wild; c]

(** [enc_arg aname] where [aname] is "A" returns [("EA", Enc A)] *)

let enc_arg aname =
  let eaname = "E" ^ aname in (* TODO: check conflicts *)
  (eaname, enc_type (coq_var aname))

(* enc_args builds [(A1:Type) (EA1:Enc A1) .. (xn:Type) (EAn:Enc An)] from [A1... An]*)

let enc_args names =
  List.flatten (List.map (fun aname -> [(aname,Coq_type); enc_arg aname]) names)

(** Universal [forall (A1:Type) (EA1:Enc A1) .. (xn:Type) (EAn:Enc An), c] *)

let coq_forall_enc_types names c =
  coq_foralls (enc_args names) c

(** Function [fun (A1:Type) (EA1:Enc A1) .. (xn:Type) (EAn:Enc An) => c] *)

let coq_fun_enc_types names c =
  coq_funs (enc_args names) c

(** Syntax of application *)

let trm_apps cf cvs =
  coq_apps (coq_cfml_var "Semantics.trm_apps") [cf; coq_list cvs]

let trm_apps_lifted cf cvs =
  coq_apps (coq_cfml_var "SepLifted.Trm_apps") [cf; coq_list cvs]

(** Abstract datatype for functions --TODO: could use val directly? *)

let func_type = val_type (* coq_cfml_var "WPBuiltin.func" *)

(** Abstract data type for fields *)

let field_type =
  coq_cfml_var "Semantics.field"

(** Abstract data type for locations *)

let loc_type =
  coq_cfml_var "Semantics.loc"

(** Abstract data type for heaps *)

let heap =
  coq_cfml_var "SepBase.SepBasicCore.heap"

(** Type of proposition on heaps, [hprop], a shorthand for [heap->Prop] *)

let hprop =
   coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hprop"

(** Type of representation predicates *)

let htype c_abstract c_concrete =
   coq_apps (coq_cfml_var "WPLib.htype") [c_abstract; c_concrete]

(** Predicate transformer for Separation Logic *)

(* FIXME unused
let mkstruct =
  coq_cfml_var "WPLifted.MkStruct"
 *)

(** The identity representation predicate *)

let id_repr =
   coq_cfml_var "SepBase.SepBasicSetup.HS.Id" (* TODO: introduce a shortname *)

(** Representation predicate tag *)

let hdata c_concrete c_abstract =
   coq_apps (coq_cfml_var "SepBase.SepBasicSetup.HS.repr") [c_abstract; c_concrete]

(** Type of pure post-conditions [_ -> Prop] *)

let wild_to_prop =
   coq_pred Coq_wild

(** Type of imperative post-conditions [_ -> hrop] *)

let wild_to_hprop =
   Coq_impl (Coq_wild, hprop)

(** Hprop entailment [H1 ==> H2] *)

let himpl h1 h2 =
  coq_apps (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.himpl") [h1;h2]

(** Specialized Hprop entailment [H1 ==> Q2 tt] *)

let himpl_unit h1 q2 =
  himpl h1 (Coq_app (q2, coq_tt))

(** Postcondition entailment [Q1 ===> Q2] *)

let qimpl q1 q2 =
  coq_apps (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.qimpl") [q1;q2]

(** Specialized post-conditions [fun (_:unit) => H], i.e. [# H] *)

let post_unit h =
  coq_fun ("_",coq_typ_unit) h

(** Separating conjunction [H1 * H2] *)

let hstar h1 h2 =
  coq_apps (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hstar") [h1;h2]

(** Separating conjunction [Q1 * H2] *)

let qstar q1 h2 =
  let temp = "res__" in (* TODO: clash check *)
  coq_fun (temp,coq_wild) (hstar (coq_app q1 (coq_var temp)) h2)

(** Pure heap predicates [ \[P] ] *)

let hpure c =
   coq_app (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hpure") c

(** Pure heap predicates [ \GC ] *)

let hgc =
   (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hgc")

(** Magic wand [H1 \-* H2] *)

let hwand h1 h2 =
  coq_apps (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hwand") [h1;h2]

(** Magic wand with pure left hand side [\[P] \-* H] *)

let hwand_hpure p h =
  hwand (hpure p) h

(** Magic wand with several pure left hand sides [\[P1] \-* \[P2] \-* H] *)

let hwand_hpures ps h =
  List.fold_right hwand_hpure ps h

(** Magic wand for postconditions [Q1 \--* Q2] *)

let qwand q1 q2 =
  coq_apps (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.qwand") [q1;q2]

(** Base data [hsingle c1 c2] *)

let hsingle c1 c2 =
  coq_apps (coq_var_at "CFML.SepBase.hsingle") [c1;Coq_wild;c2]

(** Empty heap predicate [[]] *)

let hempty =
   coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hempty"

(** Iterated separating conjunction [H1 * .. * HN] *)

let hstars hs =
   match (List.rev hs) with
   | [] -> hempty
   | hn::hs' -> List.fold_left (fun acc x -> hstar x acc) hn hs'

(** Lifted existentials [\exists x, H] *)

let hexists xname xtype h =
   Coq_app (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hexists", coq_fun (xname, xtype) h)

(** Lifted existentials [\exists x, H], alternative *)

let hexists_one (xname, xtype) h =
   hexists xname xtype h

(** Iteration of lifted existentials [\exists x1, .. \exists xn, H] *)

let hexistss x_names_types h =
  List.fold_right (fun (xname,xtype) acc -> hexists xname xtype acc) x_names_types h

(** Lifted universal [\forall x, H] *)

let hforall xname xtype h =
   Coq_app (coq_cfml_var "SepBase.SepBasicSetup.SepSimplArgsCredits.hforall", coq_fun (xname, xtype) h)

(** Lifted universal [\forall x, H], alternative *)

let hforall_one (xname, xtype) h =
   hforall xname xtype h

(** Iteration of lifted universals [\forall x1, .. \forall xn, H] *)

let hforalls x_names_types h =
  List.fold_right hforall_one x_names_types h

(** Precise type of formulae [hprop->(T->hprop)->Prop] *)

let formula_type_of c =
   coq_impls [hprop; Coq_impl (c, hprop)] Coq_prop

(** Generic type of formulae [hprop->(_->hprop)->Prop] *)

let formula_type =
   formula_type_of Coq_wild

(** Application of a formula [F _ _ Q] *)

let formula_app f q =
  coq_apps f [coq_wild; coq_wild; q]

(** Entailment for a formula [H ==> F _ _ Q] *)

let himpl_formula_app h f q =
  himpl h (formula_app f q)

(** Construction of a formula of the form [fun A (EA:enc A) (Q:A->hprop) => H] *)

let formula_def aname qname c =
  let typ_a = Coq_type in
  let typ_q = coq_impl (coq_var aname) hprop in
  coq_funs [(aname,typ_a); enc_arg aname; (qname,typ_q)] c

(** Construction of a proposition of the form [forall (H:hprop) A (EA:enc A) (Q:A->hprop) => P] *)

let forall_prepost h aname qname p =
  let typ_a = Coq_type in
  let typ_q = coq_impl (coq_var aname) hprop in
  coq_foralls [(h,hprop); (aname,typ_a); enc_arg aname; (qname,typ_q)] p


(* TODO: check which of these bindings are actually needed *)
