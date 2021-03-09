open Coq
open Mytools
open Formula
open Renaming


(*#########################################################################*)
(* ** Conversion of characteristic formulae to Coq *)

let coq_apps_cfml_var x args =
  coq_apps (coq_cfml_var x) args


(* TODO: extract hard coded constants*)

let rec coqtops_of_cf cf =
  let aux = coqtops_of_cf in

  let h = Coq_var "H" in (* TODO: later not used? *)
  let q = Coq_var "Q" in

  match cf with

  | Cf_val v ->
      coq_apps_cfml_var "WPLifted.Wpgen_Val" [v]

  | Cf_assert cf1 ->
      coq_apps_cfml_var "WPLifted.Wpgen_assert" [aux cf1]

  | Cf_fail ->
      coq_cfml_var "WPLifted.Wpgen_fail"

  | Cf_done ->
      coq_cfml_var "WPLifted.Wpgen_done"

  | Cf_record_new (record_name, items) ->
      (* Each item is a tuple (fi, ti, vi) *)
      (* Dynlistof = (fun r => [(f1, @dyn t1 _ v1); ...; (fn, @dyn tn _ vn)]) *)
      let build_field (field_name, field_type, field_value) =
        Coq_tuple [Coq_var field_name; coq_dyn_of field_type field_value] in
      let dynlist = coq_list (List.map build_field items) in
      let dynlistof = coq_fun (record_name, loc_type) dynlist in
      coq_apps_cfml_var "WPRecord.Wpgen_record_new" [dynlistof]

  | Cf_app (ts, tret, f, vs) ->
      (* Wpgen_App_typed tret f [(@dyn t1 _ v1); (@dyn t2 _ v2)] *)
      assert (List.length ts = List.length vs);
      let args = List.map2 coq_dyn_of ts vs in
      coq_apps_cfml_var "WPLifted.Wpgen_App_typed" [tret; f; args]

  | Cf_body (f, fvs, targs, typ, cf1) ->
      (* Wpgen_body (forall Ai x1 x2 H A EA Q,
                       (H ==> ^F Q) ->
                       Triple (trm_Apps f [(@dyn t1 _ v1);.. ; (@dyn tn _ xn)]) H Q) *)
      let args = coq_list (List.map (fun (x,t) -> coq_dyn_of t x) targs) in
      let premi = himpl h (formula_app (aux cf1) q) in
      let concl = coq_apps_cfml_var "SepLifted.Triple" [f; args; h; q] in
      let hyp1 = forall_prepost h a q (coq_impl premi concl) in
      let hyp = coq_forall_types fvs (coq_foralls targs hyp1) in
      coq_apps_cfml_var "WPLifted.Wpgen_body" [hyp]
      (* TODO later find how to factorize over the list of arguments *)

  | Cf_let (typed_x, cf1, cf2) ->
      let c1 = aux cf1 in
      let c2 = coq_fun typed_x (aux cf2) in
      coq_apps_cfml_var "WPLifted.Wpgen_let_typed" [c1; c2]

  | Cf_let_poly (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
      coq_var "unsupported"
      (* LATER
      let type_of_x = coq_forall_types fvs_strict typ in
      let tvars = coq_vars fvs_strict in
      let p1_on_tvars = coq_app_var_at "P1" tvars in
      let p1_on_arg = Coq_app (p1_on_tvars, Coq_var "_r") in
      let h1 = Coq_var "H1" in
      let q1 = Coq_fun (("_r",typ), heap_star (hpure p1_on_arg) h1) in
      let c1 = coq_forall_types (fvs_strict @ fvs_other) (coq_apps (aux cf1) [h;q1]) in
      let x_on_tvars = coq_app_var_at x tvars in
      let hyp_on_x = coq_forall_types fvs_strict (coq_apps (coq_var_at "P1") (tvars @ [ x_on_tvars ])) in
      let c2 = coq_foralls [x,type_of_x] (Coq_impl (hyp_on_x, coq_apps (aux cf2) [h1;q])) in
      let type_of_p1 = coq_forall_types fvs_strict (coq_pred typ) in
      funhq "tag_let_poly" (*~label:x*) (coq_exist "P1" type_of_p1 (coq_exist "H1" hprop (coq_conj c1 c2)))
      (*(!L a: (fun H Q => exists (P1:forall A1, T -> Prop) (H1:hprop),
                            (forall A1 B1, C1 H (fun r => \[P A1 r] \* H1))
                         /\ forall (x1:forall A1,T), ((forall A1, P1 A1 (x1 A1)) -> C2 H1 Q)) *)
      (* TODO: (fun A EA Q =>
                          \exists (P1:forall A1, T -> Prop) H1,
                               (\forall A1 B1, C1 (fun r => \[P A1 r] \* H1))
                            \hand
                               \[H1 ==> forall (x1:forall A1,T), ((forall A1, P1 A1 (x1 A1)) -> C2 Q)\] *)
      *)
  | Cf_let_val (x, fvs, typ_body, v, cf) ->
      (* let x : (forall fvs, typ_body) = v in cf *)
      (* Wpgen_let_val (fun A EA Q =>
           \forall (x:(forall Ai,T)), \[x = (fun Ai => v)] \-* ^F Q) *)
      let typ = coq_forall_types fvs typ_body in
      let lifted_v = coq_fun_types fvs v in
      let c = coq_fun (x,typ) (aux cf) in
      coq_apps_cfml_var "WPLifted.Wpgen_let_Val" [lifted_v; c]

  | Cf_let_fun (fcs, cf) ->
      (* fcs list of pairs (fi, bi) *)
      (* Wpgen_let_fun (fun A EA Q =>
            \forall f1 f2, \[B1] \-* \[B2] \-* (^F Q)) *)
      let a = "__A" in (* TODO: make sure it is reserved *)
      let q = "__Q" in (* TODO: make sure it is reserved *)
      let fs, bs = List.split fcs in
      (* fs list of pairs (fi,Type) *)
      let fts = List.map (fun f -> (f, func_type)) fs in
      let body = hforalls fts (hwand_hpures bs (formula_app (aux cf) q)) in
      let bodyof = formula_def a q body in
      coq_apps_cfml_var "WPLifted.Wpgen_let_fun" bodyof

  | Cf_if (v,cf1,cf2) ->
      coq_apps_cfml_var "WPLifted.Wpgen_if_bool" [v; aux cf1; aux cf2]

  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
    coq_var "unsupported"
    (* TODO: later
      let add_alias ((name,typ),exp) cf : coq =
         funhq "tag_alias" (coq_foralls [name,typ] (coq_impls [coq_eq (Coq_var name) exp] (coq_apps cf [h;q])))
         (* !L a: (fun H Q => forall y, y = v -> F H Q) *)
         in
      let cf1_aliased = List.fold_right add_alias aliases (aux cf1) in
      let same = coq_eq v pat in
      let same_when = match vwhenopt with None -> [same] | Some w -> [same; w] in
      let c1 = coq_foralls tps (coq_impls same_when (coq_apps (cf1_aliased) [h;q])) in
      let diff = coq_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_disj diff (coq_neg w) in
      let c2 = Coq_impl (coq_foralls tps diff_when, coq_apps (aux cf2) [h;q]) in
      let tag = match vwhenopt with None -> "tag_case" | Some w -> "tag_casewhen" in
      funhq tag (coq_conj c1 c2)
      (* (!C a: (fun H Q => (forall x1, x = p [-> trueb w] -> (!L a: y := v in F1) H Q)
                      /\ ((forall x1, x <> p [\/ trueb !w]) -> F2 H Q)))
          where trueb are implicit by coercions *)
      *)

  | Cf_match (label, n, cf1) ->
      coq_var "unsupported"
      (* TODO: later
       let f = Coq_app (coq_cfml_var "CFHeaps.local", (aux cf1)) in
       coq_tag "tag_match" f
       *)

  | Cf_pay (cf1) ->
      coq_var "unsupported"
      (* TODO: LATER
      let h' = Coq_var "H'" in
      let c1 = coq_apps (coq_cfml_var "CFHeaps.pay_one") [h;h'] in
      let c2 = coq_apps (aux cf1) [h'; Coq_var "Q"]  in
      funhq "tag_pay" (coq_exist "H'" hprop (coq_conj c1 c2))
      (* (!Pay: fun H Q => exists H', pay_one H H' /\ F1 H' Q *)
      *)

  | Cf_manual c -> c


  (* TODO: for each ocaml typedef, need an instance of Enc *)

  (* --todo: scope of type variables should be different than that of program variables: prefix them! *)


(*#########################################################################*)
(* ** Characteristic formulae for top level declarations *)

let coqtops_of_cftop coq_of_cf cft =
  match cft with

  | Cftop_val (x,t) ->
     (* Parameter x : t. *)
     [ Coqtop_param (x,t) ]

     (* TODO: later, when side effects are allowed, we need to check type is inhabited
     [ Coqtop_instance ((x ^ "_type_inhab", Coq_app (Coq_var "Inhab", t)), true);
       Coqtop_proof "inhab.";
       Coqtop_text ""; ] @
       *)
     (* --Lemma x_safe : Inhab t. Proof. typeclass. Qed.
        Parameter x : t *)

  | Cftop_val_cf (x,fvs_strict,fvs_other,v) ->
      (* Parameter x_cf : (forall Ai Bi, x = v). *)
      let hyp = coq_forall_types (fvs_strict @ fvs_other) (coq_eq (coq_var x) v) in
      [ Coqtop_param (cf_axiom_name x, hyp)]
      (* DEPRECATED let t = coq_tag "tag_top_val" hyp in *)

  | Cftop_fun_cf (x,cf) ->
      (* Parameter x_cf : hyp. *)
      [ Coqtop_param (cf_axiom_name x, coq_of_cf cf) ]
      (* DEPRECATED let t = coq_tag "tag_top_fun" () in *)


  | Cftop_heap h -> (* TODO: not used! *)
      failwith "not used"
      [ Coqtop_param (h, heap) ]
      (* Parameter h : heap. *)

  | Cftop_let_cf (x,h,h',cf) -> (* TODO: not used! *)
      failwith "not used"
      (*
      let conc = coq_apps (Coq_var "Q") [Coq_var x; Coq_var h'] in
      let hyp1 = Coq_app (Coq_var "H", Coq_var h) in
      let hyp2 = coq_apps (coq_of_cf cf) [Coq_var "H"; Coq_var "Q"] in
      let cf_body = coq_foralls [("H",hprop); ("Q",wild_to_hprop)] (coq_impls [hyp1;hyp2] conc) in
      let t = coq_tag "tag_top_trm" cf_body in
      [ Coqtop_param (cf_axiom_name x, t) ]
      (* Parameter x_cf : (!TT: forall H Q, H h -> F H Q -> Q x h') *)
      *)

  | Cftop_coqs cmds -> cmds


(*#########################################################################*)
(** Main entry point *)

let coqtops_of_cftops cfts =
   list_concat_map (coqtops_of_cftop coqtops_of_cf) cfts



