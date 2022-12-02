open Coq
open Mytools
open Formula
open Renaming


(*#########################################################################*)
(* ** Conversion of characteristic formulae to Coq *)

let coq_apps_cfml_var x args =
  coq_apps (coq_cfml_var x) args

let wpgen_app x args =
  (* Add a pair of parentheses on applications, or a "@" symbol on constants,
     to disable implicit arguments on the resulting Formula *)
  let body =
    match args with
    | [] -> Coq_par (coq_at (coq_cfml_var x))
    | _ -> Coq_par (coq_apps (coq_cfml_var x) args)
    in
  (* Add a tag to allow pretty printing of goals *)
  coq_app (coq_at (coq_cfml_var "WPLifted.Wptag")) body

let _dummy =
  wpgen_app "WPLifted.Wpgen_dummy" []

let dynlist_of_record_fields items =
  let build_field (field_name, field_type, field_value) =
    Coq_tuple [Coq_var field_name; coq_dyn_of field_type field_value] in
  coq_list (List.map build_field items)

(* TODO: extract hard coded constants*)

let rec coqtops_of_cf cf =
  let aux = coqtops_of_cf in

  (* TODO: check clashes with constructors, else add trailing underscore *)
  let aname = "A" in
  let hname = "H" in
  let qname = "Q" in
  (*let a = coq_var aname in*)
  let h = coq_var hname in
  let q = coq_var qname in

  match cf with

  | Cf_val v ->
      wpgen_app "WPLifted.Wpgen_val" [v]

  | Cf_assert cf1 ->
      wpgen_app "WPLifted.Wpgen_assert" [aux cf1]

  | Cf_fail ->
      wpgen_app "WPLifted.Wpgen_fail" []

  | Cf_done ->
      wpgen_app "WPLifted.Wpgen_done" []

  | Cf_record_new (record_name, items) ->
      (* Each item is a tuple (fi, ti, vi) *)
      (* Dynlistof is (fun r => [(f1, @dyn t1 _ v1); ...; (fn, @dyn tn _ vn)]) *)
      let dynlistof = coq_fun (record_name, loc_type) (dynlist_of_record_fields items) in
      wpgen_app "WPRecord.Wpgen_record_new" [dynlistof]

  | Cf_record_with (v, updated_items, all_fields) ->
      (* Each item is a tuple (fi, ti, vi) *)
      wpgen_app "WPRecord.Wpgen_record_with" [v; dynlist_of_record_fields updated_items; coq_list all_fields]

  | Cf_app (ts, tret, f, vs) ->
      (* Wpgen_app tret f [(@dyn t1 _ v1); (@dyn t2 _ v2)] *)
      assert (List.length ts = List.length vs);
      let args = coq_list (List.map2 coq_dyn_of ts vs) in
      wpgen_app "WPLifted.Wpgen_app" [tret; f; args]

  | Cf_body (f, fvs, targs, typ, cf1) ->
      (* targs list of (xi,ti) *)
      (* Wpgen_body (forall Ai x1 x2 H A EA Q,
                       (H ==> ^F (Q \*+ \GC)) ->
                       Triple (trm_Apps f [(@dyn t1 _ v1);.. ; (@dyn tn _ xn)]) H Q) *)
      (* Optimization: don't quantify arguments of type unit
          --bad idea, it breaks notations. we'll remove them in ltac instead.
      let args = List.map (fun (x,t) ->
         coq_dyn_of t (if t <> coq_typ_unit then coq_var x else coq_tt)) targs in
      let targs_nonunit = List.filter (fun (x,t) -> t <> coq_typ_unit) targs in
      *)
      (* TODO: use name tt1__ for generated names of unit type *)
      let args = List.map (fun (x,t) -> coq_dyn_of t (coq_var x)) targs in
      let premi = himpl_formula_app h (aux cf1) (qstar q hgc) in
      let trm = trm_apps_lifted (coq_var f) args in
      let concl = coq_apps_cfml_var "SepLifted.Triple" [trm; h; q] in
      let hyp1 = forall_prepost hname aname qname (coq_impl premi concl) in
      let hyp = coq_forall_enc_types fvs (coq_foralls targs (*targs_nonunit*) hyp1) in
      coq_apps_cfml_var "WPLifted.Wpgen_body" [hyp]
      (* TODO later find how to factorize over the list of arguments *)

  | Cf_let (typed_x, cf1, cf2) ->
      let c1 = aux cf1 in
      let c2 = coq_fun typed_x (aux cf2) in
      wpgen_app "WPLifted.Wpgen_let_trm" [c1; c2]

  | Cf_let_poly (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
      let type_of_x = coq_forall_types (*coq_forall_enc_types *) fvs_strict typ in
      let app_on_tvars f = coq_apps (Coq_par (coq_var_at f)) (List.flatten (List.map (fun v -> [coq_var v (*; coq_var (fst (enc_arg v))*)]) fvs_strict)) in
      let p1_on_arg = Coq_app (app_on_tvars "P1", Coq_var "_r") in
      let h1 = Coq_var "H1" in
      let q1 = coq_fun ("_r",typ) (hstar (hpure p1_on_arg) h1) in
      let c1 = coq_forall_types fvs_strict (coq_forall_enc_types fvs_other (himpl_formula_app h (aux cf1) q1)) in
      let hyp_on_x = coq_forall_types (*coq_forall_enc_types *) fvs_strict (coq_app (app_on_tvars "P1") (app_on_tvars x)) in
      let c2 = coq_foralls [(x,type_of_x)] (coq_impl (hyp_on_x) (himpl_formula_app h1 (aux cf2) q)) in
      let type_of_p1 = coq_forall_types (*coq_forall_enc_types*) fvs_strict (coq_pred typ) in
      let c = coq_exists [("P1",type_of_p1); ("H1",hprop)] (coq_app_conj c1 c2) in (* TODO:name conflicts?*)
      let body = formula_def aname qname (coq_fun (hname,hprop) c) in
      wpgen_app "WPLifted.Wpgen_let_trm_poly" [body]
      (* Define CF as:  (HO is named h above)
          (fun A EA Q => \exists H0, H0 \*
             \[ exists (P1:forall A1, T -> Prop) H1,
                   (forall A1 B1 EB1, H0 ==> C1 (fun r => \[P1 A1 r] \* H1))
                /\ (forall (x1:forall A1,T), (forall A1, P1 A1 (x1 A1 E1)), H1 ==> C2 Q) ]
         Defined as:
           Wpgen_prop (fun A EA Q H => exists (P1:...) ... ) *)
      (* To prove:   H ==> (LetPoly x F1 F2) Q
         Type xsimpl; exists P1; esplit; split; [ intros | intros x Hx ]. *)
      (* Wpgen_prop BodyOf short for [fun A EA Q => \exists H0, H0 \* \[ Bodyof HO Q ] ] *)

  | Cf_let_val (x, fvs, typ_body, v, cf) ->
      (* CF is:  LetVal x : (forall fvs, typ_body) = v in cf *)
      (* CF is:  Wpgen_let_val (fun Ai => v) (fun x : (forall Ai,T) => cf *)
      (* CF is: (fun A EA Q =>
           \forall (x:(forall Ai,T)), \[x = (fun Ai => v)] \-* ^F Q) *)
      (* Def is: Wpgen_let_val V Fof := fun A (EA:Enc A) (Q:A->hprop) =>
                         \forall (x:A1), \[x = V] \-* ^(Fof x) Q). *)
      let typ = coq_forall_types  (*coq_forall_enc_types *) fvs typ_body in
      let lifted_v = coq_fun_types  (* coq_fun_enc_types *) fvs v in
      let c = coq_fun (x,typ) (aux cf) in
      wpgen_app "WPLifted.Wpgen_let_val" [lifted_v; c]

  | Cf_let_fun (fcs, cf) ->
      (* fcs list of pairs (fi, bi) *)
      (* Wpgen_let_fun (fun A EA Q =>
            \forall f1 f2, \[B1] \-* \[B2] \-* (^F Q)) *)
      let fs, cs = List.split fcs in
      let bs = List.map aux cs in
      (* fs list of pairs (fi,Type) *)
      let fts = List.map (fun f -> (f, func_type)) fs in
      let body = hforalls fts (hwand_hpures bs (formula_app (aux cf) q)) in
      let bodyof = formula_def aname qname body in
      wpgen_app "WPLifted.Wpgen_let_fun" [bodyof]

  | Cf_if (v,cf1,cf2) ->
      wpgen_app "WPLifted.Wpgen_if" [v; aux cf1; aux cf2]

  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
      (* TODO: in simple cases: no need for negation hypothesis *)
      (* same_when is [x = p /\ trueb w]
         diff_when is  [x <> p /\ trueb !w]
         // formula is simplified if the when-clause is missing
         formula is (ignoring aliases for simplicity):
           let c1 = `(fun A EA Q => \forall tps, ([same_when] \-* ^(aux cf1) Q)` in
           Wpgen_case c1 (diff_when) (aux cf2) *)
      let add_alias (typed_name,lifted_v) c : coq =
        (* Wpgen_alias (Wpgen_let_val v (fun y => F)) *)
        let calias = wpgen_app "WPLifted.Wpgen_let_val" [lifted_v; coq_fun typed_name c] in
        wpgen_app "WPLifted.Wpgen_alias" [calias] in
      let cf1_aliased = List.fold_right add_alias aliases (aux cf1) in
      let same = coq_app_eq v pat in
      let same_when = match vwhenopt with None -> same | Some w -> coq_app_conj same w in
      let c1_body = hforalls tps (hwand_hpure same_when (formula_app (cf1_aliased) q)) in
      let c1 = formula_def aname qname c1_body in
      let diff = coq_app_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_app_disj diff (coq_app_neg w) in
      let diff_hyp = coq_apps_cfml_var "WPLifted.Wpgen_negpat" [coq_foralls tps diff_when] in
      wpgen_app "WPLifted.Wpgen_case" [c1; diff_hyp; aux cf2]

     (* DEPRECATED
      let cf1_aliased = List.fold_right add_alias aliases (aux cf1) in
      let same = coq_app_eq v pat in
      let same_when = match vwhenopt with None -> [same] | Some w -> [same; w] in
      let c1 = coq_foralls tps (coq_impls same_when (coq_apps (cf1_aliased) [h;q])) in
      let diff = coq_app_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_app_disj diff (coq_app_neg w) in
      let c2 = Coq_impl (coq_foralls tps diff_when, coq_apps (aux cf2) [h;q]) in
      let tag = match vwhenopt with None -> "tag_case" | Some w -> "tag_casewhen" in
      funhq tag (coq_app_conj c1 c2)
      (* (!C a: (fun H Q => (forall x1, x = p [-> trueb w] -> (!L a: y := v in F1) H Q)
                      /\ ((forall x1, x <> p [\/ trueb !w]) -> F2 H Q)))
          where trueb are implicit by coercions *)
      *)

  | Cf_match (label, arg, n, cf1) ->
      wpgen_app "WPLifted.Wpgen_match" [arg; aux cf1]

  | Cf_seq (cf1,cf2) ->
      (* Wpgen_seq F1 F2 *)
      wpgen_app "WPLifted.Wpgen_seq" [aux cf1; aux cf2]

  | Cf_for (dir,i_name,v1,v2,cf1) ->
      (* Wpgen_for_int n1 n2 F *)
      (* Wpgen_for_downto_int n1 n2 F *)
      let pred = match dir with
        | For_loop_up -> "WPLifted.Wpgen_for_int"
        | For_loop_down -> "WPLifted.Wpgen_for_downto_int"
        in
      let body = coq_fun (i_name, coq_typ_int) (aux cf1) in
      wpgen_app pred [v1; v2; body]

  | Cf_while (cf1,cf2) ->
      (* Wpgen_while F1 F2 *)
      wpgen_app "WPLifted.Wpgen_while" [aux cf1; aux cf2]

  | Cf_pay (cf1) ->
      (* Wpgen_pay F1 *)
      wpgen_app "WPLifted.Wpgen_pay" [aux cf1]

  | Cf_manual c -> c


  (* TODO: for each ocaml typedef, need an instance of Enc *)

  (* --todo: scope of type variables should be different than that of program variables: prefix them! *)


(*#########################################################################*)
(* ** Characteristic formulae for top level declarations *)

let coqtops_of_cftop coq_of_cf cft =
  match cft with

  | Cftop_val ((x,t), None) ->
     (* Parameter x : t. *)
     [ Coqtop_param (x,t) ]

     (* TODO: later, when side effects are allowed, we need to check type is inhabited
     [ Coqtop_instance ((x ^ "_type_inhab", Coq_app (Coq_var "Inhab", t)), None, true);
       Coqtop_proof "inhab.";
       Coqtop_text ""; ] @
       *)
     (* --Lemma x_safe : Inhab t. Proof. typeclass. Qed.
        Parameter x : t *)

  | Cftop_val ((x,t), Some tdef) ->
     (* Defintition x : t := tdef. *)
     [ Coqtop_def ((x,t), tdef) ]

  | Cftop_val_cf (x,fvs_strict,fvs_other,v) ->
      (* Parameter x_cf : (forall Ai Bi, x = v). *)
      let hyp = coq_forall_enc_types (fvs_strict @ fvs_other) (coq_app_eq (coq_var x) v) in
      [ Coqtop_param (cf_axiom_name x, hyp)]
      (* DEPRECATED let t = coq_tag "tag_top_val" hyp in *)

  | Cftop_fun_cf (x,cf) ->

      if !Mytools.generate_deep_embedding then begin
        (* Definition x_cf_def := hyp.
           Parameter x_cf : x_cf_def. *)
        let xcf = cf_statement_name x in
        [ Coqtop_def ((xcf, Coq_prop), coq_of_cf cf);
          Coqtop_param (cf_axiom_name x, Coq_var xcf); ]
      end else begin
        (* Parameter x_cf : hyp. *)
        [ Coqtop_param (cf_axiom_name x, coq_of_cf cf) ]
      end

      (* DEPRECATED let t = coq_tag "tag_top_fun" () in *)


  | Cftop_heap h -> (* TODO: not used! *)
      failwith "not used"
      (* [ Coqtop_param (h, heap) ] *)
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



