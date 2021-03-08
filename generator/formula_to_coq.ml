open Coq
open Mytools
open Formula
open Renaming


(*#########################################################################*)
(* ** Conversion of characteristic formulae to Coq *)

(* TODO: extract hard coded constants*)

let rec coqtops_of_imp_cf cf =
  let coq_of_cf = coqtops_of_imp_cf in
  let h = Coq_var "H" in
  let q = Coq_var "Q" in
  let funhq tag ?label ?rettype c = 
       let typ = match rettype with
       | None -> Coq_wild
       | Some t -> t
       in
     let f_core = coq_funs [("H", hprop);("Q", Coq_impl(typ,hprop))] c in
     let f = Coq_app (Coq_var "CFML.CFHeaps.local", f_core) in
     match label with 
     | None -> coq_tag tag f 
     | Some x ->  (*todo:remove this hack*) if x = "_c" then coq_tag tag f  else
        coq_tag tag ~label:x f 
     in 

  match cf with

  | Cf_ret v -> 
      funhq "tag_ret" (heap_impl h (Coq_app (q,v)))
      (* (!R: fun H Q => H ==> Q v *)

  | Cf_assert cf1 ->
      let p = coq_eq (Coq_var "_b") coq_bool_true in
      let q' = Coq_fun (("_b",coq_bool), heap_star (heap_pred p) h) in       
      let c1 = coq_apps (coq_of_cf cf1) [h;q'] in
      let c2 = heap_impl h (Coq_app (q,coq_tt)) in
      funhq "tag_assert" (coq_conj c1 c2)
      (* (!Assert (fun H Q => F1 H (fun (b:bool) => \[b = true] \* H) /\ H ==> Q tt)) *)
    
  | Cf_fail -> 
      funhq "tag_fail" coq_false

  | Cf_done -> 
      funhq "tag_done" coq_true

  | Cf_record_new (arg) ->
      (* AppNew [.. (fi, @dyn Ai xi) .. ] *)
      coq_tag "tag_record_new" (coq_apps (Coq_var "CFML.CFApp.app_record_new") [arg])

  | Cf_app (ts, tret, f, vs) -> (* TODO: maybe make the return type explicit? *)
      (* old:  let arity = List.length vs in *)
      assert (List.length ts = List.length vs);
      let tvs = List.combine ts vs in
      let args = List.map (fun (t,v) -> coq_apps coq_dyn_at [t;v]) tvs in
      coq_tag "tag_apply" (coq_apps (coq_var_at "CFML.CFApp.app_def") [f; coq_list args; tret])
      (* (!Apply: (app_def f [(@dyn t1 v1) (@dyn t2 v2)])) *)

  (* DEPRECATED
  | Cf_body (f, fvs, targs, typ, cf) ->
      let type_of_k = coq_impls ((List.map snd targs) @ [formula_type_of typ]) Coq_prop in
      let args = List.map fst targs in
      let args_of_k = (List.map coq_var args) @ [ coq_of_cf cf ] in
      let var_k = Coq_var "K" in
      let sarity = string_of_int (List.length targs) in
      let spec_n = Coq_var ("spec_" ^ sarity) in
      let is_spec_k = Coq_app (Coq_var ("is_spec_" ^ sarity), var_k) in
      let hyp_k = coq_foralls targs (coq_apps var_k args_of_k) in
      let concl_k = coq_apps spec_n [var_k; coq_var f] in
      coq_tag "tag_app_curried" (coq_forall_types fvs (coq_foralls ["K", type_of_k] (coq_impls [is_spec_k;hyp_k] concl_k)))       
      (* (!B: (forall Ai K, is_spec_2 K -> 
                 (forall x1 x2, K x1 x2 F) -> spec_2 K f)) *)
  *)

  | Cf_body (f, fvs, targs, typ, cf1) ->
      let narity = Coq_nat (List.length targs) in
      let h_curried = coq_apps (Coq_var "CFML.CFApp.curried") [narity; coq_var f] in 
      let h_body_hyp = coq_apps (coq_of_cf cf1) [h; q] in
      let args = List.map (fun (x,t) -> coq_apps coq_dyn_at [t; coq_var x]) targs in
      let h_body_conc = coq_apps (Coq_var "CFML.CFApp.app_def") [coq_var f; coq_list args; h; q]  in
      let h_body_2 = Coq_impl (h_body_hyp, h_body_conc) in
      let h_body_1 = coq_foralls [("H", hprop); ("Q", Coq_impl (typ, hprop))] h_body_2 in
      let h_body = coq_forall_types fvs (coq_foralls targs h_body_1) in
      coq_tag "tag_app_curried" (coq_conj h_curried h_body)
      (* (!B: curried 2 f /\ 
              (forall Ai x1 x2 H Q, CF H Q -> app f [(dyn t1 x1) (dyn t2 x2)] H Q) *)

  | Cf_let ((x,typ), cf1, cf2) ->
      let c1 = coq_of_cf cf1 in
      let c2 = Coq_fun ((x, typ), coq_of_cf cf2) in
      let f_core = coq_apps (coq_var "CFML.CFPrint.cf_let") [c1;c2] in
      let f = Coq_app (Coq_var "CFML.CFHeaps.local", f_core) in
      coq_tag "tag_let" ~label:x f


  (* OLD
  | Cf_let ((x,typ), cf1, cf2) ->
      let q1 = Coq_var "Q1" in
      let type_of_q1 = Coq_impl (typ, hprop) in
      let c1 = coq_apps (coq_of_cf cf1) [h; q1] in
      let c2 = coq_foralls [x,typ] (coq_apps (coq_of_cf cf2) [(Coq_app (q1, Coq_var x)); q]) in
      funhq "tag_let" ~label:x (coq_exist "Q1" type_of_q1 (coq_conj c1 c2))
      (* !L: fun H Q => exists Q1, F1 H Q1 /\ forall (x:T), F2 (Q1 x) Q *)
  *)

  | Cf_let_poly (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
      let type_of_x = coq_forall_types fvs_strict typ in
      let tvars = coq_vars fvs_strict in
      let p1_on_tvars = coq_app_var_at "P1" tvars in
      let p1_on_arg = Coq_app (p1_on_tvars, Coq_var "_r") in
      let h1 = Coq_var "H1" in
      let q1 = Coq_fun (("_r",typ), heap_star (heap_pred p1_on_arg) h1) in       
      let c1 = coq_forall_types (fvs_strict @ fvs_other) (coq_apps (coq_of_cf cf1) [h;q1]) in
      let x_on_tvars = coq_app_var_at x tvars in 
      let hyp_on_x = coq_forall_types fvs_strict (coq_apps (coq_var_at "P1") (tvars @ [ x_on_tvars ])) in
      let c2 = coq_foralls [x,type_of_x] (Coq_impl (hyp_on_x, coq_apps (coq_of_cf cf2) [h1;q])) in
      let type_of_p1 = coq_forall_types fvs_strict (coq_pred typ) in
      funhq "tag_let_poly" (*~label:x*) (coq_exist "P1" type_of_p1 (coq_exist "H1" hprop (coq_conj c1 c2)))
      (*(!L a: (fun H Q => exists (P1:forall A1, T -> Prop) (H1:hprop), 
                            (forall A1 B1, Q1 H (fun r => \[P A1 r] \* H1))
                         /\ forall (x1:forall A1,T), ((forall A1, P1 A1 (x1 A1)) -> Q2 H1 Q)) *)

  | Cf_val (x, fvs_strict, typ, v, cf) ->
      let type_of_x = coq_forall_types fvs_strict typ in
      let equ = coq_eq (Coq_var x) (coq_fun_types fvs_strict v) in
      let conc = coq_apps (coq_of_cf cf) [h;q] in
      funhq "tag_val" (*~label:x*) (Coq_forall ((x, type_of_x), Coq_impl (equ, conc)))
      (*(!!L x: (fun H Q => forall (x:forall Ai,T), x = (fun Ai => v) -> F H Q)) *)
 
  | Cf_fun (ncs, cf) ->
      let ns, cs = List.split ncs in
      let fs = List.map (fun n -> (n, func_type)) ns in
      let chyps = List.map coq_of_cf cs in
      let cconc = coq_apps (coq_of_cf cf) [h;q] in
      let x = List.hd ns in
      funhq "tag_fun" ~label:x (coq_foralls fs (coq_impls chyps cconc))
      (* (!F a: fun H Q => forall f1 f2, B1 -> B2 -> F H Q) *)            

  (* DEPRECATED
  | Cf_fun (ncs, cf) ->
      let ns, cs = List.split ncs in
      let p_of n = "P" ^ n in
      let fs = List.map (fun n -> (n, func_type)) ns in
      let ps = List.map (fun n -> (p_of n, coq_pred func_type)) ns in
      let c1hyps = List.map coq_of_cf cs in
      let c1conc = coq_conjs (List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns) in
      let c1 = coq_impls c1hyps c1conc in
      let c2hyps = List.map (fun n -> Coq_app (Coq_var (p_of n), Coq_var n)) ns in
      let c2conc = coq_apps (coq_of_cf cf) [h;q] in
      let c2 = coq_impls c2hyps c2conc in
      let x = List.hd ns in
      funhq "tag_fun" ~label:x (coq_foralls fs (coq_exists ps (coq_conj c1 c2)))
      (* (!F a: fun H Q => forall f1 f2, exists P1 P2,
              (B1 -> B2 -> P1 f1 /\ P2 f2) /\ (P1 f1 -> P2 f2 -> F H Q)) *)            
   *)

 (* old
   | Cf_caseif (cf0,cf1,cf2) ->
      let q' = Coq_var "Q'" in
      let c0 = coq_apps (coq_of_cf cf0) [h;q'] in
      let c1 = coq_apps (coq_of_cf cf1) [ Coq_app (q',coq_bool_true); q] in
      let c2 = coq_apps (coq_of_cf cf2) [ Coq_app (q',coq_bool_false); q] in
      funhq "tag_if" (coq_exist "Q'" (Coq_impl (coq_bool,hprop)) (coq_conjs [c0;c1;c2]))
      (* (!I a: (fun H Q => exists Q', Q0 H Q' /\ Q1 (Q' true) Q /\ Q2 (Q' false) Q)) *)
   *)

  | Cf_caseif (v,cf1,cf2) ->
      let c1 = Coq_impl (coq_eq v coq_bool_true,  coq_apps (coq_of_cf cf1) [h;q]) in
      let c2 = Coq_impl (coq_eq v coq_bool_false, coq_apps (coq_of_cf cf2) [h;q]) in
      funhq "tag_if" (coq_conj c1 c2)
      (* (!I a: (fun H Q => (x = true -> Q1 H Q) /\ (x = false -> Q2 H Q))) *)

  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
      let add_alias ((name,typ),exp) cf : coq =
         funhq "tag_alias" (coq_foralls [name,typ] (coq_impls [coq_eq (Coq_var name) exp] (coq_apps cf [h;q])))
         (* !L a: (fun H Q => forall y, y = v -> F H Q) *)
         in
      let cf1_aliased = List.fold_right add_alias aliases (coq_of_cf cf1) in
      let same = coq_eq v pat in
      let same_when = match vwhenopt with None -> [same] | Some w -> [same; w] in
      let c1 = coq_foralls tps (coq_impls same_when (coq_apps (cf1_aliased) [h;q])) in
      let diff = coq_neq v pat in
      let diff_when = match vwhenopt with None -> diff | Some w -> coq_disj diff (coq_neg w) in
      let c2 = Coq_impl (coq_foralls tps diff_when, coq_apps (coq_of_cf cf2) [h;q]) in
      let tag = match vwhenopt with None -> "tag_case" | Some w -> "tag_casewhen" in
      funhq tag (coq_conj c1 c2)
      (* (!C a: (fun H Q => (forall x1, x = p [-> trueb w] -> (!L a: y := v in F1) H Q) 
                      /\ ((forall x1, x <> p [\/ trueb !w]) -> F2 H Q))) 
          where trueb are implicit by coercions *)
  
  | Cf_match (label, n, cf1) ->
     let f = Coq_app (Coq_var "CFML.CFHeaps.local", (coq_of_cf cf1)) in
     coq_tag "tag_match" f 
     (* DEPRECATED
     coq_tag "tag_match" ~args:[Coq_var (Printf.sprintf "%d%s" n "%nat")]  (coq_of_cf cf1)
     *) (*~label:label*)

  | Cf_seq (cf1,cf2) -> 
      let q' = Coq_var "Q'" in
      let c1 = coq_apps (coq_of_cf cf1) [h;q'] in
      let c2 = coq_apps (coq_of_cf cf2) [Coq_app (q', coq_tt); Coq_var "Q"]  in
      funhq "tag_seq" (coq_exist "Q'" wild_to_hprop (coq_conj c1 c2))
      (* (!S: fun H Q => exists Q', F1 H Q /\ F2 (Q' tt) Q *)

  | Cf_for (dir,i_name,v1,v2,cf) ->
      let c = Coq_fun ((i_name, coq_int), coq_of_cf cf) in
      let tag, cf_for = 
         match dir with
         | For_loop_up -> "tag_for", "CFML.CFPrint.cf_for"
         | For_loop_down -> "tag_for_down", "CFML.CFPrint.cf_for_down"
         in
      let f_core = coq_apps (coq_var cf_for) [v1;v2;c] in
      let f = Coq_app (Coq_var "CFML.CFHeaps.local", f_core) in
      coq_tag tag f

      (* DEPRECATED
      let s = Coq_var "S" in
      let i = Coq_var i_name in
      let tag, cond_test, istep = 
         match dir with
         | For_loop_up -> "tag_for", (coq_le i v2), (coq_plus i (Coq_int 1))
         | For_loop_down -> "tag_for_down", (coq_ge i v2), (coq_minus i (Coq_int 1))
         in
      let typs = Coq_impl (coq_int,formula_type) in
      let locals = Coq_app (Coq_var "CFML.CFHeaps.is_local_pred", s) in
      let snext = coq_apps s [ istep ] in
      let cf_step = Cf_seq (cf, Cf_manual snext) in 
      let cf_ret = Cf_ret coq_tt in
      let cond = coq_apps (Coq_var "TLC.LibReflect.isTrue") [ cond_test ] in
      let cf_if = Cf_caseif (cond, cf_step, cf_ret) in
      let bodys = coq_of_cf cf_if in
      let hypr = coq_foralls [(i_name, coq_int); ("H", hprop); ("Q", Coq_impl (coq_unit, hprop))] (Coq_impl (coq_apps bodys [h;q], (coq_apps s [i;h;q]))) in
      funhq tag (Coq_forall (("S",typs), coq_impls [locals; hypr] (coq_apps s [v1;h;q])))
      *)
      (* UP:
         (!For (fun H Q => forall S:int->~~unit, is_local_pred S ->
           (forall i H Q,  
               (If_ i <= v2       
                  Then Seq (F1 ;; S (i+1)) H Q))
                  Else Ret tt) H Q
              -> S i H Q) 
            -> S v1 H Q) 
         
        DOWN:
             (!For (fun H Q => forall S:int->~~unit, is_local_pred S ->
             (forall i H Q,  
               (If_ i >= v2       
                  Then Seq (F1 ;; S (i-1)) H Q))
                  Else Ret tt) H Q
              -> S i H Q) 
            -> S v1 H Q)      
         
         *)

      (* DEPRECATED
      let s = Coq_var "S" in
      let i = Coq_var i_name in
      let typs = Coq_impl (coq_int,formula_type) in
      let q' = Coq_var "Q'" in
      let c1 = coq_apps (coq_of_cf cf) [h;q'] in
      let c2 = coq_apps s [ coq_plus i (Coq_var "1"); Coq_app (q', coq_tt); q] in
      let body_le = funhq "tag_seq" ~rettype:coq_unit (coq_exist "Q'" (Coq_impl (coq_unit, hprop)) (coq_conj c1 c2)) in
      let ple = Coq_impl (coq_le i v2, coq_apps body_le [h; q]) in 
      let body_gt = funhq "tag_ret" ~rettype:coq_unit (heap_impl_unit h q) in     
      let pgt = Coq_impl (coq_gt i v2, coq_apps body_gt [h; q]) in
      let locals = Coq_app (Coq_var "CFML.CFHeaps.is_local_pred", s) in
      let bodys = coq_conj ple pgt in
      let hypr = coq_foralls [(i_name, coq_int); ("H", hprop); ("Q", Coq_impl (coq_unit, hprop))] (Coq_impl (bodys,(coq_apps s [i;h;q]))) in
      funhq "tag_for" (Coq_forall (("S",typs), coq_impls [locals; hypr] (coq_apps s [v1;h;q])))
      *)

  | Cf_while (cf1,cf2) -> 
      let c1 = coq_of_cf cf1 in
      let c2 = coq_of_cf cf2 in
      let f_core = coq_apps (coq_var "CFML.CFPrint.cf_while") [c1;c2] in
      let f = Coq_app (Coq_var "CFML.CFHeaps.local", f_core) in
      coq_tag "tag_while" f

      (*DEPRECATED
      let r = Coq_var "R" in
      let typr = formula_type in
      let cf_step = Cf_seq (cf2, Cf_manual r) in
      let cf_ret = Cf_ret coq_tt in
      let cfif = Cf_caseif (Coq_var "_c", cf_step, cf_ret) in
      let bodyr = coq_of_cf (Cf_let (("_c",coq_bool), cf1, cfif)) in
      let hypr = coq_foralls [("H", hprop); ("Q", Coq_impl (coq_unit, hprop))] (Coq_impl (coq_apps bodyr [h;q],(coq_apps r [h;q]))) in
      let localr = Coq_app (Coq_var "CFML.CFHeaps.is_local", r) in
      funhq "tag_while" (Coq_forall (("R",typr), coq_impls [localr; hypr] (coq_apps r [h;q])))
      *)
      (* (!While: (fun H Q => forall R:~~unit, is_local R ->
          (forall H Q,
             (Let _c = F1 in If _c Then (F2 ; R) Ret tt) H Q
             -> R H Q) 
          -> R H Q). *)

  | Cf_pay (cf1) -> 
      let h' = Coq_var "H'" in
      let c1 = coq_apps (Coq_var "CFML.CFHeaps.pay_one") [h;h'] in
      let c2 = coq_apps (coq_of_cf cf1) [h'; Coq_var "Q"]  in
      funhq "tag_pay" (coq_exist "H'" hprop (coq_conj c1 c2))
      (* (!Pay: fun H Q => exists H', pay_one H H' /\ F1 H' Q *)

(* DEPRECATED:
      let r = Coq_var "R" in
      let typr = formula_type in
      let q' = Coq_var "Q'" in
      let p1 = coq_apps (coq_of_cf cf1) [h;q'] in
      let c1 = coq_apps (coq_of_cf cf2) [h;q'] in
      let c2 = coq_apps r [ Coq_app (q', coq_tt); q] in
      let body2 = funhq "tag_seq" ~rettype:coq_unit (coq_exist "Q'" wild_to_hprop (coq_conj c1 c2)) in
      let p2 = coq_apps body2 [Coq_app(q',coq_bool_true); q] in
      let body3 = funhq "tag_ret" ~rettype:coq_unit (heap_impl_unit h q) in     
      let p3 = coq_apps body3 [Coq_app(q',coq_bool_false); q] in    
      let bodyif = coq_exist "Q'" (Coq_impl (coq_bool, hprop)) (coq_conjs [p1;p2;p3]) in
      let bodyr = coq_apps (funhq "tag_if" bodyif) [h;q] in
      let hypr = coq_foralls [("H", hprop); ("Q", Coq_impl (coq_unit, hprop))] (Coq_impl (bodyr,(coq_apps r [h;q]))) in
      funhq "tag_while" (Coq_forall (("R",typr), coq_impls [localr; hypr] (coq_apps r [h;q])))
      (* (!While: (fun H Q => forall R:~~unit, is_local R ->
          (forall H Q,
             !If: (fun H Q => exists Q', 
                  F1 H Q' 
               /\ (!Seq: (fun H Q => exists Q', F2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
               /\ (!Ret: (fun H Q => H ==> Q tt) (Q' false) Q) 
               H Q
             -> R H Q) 
          -> R H Q). *)
*)
  | Cf_manual c -> c


   (*
  | Cf_letpure (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
      let type_of_x = coq_forall_types fvs_strict typ in
      let tvars = coq_vars fvs_strict in
      let p1_on_tvars = if tvars = [] then Coq_var "P1" else coq_apps (coq_var_at "P1") tvars in
      let c1 = coq_forall_types (fvs_strict @ fvs_other) (Coq_app (coq_of_cf cf1, p1_on_tvars)) in
      let x_on_tvars = if tvars = [] then Coq_var x else coq_apps (coq_var_at x) tvars in 
      let hyp_on_x = coq_forall_types fvs_strict (coq_apps (Coq_var "@P1") (tvars @ [ x_on_tvars ])) in
      let c2 = coq_foralls [x,type_of_x] (Coq_impl (hyp_on_x, Coq_app (coq_of_cf cf2, p))) in
      let type_of_p1 = coq_forall_types fvs_strict (coq_pred typ) in
      funp "tag_let" ~label:x (coq_exist "P1" type_of_p1 (coq_conj c1 c2))
      (*(!L a: (fun P => exists (P1:forall A1, T -> Prop), (forall A1 B1, Q1 (P1 A1))
                             /\ forall (x1:forall A1,T), ((forall A1, P1 A1 (x1 A1)) -> Q2 P)) *)
    
   *)

  (* --todo: scope of type variables should be different than that of program variables: prefix them! *)


(*#########################################################################*)
(* ** Characteristic formulae for top level declarations *)

let coqtops_of_cftop coq_of_cf cft =
  match cft with

  | Cftop_val (x,t) ->
      (* the following is the same as for pure *)
      (* TODO: later, when side effects are allowed, we need to check type is inhabited 
     [ Coqtop_instance ((x ^ "_type_inhab", Coq_app (Coq_var "Inhab", t)), true);
       Coqtop_proof "inhab.";
       Coqtop_text ""; ] @
       *)
     [ Coqtop_param (x,t) ]
     (* --Lemma x_safe : Inhab t. Proof. typeclass. Qed.
        Parameter x : t *)

  | Cftop_pure_cf (x,fvs_strict,fvs_other,cf) -> 
      let type_of_p = coq_forall_types fvs_strict wild_to_prop in
      let p_applied = coq_app_var_at "P" (coq_vars fvs_strict) in
      let x_applied = coq_app_var_at x (coq_vars fvs_strict) in
      let cf_body = coq_foralls ["P", type_of_p] (Coq_impl (Coq_app (coq_of_cf cf, p_applied), Coq_app (p_applied, x_applied))) in
      let hyp = coq_forall_types (fvs_strict @ fvs_other) cf_body in
      let t = coq_tag "tag_top_val" hyp in
      [ Coqtop_param (cf_axiom_name x, t)]
      (* Parameter x_cf : (!TV forall Ai Bi, (forall P:_->Prop, R (P Ai) -> P Ai (x Ai))) *)

  | Cftop_val_cf (x,fvs_strict,fvs_other,v) -> 
      let hyp = coq_forall_types (fvs_strict @ fvs_other) (coq_eq (Coq_var x) v) in
      let t = coq_tag "tag_top_val" hyp in
      [ Coqtop_param (cf_axiom_name x, t)]
      (* Parameter x_cf: (!TV forall Ai Bi, x = v) *)

  | Cftop_fun_cf (x,cf) -> 
      let t = coq_tag "tag_top_fun" (coq_of_cf cf) in
      [ Coqtop_param (cf_axiom_name x, t) ]
      (* Parameter x_cf : (!TF a: H) *)

  | Cftop_heap h ->
      [ Coqtop_param (h, heap) ]
      (* Parameter h : heap. *)

  | Cftop_let_cf (x,h,h',cf) ->   
      let conc = coq_apps (Coq_var "Q") [Coq_var x; Coq_var h'] in
      let hyp1 = Coq_app (Coq_var "H", Coq_var h) in
      let hyp2 = coq_apps (coq_of_cf cf) [Coq_var "H"; Coq_var "Q"] in
      let cf_body = coq_foralls [("H",hprop); ("Q",wild_to_hprop)] (coq_impls [hyp1;hyp2] conc) in
      let t = coq_tag "tag_top_trm" cf_body in 
      [ Coqtop_param (cf_axiom_name x, t) ]
      (* Parameter x_cf : (!TT: forall H Q, H h -> F H Q -> Q x h') *)

  | Cftop_coqs cmds -> cmds


(*#########################################################################*)
(** Main entry point *)

let coqtops_of_cftops cfts =
   list_concat_map (coqtops_of_cftop coqtops_of_imp_cf) cfts



