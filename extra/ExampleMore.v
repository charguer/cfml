


(* WORK IN PROGRESS




  (***********************************************************************)
  (** Stack *)

  module StackList = struct

    type 'a t = {
       mutable items : 'a list;
       mutable size : int }

    let create () =
      { items = [];
        size = 0 }

    let size s =
      s.size

    let is_empty s =
      s.size = 0

    let push x s =
      s.items <- x :: s.items;
      s.size <- s.size + 1

    let pop s =
      match s.items with
      | hd::tl ->
          s.items <- tl;
          s.size <- s.size   - 1;
          hd
      | [] -> assert false

  end


  (***********************************************************************)
  (** Array *)

  let demo_array () =


    let t = Array.make 3 true in
    t.(0) <- false;
    t.(1) <- false;
    t

  let exercise_array () =
    let t = Array.make 3 true in
    t.(2) <- false;
    t.(1) <- t.(2);
    t


  (***********************************************************************)
  (** Vector *)

  module Vector = struct

    type 'a t = {
      mutable data : 'a array;
      mutable size : int;
      default: 'a; }

    let create size def =
      { data = Array.make size def;
        size = size;
        default = def; }

    let size t =
      t.size

    let get t i =
      t.data.(i)

    let set t i v =
      t.data.(i) <- v

    let double_size t =
      let src = t.data in
      let size = t.size in
      let size2 = 2 * size in
      let dst = Array.make size2 t.default in
      for i = 0 to pred size do
        dst.(i) <- src.(i);
      done

    let push t v =
      let size = t.size in
      let capa = Array.length t.data in
      if size = capa
        then double_size t;
      t.size <- size+1;
      t.data.(size) <- v

  end

  (* Variants for double_size t:
     Array.iteri (fun i v <- dst.(i) <- v) src
     Array.init size2 (fun i -> if i < size then src.(i) else t.default)
  *)




  (***********************************************************************)
  (** Stack *)

  (*---------------------------------------------------------------------*)
  (*----
  module StackList = struct

    type 'a t = {
       mutable items : 'a list;
       mutable size : int }

    let create () =
      { items = [];
        size = 0 }

    let size s =
      s.size

    let is_empty s =
      s.size = 0

    let push x s =
      s.items <- x :: s.items;
      s.size <- s.size + 1

    let pop s =
      match s.items with
      | hd::tl ->
          s.items <- tl;
          s.size <- s.size - 1;
          hd
      | [] -> assert false

  end
  ----*)

  Module StackListProof.

  Import StackList_ml.

  (** Definition of [r ~> Stack L], which is a notation for [Stack L r] of type [hprop] *)

  Definition Stack A (L:list A) r :=
    Hexists n,
        r ~> `{ items' := L; size' := n }
     \* \[ n = length L ].


  (**--- begin customization of [xopen] and [xclose] for [Stack] ---*)

    Lemma Stack_open : forall r A (L:list A),
      r ~> Stack L ==>
      Hexists n, r ~> `{ items' := L; size' := n } \* \[ n = length L ].
    Proof using. intros. xunfolds~ Stack. Qed.

    Lemma Stack_close : forall r A (L:list A) (n:int),
      n = length L ->
      r ~> `{ items' := L; size' := n } ==>
      r ~> Stack L.
    Proof using. intros. xunfolds~ Stack. Qed.

    Arguments Stack_close : clear implicits..

    Hint Extern 1 (RegisterOpen (Stack _)) =>
      Provide Stack_open.
    Hint Extern 1 (RegisterClose (record_repr _)) =>
      Provide Stack_close.

  (*--- end ---*)

  Lemma create_spec : forall (A:Type),
    app create [tt]
      PRE \[]
      POST (fun r => r ~> Stack (@nil A)).
  Proof using.
    xcf. xapps. => r. xclose r. auto. xsimpl.
  Qed.

  Lemma size_spec : forall (A:Type) (L:list A) (s:loc),
    app size [s]
      INV (s ~> Stack L)
      POST (fun n => \[n = length L]).

  (* Remark: the above is a notation for:
    app size [s]
      PRE (s ~> Stack L)
      POST (fun n => \[n = length L] \* s ~> Stack L).
  *)

  Proof using.
    xcf.
    xopen s. xpull ;=> n Hn. xapp. => m. xpull ;=> E.
    xclose s. auto. xsimpl. math.
  Unshelve. solve_type. (* todo: xcf A *)
  Qed.

  Lemma length_zero_iff_nil : forall A (L:list A),
    length L = 0 <-> L = nil.
  Proof using.
    =>. subst. destruct L; rew_list. autos*. iff M; false; math.
  Qed.

  Lemma is_empty_spec : forall (A:Type) (L:list A) (s:loc),
    (* <EXO> *)
    app is_empty [s]
      INV (s ~> Stack L)
      POST (fun b => \[b = isTrue (L = nil)]).
    (* </EXO> *)
  Proof using.
    (* <EXO> *)
    xcf. xopen s. xpull ;=> n Hn. xapps. xclose~ s. xrets.
    subst. apply length_zero_iff_nil.
    (* </EXO> *)
  Unshelve. solve_type. (* todo: xcf A *)
  Qed.

  Lemma push_spec : forall (A:Type) (L:list A) (s:loc) (x:A),
    app push [x s]
      PRE (s ~> Stack L)
      POST (# s ~> Stack (x::L)).
  Proof using.
    (* <EXO> *)
    xcf.
    xopen s. (* Same as [xchange (@Stack_open s)] *)
    xpull ;=> n Hn.
    xapps. xapps. xapps. xapp.
    xclose s. (* Same as [xchange (@Stack_close s)] *)
    rew_list. math.
    xsimpl.
    (* </EXO> *)
  Qed.

  Lemma pop_spec : forall (A:Type) (L:list A) (s:loc),
    L <> nil ->
    app pop [s]
      PRE (s ~> Stack L)
      POST (fun x => Hexists L', \[L = x::L'] \* s ~> Stack L').
  Proof using.
    (* <EXO> *)
    =>> HL. xcf. xopen s. xpull ;=> n Hn. xapps. xmatch.
    xapps. xapps. xapps. xret. xclose~ s. rew_list in Hn. math.
    (* </EXO> *)
  Qed.



  (***********************************************************************)
  (** Array *)

  (*---------------------------------------------------------------------*)
  (*----
  let demo_array () =
    let t = Array.make 3 true in
    t.(0) <- false;
    t.(1) <- false;
    t
  ----*)

  Lemma demo_array_spec :
    app demo_array [tt]
      PRE \[]
      POST (fun (t:loc) => Hexists M, (t ~> Array M)
         \* \[forall k, 0 <= k < 3 -> M[k] = isTrue(k > 1)]).
  Proof using.
    dup 2.
    { xcf.
      xapp. math. => M EM.
      xapp. autos.
      xapp. autos.
      xret. xsimpl. =>> Hk. subst M. rew_array; autos.
       case_ifs. math. math. math. }
    { xcf. xapp~. => M EM. xapp~. xapp~. xrets.
      =>> Hk. subst M. rew_array~. case_ifs; math. }
  Qed.



  (*---------------------------------------------------------------------*)
  (*----
  let exercise_array () =
    let t = Array.make 3 true in
    t.(2) <- false;
    t.(1) <- t.(2);
    t
  ----*)

  (* LATER
    Lemma example_array_spec :
      App example_array tt;
        \[]
        (fun (t:loc) => Hexists M, (t ~> Array M) \*
          \[length M = 3
        /\ forall k, 0 <= k < 3 -> M[k] = isTrue(k<1)]).
    Proof using.
      xcf.
      xapp. autos. intros M EM. subst M.
      xapp. autos.
      xapp~ as v. intros Ev.
      xapp~.
      xret.
      xsimpl. split.
        rew_array~.
        introv Hk. rew_array~. case_ifs.
          subst v. rew_array~. case_if~. math.
          math.
          math.
      (* Optional forward reasoning after [intros Ev]:
        asserts Ev': (v = false).
          subst. rew_array~. case_if~.
          clear Ev. subst v. *)
    Qed.
  *)



*)

simpl. applys~ wp_sound_getval (fun t1 => trm_for v t1 t2 t3).
    intros v1. applys~ wp_sound_getval (fun t2 => trm_for v v1 t2 t3).
    intros v2. applys~ wp_sound_for_val. }
  { applys* wp_sound_case_trm. 
    (* TODO inlined:
    simpl. applys~ wp_sound_getval (fun t1 => trm_case t1 p t2 t3).
    intros v. applys~ wp_sound_case_val. *) }
  { applys wp_sound_fail. }

  (* TODO alternative but non
Definition wp_app wp (E:ctx) : list val -> trm -> formula := 
  (fix mk (rvs : list val) (t : trm) {struct t} : formula :=
    match t with
    | trm_app t1 t2 => wp_getval wp E t2 (fun v2 => mk (v2::rvs) t1)
    | _ => wp_fail (* wp_getval wp E t (fun v =>
             local (wp_triple (trm_apps v (trms_vals (List.rev rvs))))) *)
    end) .
*)

(* TODO    wp_getval wp E t1 (fun v1 =>
       wp_getval wp E t2 (fun v2 =>
         wp_app (trm_app v1 v2))) *)


         
Lemma wp_sound_app_trm : forall E t1 t2,
  wp_sound t1 ->
  wp_sound t2 ->
  wp E (trm_app_val t1 t2) ===> wp_triple_ E (trm_app t1 t2).
Proof using.
  introv M1 M2. intros Q. simpl.
  applys~ wp_sound_getval (fun t1 => trm_app t1 t2).
  intros v1. applys~ wp_sound_getval (fun t2 => trm_app v1 t2).
  intros v2. applys* local_erase_l. applys is_local_wp_triple.
Qed.


(* TODO *)
Lemma trms_vals_rev : forall vs,
  trms_vals (rev vs) = rev (trms_vals vs).
Proof using. intros. unfold trms_vals. rewrite~ LibList.map_rev. Qed.



(* ALT

Lemma wp_sound_redbinop : forall v op v1 v2 E,
  redbinop op v1 v2 v ->
  wp_val v ===> wp_triple_ E (trm_apps op (trms_vals (v1::v2::nil))).
Proof using.
  introv M. applys qimpl_wp_triple; intros Q; simpl.
  remove_local. applys triple_combined.
  { applys triple_binop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wp_sound_redunop_int : forall (F:int->val) op v1 E,
  (forall (n1:int), redunop op n1 (F n1)) ->
  wp_unop_int v1 F ===> wp_triple_ E (trm_apps op (trms_vals (v1::nil))).
Proof using.
  introv M. applys qimpl_wp_triple; intros Q; simpl.
  remove_local. intros n1 ->. applys triple_combined.
  { applys triple_unop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wp_sound_redunop_bool : forall (F:bool->val) op v1 E,
  (forall (b1:bool), redunop op b1 (F b1)) ->
  wp_unop_bool v1 F ===> wp_triple_ E (trm_apps op (trms_vals (v1::nil))).
Proof using.
  introv M. applys qimpl_wp_triple; intros Q; simpl.
  remove_local. intros n1 ->. applys triple_combined.
  { applys triple_unop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wp_sound_redbinop_int : forall (F:int->int->val) op v1 v2 E,
  (forall (n1 n2:int), redbinop op n1 n2 (F n1 n2)) ->
  wp_binop_int v1 v2 F ===> wp_triple_ E (trm_apps op (trms_vals (v1::v2::nil))).
Proof using.
  introv M. applys qimpl_wp_triple; intros Q; simpl.
  remove_local. intros n1 n2 (->&->). applys triple_combined.
  { applys triple_binop M. } { hsimpl. } { hpull ;=> ? ->. hsimpl. }
Qed.

Lemma wp_sound_apps_val : forall E v0 vs,
  wp_apps_val v0 vs ===> wp_triple_ E (trm_apps v0 vs).
Proof using.
  Hint Constructors redunop redbinop.
  intros.
  asserts Common: (local (wp_triple (trm_apps v0 vs)) ===> wp_triple_ E (trm_apps v0 vs)).
  { apply~ local_erase_l. { applys is_local_wp_triple. } 
    intros Q. applys qimpl_wp_triple. intros Q'; clear Q. simpl.
     rewrite List_map_eq. rewrite map_isubst_trms_vals. applys triple_wp_triple. }
  intros Q. destruct v0; try solve [ apply Common ].
  rename p into p. destruct p; try solve [ apply Common ];
   destruct vs as [|v1 [|v2 [|]]]; try solve [ apply Common ].
  { applys* wp_sound_redunop_bool. }
  { applys* wp_sound_redunop_int. }
  { applys* wp_sound_redbinop. }
  { applys* wp_sound_redbinop. eauto. }
  { applys* wp_sound_redbinop_int. }
  { applys* wp_sound_redbinop_int. }
  { applys* wp_sound_redbinop_int. }
Qed.

*)


(* DEPRECATED
  Definition wp_app_val (E:ctx) (t:trm) : formula := 
  local (wp_triple (isubst E t)). *)
  (* Note that the substitution is usually the identity
     because [t] is the application of a value to values *)
    (* wp_app_val E (trm_apps v0 (trms_vals (List.rev rvs))) *)



(*  DEPRECATED
Lemma hoare_if : forall Q1 t0 t1 t2 H Q,
  hoare t0 H Q1 ->
  (forall (b:bool), hoare (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. applys* hoare_if_trm.
  intros v. tests C: (is_val_bool v).
  { destruct C as (b&E). subst. applys* hoare_if_bool. }
  { ... M3 false .. }
Qed.
*)



(*
Lemma Substn_eq_isubstn : forall xs (Vs:dyns) t,
  length xs = length Vs ->
  Substn xs Vs t = isubstn xs (encs Vs) t.
Proof using.
  introv E. unfold Substn. rewrite~ isubstn_eq_substn.
  rewrite* length_encs.
Qed.

*)


Lemma Triple_apps_funs_of_Wp : forall F (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
Admitted.
(*
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Triple_apps_funs. 
  unfolds in N. rewrite* Substn_eq_isubstn.
  applys* Triple_isubst_of_Wp.
Qed.
*)

Lemma Triple_apps_funs_of_Wp' : forall F (Vs:dyns) (vs:vals) (ts:trms) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  ts = trms_vals vs ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  H ==> ^(Wp (combine xs (encs Vs)) t) Q ->
  Triple (trm_apps F ts) H Q.
Proof using.
  intros. subst. applys* Triple_apps_funs_of_Wp.
Qed.
(*
  xcf_prepare_args tt. (* -- not needed here *)
*)

Lemma Triple_apps_fixs_of_Wp : forall F (f:var) (Vs:dyns) (vs:vals) xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  vs = encs Vs ->
  var_fixs_exec f (length Vs) xs ->
  H ==> ^(Wp (combine (f::xs) (encs ((Dyn F)::Vs))) t) Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
Admitted.
(*
  introv EF EV N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
  subst. applys* Triple_apps_fixs.
  rewrite~ Substn_eq_isubstn. 
  { applys @Triple_isubst_of_Wp M. }
  { rew_list. math. }
Qed.
*)
