


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



(*
Definition enc_list `{Enc A} := (fix f (l:list A) :=
  match l with
  | nil => val_constr 0%nat nil
  | x::l' => val_constr 1%nat ((``x)::(f l')::nil)
  end).

Instance Enc_list2 : forall `{Enc A}, Enc (list A).
Proof using. constructor. applys enc_list. Defined.

Opaque enc_list.
*)


Lemma xlet_instantiate' : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.




(*
Lemma xlet_lemma : forall Q1 (F1:formula) (F2of:forall `{EA1:Enc A1},A1->Formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> Wp_let F1 F2of Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.



Definition Wp_let (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1) ,
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

*)

(* use:  notypeclasses refine (xlet_instantiate _ _ _). *)


(*
Lemma xlet_typed_instantiate : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.
*)

Lemma xapp_lemma' : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q, (* DEPRECATED *)
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Wp_Triple t) Q.
Proof using. 
  introv M1 M2. lets M: xapp_triple_to_Wp_Triple (rm M1).
  hchanges (rm M2). hchanges (rm M).
  applys weakestpre_conseq_wand.
  applys is_local_Triple.
Qed.



(** Extension of [xlocal] tactic *)

Ltac xlocal_base tt ::=
  try first [ applys is_local_local
            | applys is_local_triple
            | applys is_local_Triple ].

            
(*
(* ---------------------------------------------------------------------- *)
(** Notation for WP *)

(** [WP] denotes [Wp_triple], which is [Weakestpre (@Triple t)],
    where [Weakestpre] is the lifted version of the generic [weakestpre]
    predicate defined in [SepFunctor]. *)

Notation "'WP' t Q" := (^(Wp_Triple t) Q)
  (at level 39, t at level 0, Q at level 0) : triple_scope.

Open Scope triple_scope.
*)





(* ********************************************************************** *)
(* * Notation for triples *)





(* ---------------------------------------------------------------------- *)
(** WIP... *)

(** Notation [TRIPLE t PRE H POST Q]
    in weakest-precondition form *)

(*
Definition TRIPLE_def t H `{EA:Enc A} (Q:A->hprop) :=
  forall Q', H \* \[Q ===> Q'] ==> WP t Q'.

Notation "'TRIPLE' t 'PRE' H1 'POST' Q1" :=
  (TRIPLE_def t H1 Q1)
  (at level 39, t at level 0) : triple_scope.


Notation "'TRIPLE' t 'PRE' H1 'POST' Q1" :=
  (forall Q, H1 \* \[Q1 ===> Q] ==> WP t Q)
  (at level 39, t at level 0) : triple_scope.

*)

(** Notation [TRIPLE t PRE H BIND x y RET v POST Q] 
    in weakest-precondition form  

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[(fun r => \[r = v] \* H2) ===> Q] ==> WP t Q)
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (TRIPLE t PRE H1 POST (fun r => \exists x1, \[r = v] \* H2))
  (* (forall Q, H1 \* \[(fun r => \exists x1, \[r = v] \* H2) ===> Q] ==> Wp_Triple t Q) *)
  (at level 39, t at level 0, x1 ident) : triple_scope.
*)

(* ALTERNATIVE

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 x3 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1 x2 x3, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident, x2 ident, x3 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 x3 x4 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1 x2 x3 x4, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident, x2 ident, x3 ident, x4 ident) : triple_scope.

*)

(* TODO: use recursive notation *)


(* TODO:

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2) Q)
 or just:
  (forall Q, H1 \* \[forall x1, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident) : triple_scope.

*)







(* DEPRECATED
Definition tag_himpl_wp (A:Type) (X:A) := X.

Lemma tag_himpl_wp_intro : forall H F `{EA:Enc A} (Q:A->hprop),
  tag_himpl_wp (H ==> ^F Q) ->
  H ==> ^F Q.
Proof using. auto. Qed.

Notation "'PRE' H 'CODE' F 'POST' Q" := (tag_himpl_wp (H ==> F _ _ Q)) 
  (at level 67, format "'[v' 'PRE'  H '/' 'CODE'  F '/' 'POST'  Q ']'") : charac.

Ltac tag := applys tag_himpl_wp_intro.

*)




(* DEPRECATED
Definition record_get_compute_spec' (f:field) (L:Record_fields) : option Prop :=
  match record_get_compute_dyn f L with
  | None => None
  | Some (Dyn V) => Some (forall p H H1 Q,
     H ==> p ~> Record L \* H1 ->
     p ~> Record L \* H1 ==> Q V -> (* nosubst: (fun x => \[x = v] \* H) ===> Q *)
     H ==> ^(Wp_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q)
  end.

Lemma record_get_compute_spec_correct' : forall (f:field) L (P:Prop),
  record_get_compute_spec' f L = Some P ->
  P.
Proof using.
  introv M. unfolds record_get_compute_spec'.
  lets R: record_get_compute_spec_correct f L.
  unfolds record_get_compute_spec. 
  destruct (record_get_compute_dyn f L) as [[T ET V]|]; tryfalse.
  inverts M. introv M1 M2.
  forwards R': R. eauto. 
  hchange M1. apply himpl_wp_app_of_Triple. xapplys R'.
  intros. subst. hchanges M2.
Qed.
*)



(* DEPRECATED
Lemma xapp_record_set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) H H1 (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* H1 ->
  match record_set_compute_dyn f (Dyn W) L with
  | None => False
  | Some L' =>  
      p ~> Record L' \* H1 ==> Q tt
  end ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_set_field f)) (trms_vals ((p:val)::(``W)::nil)))) Q.
Proof using.
  introv M1 M2.
  hchanges (rm M1).
  lets R: record_set_compute_spec_correct f W L.
  unfolds record_set_compute_spec.
  destruct (record_set_compute_dyn f (Dyn W) L); tryfalse.
  forwards R': R; eauto. clear R. specializes R' p. 
  applys himpl_wp_app_of_Triple.
  xapplys R'. hsimpl. hchanges M2. 
Qed. (* TODO: simplify proof *)
*)



(* DEPRECATED
Lemma xapp_record_get : forall A `{EA:Enc A} (Q:A->hprop) H H1 (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* H1 ->
  match record_get_compute_dyn f L with
  | None => False
  | Some (Dyn V) =>  
      PostChange (fun x => \[x = V] \* p ~> Record L \* H1) Q
  end ->
  H ==> ^(Wp_app (trm_apps (trm_val (val_get_field f)) (trms_vals ((p:val)::nil)))) Q.
*)



(*

Arguments trm_to_pat t /.

Arguments hprop_forall_vars Hof G xs /.
Arguments prop_forall_vars Hof G xs /.
Arguments patvars p /.


Ltac xwp_simpl ::=
   cbn beta delta [ combine
  List.rev Datatypes.app List.fold_right List.map
   Wp_app Wp_getval_typed Wp_constr 
   Wp_getval Wp Wp_case_val  Wp_getval_val Wp_apps Wp_app Wp_getval_int
  hprop_forall_vars prop_forall_vars
   patvars  patsubst  trm_to_pat
     Ctx.app Ctx.empty  Ctx.lookup Ctx.add 
      combiner_to_trm Wp_apps_or_prim
      var_eq eq_var_dec string_dec 
     string_rec string_rect sumbool_rec sumbool_rect
     Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect 
    Bool.bool_dec bool_rec  bool_rect] iota zeta.
Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).

Definition trm_Nil : trm := trm_constr "nil" nil.
Definition trm_Cons (t1 t2:trm) : trm := trm_constr "cons" (t1::t2::nil).

Definition pat_Nil : pat := pat_constr "nil" nil.
Definition pat_Cons (p1 p2:pat) : pat := pat_constr "cons" (p1::p2::nil).




*)
(*
Definition trm_Nil : trm := trm_constr "nil" nil.
Definition trm_Cons (t1 t2:trm) : trm := trm_constr "cons" (t1::t2::nil).

Definition pat_Nil : pat := pat_constr "nil" nil.
Definition pat_Cons (p1 p2:pat) : pat := pat_constr "cons" (p1::p2::nil).
*)





Lemma Tree_eq : forall n q,
  q ~> Tree n =
    match n with
    | Node x hs =>
        \exists l, q ~> Record`{ value := x; sub := l }
                \* l ~> MList.MListOf Tree hs
  end.
Proof using.
  intros n. induction n as [x hs]; intros.
  xunfold Tree. fequals; applys fun_ext_1 ;=> l. fequals.
  gen l. induction hs as [|n hs']; intros.
  { auto. }
  { rewrite MList.MListOf_eq. fequals; applys fun_ext_1 ;=> y.
    fequals; applys fun_ext_1 ;=> p'. fequals. fequals.
    rewrite~ <- IHhs'. }
Qed.



(**
[[

Fixpoint Repr (n:node) (q:loc) : hprop :=
  match n with
  | Node x hs => 
      \exists q',
         q ~> Record`{ value := x; sub := q' } 
      \* q' ~> MList.MListOf.MListOf Repr hs
  end.

]]
*)


(*
Definition hfold_list' A (f:A->hprop) :=
  fix hfold_list' (l1:list A) { struct l1 } : hprop := 
  match l1 with 
  | nil => \[]
  | x1::l1' => f x1 \* hfold_list' l1'
  end.

Definition hfold_list2'' A B (f:A->B->hprop) (l1:list A) (l2:list B) : hprop :=
  hfold_list (fun '(a,b) => f a b) (List.combine l1 l2).

Definition hfold_list2' A B (f:A->B->hprop) :=
  fix hfold_list2' (l1:list A) (l2:list B) { struct l1 } : hprop := 
  match l1,l2 with 
  | nil, nil => \[]
  | x1::l1', x2::l2' => f x1 x2 \* hfold_list2' l1' l2'
  | _,_ => arbitrary
  end.


Definition MListOf' A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  \exists (l:list A), \[length l = length L] \* p ~> MList.MList l
                      \* hfold_list2 (fun (X:TA) (x:A) => x ~> R X) L l. 
*)


Lemma xapp_record_new' : forall (Vs:dyns) (ks:fields) (vs:vals),
  noduplicates_fields_exec ks = true ->
  ks <> nil ->
  List.length ks = List.length Vs ->
  vs = encs Vs ->
  TRIPLE (trm_apps (val_record_init ks) vs)
    PRE \[]
    POST (fun r => r ~> Record (List.combine ks Vs)).
Proof using.
Admitted.



(* ---------------------------------------------------------------------- *)
(* ** Record allocation *)

(* DEPRECATED

Lemma Triple_record_alloc : forall (ks:fields),
  noduplicates ks ->
  TRIPLE ((val_record_alloc ks) '())
    PRE \[]
    POST (fun r => \exists vs, \[length ks = length vs] \* r ~> Record (List.combine ks vs)).
Proof using.
  xwp. xapp. { math. } intros p N.
  sets n: (abs (1 + fold_right Init.Nat.max 0%nat ks)%nat).

Lemma trms_to_vals_trms_vals : forall vs,
  trms_to_vals (trms_vals vs) = Some vs.

Lemma Triple_record_init : forall (ks:fields) (Vs:dyns) (vs:vals),
  noduplicates ks ->
  ks <> nil ->
  length ks = length Vs ->
  vs = encs Vs ->
  TRIPLE (trm_apps (val_record_init ks) vs)
    PRE \[]
    POST (fun r => r ~> Record (List.combine ks Vs)).
Proof using.
  introv Nd Nn L E.
  unfold val_record_init.
  sets xs: (var_seq 0 (Datatypes.length ks)).
  asserts L'': (length xs = length ks).
  { subst xs. rewrite length_var_seq. rewrite~ List_length_eq. }
  applys xwp_lemma_funs.
  { reflexivity. }
  { applys trms_to_vals_trms_vals. }
  { rewrite var_funs_exec_eq. rew_bool_eq. splits.
    { applys var_distinct_var_seq. }
    { subst vs. unfold encs. rewrite List_map_eq. rew_listx. math. }
    { . } }
  { xwp_simpl. xapp~ Triple_record_alloc ;=> p Vs' L'.
    sets_eq kxs: (List.combine ks xs).
    induction kxs as [|(k,x) kxs'].
    { asserts: (ks = nil). .
      asserts: (xs = nil). .
      xwp_simpl. xval p. 
      rewrite @List_combine_eq in *; try math.
      rewrite @List_combine_eq in *; try math.
      asserts: (Vs = nil). admit.
      asserts: (Vs' = nil). admit.
      subst. rewrite combine_nil. rew_listx. xsimpl. }
Admitted.

*)

(* do not include
Instance Decode_val : forall (v:val), (* LATER: redundant with above? *)
  Decode v v.
Proof using. intros. constructors~. Defined.  
*)




(* ********************************************************************** *)
(* * Automation *)

(** Strengthen version of the automation associated with the star,
    e.g. in [mytactic* args]. *)
 
Ltac auto_star ::=
  try solve [ intuition eauto
            | intros; subst; rew_list in *; 
              solve [ math 
                    | auto_false_base ltac:(fun tt => intuition eauto) ] ].



