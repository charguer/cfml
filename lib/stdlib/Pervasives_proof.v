Set Implicit Arguments.
From CFML Require Import WPLib.

(* TODO *)
From CFML Require Import WPRecord.

Generalizable Variable A.
Require Import Pervasives_ml.

(************************************************************)
(** updates *)

Ltac xgoal_fun tt ::=
  match xgoal_code_without_wptag tt with
  | Wpgen_app (trm_apps (trm_val ?f) _) => constr:(f)
  | Wpgen_App_typed ?T ?f ?Vs => constr:(f)
  end.





(* TODO : also rename heap_scope to hprop_scope 
   see what to import from SLF records *)



Notation "p '~~~>' kvs" := (p ~> Record kvs)
  (at level 32) : heap_scope.




(************************************************************)
(** [DEPRECATED?] *)

Ltac solve_type := (* TODO: still needed? *)
  match goal with |- Type => exact unit end.

Ltac remove_head_unit tt :=
  repeat match goal with
  | |- unit -> _ => intros _
  end.

Ltac xcf_post tt := (* TODO: still needed? *)
  cbv beta;
  remove_head_unit tt.
  (* DEPRECATED
  cbv beta;
  remove_head_unit tt. TODO: should be hnf?
  *)




(************************************************************)
(** Notation for parsing lifted applications *)

(** This set up allows writing [f V1 .. VN] as short for
    [Trm_apps f ((Dyn V1):: .. ::(Dyn Vn)::nil)]. *)

Declare Custom Entry Trm_apps.

Notation "f x" := (Trm_apps f ((Dyn x)::nil))
  (in custom Trm_apps at level 1,
   f constr at level 0, 
   x constr at level 0, 
   left associativity)
  : Trm_apps_scope.

Notation "f x1 x2 .. xn" := (Trm_apps f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..)))
  (in custom Trm_apps at level 1,
   f constr at level 0, 
   x1 constr at level 0, 
   x2 constr at level 0, 
   xn constr at level 0, 
   left associativity)
  : Trm_apps_scope.

Notation "( x )" :=
  x
  (in custom Trm_apps,
   x at level 99) : Trm_apps_scope.

Notation "'SPEC' t 'PREC' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'PREC'  H  '/' 'POST'  Q ']'") : triple_scope.

Open Scope Trm_apps_scope.
Open Scope triple_scope.

(*
Lemma test_spec : forall (a b:bool),
  SPECS (not a b)
    PRES \[]
    POST \[= !a ].
*)

(************************************************************)
(** [xcf] *)

(** [xcf] applies to a goal with a conclusion of the form
    [Triple t H Q], possibly written using the [SPEC] notation.
    It looks up the characteristic formula associated with [f]
    in the database "database_cf", and exploits it to start
    proving the goal. [xcf] first calls [intros] if needed.

    When [xcf] fails to apply, it is (most usually) because the number
    of arguments, or the types of the arguments, or the return type,
    does not match.

    Variants:

    - [xcf_show] will only display the CF lemma found in the database,
      putting it at the head of the goal.

    - [xcf_show f] displays the CF associated with a given value [f].

*)

 (* TODO: extend to support partial application *)

Ltac xcf_pre tt :=
  intros.

Ltac xcf_target tt :=
  match goal with 
  | |- ?f = _ => constr:(f)
  | |- Triple (Trm_apps (trm_val ?f) ?Vs) ?H ?Q => constr:(f)
  end.

Ltac xcf_find f :=
  ltac_database_get database_cf f.

Tactic Notation "xcf_show" constr(f) :=
  xcf_find f.

Tactic Notation "xcf_show" :=
  xcf_pre tt;
  let f := xcf_target tt in
  xcf_find f.

Ltac xcf_top_fun tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  eapply Sf;
  clear Sf.
  (* xcf_post *) (* try solve_type;  instantiate; *)
  (* TODO: first [ xc f_top_value f | xcf_fallback f | fail 2 ] *)

Ltac xcf_top_value tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  rewrite Sf;
  clear Sf. 
  (* xcf_post *)

Ltac xcf_core tt :=
  xcf_pre tt;
  match goal with
  | |- ?f = _ => xcf_top_value tt
  | _ => xcf_top_fun tt
  end. 

(* TODO notation SPECVAL f = v and SPECVAL f st P *)

Tactic Notation "xcf" :=
  xcf_core tt.
Tactic Notation "xcf" "~" :=
  xcf; auto_tilde.
Tactic Notation "xcf" "*" :=
  xcf; auto_star.


(************************************************************)

(*
Ltac xgoal_code tt ::=
  match goal with 
  | |- PREC _ CODE ?F POST _ => constr:(F)  (*  (H ==> (Wptag F) _ _ Q) *)
  end.

Ltac xgoal_code_strip_wptag C :=
  match C with
  | Wptag ?C' => xgoal_code_strip_wptag C'
  | ?C' => constr:(C')
  end.

Ltac xgoal_code_without_wptag tt :=
  let C := xgoal_code tt in
  xgoal_code_strip_wptag C.
*)


(************************************************************)

Lemma xval_lifted_lemma : forall A `{EA:Enc A} (V:A) H (Q:A->hprop),
  H ==> Q V ->
  H ==> ^(Wpgen_Val V) Q.
Proof using.
  introv M. subst. applys MkStruct_erase. 
  applys xcast_lemma M.
Qed.

Ltac xval_pre tt ::=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
  | (Wpgen_Val _) => idtac
  end.

Ltac xval_core tt :=
  xval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => applys @xval_lemma_decode; [ try xdecode | ]
  | (Wpgen_Val _) => applys xval_lifted_lemma
  end;
  xval_post tt.


(************************************************************)
(** [xgo], [xcf_go] and [xstep] *)

Ltac xstep_once tt :=
  match goal with
  | |- ?G => match xgoal_code_without_wptag tt with
    | (Wpgen_seq _ _) => xseq
    | (Wpgen_let_typed _ _) => xlet
    | (Wpgen_let _ _) => xlet
    | (Wpgen_app _) => xapp
    | (Wpgen_App_typed _ _ _) => xapp
    | (Wpgen_record_new _) => xapp
    | (Wpgen_if_bool _ _ _) => xif
    | (Wpgen_val _) => xval
    | (Wpgen_Val _) => xval
    | (Wpgen_Val_no_mkstruct _) => xcast
    | (Wpgen_fail) => xfail
    (* | (Wpgen_case _ _ _) => xcase *)
    (* TODO complete *)
    end
  | |- _ ==> _ => xsimpl
  | |- _ ===> _ => xsimpl
  end.

(*
Definition Wpgen_assert (F1:Formula) : Formula :=
Definition Wpgen_done : Formula :=
Definition Wpgen_Val A1 {EA1:Enc A1} (V:A1) : Formula :=
Definition Wpgen_app_typed (A1:Type) `{EA1:Enc A1} (t:trm) : Formula :=
Definition Wpgen_App_typed (A1:Type) `{EA1:Enc A1} (f:trm) (Vs:dyns) : Formula :=
Definition Wpgen_for_downto_int (n1 n2:int) (F1:int->Formula) : Formula :=
Definition Wpgen_let_fun (BodyOf:forall A,Enc A->(A->hprop)->hprop) : Formula :=
Definition Wpgen_let_Val A1 `{EA1:Enc A1} (V:A1) (Fof:A1->Formula) : Formula :=
Definition Wpgen_body (P:Prop) : Prop :=
Definition Wpgen_dummy : Formula :=
*)

Ltac xstep_pre tt :=
  try xpull; intros.

Ltac xstep_core tt :=
  xstep_pre tt; xstep_once tt; instantiate.

Tactic Notation "xstep" :=
  xstep_core tt.
Tactic Notation "xstep" "~" :=
  xstep; auto_tilde.
Tactic Notation "xstep" "*" :=
  xstep; auto_star.

Ltac xgo_core tt :=
  repeat (xstep_core tt).

Tactic Notation "xgo" :=
  xgo_core tt.
Tactic Notation "xgo" "~" :=
  xgo; auto_tilde.
Tactic Notation "xgo" "*" :=
  xgo; auto_star.


Tactic Notation "xcf_go" :=
  xcf; xgo.
Tactic Notation "xcf_go" "~" :=
  xcf_go; auto_tilde.
Tactic Notation "xcf_go" "*" :=
  xcf_go; auto_star.


(************************************************************)

Notation "'RegisterSpec' f" := (Register_goal (Triple (Trm_apps (trm_val f) _) _ _))
  (at level 69) : wptactics_scope.




(************************************************************)
(** Boolean *)
Lemma not_spec : forall (a:bool),
  SPEC (not a)
    PREC \[]
    POST \[= !a ].
Proof using.
  xcf. xgo*.
Qed.

Hint Extern 1 (RegisterSpec not) => Provide not_spec.


(************************************************************)
(** Physical equality *)

(** There are two specifications:
    - [==] at type [loc] implements comparison of locations
    - [==] in general, if it returns true, then implies logical equality.

    The first specification is used by default.
    Use [xapp_spec infix_eq_eq_gen_spec] for the latter.
*)

Parameter infix_eq_eq_loc_spec : forall (a b:loc),
  SPEC (infix_eq_eq__ a b)
    PREC \[]
    POST \[= isTrue (a = b) ].

Parameter infix_eq_eq_gen_spec : forall (A:Type) (a b:A),
  SPEC (infix_eq_eq__ a b)
    PREC \[]
    POST (fun r => \[r = true -> isTrue (a = b)]).

Hint Extern 1 (RegisterSpec infix_eq_eq__) => Provide infix_eq_eq_loc_spec.


(*********TODO*******)

Ltac xspec_context tt ::=
  xspec_remove_combiner tt;
  match goal with
  | H: context [ Triple (trm_apps (trm_val ?f) _) _ _ ]
    |- Triple (trm_apps (trm_val ?f) _) _ _ => generalize H
  | H: context [ Triple (Trm_apps (trm_val ?f) _) _ _ ]
    |- Triple (Trm_apps (trm_val ?f) _) _ _ => generalize H
  end.

Ltac xapp_pre_wp tt ::=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) => idtac
  | (Wpgen_App_typed ?T ?f ?Vs) => idtac
  | (Wpgen_record_new ?Lof) => idtac
  end.

Lemma xapp_lifted_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  applys xreturn_lemma_typed. rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lifted_lemma : forall A `{EA:Enc A} (V:A) H2 (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapp_lifted_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lifted_lemma_pure : forall A `{EA:Enc A} (V:A) (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapps_lifted_lemma \[]; rew_heap; eauto.
Qed.

Lemma xapp_find_spec_lifted_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:trm) (Vs:dyns) H1 H (Q:A->hprop),
  Triple (Trm_apps f Vs) H1 Q1 ->
  (Triple (Trm_apps f Vs) H1 Q1 ->
   H ==> ^(Wpgen_App_typed A f Vs) Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using. auto. Qed.

Ltac xapp_select_lifted_lemma tt := (* TODO: factorize better with xapp_select_lemma *)
  let S := fresh "Spec" in
  intro S;
  match type of S with
  | Triple _ _ (fun _ => \[_ = _] \* _) => applys @xapps_lifted_lemma
  | Triple _ _ (fun _ => \[_ = _]) => applys @xapps_lifted_lemma_pure
  | _ => applys @xapp_lifted_lemma
  end; [ applys S | clear S ].

Ltac xapp_apply_lifted_lemma cont_prove_triple :=
  (* --TODO should remove *) xapp_pre tt;
  applys xapp_find_spec_lifted_lemma;
    [ cont_prove_triple tt
    | xapp_select_lifted_lemma tt; xapp_post tt ].


Ltac xapp_general tt ::=
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) => xapp_apply_lemma ltac:(xspec_prove_triple)
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma ltac:(xspec_prove_triple)
  end.

Ltac xapp_arg_core E ::=
  xapp_pre tt;
  let cont := ltac:(fun tt => xspec_prove_triple_with_args E) in
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) =>  xapp_apply_lemma cont
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma cont
  end.


(****************)

Lemma infix_emark_eq_loc_spec : forall (a b:loc),
  SPEC (infix_emark_eq__ a b)
    PREC \[]
    POST \[= isTrue (a <> b) ].
Proof using.
  xcf. xgo*. rew_isTrue*.
Qed.

Lemma infix_emark_eq_gen_spec : forall (A:Type) (a b:A),
  SPEC (infix_emark_eq__ a b)
    PREC \[]
    POST (fun r => \[r = false -> isTrue (a = b)]).
Proof using.
  xcf. xapp infix_eq_eq_gen_spec. 
  introv E. xvals*.
Qed.

Hint Extern 1 (RegisterSpec infix_emark_eq__) => Provide infix_emark_eq_loc_spec.


(************************************************************)
(** Comparison *)

Parameter infix_eq_spec : forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  SPEC (infix_eq__ a b)
    PREC \[]
    POST \[= isTrue (a = b) ].

Hint Extern 1 (RegisterSpec infix_eq__) => Provide infix_eq_spec.

Parameter infix_neq_spec : forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  SPEC (infix_lt_gt__ a b)
    PREC \[]
    POST \[= isTrue (a <> b) ].

Hint Extern 1 (RegisterSpec infix_lt_gt__) => Provide infix_neq_spec.

Lemma min_spec : forall (n m:int),
  SPEC (min n m)
    PREC \[]
    POST \[= Z.min n m ].
Proof using.
  xcf. xgo*.
  { rewrite~ Z.min_l. }
  { rewrite~ Z.min_r. math. }
Qed.

Lemma max_spec : forall (n m:int),
  SPEC (max n m)
    PREC \[]
    POST \[= Z.max n m ].
Proof using.
  xcf. xgo*.
  { rewrite~ Z.max_l. }
  { rewrite~ Z.max_r. math. }
Qed.

Hint Extern 1 (RegisterSpec min) => Provide min_spec.
Hint Extern 1 (RegisterSpec max) => Provide max_spec.


(************************************************************)
(** Boolean *)

Parameter infix_bar_bar_spec : forall (a b:bool),
  SPEC (infix_bar_bar__ a b)
    PREC \[]
    POST \[= a && b ].

Parameter infix_amp_amp_spec : forall (a b:bool),
  SPEC (infix_amp_amp__ a b)
    PREC \[]
    POST \[= a || b ].

Hint Extern 1 (RegisterSpec infix_bar_bar__) => Provide infix_bar_bar_spec.
Hint Extern 1 (RegisterSpec infix_amp_amp__) => Provide infix_amp_amp_spec.


(************************************************************)
(** Integer *)

Parameter infix_tilde_minus_spec : forall (n:int),
  SPEC (infix_tilde_minus__ n)
    PREC \[]
    POST \[= Z.opp n ].

Parameter infix_plus_spec : forall (n m:int),
  SPEC (infix_plus__ n m)
    PREC \[]
    POST \[= Z.add n m ].

Parameter infix_minus_spec : forall (n m:int),
  SPEC (infix_minus__ n m)
    PREC \[]
    POST \[= Z.sub n m ].

Parameter infix_star_spec : forall (n m:int),
  SPEC (infix_star__ n m)
    PREC \[]
    POST \[= Z.mul n m ].

Parameter infix_slash_spec : forall (n m:int),
  m <> 0 ->
  SPEC (infix_slash__ n m)
    PREC \[]
    POST \[= Z.quot n m ].

Parameter mod___spec : forall (n m:int),
  m <> 0 ->
  SPEC (mod__ n m)
    PREC \[]
    POST \[= Z.rem n m ].

Hint Extern 1 (RegisterSpec infix_tilde_minus__) => Provide infix_tilde_minus_spec.
Hint Extern 1 (RegisterSpec infix_plus__) => Provide infix_plus_spec.
Hint Extern 1 (RegisterSpec infix_minus__) => Provide infix_minus_spec.
Hint Extern 1 (RegisterSpec infix_star__) => Provide infix_star_spec.
Hint Extern 1 (RegisterSpec infix_slash__) => Provide infix_slash_spec.
Hint Extern 1 (RegisterSpec mod__) => Provide mod___spec.

Notation "x `/` y" := (Z.quot x y)
  (at level 69, right associativity) : charac.
Notation "x `mod` y" := (Z.rem x y)
  (at level 69, no associativity) : charac.
(* TODO: check levels for these notations *)


(* NOT NEEDED
Notation "`~- n" := (App infix_tilde_minus_ n;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_plus_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_minus_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_star_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_div_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_mod_ n m;)
  (at level 69, no associativity) : app_scope.
 *)

Lemma succ_spec : forall (n:int),
  SPEC (succ n)
    PREC \[]
    POST \[= n+1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma pred_spec : forall (n:int),
  SPEC (pred n)
    PREC \[]
    POST \[= n-1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma abs___spec : forall (n:int),
  SPEC (abs__ n)
    PREC \[]
    POST \[= Z.abs n ].
Proof using.
  xcf. xgo.
  { rewrite~ Z.abs_eq. }
  { rewrite~ Z.abs_neq. math. }
Qed.

Hint Extern 1 (RegisterSpec succ) => Provide succ_spec.
Hint Extern 1 (RegisterSpec pred) => Provide pred_spec.
Hint Extern 1 (RegisterSpec abs__) => Provide abs___spec.


(************************************************************)
(** Bit-level Integer *)

(* TODO: check *)

Parameter land_spec : forall (n m:int),
  SPEC (land n m)
    PREC \[]
    POST \[= Z.land n m ].

Parameter lor_spec :  forall (n m:int),
  SPEC (lor n m)
    PREC \[]
    POST \[= Z.lor n m ].

Parameter lxor_spec : forall (n m:int),
  SPEC (lxor n m)
    PREC \[]
    POST \[= Z.lxor n m ].

Definition Zlnot (x : Z) : Z := -(x + 1).

Parameter lnot_spec : forall (n:int),
  SPEC (lnot n)
    PREC \[]
    POST \[= Zlnot n ].

Parameter lsl_spec : forall (n m:int),
  0 <= m ->   (* y < Sys.word_size -> *)
  SPEC (lsl n m)
    PREC \[]
    POST \[= Z.shiftl n m ].

  (* TODO We temporarily? restrict [lsr] to nonnegative integers,
     so it behaves like [asr]. Anyway, [lsr] really operates
     on unsigned integers, and this notion is missing in CFML. *)

Parameter lsr_spec : forall (n m:int),
  0 <= n ->
  0 <= m ->
  (* m < Sys.word_size -> *)
  SPEC (lsr n m)
    PREC \[]
    POST \[= Z.shiftr n m ].

Parameter asr_spec : forall (n m:int),
  0 <= m ->
  (* m < Sys.word_size -> *)
  SPEC (asr n m)
    PREC \[]
    POST \[= Z.shiftr n m ].

Hint Extern 1 (RegisterSpec land) => Provide land_spec.
Hint Extern 1 (RegisterSpec lor) => Provide lor_spec.
Hint Extern 1 (RegisterSpec lxor) => Provide lxor_spec.
Hint Extern 1 (RegisterSpec lnot) => Provide lnot_spec.
Hint Extern 1 (RegisterSpec lsl) => Provide lsl_spec.
Hint Extern 1 (RegisterSpec land) => Provide land_spec.
Hint Extern 1 (RegisterSpec lsr) => Provide lsr_spec.
Hint Extern 1 (RegisterSpec asr) => Provide asr_spec.


(************************************************************)
(** References *)

Definition Ref `{EA:Enc A} (v:A) (r:loc) :=
  r ~~~> `{ contents' := v }.

(* TODO: THIS IS NOW REALIZED AT A LOWER LEVEL 

Axiom Ref_Heapdata : forall A,
  (Heapdata (@Ref A)).

Existing Instance Ref_Heapdata.
(* TODO: need an axiom about allocated records *)
(*
Proof using.
  intros. applys Heapdata_prove. intros x X1 X2.
  xunfold @Ref.
lets: star_is_single_same_loc.
  hchange (@star_is_single_same_loc x). hsimpl.
Qed.
*)
*)

Notation "r '~~>' v" := (r ~> Ref v)
  (at level 32, no associativity) : heap_scope.

Lemma haffine_Ref : forall `{EA:Enc A} r (v: A),
  haffine (r ~~> v).
Admitted. (* TODO Proof. intros. unfold Ref, hdata. affine. Qed. *)

Hint Resolve haffine_Ref : haffine.

(* Expose that [ref_ A] (defined in Pervasives_ml) is defined as [loc] *)
Hint Transparent ref_ : haffine.



(* TODO *)
Ltac xapp_record tt ::= (* initial dummy binding located in WPTactics *)
  match xgoal_code_without_wptag tt with
  | Wpgen_record_new ?Lof => applys xapp_lemma_record_new
  | Wpgen_App_typed ?T ?f ?Vs => 
      match f with
      | trm_val (val_get_field _) => xapp_record_get tt
      | trm_val (val_set_field _) => xapp_record_set tt
      | trm_val (val_record_init _) => xapp_record_new tt (* TODO redundant? *)
      | trm_val (val_record_delete _) => xapp_record_delete tt
      end
  end.




Lemma ref_spec : forall `{EA:Enc A} (v:A),
  SPEC (ref v)
    PREC \[]
    POST (fun r => r ~~> v).
Proof using. xcf. xgo~. Qed.

Notation "'SPEC' t 'INVA' H 'POST' Q" :=
  (Triple t H (Q \*+ H))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'INVA'  H  '/' 'POST'  Q ']'") : triple_scope.



(************************************************************)
(** [show_types] *)

(* TODO LATER

    - [xcf_types] shows the type of the application in the
      goal, compared with the one from the specification.

    - [xcf_types S] shows the types of the function involved
      in a specification [S].
*)

Ltac xtypes_type show_arrow T ET :=
  match show_arrow with
  | true => idtac T " { " ET " } -> "
  | false => idtac T " { " ET " } "
  end.

(* [xtypes_dyn_list L] displays the types of the
   arguments in the list [L] *)

Ltac xtypes_dyn_list L :=
  match L with
  | nil => idtac
  | (@dyn_make ?T ?ET ?x) :: ?R => xtypes_type true T ET
  end.

Ltac xtypes_triple E := 
  let aux Vs T ET := 
    xtypes_dyn_list Vs; xtypes_type false T ET in
  match E with
  | (Wptag ?F) => xtypes_triple F
  | (@Wpgen_App_typed ?T ?ET ?f ?Vs) => aux Vs T ET
  | (@Triple (Trm_apps ?f ?Vs) ?T ?ET ?H ?Q) => aux Vs T ET
  end.

Ltac xtypes_goal tt :=
  idtac "=== type of application in goal ===";
  let G := match goal with |- ?G => constr:(G) end in (* TODO: ltac op *)
  xtypes_triple G.

Ltac xtypes_hyp S :=
  idtac "=== type of application in hypothesis ===";
  forwards_nounfold_admit_sides_then S ltac:(fun K =>
    let T := type of K in
    xtypes_triple T).

Ltac xcf_types_core tt :=
  let S := fresh "Spec" in
  intros S;
  xtypes_goal tt;
  xtypes_hyp S;
  clear S.

Ltac xcf_types_core_noarg tt :=
  xcf_show;
  xcf_types_core tt.

Ltac xcf_types_core_arg S :=
  xcf_pre tt;
  generalize S;
  xcf_types_core tt.

Tactic Notation "xcf_types" :=
  xcf_types_core_noarg tt.

Tactic Notation "xcf_types" constr(S) :=
  xcf_types_core_arg S.


(* LATER
Ltac xcf_fallback f :=
  idtac "Warning: could not exploit the specification; maybe the types don't match; check them using [xcf_types]; if you intend to use the specification manually, use [xcf_show].";
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf.
*)



Parameter xapp_record_Get : forall A `{EA:Enc A} (Q:A->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* (match record_get_compute_dyn f L with
    | None => \[False]
    | Some (Dyn V) => (p ~> Record L) \-* ^(Wptag (Wpgen_Val_no_mkstruct V)) (protect Q) end) ->
  H ==> ^(Wpgen_App_typed A (trm_val (val_get_field f)) ((Dyn p)::nil)) Q.
(* TODO: proof *)

Parameter xapp_record_Set : forall A1 `{EA1:Enc A1} (W:A1) (Q:unit->hprop) (H:hprop) (p:loc) (f:field) (L:Record_fields),
  H ==> p ~> Record L \* ((
    match record_set_compute_dyn f (Dyn W) L with
    | None => \[False]
    | Some L' =>
        (p ~> Record L' \-* protect (Q tt)) end)  ) ->
  H ==> ^(Wpgen_App_typed unit (trm_val (val_set_field f)) ((Dyn p)::(Dyn W)::nil)) Q.


Ltac xapp_record_get_grouped tt ::=
  applys xapp_record_Get; xapp_record_get_set_post tt.

Ltac xapp_record_set_grouped tt ::=
  applys xapp_record_Set; xapp_record_get_set_post tt.


Ltac xcast_debug tt :=
  idtac "[xcast] fails to simplify due to type mismatch";
  match goal with |- 
   ?H ==> (Wptag (@Wpgen_Val_no_mkstruct ?A1 ?EA1 ?X)) ?A2 ?EA2 ?Q => 
   xtypes_type false A1 EA1;
   xtypes_type false A2 EA2
 end.

Ltac xcast_core tt ::=
  first [ xcast_pre tt; applys xcast_lemma 
        | xcast_debug tt ].


Lemma infix_emark_spec : forall A `{EA:Enc A} (v:A) r,
  SPEC (infix_emark__ r)
    INVA (r ~~> v)
    POST \[= v].
Proof using. xunfold @Ref. xcf_go*. Qed.

Notation "'SPEC' t 'PREC' H 'POSTUNIT' H2" :=
  (Triple t H (fun (_:unit) => H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'PREC'  H  '/' 'POSTUNIT'  H2 ']'") : triple_scope.


Lemma infix_colon_eq_spec : forall A `{EA:Enc A} (v w:A) r,
  SPEC (infix_colon_eq__ r w)
    PREC (r ~~> v)
    POSTUNIT (r ~~> w).
Proof using. xunfold @Ref. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ref) => Provide ref_spec.
Hint Extern 1 (RegisterSpec infix_emark__) => Provide infix_emark_spec.
Hint Extern 1 (RegisterSpec infix_colon_eq__) => Provide infix_colon_eq_spec.



Notation "'App'' `! r" := (Wpgen_App_typed _ (trm_val infix_emark__) ((Dyn r)::nil))
  (at level 69, no associativity, r at level 0,
   format "'App''  `! r") : wp_scope.

Notation "'App'' r `:= x" := (Wpgen_App_typed _ (trm_val infix_colon_eq__) ((Dyn r)::(Dyn x)::nil))
  (at level 69, no associativity, r at level 0,
   format "'App''  r  `:=  x") : wp_scope.

(* with explicit type: not needed
Notation "'App'' { T } r `:= x" := (Wpgen_App_typed T (trm_val infix_colon_eq__) ((Dyn r)::(Dyn x)::nil))
  (at level 69, no associativity, r at level 0,
   format "'App''  { T }  r  `:=  x") : wp_scope.
*)

Lemma incr_spec : forall (n:int) r,
  SPEC (incr r)
    PREC (r ~~> n)
    POSTUNIT (r ~~> (n+1)).
Proof using. xcf_go~. Qed.

Lemma decr_spec : forall (n:int) r,
  SPEC (decr r)
    PREC (r ~~> n)
    POSTUNIT (r ~~> (n-1)).
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.
Hint Extern 1 (RegisterSpec decr) => Provide decr_spec.



(************************************************************)
(** Group of References -- TODO: needs hfold_fmap

Axiom ref_spec_group : forall A (M:map loc A) (v:A),
  SPEC (ref v)
    PREC (Group Ref M)
    POST (fun (r:loc) => Group Ref (M[r:=v]) \* \[r \notindom M]).
(* TODO: proof *)

Lemma infix_emark_spec_group : forall `{Inhab A} (M:map loc A) r,
  r \indom M ->
  SPEC (infix_emark__ r)
    INV (Group Ref M)
    POST (fun x => \[x = M[r]]).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. xsimpl~.
Qed.

Lemma infix_colon_eq_spec_group : forall `{Inhab A} (M:map loc A) (v:A) r,
  r \indom M ->
  SPEC (infix_colon_eq__ r v)
    PREC (Group Ref M)
    POSTUNIT (Group Ref (M[r:=v])).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. intros tt.
  hchanges~ (Group_add' r M).
Qed.

*)


(************************************************************)
(** Pairs *)

(* TODO

Lemma fst_spec : forall A `{EA:Enc A} B `{EB:Enc B} (x:A) (y:B),
  SPEC (fst (x,y))
    PREC \[]
    POST \[= x].
Proof using. xcf_go~. Qed.

Lemma snd_spec : forall A B (x:A) (y:B),
  SPEC (snd (x,y))
    PREC \[]
    POST \[= y].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec fst) => Provide fst_spec.
Hint Extern 1 (RegisterSpec snd) => Provide snd_spec.
*)

(************************************************************)
(** Unit *)

Lemma ignore_spec :
  SPEC (ignore tt)
    PREC \[]
    POST \[= tt].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ignore) => Provide ignore_spec.


(************************************************************)
(** Float *)

(* LATER: float operations *)





(************************************************************)
(************************************************************)
(************************************************************)
(* FUTURE

  (*------------------------------------------------------------------*)

  (** Pred / Succ *)

  Definition pred (n:int) := (Coq.ZArith.BinInt.Z.sub n 1).

  Definition succ (n:int) := (Coq.ZArith.BinInt.Z.add n 1).

  (** Ignore *)

  Definition ignore A (x:A) := tt.
  Definition char := Ascii.ascii.



  (*------------------------------------------------------------------*)
  (* ** References *)

  Definition Ref a A (T:htype A a) (V:A) (r:loc) :=
    Hexists v, heap_is_single r v \* v ~> T V.

  Instance Ref_Heapdata : forall a A (T:htype A a),
    (Heapdata (@Ref a A T)).
  Proof using.
    intros. applys Heapdata_prove. intros x X1 X2.
    unfold Ref. hdata_simpl. hextract as x1 x2.
    hchange (@star_is_single_same_loc x). hsimpl.
  Qed.

  Open Local Scope heap_scope_advanced.

  Notation "'~~>' v" := (~> Ref (@Id _) v)
    (at level 32, no associativity) : heap_scope_advanced.

  (*
  Notation "l '~~>' v" := (r ~> Ref (@Id _) v)
    (at level 32, no associativity) : heap_scope.
  *)
  Notation "l '~~>' v" := (hdata (@Ref _ _ (@Id _) v) r)
    (at level 32, no associativity) : heap_scope.

  Lemma focus_ref : forall (r:loc) a A (T:htype A a) V,
    r ~> Ref T V ==> Hexists v, r ~~> v \* v ~> T V.
  Proof. intros. unfold Ref, hdata. unfold Id. hsimpl~. Qed.

  Lemma unfocus_ref : forall (r:loc) a (v:a) A (T:htype A a) V,
    r ~~> v \* v ~> T V ==> r ~> Ref T V.
  Proof. intros. unfold Ref. hdata_simpl. hsimpl. subst~. Qed.

  Lemma heap_is_single_impl_null : forall (r:loc) A (v:A),
    heap_is_single r v ==> heap_is_single r v \* \[r <> null].
  Proof.
    intros. intros h Hh. forwards*: heap_is_single_null. exists___*.
  Qed.

  Lemma focus_ref_null : forall a A (T:htype A a) V,
    null ~> Ref T V ==> \[False].
  Proof.
    intros. unfold Ref, hdata. hextract as v.
    hchanges (@heap_is_single_impl_null null).
  Qed.

  Global Opaque Ref.
  Implicit Arguments focus_ref [a A].
  Implicit Arguments unfocus_ref [a A].

*)



