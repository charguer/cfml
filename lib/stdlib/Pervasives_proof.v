Set Implicit Arguments.
From CFML Require Import WPLib.
Generalizable Variable A.

Require Import Pervasives_ml.


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

Declare Scope charac.
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


Lemma ref_spec : forall `{EA:Enc A} (v:A),
  SPEC (ref v)
    PREC \[]
    POST (fun r => r ~~> v).
Proof using. xcf. xgo~. Qed.


Lemma infix_emark_spec : forall A `{EA:Enc A} (v:A) r,
  SPEC (infix_emark__ r)
    INVA (r ~~> v)
    POST \[= v].
Proof using. xunfold @Ref. xcf_go*. Qed.


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

(* TODO variant with explicit type
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
  intros. rewrite~ (Group_rem  r M). xapp. xsimpl~.
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


(*--------------------------------------------------------*)
(* ** Auxiliary functions to manipulate goal *)

(** Auxiliary tactic for obtaining a boolean answer
    to the question "is E an evar?". TODO: move to TLC *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).

(** Auxiliary function to obtain the last argument of an application *)

Ltac ltac_get_last_arg E :=
  match E with
  | ?F ?X => constr:(X)
  end.
  (* TODO: need to deal with other arities ?*)

(* [cfml_get_precondition tt] returns the current
   pre-condition. *)

Ltac cfml_get_precondition tt :=
  match goal with |- ?H ==> _ => constr:(H) end.

(* [cfml_get_postcondition tt] returns the current
   pose-condition. *)

Ltac cfml_get_postcondition tt :=
  match goal with |- ?H ==> ?H' => ltac_get_last_arg H' end.

(** [cfml_postcondition_is_evar tt] returns a boolean indicating
    whether the post-condition of the current goal is an evar. *)

Ltac cfml_postcondition_is_evar tt :=
  let Q := cfml_get_postcondition tt in
  is_evar_as_bool Q.


(*--------------------------------------------------------*)
(* ** [xletval] and [xletvals] *)

(** [xletval] is used to reason on a let-value node, i.e. on a goal
    of the form [H ==> (Val x := v in F1) Q].
    It leaves the goal [forall x, x = v -> (H ==> F1 Q)].
    
    [xletvals] leaves the goal [H ==> F1 Q] with [x] replaced by [v]
    everywhere. *)

(* TODO: here and elsewhere, call xpull_check_not_needed tt; *)

Ltac xval_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_Val _ _) => idtac
  end.

Definition Wpgen_let_Val A1 `{EA1:Enc A1} (V:A1) (Fof:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \forall (x:A1), \[x = V] \-* ^(Fof x) Q).

Lemma xletvals_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) (Q:A->hprop),
  (H ==> ^(Fof V) Q) ->
  H ==> ^(Wpgen_let_Val V Fof) Q.
Proof using.
  introv M. applys MkStruct_erase. xchanges* M. intros ? ->. auto.
Qed.

Lemma xletval_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) (Q:A->hprop),
  (forall x, x = V -> H ==> ^(Fof x) Q) ->
  H ==> ^(Wpgen_let_Val V Fof) Q.
Proof using.
  introv M. applys xletvals_lemma. applys* M.
Qed.

Ltac xletval_core tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_Val _ (fun x => _)) => 
     let a := fresh x in
     let Pa := fresh "P" a in
     applys xletval_lemma;
     intros a P a
  end.

Tactic Notation "xletval" :=
  xletval_core tt.

Tactic Notation "xletval" "as" := (* TODO: document *)
  xval_pre tt;
  applys xletval_lemma.

Ltac xletvals_core tt :=
  xval_pre tt;
  applys xletvals_lemma.

Tactic Notation "xletvals" :=
  xletvals_core tt.

(* TODO: xlet should automatically xletval 
    xlets should be short for xletvals. *)


(*--------------------------------------------------------*)
(* ** [xcleanpat] *)

(** [xcleanpat] is a tactic for removing all the negated
    pattern assumptions. *)

Ltac xcleanpat_core :=
  repeat match goal with H: Wpgen_negpat _ |- _ => clear H end.

Tactic Notation "xcleanpat" :=
  xcleanpat_core.


(*--------------------------------------------------------*)
(* ** [xalias] -- deal with aliases using [xletval]; 
      synonymous tactics are provided *)

(** See documentation of [xletval]. *)

Ltac xalias_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_alias _ _) => idtac
  end.

Ltac xalias_core tt :=
  xalias_pre tt;
  xletval.

Tactic Notation "xalias" :=
  xalias_core tt.

Tactic Notation "xalias" "as" := (* TODO: document *)
  xalias_pre tt;
  xletval as.

Ltac xalias_subst_core tt :=
  xalias_pre tt;
  xletvals.

Tactic Notation "xalias_subst" :=
  xalias_subst_core tt.


(*--------------------------------------------------------*)
(* ** [xcase] is the new [xcase] *)

(** [xcase] applies to a goal of the form
    [(Case v = p1 Then F1 Else F2) H Q]. -- TODO: update syntax

   It produces two subgoals.
   - the first subgoal is [F1 H Q] with an hypothesis [E : v = p1].
   - the first subgoal is [F2 H Q] with an hypothesis [E : v <> p1].

   In both subgoals, it attemps deducing false from [E] or inverting [E],
   by calling the tactic [xcase_post E].

   Variants:

   - [xcase as E] allows to name [E].

   - [xcase_no_simpl] does not attempt inverting [E].

   - [xcase_no_simpl as E] allows to name [E];
     it does not attempt inverting [E].

   - [xcase_no_intros] can be used to manually name the variables and
     hypotheses from the case. It does not attempt inverting [E]. *)

(* TODO: change naming policy for handling pattern variables *)

(* [xcase_post] is a tactic that applies to an hypothesis
   of the form [v = p1] or [v <> p1], and attemps to prove
   false from it, and inverts it if possible. *)

Ltac xclean_trivial_eq tt :=
  repeat match goal with H: ?E = ?E |- _ => clear H end.

Ltac xcase_post H :=
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).

(* [xcase_core E cont1 cont2] is the underlying tactic for [xcase].
   It calls [cont1] on the first subgoal and [cont2] on the second subgoal. *)

Ltac xcase_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_case _ _ _) => idtac
  end.

Ltac xcase_extract_hyps tt :=
  pose ltac_mark;
  repeat (apply himpl_hforall_r; intro);
  repeat (apply hwand_hpure_r_intro; intro);
  gen_until_mark.

Ltac xcase_no_intros_core cont1 cont2 :=
  apply MkStruct_erase; applys himpl_hand_r;
  [ xcase_extract_hyps tt; cont1 tt
  | apply hwand_hpure_r_intro; cont2 tt ].

Ltac xcase_core H cont1 cont2 :=
  xcase_no_intros_core 
    ltac:(fun _ => introv H; cont1 tt)
    ltac:(fun _ => introv H; cont2 tt).

Tactic Notation "xcase_no_simpl" "as" ident(H) :=
  xcase_core H ltac:(fun _ => idtac) ltac:(fun _ => idtac).

Tactic Notation "xcase_no_simpl" :=
  let H := fresh "C" in xcase_no_simpl as H.

Tactic Notation "xcase" "as" ident(H) :=
  xcase_no_simpl as H; xcase_post H.

Tactic Notation "xcase" :=
  let H := fresh "C" in xcase as H.

Tactic Notation "xcase_no_intros" :=
   xcase_no_intros_core ltac:(fun _ => idtac) ltac:(fun _ => idtac).


(*--------------------------------------------------------*)
(* ** [xdone] *)

Lemma xdone_lemma : forall A `{EA:Enc A} (Q:A->hprop) H,
  H ==> ^(Wpgen_done) Q.
Proof using.
  intros. unfold Wpgen_done. applys MkStruct_erase. xsimpl.
Qed.

Ltac xdone_core tt :=
  applys xdone_lemma.

Tactic Notation "xdone" :=
  xdone_core tt.


(*--------------------------------------------------------*)
(* ** [xmatch] *)

(** [xmatch] applies to a pattern-matching goal of the form
    [(Match Case v = p1 Then F1
       Else Case v = p2 Then Alias y := w in F2
       Else Done/Fail) H Q]. -- TODO: update syntax.

    By default, the tactic calls the inversion tactic on
    the equalities [v = pi] associated with the case
    (and also calls congruence to attempt proving false).
    [xmatch_no_simpl] can be used to disable such inversions.

    Several variants are available:

    - [xmatch] investigates all the cases, doing inversions,
      and introducing all aliases as equalities.

    - [xmatch_subst_alias] performs all case analyses,
      and introduces and substitutes away all aliases.

    - [xmatch_no_cases] simply remove the [Wpgen_match] tag and
      leaves the cases to be solved manually using
      [xmatch_case] or [xcase]/[xfail]/[xdone] tactics directly.

    - [xmatch_no_intros] is like [xmatch], but does not
      perform any name introduction or any inversion.
      (One needs to manually call [xdone] for the last case.)

    - [xmatch_no_alias] is like [xmatch], but does not
      introduce aliases.

    - [xmatch_no_simpl] is like [xmatch], but does not do inversions.
      [xmatch_no_simpl_no_alias] is also available.
      [xmatch_no_simpl_subst_alias] are also available.

   Like with [xif], the tactic [xmatch] will likely not produce
   solvable goals if the post-condition is an unspecified evar.
   If the post-condition is an evar, call [xpost Q] to set the 
   post-condition. Alternatively, the syntax [xmatch Q] will do this.
*)

(* TODO put back fresh names into the goal *)

Ltac xmatch_case_alias cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => repeat xalias; xcase_post H)
               ltac:(fun _ => cont tt).

Ltac xmatch_case_no_alias cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => xcase_post H) ltac:(fun _ => cont tt).

Ltac xmatch_case_no_simpl cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => idtac) ltac:(fun _ => cont tt).

Ltac xmatch_case_no_intros cont :=
  xcase_no_intros_core
    ltac:(fun _ => idtac)
    ltac:(fun _ => let H := fresh "C" in introv H; cont tt).

Ltac xmatch_case_core cont_case :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_done) => xdone
  | (Wpgen_fail) => xfail
  | (Wpgen_case _ _ _) => first [ cont_case tt | fail 2 ]
  | ?c => idtac c; fail 100 "unexpected tag in xmatch_case"
  end.


(* [xmatch_cases case_tactic] recursively apply [xmatch_case] using
   [case_tactic] to handle each case. *)

Ltac xmatch_cases case_tactic :=
  xmatch_case_core ltac:(fun _ =>
    case_tactic ltac:(fun _ => xmatch_cases case_tactic)).

Ltac xmatch_check_post_instantiated tt :=
  match cfml_postcondition_is_evar tt with
  | true => fail 100 "xmatch requires a post-condition; use [xmatch Q] or [xpost Q] to set it."
  | false => idtac
  end.

Ltac xmatch_pre tt :=
  (* TODO xpull_check_not_needed tt; *)
  xmatch_check_post_instantiated tt.

Lemma xmatch_lemma : forall A `{EA:Enc A} H (F:Formula) (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Wptag (Wpgen_match F)) Q.
Proof using. auto. Qed.

Ltac xmatch_with cont :=
  xmatch_pre tt;
  apply xmatch_lemma;
  cont tt.

Tactic Notation "xmatch_case" := (* TODO: undocumented?*)
  xmatch_case_core ltac:(fun _ => xmatch_case_alias ltac:(fun _ => idtac)).

Tactic Notation "xmatch" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_alias).
Tactic Notation "xmatch" constr(Q) :=
  xpost Q; xmatch.
Tactic Notation "xmatch_no_alias" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_alias).
Tactic Notation "xmatch_subst_alias" :=
  xmatch_no_alias; repeat xalias_subst.
Tactic Notation "xmatch_no_cases" :=
  xmatch_with ltac:(fun _ => idtac).
Tactic Notation "xmatch_no_intros" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_intros).
Tactic Notation "xmatch_no_simpl_no_alias" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_simpl).
Tactic Notation "xmatch_no_simpl" :=
  xmatch_no_simpl_no_alias; repeat xalias.
Tactic Notation "xmatch_no_simpl_subst_alias" :=
  xmatch_no_simpl_no_alias; repeat xalias_subst.


(************************************************************)

Ltac xstep_once tt ::=
  match goal with
  | |- ?G => match xgoal_code_without_wptag tt with
    | (Wpgen_seq _ _) => xseq
    | (Wpgen_let_typed _ _) => xlet
    | (Wpgen_let _ _) => xlet
    | (Wpgen_app _) => xapp
    | (Wpgen_App_typed _ _ _) => xapp
    | (Wpgen_if_bool _ _ _) => xif
    | (Wpgen_val _) => xval
    | (Wpgen_Val _) => xval
    | (Wpgen_Val_no_mkstruct _) => xcast
    | (Wpgen_fail) => xfail
    | (Wpgen_done) => xdone
    | (Wpgen_case _ _ _) => xcase
    | (Wpgen_match _) => xmatch
    | ?F => check_is_Wpgen_record_new F; xapp
    (* | (Wpgen_case _ _ _) => xcase *)
    (* TODO complete *)
    end
  | |- Triple _ _ _ => xapp
  | |- _ ==> _ => xsimpl
  | |- _ ===> _ => xsimpl
  end.





(************************************************************)
(** Pairs *)

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



