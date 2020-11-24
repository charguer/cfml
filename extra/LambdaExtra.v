
Tactic Notation "xdef" :=
  rew_nary; rew_vals_to_trms;
  match goal with |- triple (trm_apps (trm_val ?f) _) _ _ =>
   applys rule_apps_funs;
   [unfold f; rew_nary; reflexivity | auto | simpl]
  end.


  (* detailed proof (to keep somewhere for debugging):
  intros. xdef. xchange (RO_Box_unfold p). xpull ;=> q.
  ram_apply_let rule_get_ro. { auto with iFrame. }
  unlock. move=>/= ?. xpull=> ->. apply rule_htop_post.
  ram_apply rule_get_ro. { iIntros. iFrame. iIntros. admit. }
  *)



(* ideally, ends with :
    val_box_up2 'f 'p ;;;
    val_box_get 'p.
  but requires proving rule_seq, similar to rule_let.
*)


(*
Definition is_extractible F :=
  forall A (J:A->hprop) Q,
    (forall x, F (J x) Q) ->
    F (hexists J) Q.
*)

Lemma rule_if_val : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros h1 h2 D N. forwards* (h'&v'&(N1&N2&N3&N4)): (rm M) h1.
  exists h' v'. splits~. { applys~ red_if_val. }
Qed.


Lemma red_if_bool : forall n m1 m2 (b:bool) r t1 t2,
     red n m1 (if b then t1 else t2) m2 r ->
     red n m1 (trm_if b t1 t2) m2 r.


Lemma rule_func_val : forall fopt x t1 H Q,
  H ==> Q (val_func fopt x t1) ->
  normal H ->
  triple (trm_func fopt x t1) H Q.
Proof using.
  introv M HS. intros HF h N. exists. splits*.
  { applys red_func. }
  { applys~ on_rw_sub_base. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Alternative version of [rule_if] *)

Lemma rule_if_val' : forall v t1 t2 H Q,
  (v <> val_int 0 -> triple t1 H Q) ->
  (v = val_int 0 -> triple t2 H Q) ->
  triple (trm_if v t1 t2) H Q.
Proof using. introv M1 M2. applys rule_if_val. case_if*. Qed.


Lemma rule_if_bool : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (n&h'&v'&R&K&C): (rm M) HF h.
  exists n h' v'. splits~. { applys~ red_if_bool. }
Qed.

Lemma rule_if_bool' : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using. introv M1 M2. applys rule_if_bool. case_if*. Qed.

Definition spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X H H' Q,
    pay_one H H' ->
    triple (subst f F (subst x X t1)) H' Q ->
    triple (trm_app F X) H Q.

Lemma spec_fix_val_fix : forall f x t1,
  spec_fix f x t1 (val_fix f x t1).
Proof using.
  intros f x t1 X H H' Q HP M. intros HF h N. unfolds pay_one.
  lets HP': himpl_frame_l HF (rm HP).
  lets N': (rm HP') (rm N). rew_heap in N'.
  destruct N' as (h1&h2&N1&N2&N3&N4).
  lets N1': hcredits_inv (rm N1). inverts N1'.
  lets (Na&Nb): heap_eq_forward (rm N4). simpls. subst.
  lets~ (n&h'&v&R&K&C): (rm M) HF h2.
  exists (n+1)%nat h' v. splits~.
  { applys* red_app_fix_val. fmap_red~. }
  { math. }
Qed.

Lemma rule_app_fix : forall f x F V t1 H H' Q,
  F = (val_fix f x t1) ->
  pay_one H H' ->
  triple (subst f F (subst x V t1)) H' Q ->
  triple (trm_app F V) H Q.
Proof using. introv EF N M. subst F. applys* spec_fix_val_fix. Qed.
(* TODO: choose which formulation to keep *)

Lemma rule_fix : forall f x t1 H Q,
  (forall (F:val), spec_fix f x t1 F -> H ==> Q F) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fix f x t1).
  { applys spec_fix_val_fix. }
  { applys~ rule_fix_val. }
Qed.


Lemma rule_if_val : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (n&h'&v'&R&K&C): (rm M) HF h.
  exists n h' v'. splits~. { applys~ red_if_val. }
Qed.

  | red_if_val : forall n m1 m2 v r t1 t2,
      red n m1 (If v = val_int 0 then t2 else t1) m2 r ->
      red n m1 (trm_if v t1 t2) m2 r

    (*
    cuts G: (forall (k:nat) L, LibList.length L = n-k :> int ->
       S k (Array L (p+k)%nat) (fun r => \[r = '()] \* (Array (make (length L) v) (p+k)%nat))).
    { lets R: (G 0%nat). math_rewrite ((p+0)%nat = p) in R. applys R. math. }
    clears L. intros k. induction_wf IH: (nat_upto_wf (abs n)) k. intros L EL.
    applys (rm M). case_if. (* todo: use trm_if instead of logic if *)
    { xapps.
    xapruct L as [|x L'].
    {
   *)

(* TODO: move *)
Lemma Alloc_not_null : forall k l,
  k > 0 ->
  Alloc k l ==> Alloc k l \* \[l <> null].
Proof using.
  intros.



Lemma hfield_eq_fun_hsingle :
  hfield = (fun l f v => ((l+f)%nat ~~~> v)).
Proof using. intros. auto. Qed.

(* needed? *)
Lemma hsingle_eq_fun_hfield :
  hsingle = (fun l v => (l`.`(0%nat) ~~~> v)).
Proof using.
  intros. applys fun_ext_2. intros. unfold hfield. fequals.
  Transparent loc. unfold loc. math.
Qed.




      (* ---------------------------------------------------------------------- *)
      (* ** Tactic [xfor] *)

      (*

        Ltac xfor_template xfor_tactic xseq_cont :=
          match goal with
          | |- local (cf_seq _ _) _ _ => xseq; [ xfor_tactic tt | xseq_cont tt ]
          | _ => xfor_tactic tt
          end.

        Ltac xfor_intros_all R LR HR :=
          intros R LR; hnf; intros HR.

        Ltac xfor_intros R :=
          let LR := fresh "L" R in
          let HR := fresh "H" R in
          xfor_intros_all R LR HR.

        Ltac xfor_basic xfor_intros_tactic :=
          applys local_erase;
          xfor_intros_tactic tt.

        Ltac xfor_core xfor_tactic :=
          xfor_template ltac:(xfor_tactic) ltac:(fun tt => xpull).

        Tactic Notation "xfor" "as" ident(R) :=
          xfor_core ltac:(fun tt => xfor_basic ltac:(fun tt => xfor_intros R)).

        Tactic Notation "xfor" "as" ident(R) ident(LR) ident(HR) :=
          xfor_core ltac:(fun tt => xfor_basic ltac:(fun tt => xfor_intros_all R LR HR)).
      *)


      (** [xfor] applies to a goal of the form [(For i := a To b Do F) H Q].
          It introduces an abstract local predicate [S] such that [S i]
          denotes the behavior of the loop starting from index [i].
          The initial goal is [S a H Q]. An assumption is provided to unfold
          the loop:
          [forall i H' Q',
           (If_ i <= b Then (Seq_ F ;;; S (i+1)) Else (Ret tt)) H' Q' -> S i H' Q'].

          After [xfor], the typical proof pattern is to generalize the goal
          by calling [assert (forall X i, i <= b -> S i (Hof i X) (Qof i X))],
          and then performing an induction on [i].
          (Or, using [xind_skip] to skip the termination proof.)

          Alternatively, one can call one of the [xfor_inv] tactics described
          below to automatically set up the induction. The use of an invariant
          makes the proof simpler but

          Forms:

          - [xfor] is the basic form, described above.

          - [xfor as S] is equivalent to [xwhile; intros S LS HS].

          - [xfor_inv I] specializes the goal for the case [a <= b+1].
            It requests to prove [H ==> I a] and [I (b+1) ==> Q], and
            [forall i, a <= i <= b, F (I i) (# I (i+1))] for iterations.
            Note that the goal will not be provable if [a > b+1].

          - [xfor_inv_void] simplifies the goal in case the loops runs
            no iteration, that is, when [a > b].

          - [xfor_inv_case I] provides two sub goals, one for the case
            [a > b] and one for the case [a <= b].
      *)

      (*
      Lemma xfor_simplify_inequality_lemma : forall (n:int),
        ((n-1)+1) = n.
      Proof using. math. Qed.

      Ltac xfor_simplify_inequality tt :=
        try rewrite xfor_simplify_inequality_lemma.
        (* TODO: ideally, would restrict the rewriting to the
           occurences created by the application of the lemma. *)

      Lemma xfor_inv_case_lemma : forall (I:int->hprop),
         forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
         ((a <= b) -> exists H',
                (H ==> I a \* H')
             /\ (forall i, a <= i <= b -> F i (I i) (# I(i+1)))
             /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
         ((a > b) ->
                (H ==> Q tt \* \GC)) ->
        (For i := a To b Do F i Done_) H Q.
      Proof using.
        introv M1 M2. apply local_erase. intros S LS HS.
        tests: (a <= b).
        { forwards (H'&(Ma&Mb&Mc)): (rm M1). math.
          cuts P: (forall i, a <= i <= b+1 -> S i (I i) (# I (b+1))).
          { xapply P. math. hchanges Ma. hchanges Mc. }
          { intros i. induction_wf IH: (upto (b+1)) i. intros Hi.
            applys (rm HS). xif.
            { xseq. applys Mb. math. xapply IH; auto with maths. xsimpl. }
            { xret. math_rewrite (i = b+1). xsimpl. } } }
        { applys (rm HS). xif. { math. } { xret. applys M2. math. } }
      Qed.

      Lemma xfor_inv_lemma : forall (I:int->hprop),
        forall (a:int) (b:int) (F:int->~~unit) H H',
        (a <= b+1) ->
        (H ==> I a \* H') ->
        (forall i, a <= i <= b -> F i (I i) (# I(i+1))) ->
        (For i := a To b Do F i Done_) H (# I (b+1) \* H').
      Proof using.
        introv ML MH MI. applys xfor_inv_case_lemma I; intros C.
        { exists H'. splits~. xsimpl. }
        { xchange MH. math_rewrite (a = b + 1). xsimpl. }
      Qed.

      Lemma xfor_inv_lemma_pred : forall (I:int->hprop),
        forall (a:int) (n:int) (F:int->~~unit) H H',
        (a <= n) ->
        (H ==> I a \* H') ->
        (forall i, a <= i < n -> F i (I i) (# I(i+1))) ->
        (For i := a To (n - 1) Do F i Done_) H (# I n \* H').
      Proof using.
        introv ML MH MI. applys xfor_inv_case_lemma I; intros C.
        { exists H'. splits~.
          { intros. applys MI. math. }
          { math_rewrite ((n-1)+1 = n). xsimpl. } }
        { xchange MH. math_rewrite (a = n). xsimpl. }
      Qed.

      Lemma xfor_inv_void_lemma :
        forall (a:int) (b:int) (F:int->~~unit) H,
        (a > b) ->
        (For i := a To b Do F i Done_) H (# H).
      Proof using.
        introv ML.
        applys xfor_inv_case_lemma (fun (i:int) => \[]); intros C.
        { false. math. }
        { xsimpl. }
      Qed.

      Ltac xfor_ensure_evar_post cont :=
        match cfml_postcondition_is_evar tt with
        | true => cont tt
        | false => xgc_post; [ cont tt | ]
        end.

      Ltac xfor_pre cont :=
        let aux tt := xuntag tag_for; cont tt in
        match cfml_get_tag tt with
        | tag_for => aux tt
        | tag_seq => xseq; [ aux tt | instantiate; try xpull ]
        end.

      Ltac xfor_pre_ensure_evar_post cont :=
        xfor_pre ltac:(fun _ =>
          xfor_ensure_evar_post ltac:(fun _ => cont tt)).

      Tactic Notation "xfor" :=
        xfor_pre ltac:(fun _ => apply local_erase).

      Tactic Notation "xfor" "as" ident(S) :=
        xfor_pre ltac:(fun _ =>
          let LS := fresh "L" S in
          let HS := fresh "H" S in
          apply local_erase;
          intros S LS HS).

      Ltac xfor_inv_case_check_post_instantiated tt :=
        lazymatch cfml_postcondition_is_evar tt with
        | true => fail 2 "xfor_inv_case requires a post-condition; use [xpost Q] to set it, or [xseq Q] if the loop is behind a Seq."
        | false => idtac
        end.

      Ltac xfor_inv_case_core_then I cont1 cont2 :=
        match cfml_get_tag tt with
        | tag_seq =>
             fail 1 "xfor_inv_case requires a post-condition; use [xseq Q] to assign it."
        | tag_for =>
             xfor_inv_case_check_post_instantiated tt;
             xfor_pre ltac:(fun _ => apply (@xfor_inv_case_lemma I); [ cont1 tt | cont2 tt ])
        end.

      Ltac xfor_inv_case_no_intros_core I :=
        xfor_inv_case_core_then I
          ltac:(fun _ => xfor_simplify_inequality tt)
          ltac:(fun _ => idtac).

      Ltac xfor_inv_case_core I :=
        let C := fresh "C" in
        xfor_inv_case_core_then I
          ltac:(fun _ => intros C; esplit; splits 3; [ | | xfor_simplify_inequality tt ])
          ltac:(fun _ => intros C).

      Tactic Notation "xfor_inv_case" constr(I) :=
        xfor_inv_case_core I.

      Ltac xfor_inv_core I :=
        xfor_pre_ensure_evar_post ltac:(fun _ =>
           first [ apply (@xfor_inv_lemma_pred I)
                 | apply (@xfor_inv_lemma I) ];
           [ | | xtag_pre_post ]).

      Tactic Notation "xfor_inv" constr(I) :=
        xfor_inv_core I.

      Ltac xfor_inv_void_core tt :=
        xfor_pre_ensure_evar_post ltac:(fun _ =>
          apply (@xfor_inv_void_lemma)).

      Tactic Notation "xfor_inv_void" :=
        xfor_inv_void_core tt.

      *)


Lemma Rule_for : forall x (n1 n2:int) t3 H (Q:unit->hprop),
  (If (n1 <= n2) then
    (exists (Q1:unit->hprop),
      Triple (subst x n1 t3) H Q1 /\
      Triple (trm_for x (n1+1) n2 t3) (Q1 tt) Q)
  else
    ((fun (r:unit) => H) ===> Q)) ->
  Triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. applys rule_for. case_if.
  { destruct M as (Q1&M1&M2). exists (fun r => \[r = val_unit] \* Q1 tt).
    splits.
    { unfold Triple, Post in M1. xapply M1. hsimpl.
      hpull ;=> r u E. destruct u. subst r. hsimpl~. }
    { xpull ;=> _. applys M2. }
    { intros v N. hpull. } }
  { hpull ;=> r E. unfold Post. hchange (M tt). subst r. hsimpl~ tt. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Lifting of postcondition for alloc *)

(* TODO: rename Alloc and Alloc' *)

Fixpoint Alloc' (k:nat) (l:loc) :=
  match k with
  | O => \[]
  | S k' => (Hexists (A1:Type) (EA1:Enc A1) (V:A1), l ~~> V)
            \* (Alloc' k' (S l)%nat)
  end.

Lemma Alloc'_zero_eq : forall l,
  Alloc' O l = \[].
Proof using. auto. Qed.

Lemma Alloc'_succ_eq : forall l k,
  Alloc' (S k) l = (Hexists (A1:Type) (EA1:Enc A1) (V:A1), l ~~> V)
                   \* Alloc' k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc'.

Hint Rewrite Alloc'_zero_eq Alloc'_succ_eq : rew_Alloc'.

Tactic Notation "rew_Alloc'" :=
  autorewrite with rew_Alloc'.

Lemma Alloc_to_Alloc' : forall (l:loc) (k:nat),
  Alloc k l ==> Alloc' k l.
Proof using.
  intros. gen l. induction k; intros; rew_Alloc'; rew_Alloc.
  { auto. }
  { hpull ;=> x. sets d: (decode x).
    hsimpl Enc_dyn d. hchange (IHk (S l)).
    unfold d. rewrite Hsingle_to_hsingle. hsimpl.
    rewrite enc_decode. hsimpl~. }
Qed.




Lemma Rule_alloc : forall n,
  n >= 0 ->
  Triple (val_alloc n)
    \[]
    (fun l => Alloc' (abs n) l).
Proof using.
  introv N. xapplys~ rule_alloc.
  intros r. hchanges Alloc_to_Alloc'.
Qed.



(* REFINED IMPLEMENTATION OF POST PROCESSING IN HSIMPL
  Ltac hsimpl_post_before_generalize tt :=
    idtac. (* autorewrite with rew_isTrue in *. *)

  Ltac hsimpl_post_after_generalize tt :=
    autorewrite with rew_isTrue.

  Ltac himpl_post_processing_for_hyp H :=
    autorewrite with rew_isTrue in H.

  Ltac hsimpl_core tt ::=
    pose ltac_mark;
    hcancel_prepare tt;
    hpull;
    intros;
    hcancel;
    hsimpl_post_before_generalize tt;
    gen_until_mark_with_processing ltac:(himpl_post_processing_for_hyp);
    hsimpl_post_after_generalize tt.
*)


Ltac hsimpl_post_before_generalize tt :=
  idtac. (* autorewrite with rew_isTrue in *. *)

Ltac hsimpl_post_after_generalize tt :=
  autorewrite with rew_isTrue.

Ltac himpl_post_processing_for_hyp H :=
  autorewrite with rew_isTrue in H.

Ltac gen_until_mark_with_processing cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H; generalize H; clear H; gen_until_mark
  end end.

Ltac hsimpl_core tt ::=
  pose ltac_mark;
  hcancel_prepare tt;
  hpull;
  intros;
  hcancel;
  hsimpl_post_before_generalize tt;
  gen_until_mark_with_processing ltac:(himpl_post_processing_for_hyp);
  hsimpl_post_after_generalize tt.


(* ** Configure [hcancel] to make it aware of [hsingle]
DEPRECATED
Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  | Hsingle _ _ => hcancel_try_same tt
  | Hfield _ _ _ => hcancel_try_same tt
  end.
*)


Definition Hfield `{EA:Enc A} (l:loc) (i:field) (V:A) : hprop :=
  hfield l i (enc V).

(* Notation for parsing *)
Notation "l `.` i '~>' v" := (Hfield l i v)
  (at level 32, i at level 0, no associativity,
   format "l `.` i  '~>'  v") : heap_scope.

Lemma Hfield_to_hfield : forall `{EA:Enc A} (l:loc) (i:field) (V:A),
  Hfield l i V = hfield l i (enc V).
Proof using. auto. Qed.

Lemma Hfield_not_null : forall l f `{EA:Enc A} (V:A),
  f = 0%nat -> (* TODO: generalize *)
  (l`.`f ~> V) ==> (l`.`f ~> V) \* \[l <> null].
Proof using. intros. applys~ hfield_not_null. Qed.

Arguments Hfield_not_null : clear implicits.

Definition Hsingle `{EA:Enc A} (l:loc) (V:A) :=
  hsingle l (enc V).

Notation "l '~~>' v" := (l ~> Ref v)
  (at level 32, no associativity) : heap_scope.

Lemma Cf_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) (F1 F2 : Formula),
  forall H H' (Q:unit->hprop),
  wf R ->
  (H ==> Hexists b X, I b X \* H') ->
  (forall (F:Formula) b X, is_local (@F unit _) ->
      (forall b' X', R X' X -> 'F (I b' X') (fun _ => Hexists Y, I false Y)) ->
      '(Local (Cf_if F1 (Local (Cf_seq F2 F)) (Local (Cf_val val_unit))))
        (I b X) (fun _ => Hexists Y, I false Y)) ->
  '(Cf_while F1 F2) H Q.


Notation "F 'PRE' H 'POST' Q" :=
  (F H Q)
  (at level 69, only parsing) : charac.

(** Notation [PRE H CODE F POST Q] for displaying characteristic formulae *)

Notation "'PRE' H 'CODE' F 'POST' Q" :=
  (@Local F _ _ H Q) (at level 69,
  format "'[v' '[' 'PRE'  H  ']' '/' '[' 'CODE'  F  ']' '/' '[' 'POST'  Q  ']' ']'")
  : charac2.

(*
Notation "'`Val' v" :=
  (Cf_val v)
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  (Cf_if F0 F1 F2)
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  (Cf_if_val v F1 F2)
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  (Cf_seq F1 F2)
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' x ':=' F1 'in' F2" :=
  (Cf_let_typed F1 (fun x => F2))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' [ A EA ] x ':=' F1 'in' F2" :=
  (Cf_let F1 (fun A EA x => F2))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' '`Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  (Cf_app t)
  (at level 68, t at level 0) : charac.

Notation "'`Fail'" :=
  (Cf_fail)
  (at level 69) : charac.
*)


Notation "'`Val' v" :=
  (Cf_val v)
  (at level 69) : charac2.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  (Cf_if F0 F1 F2)
  (at level 69, F0 at level 0) : charac2.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  (Cf_if_val v F1 F2)
  (at level 69) : charac2.

Notation "'`Seq' F1 ;;; F2" :=
  (Cf_seq F1 F2)
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac2.

Notation "'`Let' x ':=' F1 'in' F2" :=
  (Cf_let_typed F1 (fun x => F2))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac2.

Notation "'`Let' [ A EA ] x ':=' F1 'in' F2" :=
  (Cf_let F1 (fun A EA x => F2))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' '`Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac2.

Notation "'`App' t " :=
  (Cf_app t)
  (at level 68, t at level 0) : charac2.

Notation "'`Fail'" :=
  (Cf_fail)
  (at level 69) : charac2.




Notation "'`Val' v" :=
  (Local (Cf_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  (Local (Cf_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  (Local (Cf_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  (Local (Cf_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'``Let' x ':=' F1 'in' F2" :=
  (Local (Cf_let_typed F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '``Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' [ A EA ] x ':=' F1 'in' F2" :=
  (Local (Cf_let F1 (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' '`Let'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  (Local (Cf_app t))
  (at level 68, t at level 0) : charac.

Notation "'`Fail'" :=
  (Local (Cf_fail))
  (at level 69) : charac.


Open Scope charac2.
Open Scope charac.


(*--------------------------------------------------------*)
(* ** [xformat] *)



Definition tag_cf (F:Formula) A `{EA:Enc A} := F A EA.

Arguments tag_cf [A] {EA}.

(*
Notation "'PRE' H 'POST' Q 'CODE' F" :=
  (tag_cf F H Q) (at level 69,
  format "'[v' '[' 'PRE'  H  ']'  '/' '[' 'POST'  Q  ']'  '/' '[' 'CODE'  F  ']'  ']'")
  : charac.
*)

(** [xtag_add] adds [tag_cf] from the head of the goal,
    or does nothing if there is no such tag. *)

Ltac xtag_add_core tt :=
  match goal with
  | |- tag_cf ?F ?H ?Q => idtac
  | |- Local ?F ?H ?Q => change ((tag_cf (Local F)) H Q) in |-*
  | |- forall _, _ =>
     intro;
     xtag_add_core tt;
     let x := get_last_hyp tt in
     revert x
  | _ => idtac
  end.

Tactic Notation "xtag_add" :=
  xtag_add_core tt.

(* TODO
Ltac xformat_core tt ::=
  xtag_add.
*)


(** [xtag_remove] removes [tag_cf] from the head of the goal,
    or does nothing if there is no such tag. *)

Ltac xtag_remove_core tt :=
  match goal with
  | |- tag_cf ?F ?H ?Q => unfold tag_cf at 1
  | _ => idtac
  end.

Tactic Notation "xtag_remove" :=
  xtag_remove_core tt.



(* ********************************************************************** *)
(* * Counter function *)

Implicit Types g : val.


(* ---------------------------------------------------------------------- *)
(** Representation *)

Definition MCount (n:int) (g:val) : hprop :=
  Hexists p, (p ~~> n) \*
    \[ forall n', triple (g val_unit)
                  (p ~~> n')
                  (fun r => \[r = n'+1] \* (p ~~> (n'+1))) ].

(* TODO: fix priority of p ~~> (n'+1) differently *)


(* ---------------------------------------------------------------------- *)
(** Specification *)

Lemma rule_MCount : forall n g,
  triple (g '()) (MCount n g) (fun r => \[ r = n+1 ] \* MCount (n+1) g).
Proof using.
  intros. unfold MCount at 1. xpull ;=> p Hg.
  xapply Hg. hsimpl. (* todo: why not xapplys? *)
  hpull ;=> r Er. unfold MCount. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Implementation *)

Definition val_mkcounter : val :=
  Vars U, V, P, G in
  ValFun U :=
    Let P := val_ref 0 in
    (Fun V := val_incr P ;;; val_get P).


(* ---------------------------------------------------------------------- *)
(** Verification *)

Lemma rule_mkcounter :
  triple (val_mkcounter val_unit)
    \[]
    (fun g => MCount 0 g).
Proof using.
  xcf. xapps. intros r p E. subst r.
  xval as F. unfold MCount. hsimpl.
  { intros n'. xcf. xapp~. xapp. hsimpl~. }
Qed.

Hint Extern 1 (Register_spec val_mkcounter) => Provide rule_mkcounter.


(* ---------------------------------------------------------------------- *)
(** Demo *)

Definition trm_test_mkcounter : trm :=
  Vars C, M, N in
  Let C := val_mkcounter '() in
  Let N := C '() in
  Let M := C '() in
  val_add N M.

Lemma rule_test_mkcounter :
  triple trm_test_mkcounter
    \[]
    (fun r => \[r = 3]).
Proof using.
  xcf.
  xapp as C.
  xapps rule_MCount.
  xapps rule_MCount.
  xapps~.
Qed.

xwhile: xseq. applys local_erase. intros R LR; hnf; intros HR.


Lemma rule_if' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  triple t1 (Q1 true) Q ->
  triple t2 (Q1 false) Q ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3 M4. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  tests C: (is_val_bool v).
  { destruct C as (b&E). destruct b.
    { subst v. forwards* (h'&v'&R&K): (rm M2) h1'.
      exists h' v'. splits~.
      { applys* red_if. }
      { rewrite <- htop_hstar_htop. rew_heap~. } }
    { subst v. forwards* (h'&v'&R&K): (rm M3) h1'.
      exists h' v'. splits~.
      { applys* red_if. }
      { rewrite <- htop_hstar_htop. rew_heap~. } } }
    (* TODO: factorize better *)
  { specializes M4 C.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange M4. hsimpl. hsimpl. }
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. }
  (* TODO: shorten this *)
Qed.


  { destruct P as (Q1&P1&P2). applys rule_if.
    { applys* IH. }
    { specializes P2 true. applys sound_for_local (rm P2).
      intros H' Q' P'. destruct P' as (b&P1'&P2'&P3').
      inverts P1'. applys* IH. }
    { specializes P2 false. applys sound_for_local (rm P2).
      intros H' Q' P'. destruct P' as (b&P1'&P2'&P3').
      inverts P1'. applys* IH. }
    { intros v N. specializes P2 v. applys local_extract_false P2.
      intros H' Q' (b&E&S1&S2). subst. applys N. hnfs*. } }



(*
Lemma bool_eq_false_of_neq_true : forall b,
  b <> true ->
  b = false.
Proof using. intros. destruct b; auto_false. Qed.

Hint Resolve bool_eq_false_of_neq_true.
*)


(* not used

Lemma trm_size_Subst : forall y d t,
  trm_size (Subst y d t) = trm_size t.
Proof using. intros. unfold Subst. rewrite~ trm_size_subst. Qed.

Ltac solve_measure_trm_size tt ::=
  unfold measure in *; simpls; repeat rewrite trm_size_Subst; math.

*)


(* ---------------------------------------------------------------------- *)
(* ** Specification of functions with lifted arguments *)

(*
Definition Apps (f:val) (Vs:dyns) :=
  apps f (encs Vs).

Definition Spec (f:val) (Vs:dyns) :=
  @Triple (Apps f Vs).

Implicit Arguments Spec [A [EA]].
*)

(* Remark: eta-expansion of [Spec]
    Definition Spec (f:val) (Vs:dyns) A `{EA:Enc A} (H:hprop) (Q:A->hprop) :=
      Triple (Apps f Vs) H Q.
*)

(* ---------------------------------------------------------------------- *)
(** TODO

Definition F := 3%nat.

    Definition val_compress' :=
      Vars P, X in
      ValFun P X :=
        LetFix F X := X in
        F X.

Lemma test0 : forall A B C (V: A -> B -> C) (P:C->Prop) (a:A) (b:B),
  (let x := a in let y := b in P (V x y)) ->
  P (let x := a in let y := b in V x y).
Proof using. auto. Qed.

Lemma demo : forall A B C (V: A -> B -> C) (P:C->Prop) (a:A) (b:B),
  P (let x := a in let y := b in V x y).
Proof using.
  intros. eapply test0.
Abort.

Lemma test0nat : forall C F  (P:C->Prop) (V: nat -> nat -> C)  (a b:nat),
  F = (let x := a in let y := b in V x y) ->
  (let x := a in let y := b in P (V x y)) ->
  P F.
Proof using. auto. Qed.

Transparent var.

Lemma test1 : forall C (V: var -> var -> C) (P:C->Prop),
  (let x : var := 0%nat in let y : var := 1%nat in P (V x y)) ->
  P (let x : var := 0%nat in let y : var :=  1%nat  in V x y).
Proof using. auto. Qed.

Lemma demo2 : forall  (V: var -> var -> trm) (P:trm->Prop) H Q,
  triple (let x : var := 0%nat in let y : var :=  1%nat  in V x y) H Q.
Proof using.
  intros. eapply test1.
Abort.



Lemma test : forall (V: var -> var -> val) (P:val->Prop),
  (Vars A, B in P (V A B)) ->
  P (Vars A, B in V A B).
Proof using. auto. Qed.

Lemma test' : forall (F:val) (V: var -> var -> val) (P:val->Prop),
  F = (Vars A, B in V A B) ->
  (Vars A, B in P (V A B)) ->
  P F.
Proof using. intros. subst. auto. Qed.

    Lemma rule_compress' : forall n p x z,
      triple (val_compress' p x z)
        (\[])
        (fun r => \[]).
    Proof using.
      intros. (* unfold val_compress'. xcf. *)
  pattern val_compress'.
  cbv delta [ val_compress' ].


  match goal with |- ?P ?F => eapply (@test1 _ _ P) end.

  match goal with |- ?P ?F => eapply (@test0 nat nat _ _ P) end.

  match goal with |- ?P ?F => eapply (@test0nat _ F P) end.
  reflexivity.

 eapply test0nat; intros.

  eapply (@test' val_compress').
  cbv delta [ val_compress' ].
  generalize 1%nat. generalize 0%nat. intros. simpl. reflexivity.
  intros A B. simpl. xcf.

 pattern 1%nat.  pattern 0%nat. gener simpl. reflexivity.


      eapply test.
      Global Opaque var. xcf.

*)


Definition F : var := 0%nat.
Definition P : var := 1%nat.
Definition Q : var := 2%nat.
Definition N : var := 3%nat.


Definition F : var := 0%nat.
Definition P : var := 1%nat.
Definition Q : var := 2%nat.
Definition X : var := 4%nat.
Definition Y : var := 5%nat.


Ltac hsimpl_remove_head_units tt :=
  repeat match goal with |- unit -> _ => intros _ end.




(* Disequality  xcf details:
  xcf_prepare tt.
  let f := xcf_get_fun tt in
            match f with
            | val_funs _ _ =>
                applys Triple_apps_funs_of_Cf_iter 20%nat;
                [ reflexivity | try xeq_encs | reflexivity | xcf_post tt ]
            end.  *)

  (* xspec ;=> H. *)
  (* xapps Spec_eq_int. *)
  (* xapp_basic_prepare tt. xapplys Spec_eq_int. *)
  (*
    forwards_nounfold_then G ltac:(fun K =>
     eapply local_frame; [ xlocal | eapply K | hcancel |  try apply refl_rel_incl' ]).
    forwards_nounfold_then G ltac:(fun K => instantiate;
     eapply local_frame; [ xlocal | sapply K | hcancel | try apply refl_rel_incl' ]).
    forwards_nounfold_then G ltac:(fun K => pose (X:=K)).
     eapply local_frame; [ xlocal | sapply X | hcancel | try apply refl_rel_incl' ].
  *)


 (*  DEPRECATED fun `{Enc A} H (Q:A->hprop) =>
    exists (Q1:bool->hprop),
      'F0 H Q1
   /\ 'F1 (Q1 true) Q
   /\ 'F2 (Q1 false) Q.
  *)
(* DEPRECATED
  { destruct P as (Q1&P1&P2&P3). applys Rule_if; applys* IH. }
*)

(* ---------------------------------------------------------------------- *)

Definition bool_of_val (v:val) : bool :=
  If v = val_int 0 then false else true.

Lemma bool_of_val_eq : forall v,
  bool_of_val v = If v = val_int 0 then false else true.
Proof using. auto. Qed.

Lemma bool_of_val_zero :
  bool_of_val 0 = false.
Proof using. intros. unfold bool_of_val. case_if*. Qed.

Lemma bool_of_val_nonzero : forall v,
  v <> val_int 0 ->
  bool_of_val v = true.
Proof using. intros. unfold bool_of_val. case_if*. Qed.

Opaque bool_of_val.

Lemma rule_if'' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (v:val), triple (if bool_of_val v then t1 else t2) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* rule_if. intros v.
  specializes M2 v. rewrite bool_of_val_eq in M2. case_if*.
Qed.



Ltac xcf_reveal_fun tt :=
  match goal with
  | |- triple (trm_apps (trm_val ?f) _) _ _ =>
     first [ unfold f
           | match goal with H: f = _ |- _ => rewrite H end
           | idtac ]
  | _ => idtac
  end.


(*

    (* xapp Spec_get'. *)
    xapp_basic_prepare tt. (* xapply @Spec_get. hsimpl.*)

    forwards_nounfold_then Spec_get ltac:(fun K =>
      eapply local_frame; [ xlocal | eapply K | hcancel | try apply refl_rel_incl' ]).
  *)

  (* Try in 8.6 to use [notypeclasses refine]
    forwards_nounfold_then Spec_get ltac:(fun K =>
      eapply local_frame; [ xlocal | notypeclasses refine @K | hcancel | try apply refl_rel_incl' ]).
  *)

    eapply local_frame; [ xlocal | fast_apply Spec_get | hcancel | try apply refl_rel_incl' ].

   eapply local_frame.
      skip. eapply @Spec_get. hsimpl. hsimpl.

  xapps. hsimpl.

*)



(* DEPRECATED

Ltac xcf_post tt :=
  simpl; rew_dyn; xformat.

Ltac xcf_compute n :=
  first [
          | fail 1 ]
        | applys Triple_trm_of_Cf_iter n; [ xcf_post tt ] ].

Ltac xcf_core n ::=

Lemma rule_neq_3 : forall (v1 v2:int),
  Triple (val_neq v1 v2)
    \[]
    (fun (r:int) => \[r = (If v1 = v2 then 0 else 1)]).
Proof using.
  intros. unfold val_neq. rew_compact. simpl.
  applys Triple_apps_funs_of_Cf_iter 20%nat;
    [ try reflexivity | try xeq_encs | try reflexivity | simpl; rew_dyn ].
Abort.

Lemma rule_neq_3'' : forall (v1 v2:int),
  Spec val_neq ``[ v1, v2 ]
    \[]
    (fun (r:int) => \[r = (If v1 = v2 then 0 else 1)]).
Proof using.
  intros. unfold val_neq. rew_compact.
  applys Triple_apps_funs_of_Cf_iter 20%nat;
    [ try reflexivity | try xeq_encs | try reflexivity
    | simpl; rew_dyn; rew_compact ].
Abort.

  Lemma rule_neq_3'' : forall (v1 v2:int),
    App val_neq '[ ``v1, ``v2 ]
      \[]
      (fun (r:int) => \[r = (If v1 = v2 then 0 else 1)]).
  Proof using.
    intros. unfold val_neq. rew_compact.
    applys Triple_apps_funs_of_Cf_iter 20%nat;
      [ try reflexivity | try xeq_encs | try reflexivity | simpl ].
  Abort.

*)

(* ---------------------------------------------------------------------- *)


(* DEPRECATED
Lemma Rule_eq_int : forall (v1 v2 : int),
  Spec val_eq ``[v1, v2]
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2 :> int)]).
Proof using.
  intros. applys Spec_eq. applys Enc_injective_Enc_int.
Qed.

Hint Extern 1 (RegisterSpec (val_prim val_eq)) =>
  Provide Spec_eq.
*)




(* ---------------------------------------------------------------------- *)

(*
Notation "`` V" := (enc V) (at level 8, format "`` V").
*)


Ltac xget_fun tt :=
  match goal with
  | |- Spec ?f _ _ _ => constr:(f)
  | |- Triple (apps ?f _) _ _ => constr:(f)
  | |- Triple (trm_apps (trm_val ?f) _) _ _ => constr:(f)
  end.

Ltac xcf_core n ::=
  intros;
  rew_compact;
  let f := xget_fun tt in
  unfold f;
  rew_compact;
  applys Triple_apps_funs_of_Cf_iter 20%nat;
    [ try reflexivity
    |
    | try reflexivity
    | simpl; rew_compact; rew_dyn; simpl;  ].


Notation "'`Apps' f vs " :=
  (Local (@Triple (trm_apps f vs%enc)))
  (at level 68, f at level 0) : charac.

Notation "'`Apps' f vs " :=
  (`App (apps f vs%enc))
  (at level 68, f at level 0) : charac.


Sound If
{ destruct P as (A1&EA1&Q1&P1&P2). applys Rule_if.
    { applys (@Triple_enc_change A1).
      { applys* IH. }
      { intros X.
    { intros X. specializes P2 X. applys Sound_for_Local (rm P2).
      clears Q1 H Q A. intros A2 EA2 H Q (X'&E'&P3&P4).
      rewrite E'; tests C: (X' = 0); case_if; simpls; tryfalse; applys~ IH. } }*)



(* ---------------------------------------------------------------------- *)
(** Functions of three arguments *)

Definition Spec_fun3 (x1 x2 x3:var) (t1:trm) (F:val) :=
  forall X1 X2 X3, Triple (subst x3 X3 (subst x2 X2 (subst x1 X1 t1))) ===> Triple (F X1 X2 X3).

Lemma Rule_app_fun3 : forall x1 x2 x3 F V1 V2 V3 t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fun3 x1 x2 x3 t1) ->
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  Triple (subst x3 V3 (subst x2 V2 (subst x1 V1 t1))) H Q ->
  Triple (F V1 V2 V3) H Q.
Proof using. introv E N M. unfold Triple. applys* rule_app_fun3. Qed.

Lemma Spec_fun3_val_fun3 : forall x1 x2 x3 t1,
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  Spec_fun3 x1 x2 x3 t1 (val_fun3 x1 x2 x3 t1).
Proof using. introv N M. applys* Rule_app_fun3. Qed.






Section RuleStateOps.
Transparent Hsingle.

Lemma Rule_ref : forall A `{EA:Enc A} (V:A) v,
  v = enc V ->
  Triple (val_ref v)
    \[]
    (fun l => l ~~~> V).
Proof using.
  introv E. applys_eq rule_ref 1. subst~.
Qed.

Lemma Rule_get : forall A `{EA:Enc A} (V:A) l,
  Triple (val_get l)
    (l ~~~> V)
    (fun x => \[x = V] \* (l ~~~> V)).
Proof using.
  introv. unfold Triple, Post, Hsingle. xapplys* rule_get.
Qed.

Lemma Rule_set' : forall v1 A2 `{EA2:Enc A2} (V2:A2) l v2,
  v2 = enc V2 ->
  Triple (val_set l v2)
    (l ~~> v1)
    (fun u => l ~~~> V2).
Proof using.
  introv E. subst. unfold Triple, Hsingle. xapplys rule_set.
  intros. subst. unfold Post. hsimpl~ tt.
Qed.

Lemma Rule_set : forall A1 A2 `{EA1:Enc A1} (V1:A1) `{EA2:Enc A2} (V2:A2) l v2,
  v2 = enc V2 ->
  Triple (val_set l v2)
    (l ~~~> V1)
    (fun u => l ~~~> V2).
Proof using. introv E. applys~ Rule_set'. Qed.

Lemma Rule_alloc : forall n,
  n >= 0 ->
  Triple (val_alloc n)
    \[]
    (fun l => Alloc' (abs n) l).
Proof using.
  introv N. xapplys~ rule_alloc.
  intros r. hchanges Alloc_to_Alloc'.
Qed.

End RuleStateOps.

Implicit Types v : val.
Implicit Types n : int.

Lemma Rule_eq : forall v1 v2,
  Triple (val_eq v1 v2)
    \[]
    (fun n => \[ n = (If v1 = v2 then 1 else 0) ]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_eq. Qed.

Lemma Rule_add : forall n1 n2,
  Triple (val_add n1 n2)
    \[]
    (fun n => \[n = n1 + n2]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_add. Qed.

Lemma Rule_ptr_add : forall (l:loc) (n:int),
  (l:nat) + n >= 0 ->
  Triple (val_ptr_add l n)
    \[]
    (fun l' => \[(l':nat) = abs ((l:nat) + n)]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_ptr_add. Qed.

Lemma Rule_ptr_add_nat : forall (l:loc) (f:nat),
  Triple (val_ptr_add l f)
    \[]
    (fun l' => \[(l':nat) = (l+f)%nat]).
Proof using. intros. unfold Triple, Post. xapplys~ rule_ptr_add_nat. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Specification of primitive operations *)

(* TODO: merge and cleanup and complete *)

Section SpecBasic.

Transparent trm_apps apps. (* TODO: fix *)

Lemma Spec_ref : forall A `{EA:Enc A} (v:A),
  Spec val_ref ``[v]
    \[]
    (fun (l:loc) => l ~~~> v).
Proof using. intros. applys~ @Rule_ref. Qed.

Lemma Spec_get : forall A `{EA:Enc A} (v:A) l,
  Spec val_get ``[l]
    (l ~~~> v)
    (fun (x:A) => \[x = v] \* (l ~~~> v)).
Proof using. intros. applys~ Rule_get. Qed.

Lemma Spec_set : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} l (v:A1) (w:A2),
  Spec val_set ``[l,w]
    (l ~~~> v)
    (fun (_:unit) => l ~~~> w).
Proof using. intros. applys~ Rule_set. Qed.

End SpecBasic.

Arguments Spec_ref : clear implicits.
Arguments Spec_get : clear implicits.
Arguments Spec_set : clear implicits.

Hint Extern 1 (RegisterSpec (val_prim val_ref)) =>
  Provide Spec_ref.
Hint Extern 1 (RegisterSpec (val_prim val_get)) =>
  Provide @Spec_get.
Hint Extern 1 (RegisterSpec (val_prim val_set)) =>
  Provide Spec_set.




(* ---------------------------------------------------------------------- *)
(** Functions of three arguments *)

Definition Spec_fun3 (x1 x2 x3:var) (t1:trm) (F:val) :=
  forall X1 X2 X3, Triple (subst x3 X3 (subst x2 X2 (subst x1 X1 t1))) ===> Triple (F X1 X2 X3).

Lemma Rule_app_fun3 : forall x1 x2 x3 F V1 V2 V3 t1 H A `{EA: Enc A} (Q:A->hprop),
  F = (val_fun3 x1 x2 x3 t1) ->
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  Triple (subst x3 V3 (subst x2 V2 (subst x1 V1 t1))) H Q ->
  Triple (F V1 V2 V3) H Q.
Proof using. introv E N M. unfold Triple. applys* rule_app_fun3. Qed.

Lemma Spec_fun3_val_fun3 : forall x1 x2 x3 t1,
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  Spec_fun3 x1 x2 x3 t1 (val_fun3 x1 x2 x3 t1).
Proof using. introv N M. applys* Rule_app_fun3. Qed.




Lemma Rule_if : forall t0 t1 t2 H (Q1:int->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  (forall X, Triple (If X = 0 then t2 else t1) (Q1 X) Q) ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* rule_if.
  intros v. unfold Post. xpull. intros V. intro_subst.
  specializes M2 V. tests: (V = 0); simpl; case_if~.
Qed.

Lemma Rule_if' : forall t0 t1 t2 H `{EA1:Enc A1} (Q1:A1->hprop) A `{EA:Enc A} (Q:A->hprop),
  Triple t0 H Q1 ->
  (forall X, Triple (If (enc X) = 0 then t2 else t1) (Q1 X) Q) ->
  Triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* rule_if.
  intros v. unfold Post. xpull. intros V. intro_subst. applys~ M2.
Qed.


Lemma rule_if_bool : forall v t1 t2 H Q,
  (v = true -> triple t1 H Q) ->
  (v = false -> triple t2 H Q) ->
  (is_val_bool v) ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M1 M2 C. applys rule_if (fun r => \[r = v] \* H).
  { applys rule_val. hsimpl~. }
  { applys~ rule_extract_hprop. }
  { applys~ rule_extract_hprop. }
  { intros v' N. hpull; false. }
Qed.

Notation "'Register_rule_1' f" := (Register_rule (trm_app (trm_val f) _))
  (at level 69) : charac.
Notation "'Register_rule_2' f" := (Register_rule (trm_app (trm_app (trm_val f) _) _))
  (at level 69) : charac.
Notation "'Register_rule_3' f" := (Register_rule (trm_app (trm_app (trm_app (trm_val f) _) _) _))
  (at level 69) : charac.
Notation "'Register_rule_4' f" := (Register_rule (trm_app (trm_app (trm_app (trm_app (trm_val f) _) _) _) _))
  (at level 69) : charac.


(*
Hint Extern 1 (Register_rule_1 val_not) => Provide rule_not.
*)




(* ---------------------------------------------------------------------- *)
(** Negation *)

Definition val_not :=
  Vars N in
  ValFun N := If_ val_eq N 0 Then 1 Else 0.

Lemma rule_not : forall n,
  triple (val_not n)
    \[]
    (fun r => \[r = val_int (If n = 0 then 1 else 0)]).
Proof using.
  xcf. xapps.
  applys local_erase; splits; xformat.
  { intros C1. do 2 case_if; xval; hsimpl~. }
  { intros C1. do 2 case_if; xval; hsimpl~. }
  { skip. } (*  xif ;=> C1; do 2 case_if; xval; hsimpl~. *)
Qed.

Hint Extern 1 (Register_rule_1 val_not) => Provide rule_not.


(* ---------------------------------------------------------------------- *)
(** Disequality test *)

Definition val_neq :=
  Vars M, N in
  ValFun M N :=  If_ val_eq M N Then 0 Else 1.

Lemma rule_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = val_int (If v1 = v2 then 0 else 1)]).
Proof using.
  xcf. xapps. xif ;=> C; case_if; xvals~.
Qed.

Hint Extern 1 (Register_rule_2 val_neq ?x ?y) => Provide rule_neq.



(*
Lemma trm_funs_fold_next : forall x xs t,
  trm_fun x (trm_funs xs t) = trm_funs (x::xs) t.
Proof using. auto. Qed.

Lemma trm_fixs_fold_start : forall f x xs t,
  trm_fix f x (trm_funs xs t) = trm_fixs f (x::xs) t.
Proof using. auto. Qed.

Lemma val_funs_fold_start : forall x t,
  val_fun x t = val_funs (x::nil) t.
Proof using. auto. Qed.

Lemma val_funs_fold_next : forall xs ys t,
  val_funs xs (trm_funs ys t) = val_funs (List.app xs ys) t.
Proof using. auto. Qed.


*)

(*
Hint Rewrite
  trm_apps_fold_start trm_apps_fold_next trm_apps_fold_concat
  trm_funs_fold_start trm_funs_fold_next
  val_funs_fold_start val_funs_fold_next
  trm_fixs_fold_start val_fixs_fold_start
  trm_funs_fold_app trm_fixs_fold_app: rew_nary.
  (* note: folding of fix should be performed after folding of funs *)
  (* note: folding lemma for apps might not be all needed, depending
           on whether rewriting is outermost-first or not. *)
*)

Global Transparent trm_apps trm_funs trm_fixs val_funs val_fixs.

Global Opaque trm_apps trm_funs trm_fixs val_funs val_fixs.

Ltac xcf_core n :=
  intros;
  first [ applys triple_app_fun3_of_cf_iter n; [ reflexivity | splits; var_neq | simpl ]
        | applys triple_app_fun2_of_cf_iter n; [ reflexivity | var_neq | simpl ]
        | applys triple_app_fun_of_cf_iter n; [ reflexivity | simpl ]
        | applys triple_app_fix_of_cf_iter n; [ reflexivity | simpl ]
        | applys triple_trm_of_cf_iter n; [ simpl ] ].



Sound for seq
{ destruct P as (H1&P1&P2). applys rule_seq H1.
    { applys~ IH. }
    { intros X. applys~ IH. } }

Definition cf_seq (F1 : formula) (F2 : formula) : formula := fun H Q =>
  exists H1,
      F1 H (fun r => \[r = val_unit] \* H1)
   /\ F2 H1 Q.



    Lemma triple_app_fun3_of_cf_iter : forall n F v1 v2 v3 x1 x2 x3 t H Q,
  F = val_fun3 x1 x2 x3 t ->
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  func_iter n cf_def cf (subst x3 v3 (subst x2 v2 (subst x1 v1 t))) H Q ->
  triple (F v1 v2 v3) H Q.
Proof using.
  introv EF N M. applys* rule_app_fun3.
  applys* triple_trm_of_cf_iter.
Qed.


Lemma rule_seq' : forall t1 t2 H Q H1,
  triple t1 H (fun r => \[r = val_unit] \* H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  rew_heap in K1. destruct K1 as (h11'&h12'&N1&N2&N3&N4).
  lets (E&E11'): hpure_inv (rm N1). subst v1.
  lets E11'': hempty_inv (rm E11'). subst h11'.
  rew_fmap. subst h12'. (* TODO: rew_fmap in *)
  forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_seq R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

(* ---------------------------------------------------------------------- *)
(** ALTERNATIVE Folding of n-ary constructors *)

(*

Lemma trm_funs_app : forall xs ys t,
  trm_funs (xs ++ ys) t = trm_funs xs (trm_funs ys t).
Proof using.
  intros. induction xs. { auto. }
  { (* todo: prevent simpl to apply *)
    rew_list. simpl. congruence. }
Qed.

Lemma trm_fixs_app : forall f xs ys t,
  xs <> nil ->
  trm_fixs f (xs ++ ys) t = trm_fixs f xs (trm_funs ys t).
Proof using.
  intros. destruct xs as [|x xs']. { false. }
  { rew_list. simpl. rewrite~ trm_funs_app. }
Qed.



Definition trm_apps' := trm_apps.
Definition trm_funs' := trm_funs.
Definition trm_fixs' := trm_fixs.

Lemma trm_apps'_eq : trm_apps' = trm_apps.
Proof using. auto. Qed.
Lemma trm_funs'_eq : trm_funs' = trm_funs.
Proof using. auto. Qed.
Lemma trm_fixs'_eq : trm_fixs' = trm_fixs.
Proof using. auto. Qed.

Global Opaque trm_apps' trm_funs' trm_fixs'.

Hint Rewrite trm_apps'_eq trm_funs'_eq trm_fixs'_eq : rew_nary.

Tactic Notation "rew_nary" :=
  autorewrite with rew_nary.
(* TODO: see if the original versions could be made opaque directly *)

Definition compact_vals (ts:trms) : trms :=
  let fix go vs ts' :=
    match ts' with
    | nil => vals_to_trms (List.rev vs)
    | (trm_val v)::ts'' => go (v::vs) ts''
    | t::ts'' => ts
    end in
  go nil ts.

Lemma compact_vals_eq : forall ts,
  compact_vals ts = ts.
Proof using.
  intros. unfold compact_vals.
  match goal with |- ?f _ _ = _ => set (go := f) end.
  asserts M: (forall (ts':trms) (vs:vals),
     ts = vals_to_trms (List.rev vs) ++ ts'->
     go vs ts' = ts).
  { intros ts'. induction ts' as [|t ts'']; introv E; subst; simpl.
    { rew_list~. }
    { destruct t; auto. rewrite~ IHts''.
      do 2 rewrite List_rev_eq.
      unfold vals_to_trms. do 2 rewrite List_map_eq.
      rew_list~. } }
  rewrite~ M.
Qed.

Fixpoint compact (t:trm) : trm :=
  let aux := compact in
  match t with
  | trm_val v => t
  | trm_var x => t
  | trm_fun x t1 =>
      let fix go xs tbody :=
        match tbody with
        | trm_fun y tbody' => go (y::xs) tbody'
        | _ => trm_funs' (List.rev xs) (aux tbody)
        end in
      go (x::nil) t1
  | trm_fix f x t1 =>
      let fix go xs tbody :=
        match tbody with
        | trm_fun y tbody' => go (y::xs) tbody'
        | _ => trm_fixs' f (List.rev xs) (aux tbody)
        end in
      go (x::nil) t1
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux t2)
  | trm_app t1 t2 =>
      let fix go tf targs :=
        match tf with
        | trm_app tf1 tf2 => go tf1 ((aux tf2)::targs)
        | _ => trm_apps' (aux tf) (compact_vals targs)
        end in
      go t1 ((aux t2)::nil)
  end.

Lemma compact_eq : forall t,
  compact t = t.
Proof using.
  intros t. induction_wf IH: trm_size t.
  destruct t; simpl; try solve [ repeat rewrite IH; auto ];
   try match goal with |- ?f _ _ = _ => set (go := f) end.
  { renames v to x. asserts M: (forall tbody xs,
      measure trm_size tbody (trm_fun x t) ->
      go xs tbody = trm_funs (List.rev xs) (compact tbody)).
    { intros tbody. induction_wf IH': trm_size tbody. introv N.
      destruct tbody; auto.
      { simpl go. rewrite~ IH'. simpl trm_funs. fold go.
        rewrite~ IH'. rewrite List_app_eq. rewrite~ trm_funs_app. } }
    rewrite~ M. repeat rewrite~ IH. }
  { renames v to f, v0 to x. asserts M: (forall tbody xs,
      xs <> nil ->
      measure trm_size tbody (trm_fix f x t) ->
      go xs tbody = trm_fixs f (List.rev xs) (compact tbody)).
    { intros tbody. induction_wf IH': trm_size tbody. introv L N.
      destruct tbody; auto.
      { simpl go. rewrite~ IH'; auto_false.
        do 2 rewrite List_rev_eq. rew_list.
        rewrite trm_fixs_app. fequals.
        simpl trm_funs. do 2 rewrite~ IH.
        { hint rev_eq_nil_inv. auto_false. (* todo: rev_neq_nil_inv *) } } }
    rewrite~ M. repeat rewrite~ IH. auto_false. }
  { asserts M: (forall tf targs,
      measure trm_size tf (t1 t2) ->
      go tf targs = trm_apps (compact tf) targs).
    { intros tf. induction_wf IH': trm_size tf. introv N.
      destruct tf; try solve [ simpl go; rewrite~ compact_vals_eq ].
      { simpl go. rewrite~ IH'. simpl trm_apps. fold go. rewrite~ IH'. } }
    rewrite~ M. repeat rewrite~ IH. }
Qed.

Definition compact_val (v:val) : val :=
  match v with
  | val_fun x t => val_fun x (compact t)
  | val_fix f x t => val_fix f x (compact t)
  | _ => v
  end.

Lemma compact_val_eq : forall v,
  compact_val v = v.
Proof using.
  intros. destruct v; simpl; auto; try rewrite~ compact_eq.
Qed.

  (* TODO : cleanup *)

  (* TODO: why rejected?
  Fixpoint compact (t:trm) {struct t} : trm :=
    let aux := compact in
    match t with
    | trm_val v => t
    | trm_var x => t
    | trm_fun x t1 => compact_fun (x::nil) t1
    | trm_fix f x t1 => trm_fix f x (aux t1)
    | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
    | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
    | trm_let x t1 t2 => trm_let x (aux t1) (aux t2)
    | trm_app t1 t2 =>
        let fix go tf targs :=
          match tf with
          | trm_app tf1 tf2 => go tf1 ((aux tf2)::targs)
          | _ => trm_apps (aux tf) targs
          end in
        go t1 ((aux t2)::nil)
    end

  with compact_fun xs tbody { struct tbody } :=
    match tbody with
    | trm_fun y tbody' => compact_fun (y::xs) tbody'
    | _ => trm_funs (List.rev xs) (compact tbody)
    end.
  *)



(* DEMO
  Lemma rule_neq_3 : forall v1 v2,
    triple (val_neq v1 v2)
      \[]
      (fun r => \[r = val_int (If v1 = v2 then 0 else 1)]).
  Proof using.
    intros.
    match goal with |- triple ?t _ _ => rewrite <- (@compact_eq t) end; simpl.
    rew_nary.
    applys triple_apps_funs_of_cf_iter 20%nat.
    unfold val_neq.
    match goal with |- ?v = _ => rewrite <- (@compact_val_eq v) end; simpl.
     rew_nary. reflexivity.
    auto.
    simpl.
  Abort.
*)

*)


Definition apps (v1:val) (v2s:vals) : trm :=
  trm_apps (trm_val v1) (vals_to_trms v2s).

Global Opaque apps.

Lemma trm_apps_val_compact : forall (v1:val) (v2s:vals),
    trm_apps (trm_val v1) (vals_to_trms v2s)
  = apps v1 v2s.
Proof using. auto. Qed.

Lemma trm_apps_val_compact' : forall (v1:val) (v2s:vals) (v3:val),
  trm_app (apps v1 v2s) v3 = apps v1 (List.app v2s (v3::nil)).
Proof using. skip. Qed. (* todo *)

Lemma trm_apps_val_compact'' : forall (v1:val) (v2s:vals) (v3s:vals),
  trm_apps (apps v1 v2s) v3s = apps v1 (List.app v2s v3s).
Proof using. skip. Qed. (* todo *)

Hint Rewrite trm_apps_val_compact trm_apps_val_compact' trm_apps_val_compact'' : rew_nary.

Global Opaque trm_apps trm_funs trm_fixs val_funs val_fixs.




Lemma trm_apps_fold_start : forall t1 v2,
  trm_app t1 (trm_val v2) = trm_apps t1 (vals_to_trms (v2::nil)).
Proof using. auto. Qed.

Lemma trm_apps_fold_next : forall t1 v1 v2s,
    trm_apps (trm_apps t1 (vals_to_trms (v1::nil))) (vals_to_trms v2s)
  = trm_apps t1 (vals_to_trms (v1::v2s)).
Proof using. auto. Qed.



Notation "'trm_app2_val' vf v1 v2" := (trm_app (trm_app (trm_val vf) (trm_val v1)) (trm_val v2))
  (at level 69, vf at level 0, v1 at level 0, v2 at level 0, only parsing).

Notation "'trm_app_val' vf v1" := (trm_app (trm_val vf) (trm_val v1))
  (at level 69, vf at level 0, v1 at level 0, only parsing).

Notation "'trm_app2' tf t1 t2" := (trm_app (trm_app tf t1) t2)
  (at level 69, tf at level 0, t1 at level 0, t2 at level 0, only parsing).
Notation "'trm_fun2' x1 x2 t" := (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 ident, x2 ident, only parsing).


(* ---------------------------------------------------------------------- *)
(** Functions of three arguments *)

Notation "'trm_app3' tf t1 t2 t3" := (trm_app (trm_app (trm_app tf t1) t2) t3)
  (at level 69, tf at level 0, t1 at level 0, t2 at level 0, only parsing).

Notation "'trm_app3_val' vf v1 v2 v3" := (trm_app (trm_app (trm_app (trm_val vf) (trm_val v1)) (trm_val v2)) (trm_val v3))
  (at level 69, vf at level 0, v1 at level 0, v2 at level 0, v3 at level 0, only parsing).

Notation "'trm_fun3' x1 x2 x3 t" := (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 ident, x2 ident, x3 ident, only parsing).

Notation "'val_fun3' x1 x2 x3 t" := (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 ident, x2 ident, x3 ident, only parsing).

Lemma red_app_fun3 : forall m1 m2 vf v1 v2 v3 x1 x2 x3 t r,
  vf = val_fun3 x1 x2 x3 t ->
  red m1 (subst x3 v3 (subst x2 v2 (subst x1 v1 t))) m2 r ->
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  red m1 (vf v1 v2 v3) m2 r.
Proof using.
  introv E M (N1&N2&N3). subst. do 2 applys~ red_app.
  { applys~ red_app_fun. simpl. case_if. case_if. applys red_fun. }
  { applys~ red_app_fun. simpl. case_if. applys red_fun. }
  { applys~ red_app_fun. }
Qed.

Definition spec_fun3 (x1 x2 x3:var) (t1:trm) (F:val) :=
  forall X1 X2 X3, triple (subst x3 X3 (subst x2 X2 (subst x1 X1 t1)))
    ===> triple (F X1 X2 X3).

Lemma rule_app_fun3 : forall x1 x2 x3 F V1 V2 V3 t1 H Q,
  F = (val_fun3 x1 x2 x3 t1) ->
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  triple (subst x3 V3 (subst x2 V2 (subst x1 V1 t1))) H Q ->
  triple (F V1 V2 V3) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys* red_app_fun3. }
Qed.

Lemma spec_fun3_val_fun3 : forall x1 x2 x3 t1,
  x1 <> x2 /\ x2 <> x3 /\ x1 <> x3 ->
  spec_fun3 x1 x2 x3 t1 (val_fun3 x1 x2 x3 t1).
Proof using. introv N M. applys* rule_app_fun3. Qed.



(*
Definition is_val_bool (v:val) : Prop :=
  match v with
  | val_bool _ => True
  | _ => False
  end.
*)


Definition cf_if_val v (F1 F2 : formula) : formula := fun H Q =>
     (v <> val_int 0 -> F1 H Q)
  /\ (v = val_int 0 -> F2 H Q).


Cf sound:
  { destruct P as (Q1&P1&P2). applys rule_if.
    { applys* IH. }
    { intros X. specializes P2 X.
      applys sound_for_local (rm P2). intros H' Q' P'.
      destruct P' as (P1'&P2'). case_if; applys* IH. } }


Lemma rule_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (v:val), triple (If v = val_int 0 then t2 else t1) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  forwards* (h'&v'&R&K): ((rm M2) v) h1'.
  exists h' v'. splits~.
  { applys* red_if. }
  { rewrite <- htop_hstar_htop. rew_heap~. }
Qed.

Lemma rule_if' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (v:val),
      (v <> val_int 0 -> triple t1 (Q1 v) Q)
   /\ (v = val_int 0 -> triple t2 (Q1 v) Q)) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_if (rm M1).
  intros v. forwards* (M3&M4): (rm M2) v. case_if*.
Qed.



(* Sound CF app
  { match type of P with (let _ := ?F in _) _ _ _ _ => set (go := F) in * end.
    asserts G: (forall (tf:trm) (vs:vals), Sound_for (trm_apps tf vs) (go tf vs)).
    { clears t1 t2 H Q A. intros tf. induction_wf IH': trm_size tf.
      intros vs A EA H Q M. destruct tf; simpls; tryfalse.
      { destruct M as (Vs&E&M). subst~. }
      { destruct tf2; tryfalse. forwards~: IH' M. } }
    applys G P. }
*)



(* ---------------------------------------------------------------------- *)
(* ** Lemmas about encoders *)

Lemma enc_fun : forall x t1,
  enc (val_fun x t1) = (val_fun x t1).
Proof using. auto. Qed.




(* DEPRECATED
Notation "``[ x1 ]" :=
  ((Dyn x1)::nil)
  (at level 0, format "``[ x1 ]")
  : dyns.
Notation "```[ x1 , x2 ]" :=
  ((Dyn x1)::(Dyn x2)::nil)
  (at level 0, format "``[ x1 ,  x2 ]")
  : dyns.
Notation "```[ x1 , x2 , x3 ]" :=
  ((Dyn x1)::(Dyn x2)::(Dyn x3)::nil)
  (at level 0, format "``[ x1 ,  x2  , x3 ]")
  : dyns.
Notation "```[ x1 , x2 , x3 , x4 ]" :=
  ((Dyn x1)::(Dyn x2)::(Dyn x3)::(Dyn x4)::nil)
  (at level 0, format "``[ x1 ,  x2  , x3  , x4 ]")
  : dyns.
*)

(** Notation for list of dyns, and association list of dyns *)

(* annotated

  Notation "``[ ]" := ((@nil dyn) : dyns) (format "``[ ]") : dyns_scope.

  Notation "``[ x ]" := ((cons (Dyn x) nil) : dyns) : dyns_scope.

  Notation "``[ x1 , x2 ]" :=
    (((Dyn x1)::(Dyn x2)::nil) : dyns)
    (at level 0, format "``[ x1 ,  x2 ]")
    : dyns_scope.
  Notation "``[ x1 , x2 , x3 ]" :=
    (((Dyn x1)::(Dyn x2)::(Dyn x3)::nil) : dyns)
    (at level 0, format "``[ x1 ,  x2  , x3 ]")
    : dyns_scope.
  Notation "``[ x1 , x2 , x3 , x4 ]" :=
    (((Dyn x1)::(Dyn x2)::(Dyn x3)::(Dyn x4)::nil) : dyns)
    (at level 0, format "``[ x1 ,  x2  , x3  , x4 ]")
    : dyns_scope.
*)



  (* xspec ;=> H. *)
  (* xapps Spec_eq_int. *)
  (* xapp_basic_prepare tt. xapplys Spec_eq_int. *)

  (*

    xspec ;=> G; xapp_basic_prepare tt. xapply G.

  forwards_nounfold_then G ltac:(fun K =>
   eapply local_frame; [ xlocal | eapply K | hcancel |  try apply refl_rel_incl' ]).
  (* Problematic backtracking going on *)


  (* TODO: why slow?*)
  forwards_nounfold_then G ltac:(fun K => instantiate;
   eapply local_frame; [ xlocal | sapply K | hcancel | try apply refl_rel_incl' ]).

  forwards_nounfold_then G ltac:(fun K => pose (X:=K)).
   eapply local_frame; [ xlocal | sapply X | hcancel | try apply refl_rel_incl' ].


unfolds Spec, Apps. apply s.
  match xpostcondition_is_evar tt with ?X => pose X end.

 xapply G.
  forwards_nounfold_then H ltac:(fun K =>
    match xpostcondition_is_evar tt with
    | true => eapply local_frame; [ xlocal | sapply K | cont1 tt | try apply refl_rel_incl' ]
    | false => eapply local_frame_htop; [ xlocal | sapply K | cont1 tt | cont2 tt ]
    end).


*)
(* DETAILS:
Hint Extern 1 (RegisterSpec (Triple (trm_apps (trm_val (val_prim val_eq)) ?xs) _ _)) =>
  Provide Spec_eq_int.
*)




(*
Lemma Triple_apps_funs_of_Cf_iter : forall n F (Vs:dyns) (vs:vals) xs t A `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  vs = encs Vs ->
  var_funs_exec (length Vs) xs ->
  func_iter n Cf_def Cf (Substs xs Vs t) A EA H Q ->
  Triple (trm_apps F vs) H Q.
Proof using.
  introv EF EV N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  subst. applys* Rule_apps_funs. applys* Triple_trm_of_Cf_iter.
Qed.
*)


(*
  Coercion dyns_to_vals (ds : dyns) : vals :=
    List.map dyn_to_val ds.
  *)

  (*
  Notation "'`App`' f vs" :=
    ((`App f vs) _ _)
    (at level 12, f at level 0, vs at level 40) : charac.

  Open Scope dyns_scope.
*)
(* App:
  Ltac xapp_basic_prepare tt ::=
    try match goal with |- @Local _ _ _ _ _ => apply local_erase end;
    esplit; split; [ try xeq_encs | simpl decodes ].
    (* match goal with |- exists _, ?L = _ /\ _ => *)
*)

(*
Lemma Spec_eq_int : forall (v1 v2 : int),
  Spec val_eq ``[v1, v2]
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2 :> int)]).
Proof using.
  intros. applys Triple_enc_change. { sapply Rule_eq. }
  simpl. intros X. hpull ;=> E. subst. hsimpl*.
  rew_dyn. rewrite Enc_bool_eq. unfold bool_to_val.
  do 2 case_if; auto.
  (* todo: hpull should allow head quantif to be remaining *)
Qed.
*)

(* paragraphase of definition
Lemma enc_dyn_def : forall (d:dyn),
  enc d = dyn_val d.
Proof using. auto. Qed.
*)


(*
Notation "'`Let' x ':=' F1 'in' F2" :=
  (Local (Cf_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.
*)


(*
Notation "'DynVal' V" := (dyn_to_val (Dyn V)) (at level 68).
*)

(*
Notation "'Apps' f Vs" :=
  (trm_apps f (vals_to_trms (encs Vs)))
  (at level 8, f at level 0). (* TODO all from LambdaSemantics in : trm_scope. *)
*)

(*
Notation "'`Apps' f Vs " :=
  (`App (Apps f Vs) _ _)
  (at level 8, f at level 0) : charac.
*)

(*
Notation "'Spec' f Vs " :=
  (Triple (Apps f Vs))
  (at level 8, f at level 0) : charac.
*)




(*
Notation "'Apps' f [ x1 ]" :=
  (Triple (trm_apps f (vals_to_trms '[DynVal x1])) _ _)
  (at level 8, f at level 0, x1 at level 0) : charac.

Notation "'Apps' f [ x1 , x2 ]" :=
  (Triple (trm_apps f (vals_to_trms '[DynVal x1, DynVal x2])))
  (at level 8, f at level 0, x1 at level 0,
   x2 at level 0) : charac.

Notation "'Apps' f [ x1 , x2 , x3 ]" :=
  (Triple (trm_apps f (vals_to_trms '[DynVal x1, DynVal x2, DynVal x3])))
  (at level 8, f at level 0, x1 at level 0, x2 at level 0,
   x3 at level 0) : charac.

Notation "'Apps' f [ x1 , x2 , x3 , x4 ]" :=
  (Triple (trm_apps f (vals_to_trms '[DynVal x1, DynVal x2, DynVal x3, DynVal x4])))
  (at level 8, f at level 0, x1 at level 0, x2 at level 0,
   x3 at level 0, x4 at level 0) : charac.
*)

Definition bool_to_int (b:bool) : int :=
  match b with
  | true => 1
  | false => 0
  end.

Definition bool_to_val (b:bool) : val :=
  match b with
  | true => val_int 1
  | false => val_int 0
  end.

Instance Enc_bool : Enc bool.
Proof using. constructor. applys bool_to_val. Defined.

Lemma Cf_if_val_bool : forall (b:bool) (F1 F2 : formula) H A (EA:Enc A) (Q:A->hprop),
  (b -> 'F1 H Q) ->
  (~ b -> 'F2 H Q) ->
  '(Cf_if_val (enc b) F1 F2) H Q.
Proof using.
  introv M1 M2. exists (bool_to_int b). splits; destruct b; auto_false.
Qed.

Lemma Cf_if_val_isTrue : forall (P:Prop) (F1 F2 : formula) H A (EA:Enc A) (Q:A->hprop),
  (P -> 'F1 H Q) ->
  (~ P -> 'F2 H Q) ->
  '(Cf_if_val (enc (isTrue P)) F1 F2) H Q.
Proof using.
  introv M1 M2. applys Cf_if_val_bool; intros; rew_istrue in *; auto.
Qed.



(*--------------------------------------------------------*)
(* ** Tactic [xlocal] extended *)

  (*
  Ltac xlocal_core tt ::=
    try first [ applys is_local_Local
              | applys is_local_local
              | applys is_local_triple
              | assumption ].
  *)
  (* | applys App_is_local *)


(*
Tactic Notation "xval" :=
  applys local_erase; unfold Cf_val;
  try (
    match goal with |- exists _, ?v = _ /\ _ => exists (dyn_value (decode v)) end;
    simpl enc; simpl dyn_value; split; [ reflexivity | ]).

Tactic Notation "xif" :=
  applys local_erase; unfold Cf_if;
  try esplit; split; [ reflexivity | split ].

Tactic Notation "xlet" :=
  applys local_erase; eapply @Cf_let_intro.
  (* TODO: why does not work?
  applys local_erase;
  let A := fresh "A" in let EA := fresh "E" A in
  evar (A:Type); evar (EA:Enc A); exists A EA; subst A EA;
  esplit; split. *)

Lemma red_if_val : forall m1 m2 v r t1 t2,
  red m1 (If v = val_int 0 then t2 else t1) m2 r ->
  red m1 (trm_if v t1 t2) m2 r.
Proof using. introv M1. applys~ red_if. Qed.


Ltac xapp_setup tt :=
  applys local_erase; unfold Cf_app;
  match goal with |- exists _, ?L = _ /\ _ => exists (decodes L) end;
  simpl decodes; split; [ reflexivity | ].

Tactic Notation "xapp" constr(E) :=
  xapp_setup tt; xapplys E.

Tactic Notation "xapp" :=
  xapp_setup tt;
  let G := match goal with |- ?G => constr:(G) end in
  xspec G;
  let H := fresh "TEMP" in intros H;
  xapplys H;
  clear H.

*)

(* ---------------------------------------------------------------------- *)
(* ** Tactic for induction on size *)

Hint Extern 1 (measure trm_size _ _) =>
  hnf; simpl; repeat rewrite trm_size_subst; math.


Ltac solve_measure_trm_size tt ::=
  unfold measure in *; simpls; repeat rewrite trm_size_Subst; math.



(*
Hint Extern 1 (measure trm_size _ _) =>
  hnf; simpl; repeat rewrite trm_size_subst; math.
*)

(*
Hint Extern 1 (measure trm_size _ _) =>
  hnf; simpl; repeat rewrite trm_size_Subst; math.

*)

(* DEPRECATEd
Lemma PostEnc_himpl : forall `{Enc A} Q Q',
  Q ===> Q' ->
  Post Q ===> Post Q'.
Proof using.
  introv M. unfold Post. intros v. hpull. intros x E.
  subst v. hsimpl*.
Qed.

Hint Resolve PostEnc_himpl.

*)

(* Cf_def
  | trm_app t1 t2 => Local (
      let fix go tf vs :=
        match tf with
        | trm_app tf1 tf2 =>
          match tf2 with
          | trm_val v => go tf1 (v::vs)
          | _ => Cf_fail (* snd argument of a call must be a value *)
          end
        | trm_val f => Cf_app f vs
        | _ => Cf_fail (* fst argument of a call must be an application or a value *)
        end in
      go t nil)
*)

(* PROBLEM: too early typeclass resolution *)
Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:id Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  @Triple t A1 EA1 H Q1 ->
  (forall (X:A1), Q1 X ==> Hexists (Y:A2), \[@enc A1 EA1 X = enc Y] \* Q2 Y) ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ rule_consequence (rm M).
  unfold Post. intros v. hpull ;=> V EV. subst. applys N.
Qed.



(*
Definition Cf_app (f:val) (vs:vals) : formula :=
  fun `{Enc A} H (Q:A->hprop) =>
    exists Vs, vs = encs Vs /\ App f Vs H Q.
*)



(* TODO

Notation "'RegisterSpecApps' t" := (RegisterSpec (triple t _ _))
  (at level 69) : charac.
*)

(*
Notation "'RegisterSpecApps' f" :=
  (RegisterSpec (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : charac.
*)


Notation "'`Apps' f vs " :=
  (`App (trm_apps f vs))
  (at level 68, f at level 0) : charac.
(*
Definition Apps (f:val) (Vs:dyns) :=
  trm_apps f (vals_to_trms (encs Vs)).
*)




  (*
  (* ---------------------------------------------------------------------- *)
  (* ** The [App] predicate for n-ary applications *)

  Definition App (f:func) (Vs:dyns) `{Enc A} H (Q:A->hprop) :=
    Triple (trm_apps f (encs Vs)) H Q.

  Lemma App_is_local : forall (f:func) (Vs:dyns) A `{EA:Enc A},
    is_local (@App f Vs A EA).
  Proof using. intros. unfold App. applys is_local_Triple. Qed.


  (* ---------------------------------------------------------------------- *)
  (* ** Specification of primitive operations *)

  Lemma Spec_ref : forall A `{EA:Enc A} (v:A),
    App val_ref ``[v] \[] (fun (l:loc) => l ~~~> v).
  Proof using. intros. applys~ Rule_ref. Qed.

  Lemma app_get : forall A `{EA:Enc A} (v:A) l,
    App val_get ``[l] (l ~~~> v) (fun (x:A) => \[x = v] \* (l ~~~> v)).
  Proof using. intros. applys~ Rule_get. Qed.

  Lemma app_set : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} l (v:A1) (w:A2),
    App val_set ``[l,w] (l ~~~> v) (fun (_:unit) => l ~~~> w).
  Proof using. intros. applys~ Rule_set. Qed.
  *)


(*
Lemma Spec_get' : forall A `{EA:id Enc A} (v:A) l,
  @Spec val_get ``[l]  A EA
    (@Hsingle A EA l v)
    (fun (x:A) => \[x = v] \* (@Hsingle A EA l v)).
Proof using. intros. applys~ Spec_get. Qed.
*)


(*

Inductive forced_decode : forall A `{EA:Enc A}, val -> (A -> Prop) -> Prop :=
  | forced_decode_intro : forall (v:val),
      let d := decode v in
      forall (K : dyn_type d -> Prop),
      K (dyn_value d) ->
      @forced_decode _ (dyn_enc d) v K.

Implicit Arguments forced_decode [A [EA]].

Definition Cf_if_val v (F1 F2 : formula) : formula := fun `{EA:Enc A} H (Q:A->hprop) =>
  forced_decode v (fun (V:int) =>
    (V <> 0 -> 'F1 H Q) /\ (V = 0 -> 'F2 H Q)).


Definition Cf_val v : formula := fun `{Enc A} H (Q:A->hprop) =>
  forced_decode v (fun (V:A) => H ==> Q V).

Inductive Cf_val'' v : formula :=
  | Cf_val_intro :
     let d := decode v in
     forall H (Q:(dyn_type d)->hprop),
     @Cf_val' v _ (dyn_enc d) H (fun x => \[x = dyn_value d] \* H).


Definition Cf_app f vs : formula := fun `{Enc A} H (Q:A->hprop) =>
  app f (decodes vs) H Q.

Ltac save_K K :=
  match goal with H: forced_decode ?v ?Kbody |- _ =>
    sets_eq K: (Kbody) end.

Ltac inverts_forced P :=
  let K := fresh "K" in hnf in P; save_K K; destruct P;
  instantiate; subst K.


*)




(* ---------------------------------------------------------------------- *)
(** Substitution that preserves n-ary constructors *)

(* LATER: generalize to funs and fixs *)

Fixpoint subst' (y:var) (w:val) (t:trm) : trm :=
  let aux := subst' y w in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if eq_var_dec x y then trm_val w else t
  | trm_fun x t1 => trm_fun x (if eq_var_dec x y then t1 else aux t1)
  | trm_fix f x t1 => trm_fix f x (if eq_var_dec x y then t1 else
                                   if eq_var_dec f y then t1 else aux t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if eq_var_dec x y then t2 else aux t2)
  | trm_app t1 t2 =>
      let go := (fix go tf targs :=
        match tf with
        | trm_app tf1 tf2 => go tf1 ((aux tf2)::targs)
        | _ => trm_apps (aux tf) targs
        end) in
      go t1 ((aux t2)::nil)
  end.

Lemma subst_eq_subst' : subst = subst'.
Proof using.
  extens. intros y w t. induction_wf IH: trm_size t.
  destruct t; simpl; try solve [ repeat rewrite IH; auto ].
  { match goal with |- _ _ = ?f _ _ => set (go := f) end.
    asserts M: (forall tf targs',
      measure trm_size tf (t1 t2) ->
      go tf targs' = trm_apps (subst' y w tf) targs').
    { intros tf. induction_wf IH': trm_size tf. introv N.
      destruct tf; auto.
      { simpl go. rewrite~ IH'. simpl trm_apps. fold go. rewrite~ IH'. } }
    repeat rewrite~ IH. rewrite~ M. }
Qed.

(* LATER: simplify to [t = compact t] where compact reintroduces nary constructs *)



(* not used
Lemma red_funcs : forall m fopt xs t,
  red m (trm_funcs fopt xs t) m (val_funcs fopt xs t).
Proof using.
Qed.
*)

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substs xs vs t) m2 r ->
  var_distinct xs ->
  length xs = length vs ->
  xs <> nil ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  hint red_val. introv E M N L P.
  sets tf: (trm_val vf).
  asserts R: (red m1 tf m1 (val_funs xs t)).
  { subst tf vf. apply~ red_val. }
  clear E. gen vs t tf. induction xs as [|x xs']; intros.
  { false. } clear P.
  { destruct vs as [|v vs']; rew_list in *. { false; math. }
    simpls. tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys~ red_app R. applys~ red_fun. }
    { rew_istrue in N. destruct N as [F N']. applys~ IHxs' M.
      applys~ red_app R. applys~ red_fun.
      rewrite~ subst_trm_funs. applys~ red_funs. } }
Qed.

Lemma red_app_funs_val_ind : forall xs vs m1 m2 tf t r,
  red m1 tf m1 (val_funs xs t) ->
  red m1 (substs xs vs t) m2 r ->
  var_distinct xs ->
  length xs = length vs ->
  xs <> nil ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  hint red_val.
  intros xs. induction xs as [|x xs']; introv R M N L P.
  { false. } clear P.
  { destruct vs as [|v vs']; rew_list in *. { false; math. }
    simpls. tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys~ red_app R. applys~ red_fun. }
    { rew_istrue in N. destruct N as [F N']. applys~ IHxs' M.
      applys~ red_app R. applys~ red_fun.
      rewrite~ subst_trm_funs. applys~ red_funs. } }
Qed.

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = trm_funs xs t ->
  red m1 (substs xs vs t) m2 r ->
  var_distinct xs ->
  length xs = length vs ->
  xs <> nil ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv R M N L P. applys* red_app_funs_val_ind.
  { subst. apply~ red_funs. }
Qed.
(* LATER: induction by generalization *)


 (* DEPRECATED
  | red_app_func : forall m1 m2 m3 m4 t1 t2 t3 t4 v1 v2 fopt x t r,
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      v1 = val_func fopt x t ->
      t3 = subst x v2 t ->
      t4 = match fopt with
           | Rec f => subst f v1 t3
           | Norec => t3
           end ->
      red m3 t4 m4 r ->
      red m1 (trm_app t1 t2) m4 r
  *)

(* DEPRECATED
Lemma red_app_fun_val : forall m1 m2 v1 v2 x t r,
  v1 = val_fun x t ->
  red m1 (subst x v2 t) m2 r ->
  red m1 (trm_app v1 v2) m2 r.
Proof using. introv E M. subst. applys* red_app_func. Qed.
*)

Lemma red_app_fix_val : forall m1 m2 v1 v2 f x t r,
  v1 = val_fix f x t ->
  red m1 (subst f v1 (subst x v2 t)) m2 r ->
  red m1 (trm_app v1 v2) m2 r.
Proof using. introv E M. subst. applys* red_app_func. Qed.


(* TODO: split red_app_func in two rules?
  [red_app] and [red_app_fun_val] *)

Lemma red_app : forall m1 m2 m3 m4 t1 t2 (v1 v2:val) r,
  red m1 t1 m2 v1 ->
  red m2 t2 m3 v2 ->
  red m3 (trm_app v1 v2) m4 r ->
  red m1 (trm_app t1 t2) m4 r.
Proof using.
  introv M1 M2 M3. inverts M3 as.
  { introv N1 N2. inverts N1. inverts N2. applys* red_app_func. }
  { introv N1 N2. inverts N1. inverts N2. applys red_ref.
Qed.


Lemma red_app_val : forall m1 m2 m3 t1 v1 (v2:val) r,
  red m1 t1 m2 v1 ->
  red m2 (trm_app v1 v2) m3 r ->
  red m1 (trm_app t1 v2) m3 r.
Proof using.
  hint red_val. introv M1 M2. applys* red_app.
Qed.


Definition is_val (t:trm) : Prop :=
  match t with
  | trm_val v => True
  | _ => False
  end.

Lemma red_app_steps_l : forall m1 m2 m3 t1 t2 t1' r,
  (forall v1 m', red m2 t1' m' v1 -> red m1 t1 m' v1) ->
  ~ is_val t1 ->
  red m2 (trm_app t1' t2) m3 r ->
  red m1 (trm_app t1 t2) m3 r.
Proof using.
  introv M' N M. inverts M as M1 M2 M3.
skip. skip. skip.
  lets: M' M1. inverts H.
  applys red_app. applys M'.
  applys

 inverts M; simpls; auto_false. skip. skip. auto_false. applys red_app.
Qed.

Lemma red_apps_trm_vals : forall xs vs m1 m2 tf t r,
  tf = trm_funs xs t ->
  red m1 (substs xs vs t) m2 r ->
  var_distinct xs ->
  length xs = length vs ->
  xs <> nil ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  intros vs. induction vs as [|v vs']; introv E M N L P; simpls.
  { false. }
destruct
  { inverts~ M2. }
  { applys IHvs'.
    { applys red_app. applys red_val. applys
Qed.



Lemma red_apps_val : forall (vs:vals) m1 m2 m3 t vf r,
  red m1 t m2 vf ->
  red m2 (trm_apps vf vs) m3 r ->
  red m1 (trm_apps t vs) m3 r.
Proof using.
  intros vs. induction vs as [|v vs']; introv M1 M2; simpls.
  { inverts~ M2. }
  { applys IHvs'.
    { applys red_app. applys red_val. applys
Qed.




Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substs xs vs t) m2 r ->
  var_distinct xs ->
  length xs = length vs ->
  xs <> nil ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv E M N L P.
  destruct vs as [|v vs']. { rew_list in *. false* length_zero_inv L. }
  destruct xs as [|x xs']. { false. }
  simpls. rew_list in L.
  { simpl. lets:  red_app_func.


  intros xs. induction xs;  { false. }
  subst. unfold val_funs.



  applys~ red_app_func.
  { applys* red_app_func. simpl. applys* red_func. }
  { simpl. case_if~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** State produced by [alloc] *)

Fixpoint nat_fold A (f:nat->A->A) (k:nat) (z:A) : A :=
  match k with
  | O => z
  | S k' => f k' (nat_fold f k' z)
  end.

Definition alloc_state (l:loc) (k:nat) :=
  nat_fold (fun i m => (fmap_single (l+i)%nat val_unit) \+ m) k fmap_empty.


(* ---------------------------------------------------------------------- *)


Lemma Rule_app : forall f xs F (Vs:dyns) t1 H A `{EA:Enc A} (Q:A->hprop) E,
  F = (val_fix f xs t1) ->
  List.length Vs = List.length xs ->
  (*
  E = List.combine (f::xs) ((Dyn F)::Vs) ->
  Triple (Subst_trm E t1) H Q ->
  *)
  E = List.combine (f :: xs) (Dyn F :: Vs) ->
  Triple (Subst_trm E t1) H Q ->
  Triple (trm_app F (encs Vs)) H Q.
Proof using.
  introv EF EL EE M. applys* rule_app.
  { rewrite~ encs_length. }
  { unfolds Subst_trm. subst E. rewrite~ <- Subst_to_subst_combine in M.
    (* todo: clean up script *) { simpl. fequals. } }
Qed.

Lemma Rule_app' : forall f xs F (Vs:dyns) t1 H A `{EA:Enc A} (Q:A->hprop) E,
  F = (val_fix f xs t1) ->
  List.length Vs = List.length xs ->
  (*
  E = List.combine (f::xs) ((Dyn F)::Vs) ->
  Triple (Subst_trm E t1) H Q ->
  *)
  E = List.combine (f :: xs) (F :: encs Vs) ->
  Triple (subst_trm E t1) H Q ->
  Triple (trm_app F (encs Vs)) H Q.
Proof using.
  introv EF EL EE M. applys* rule_app.
  { rewrite~ encs_length. }
Qed.

Lemma Rule_let_fix : forall f xs t1 t2 H A `{EA:Enc A} (Q:A->hprop),
  (forall (F:val),
    (forall A' `{EA:Enc A'} H' (Q':A'->hprop) (Xs:dyns) E,
      List.length Xs = List.length xs ->
      E = List.combine (f::xs) (Dyn F::Xs) ->
      Triple (Subst_trm E t1) H' Q' ->
      Triple (trm_app F (encs Xs)) H' Q') ->
    Triple (Subst_trm [(f,Dyn F)] t2) H Q) ->
  Triple (trm_let f (trm_val (val_fix f xs t1)) t2) H Q.
Proof using.
  introv M. applys (@Rule_let_val_enc _ _ (val_fix f xs t1)).
  { symmetry. applys* enc_val_fix_eq. }
  intros F EF. applys (rm M). clears H Q.
  intros A2 EA2 H Q Xs E EL EE M. subst E. applys~ Rule_app EF.
Qed.

(*
Lemma Rule_let_fix' : forall f xs t1 t2 H A `{EA:Enc A} (Q:A->hprop),
  (forall (F:val),
    (forall (Xs:dyns) H' Q' E,
      List.length Xs = List.length xs ->
      E = List.combine (f::xs) (F::(encs Xs)) ->
      Triple (subst_trm E t1) H' Q' ->
      Triple (trm_app F (encs Xs)) H' Q') ->
    Triple (subst_trm [(f,F)] t2) H Q) ->
  Triple (trm_let f (trm_val (val_fix f xs t1)) t2) H Q.
Proof using.
  introv M. applys (@Rule_let_val_enc _ _ (val_fix f xs t1)).
  { symmetry. applys* enc_val_fix_eq. }
  intros F EF. applys (rm M). clears H Q.
  intros A2 EA2 Q Xs EL EE M.
  applys~ Rule_app EF.
  { subst Xs. applys* M. }
Qed.
*)

*)


(* TEMPORARY

Lemma enc_func : forall F fopt x t1,
  F = val_func fopt x t1 ->
  enc F = F.
Proof using. intros. subst~. Qed.

Lemma enc_fun : forall F x t1,
  F = val_fun x t1 ->
  enc F = F.
Proof using. intros. applys enc_func. Qed.

Lemma enc_fix : forall F f x t1,
  F = val_fix f x t1 ->
  enc F = F.
Proof using. intros. applys enc_func. Qed.

Lemma enc_fun' : forall x t1,
  enc (val_fun x t1) = (val_fun x t1).
Proof using. auto. Qed.

Lemma enc_fix' : forall F f x t1,
  F = val_fix f x t1 ->
  enc F = F.
Proof using. intros. applys enc_func. Qed.

*)


(*

Definition link R x y R' :=
  exists z, (z = R x \/ z = R y)
         /\ (forall i, R' i = (If (R i = R x \/ R i = R y) then z else R i)).

Lemma link_related : forall R x y R',
  link R x y R' ->
  R x = R y ->
  R' = R.
Proof using.
  introv (z&D&M) E. extens ;=> i. rewrites (rm M). case_if as C.
  { rewrite E in C. destruct D; destruct C; congruence. }
  { auto. }
Qed.

Lemma is_repr_equiv_root : forall M x r,
  is_repr M x r -> is_equiv M x r.
Proof. introv H. forwards: is_repr_binds_root H. exists* r. Qed.

Lemma is_equiv_iff_same_repr : forall M x y rx ry,
  is_repr M x rx -> is_repr M y ry ->
  ((rx = ry) = is_equiv M x y).
Proof.
  introv Rx Ry. extens. iff H (r&Rx'&Ry'). subst*.
  applys (eq_trans r); applys is_repr_inj; eauto.
Qed.

Lemma is_equiv_refl : forall M x,
  x \indom M -> is_forest M -> is_equiv M x x.
Proof. introv D H. forwards* [r R]: (H x). Qed.

Lemma is_equiv_sym : forall M,
  sym (is_equiv M).
Proof. intros M x y (r&Hx&Hy). eauto. Qed.

Lemma is_equiv_trans : forall M,
  trans (is_equiv M).
Proof.
  intros M y x z (r1&Hx&Hy) (r2&Hy'&Hz).
  forwards: is_repr_inj r1 r2; eauto. subst*.
Qed.

(** Lemmas for 'create' function *)

Lemma is_forest_add_node : forall M r,
  is_forest M -> r \notindom M -> is_forest (M\(r:=Root)).
Proof.
  introv FM Dr. intros x Dx. destruct (map_indom_update_inv Dx).
    subst*.
    forwards* [y Ry]: FM x. exists y. apply* is_repr_add_node.
Qed.

Hint Resolve binds_update_neq_inv.
(*--------------------------------------------------*)
(** Function [create] *)

Lemma create_spec :
  Spec create () |R>> forall B,
    R (UF B) (fun r => [r \notin (per_dom B)] \* UF (per_add_node B r)).
Proof.
  xcf. intros. unfold UF. xextract as M (PM&FM&DM&EM).
  xapp_spec ml_ref_spec_group.
  intros r. hextract as Neq. hsimpl. splits.
    apply~ per_add_node_per.
    apply~ is_forest_add_node.
    rewrite~ dom_update_notin. rewrite per_dom_add_node. fequals.
    applys~ inv_add_node.
    rewrite~ <- DM.
Admitted. (* faster *)

Hint Extern 1 (RegisterSpec create) => Provide create_spec.


(*--------------------------------------------------*)
(** Function [same] *)

Lemma same_spec :
  Spec same x y |R>> forall B,
    x \in (per_dom B) -> y \in (per_dom B) ->
    keep R (UF B) (\= isTrue (B x y)).
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (PM&FM&DM&EM).
  rewrite <- DM in *. clear DM.
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapp. intros b. xsimpl. subst~.
  subst b. rewrite <- EM. fequals. applys~ is_equiv_iff_same_repr.
Admitted. (* faster *)

Hint Extern 1 (RegisterSpec equiv) => Provide same_spec.



*)

(*   Q = (fun F => H \* \[forall X, (Fof X) ===> triple (F X)]). *)

(*

Definition cf_func fopt x t1 : formula := fun H Q =>
  (fun (F:val) => \[F = val_func fopt x t1]) \*+ H ===> Q.


(*
Definition cf_val v : formula := fun H Q =>
  H ==> Q v \* \Top.
*)

(*





(*
Definition Cf_fix (n:nat) (F1of : func -> dyns -> formula) (F2of : func -> formula) : formula :=
  fun `{Enc A} H (Q:A->hprop) =>
  forall (F:val),
  (forall (Xs:dyns) H' `{EA':Enc A'} (Q':A'->hprop),
     List.length Xs = n -> '(F1of F Xs) H' Q' -> App F Xs H' Q') ->
  '(F2of F) H Q.

Definition Cf_fix0 (F1of : func -> formula)
                   (F2of : func -> formula) : formula := fun `{Enc A} H (Q:A->hprop) =>
  forall (F:func),
  (forall A' `{EA':Enc A'} H' (Q':A'->hprop), '(F1of F) H' Q' -> App F nil H' Q') ->
  '(F2of F) H Q.

Definition Cf_fix1 (F1of : forall A `{EA:Enc A}, func -> A -> formula)
                   (F2of : func -> formula) : formula := fun `{Enc A} H (Q:A->hprop) =>
  forall (F:func),
  (forall A' `{EA':Enc A'} A1 `{EA1:Enc A1} (X1:A1) H' (Q':A'->hprop), '(F1of _ F X1) H' Q' -> App F [Dyn X1] H' Q') ->
  '(F2of F) H Q.
*)



(* ---------------------------------------------------------------------- *)
(** Implementation *)

Definition F : var := 4%nat.
Definition X : var := 17%nat.
Definition Y : var := 18%nat.

Definition val_test_fun2 : trm :=
  Vars F, X, Y from 0%nat in
  LetFun F X Y := prim_add X Y in
  F.


(* ---------------------------------------------------------------------- *)
(** Verification *)

Lemma rule_test_fun2:
  triple val_test_fun2
    \[]
    (fun g => \[forall n1 n2, triple (g n1 n2) \[] (fun r => \[r = n1 + n2])]).
Proof using.
  xcf. xlet.
  apply local_erase. unfold cf_fun at 1. hsimpl.
  intros F. xpull. intros HF. xval. hsimpl.
  intros.

unfold val_test_fun2.
applys triple_trm_of_cf_iter 1%nat; [ simpl ].
  applys triple_of_cf.
  rewrite cf_unfold. unfold cf_def. simpl.
  rewrite cf_unfold. unfold cf_def. simpl.


  xcf.
. xapps. intros r p E. subst r.
  applys local_erase. intros F M. (* todo: xfun *)
  xvals. unfold MCount. hsimpl.
  { intros n'. applys (rm M).
    xapp~. xapp. hsimpl~. }
Qed.




*)


Notation "'`Fun' F '_' ':=' F1" :=
  (local (cf_fun (fun _ => F1)))
  (at level 69, F ident) : charac.

Notation "'`Fun' F X1 ':=' F1" :=
  (local (cf_fun (fun X => F1)))
  (at level 69, F ident, X1 ident) : charac.

Notation "'`Fix' F X1 ':=' F1" :=
  (local (cf_fix (fun F X => F1)))
  (at level 69, F ident, X1 ident) : charac.


  | trm_func Norec x t1 => local (cf_fun (fun X => cf (subst x X t1)))
  | trm_func (Rec f) x t1 => local (cf_fix (fun F X => cf (subst f F (subst x X t1))))
  { destruct r; fequals; fequals.
    { applys~ fun_ext_1. }
    { applys~ fun_ext_2. } }
 destruct r; simpl; applys sound_for_local; intros H Q P.
    { renames v to x. unfolds in P. applys rule_func_val.
      hchanges~ P. intros F H' Q' HB. applys~ rule_app_fun. applys~ IH. }
    { renames v0 to f, v to x. hnf in P. subst Q. applys rule_func_val.
      hsimpl. intros F H' Q' HB. applys~ rule_app_fix.
      applys~ IH. } }



Definition cf_fun (Fof : val -> formula) : formula := fun H Q =>
  (fun (F:val) => \[forall X, (Fof X) ===> triple (F X)]) \*+ H ===> Q.

Definition cf_fun2 (Fof : val -> val -> formula) : formula := fun H Q =>
  (fun (F:val) => \[forall X1 X2, (Fof X1 X2) ===> triple (F X1 X2)]) \*+ H ===> Q.
*)

(*
Lemma test : forall (Fof : val -> val -> formula) H Q,
  cf_fun2 Fof H Q ->
  cf_fun (fun X1 => cf_fun (fun X2 => Fof X1 X2)) H Q.
Proof using.
  introv M.
  unfolds cf_fun2. unfold cf_fun at 1.
  intros F. hsimpl. intros N.
  applys himpl_trans ((rm M) F). hsimpl.
  intros X1 X2 H' Q' R. specializes N X1.
unfold cf_fun in N.
  unfolds in N.
  intros HF h Hh.
  forwards (h'&v&HR&K): (N X1) Hh. { intros r. hsimpl. }
  exists h' v. split.
  Hint Resolve red_val.
  applys red_app_func HR. applys red_val. reflexivity.

  specializes N X2.
  applys
  unfolds in R.
Qed.

Lemma test : forall (Fof : val -> val -> formula) H Q,
  cf_fun (fun X1 => cf_fun (fun X2 => Fof X1 X2)) H Q ->
  cf_fun2 Fof H Q.
Proof using.
  introv M.
  unfold cf_fun2. unfold cf_fun in M at 1.
  intros F.
  applys himpl_trans ((rm M) F). hsimpl.
  introv N. intros G.
  intros H' Q'. introv R. specializes R F.
  unfolds in R.
Qed.


forall X : val,
     local
       (cf_fun
          (fun X0 : val => `App ((prim_add X) X0))) ===>
     triple (F X)



Definition cf_fix (Fof : val -> val -> formula) : formula := fun H Q =>
  Q = (fun F => H \* \[forall X, (Fof F X) ===> triple (F X)]).
*)

(*


Definition hfield (l:loc) (f:field) (v:val) : hprop :=
  (l+f)%nat ~~> v \* \[l <> null].

Notation "l `.` f '~~>' v" := (hfield l f v)
  (at level 32, f at level 0, no associativity,
   format "l `.` f  '~~>'  v") : heap_scope.

Lemma hstar_hfield_same_loc_disjoint : forall l f v1 v2,
  (l`.`f~~> v1) \* (l`.`f ~~> v2) ==> \[False].
Proof using.
  intros. unfold hfield.
  hchanges hstar_hsingle_same_loc_disjoint.
Qed.

Lemma hfield_not_null : forall l f v,
  f = 0%nat ->
  (l`.`f ~~> v) ==> (l`.`f ~~> v) \* \[l <> null].
Proof using.
  introv E. subst. unfold hfield. hsimpl~.
Qed.

Implicit Arguments hfield_not_null [].


Lemma hfield_eq_hsingle : forall l f v,
  l <> null ->
  (l`.`f ~~> v) = ((l+f)%nat ~~> v).
Proof using.
 Transparent hfield.
  introv N. unfold hfield.
  applys himpl_antisym; hsimpl~.
Qed.
(* ---------------------------------------------------------------------- *)
(* ** Configuration of [hsimpl] *)

(* ** Configure [hsimpl] to make it aware of [hsingle] *)

Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  end.


(* ---------------------------------------------------------------------- *)
(* ** Conversion between [hfield] and [hsingle] *)

Lemma hsingle_of_hfield : forall l f v,
  (l`.`f ~~> v) ==> ((l+f)%nat ~~> v) \* \[l <> null].
Proof using. intros. unfold hfield. hsimpl~. Qed.

Lemma hfield_of_hsingle : forall l f v,
  l <> null ->
  ((l+f)%nat ~~> v) ==> (l`.`f ~~> v).
Proof using. intros. unfold hfield. hsimpl~. Qed.


Lemma xval_lemma : forall v H Q,
  H ==> Q v \* \Top ->
  local (cf_val v) H Q.
Proof using.
  intros v H Q M. unfold cf_val.
  applys~ local_htop_post (Q \*+ \Top).
  applys local_erase. applys M.
Qed.

Tactic Notation "xval_notop" :=
  applys local_erase; unfold cf_val.

*)
(* Capturing bound names

Fixpoint nat_fold A (f:nat->A->A) (k:nat) (z:A) : A :=
  match k with
  | O => z
  | S k' => f k' (nat_fold f k' z)
  end.

(** Recovering variable names in ltac *)

Require Import Coq.Strings.String.
Open Scope string_scope.

Ltac with_var_name x cont :=
  match x with
  | F => let X := fresh "F" in cont X
  | P => let X := fresh "P" in cont X
  | N => let X := fresh "N" in cont X
  end.

Lemma test :true.
Proof using.
  let X := fresh "F" in set (X := true).

  let X := constr:(F) in
  with_var_name X (fun H => set (H := true) ).





(* not used

  let f := xget_function tt in
Ltac xget_function tt :=
  match goal with |- app ?t _ _ =>
    match t with
    | trm_app ?f _ => constr:(f)
    | trm_app (trm_app ?f) _ => constr:(f)
    end end.
*)

Definition test := local (cf_let (cf_val val_unit) (fun a =>
  local (cf_let (local (cf_val val_unit)) (fun b => cf_val (val_pair a b))))).

Lemma test' : forall H Q, test H Q.
Proof using.
  unfolds test. intros.
  apply local_erase.
  match goal with |- cf_let _ (fun x => _) _ _ =>
   let w := fresh x in
   esplit; split; [ | intros w] end.
  admit.
Qed.

*)


(*

Tactic Notation "xlet" :=
  match goal with
  | |- local (cf_let' ?x ?F1 ?F2) _ _ => let X := fresh x in xlet X
  | |- local (cf_if _ _ _) _ _ => let X := fresh "C" in xlet X
  | _ => xlet_nointro
  end.


Tactic Notation "xlet_nointro" :=
  applys local_erase; esplit; split.

Tactic Notation "xlet" simple_intropattern(X) :=
  applys local_erase; esplit; split; [ | intros X ].

Tactic Notation "xlet" :=
  match goal with
  | |- local (cf_let' ?x ?F1 ?F2) _ _ => let X := fresh x in xlet X
  | |- local (cf_if _ _ _) _ _ => let X := fresh "C" in xlet X
  | _ => xlet_nointro
  end.




EXO

Lemma rule_red : forall t1 t2 H Q,
  (forall m m' r, red m t1 m' r -> red m t2 m' r) ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv T M. intros H' h Hh.
  forwards (h'&v&R&K): (rm M) Hh. exists h' v. splits~.
Qed.


Lemma rule_red : forall t1 t2 H Q,
  (forall n m m' r, red n m t1 m' r -> red n m t2 m' r) ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv T M. intros H' h Hh.
  forwards (n&h'&v&R&K&C): (rm M) Hh. exists n h' v. splits~.
Qed.


Lemma rule_seq : forall H1 t1 t2 H Q,
  triple t1 H (fun r => \[r = val_unit] \* H1) ->
  triple (subst var_dummy val_unit t2) H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_let M1.
  intros X. xpull. intro_subst. applys M2.
Qed.

*)




(*
Definition fields := list field.
Definition star_fields_values l fvs :=
  fold_right (fun H fv => let (f,v) := fv in H \* l `.` f ~~> v) \[] fvs.

Definition star_fields l n :=
  nat_fold (fun H f => H \* (Hexists v, l `.` f ~> v)) \[] n.
*)



  (* (forall (F:val),
        (forall X H' Q',
          triple (subst x X t1) H' Q' ->
          triple (trm_app F X) H' Q') ->
        H ==> Q F) ->
      triple (trm_fun x t1) H Q.*)

(* not used
Lemma rule_red : forall t1 t2 H Q,
  (forall m m' r, red m t1 m' r -> red m t2 m' r) ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv T M. intros H' h Hh.
  forwards (h'&v&R&K): (rm M) Hh. exists h' v. splits~.
Qed.


Lemma rule_red_val : forall t v H Q,
  H ==> Q v ->
  (forall m, red m t m v) ->
  triple t H Q.
Proof using.
  introv M R. intros HF h N. exists h v. splits.
  { auto. }
  { hhsimpl. hchanges M. }
Qed.



Lemma rule_if_val' : forall v t1 t2 H Q,
  (v <> val_int 0 -> triple t1 H Q) ->
  (v = val_int 0 -> triple t2 H Q) ->
  triple (trm_if v t1 t2) H Q.
Proof using.


  introv M1 M2. intros h1 h2 D HF. tests E: (v <> val_int 0).
  { forwards* (h'&v'&(N1&N2&N3&N4)): (rm M1) HF.
    exists h' v'. splits~. { applys red_if_val; auto_false. } }
  { forwards* (h'&v'&(N1&N2&N3&N4)): (rm M2) h1 HF.
    exists h' v'. splits~. { applys red_if_val; auto_false. } }
Qed.



  | prim_fst : prim
  | prim_snd : prim

  | red_if_true : forall n1 n2 m1 m2 m3 v r t0 t1 t2,
      red n1 m1 t0 m2 v ->
      v <> val_int 0 ->
      red n2 m2 t1 m3 r ->
      red (n1+n2) m1 (trm_if t0 t1 t2) m3 r
  | red_if_false : forall n1 n2 m1 m2 m3 v r t0 t1 t2,
      red n1 m1 t0 m2 v ->
      v = val_int 0 ->
      red n2 m2 t2 m3 r ->
      red (n1+n2) m1 (trm_if t0 t1 t2) m3 r


Lemma red_if_val' : forall n m1 m2 v r t1 t2,
  red n m1 (If v = val_int 0 then t2 else t1) m2 r ->
  red n m1 (trm_if v t1 t2) m2 r.
Proof using.
  introv M1. case_if.
  { applys equates_5. applys* red_if_false. math. }
  { applys equates_5. applys* red_if_true. math. }
Qed.

Lemma red_if_val : forall n m1 m2 v r t1 t2,
  (v <> val_int 0 -> red n m1 t1 m2 r) ->
  (v = val_int 0 -> red n m1 t2 m2 r) ->
  red n m1 (trm_if v t1 t2) m2 r.
Proof using.
  introv M1 M2. tests: (v = 0).
  { applys equates_5. applys* red_if_false. math. }
  { applys equates_5. applys* red_if_true. math. }
Qed.




Lemma red_if_val' : forall m1 m2 v r t1 t2,
  red m1 (If v = val_int 0 then t2 else t1) m2 r ->
  red m1 (trm_if v t1 t2) m2 r.
Proof using.
  introv M1. case_if. { applys* red_if_false. } { applys* red_if_true. }
Qed.

Lemma red_if_val : forall m1 m2 v r t1 t2,
  (v <> val_int 0 -> red m1 t1 m2 r) ->
  (v = val_int 0 -> red m1 t2 m2 r) ->
  red m1 (trm_if v t1 t2) m2 r.
Proof using.
  introv M1 M2. tests: (v = 0).
  { applys* red_if_false. } { applys* red_if_true. }
Qed.

Lemma red_if' : forall m1 m2 m3 v r t0 t1 t2,
  red m1 t0 m2 v ->
  red m2 (If v = val_int 0 then t2 else t1) m3 r ->
  red m1 (trm_if t0 t1 t2) m3 r.
Proof using.
  introv M1 M2. case_if.
  { applys* red_if_false. } { applys* red_if_true. }
Qed.
  | red_if_true : forall m1 m2 m3 v r t0 t1 t2,
      red m1 t0 m2 v ->
      v <> val_int 0 ->
      red m2 t1 m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r
  | red_if_false : forall m1 m2 m3 v r t0 t1 t2,
      red m1 t0 m2 v ->
      v = val_int 0 ->
      red m2 t2 m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r




(* ---------------------------------------------------------------------- *)
(* ** Version of [let] binding a closed function *)

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val),
    (forall X H' Q',
      triple (subst f F (subst x X t1)) H' Q' ->
      triple (trm_app F X) H' Q') ->
    triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_val (val_fix f x t1)) t2) H Q.
Proof using.
  introv M. applys rule_let_val. intros F EF.
  applys (rm M). clears H Q. intros X H Q. applys~ rule_app.
Qed.




(* ---------------------------------------------------------------------- *)
(* ** Alternative statement of [rule_if] *)

Lemma rule_if_val' : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v'&R&K): (rm M) HF h.
  exists h' v'. splits~. { applys~ red_if_val'. }
Qed.

Lemma rule_if' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (v:val), triple (If v = val_int 0 then t2 else t1) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  forwards M: (rm M2) v.
  forwards* (h'&v'&R&K): (rm M) h1'.
  exists h' v'. splits~.
  { applys* red_if'. }
  { rewrite <- htop_hstar_htop. rew_heap~. }
Qed.


Lemma rule_if_val' : forall v t1 t2 H Q,
  triple (If v = val_int 0 then t2 else t1) H Q ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v'&R&K): (rm M) HF h.
  exists h' v'. splits~. { applys~ red_if_val'. }
Qed.

Lemma rule_if_val : forall v t1 t2 H Q,
  (v <> val_int 0 -> triple t1 H Q) ->
  (v = val_int 0 -> triple t2 H Q) ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N. tests: (v <> val_int 0).
  { forwards* (h'&v'&R&K): (rm M1) HF h.
    exists h' v'. splits~. { applys red_if_val; auto_false. } }
  { forwards* (h'&v'&R&K): (rm M2) HF h.
    exists h' v'. splits~. { applys red_if_val; auto_false. } }
Qed.

Lemma rule_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (v:val),
      (v <> val_int 0 -> triple t1 (Q1 v) Q)
   /\ (v = val_int 0 -> triple t2 (Q1 v) Q)) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  tests_nosubst E: (v <> val_int 0).
  { forwards (M&_): (rm M2) v. forwards~ M2: (rm M).
    forwards* (h'&v'&R&K): (rm M2) h1'.
    exists h' v'. splits~.
    { applys* red_if_true. }
    { rewrite <- htop_hstar_htop. rew_heap~. } }
  { forwards (_&M): (rm M2) v. forwards~ M2: (rm M).
    forwards* (h'&v'&R&K): (rm M2) h1'.
    exists h' v'. splits~.
    { applys* red_if_false. }
    { rewrite <- htop_hstar_htop. rew_heap~. } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Alternative version of [rule_if] *)

Lemma rule_if_val' : forall v t1 t2 H Q,
  (v <> val_int 0 -> triple t1 H Q) ->
  (v = val_int 0 -> triple t2 H Q) ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N. tests E: (v <> val_int 0).
  { forwards* (n&h'&v'&R&K&C): (rm M1) HF h.
    exists n h' v'. splits~. { applys red_if_val; auto_false. } }
  { forwards* (n&h'&v'&R&K&C): (rm M2) HF h.
    exists n h' v'. splits~. { applys red_if_val; auto_false. } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Alternative version of [cf_if] *)

  | trm_if t0 t1 t2 =>
      local match t0 with
      | trm_val v0 => cf_if_val v0 (cf t1) (cf t2)
      | _ => cf_if (cf t0) (cf t1) (cf t2)
      end

tests C: (exists v, t1 = trm_val v).
    { destruct C as (v&E). subst t1. hnf in P.
      applys rule_if_val; intros E; case_if; applys~ IH. }


asserts P': (cf_if (cf t1) (cf t2) (cf t3) H Q).
      { destruct t1; auto. false* C. } clear P C.


Fixpoint is_app_vals (t:trm) : bool :=
  match t with
  | trm_app (trm_val v1) (trm_val v2) => true
  | trm_app t1 (trm_val v2) => is_app_vals t1
  | _ => false
  end.

Opaque is_app_vals.

  | red_app_fun : forall m1 m2 v1 v2 x t r,
      v1 = val_fun x t ->
      red m1 (subst x v2 t) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_app_fix : forall m1 m2 v1 v2 f x t r,
      v1 = val_fix f x t ->
      red m1 (subst f v1 (subst x v2 t)) m2 r ->
      red m1 (trm_app v1 v2) m2 r



Lemma rule_app : forall f x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst f F (subst x V t1)) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros h1 h2 D P1.
  forwards~ (h1'&v&(N1&N2&N3&N4)): (rm M) h2 (rm P1).
  exists h1' v. splits~.
  { applys~ red_app_fix_val. }
Qed.

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val),
    (forall X H' Q',
      triple (subst f F (subst x X t1)) H' Q' ->
      triple (trm_app F X) H' Q') ->
    triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_val (val_fix f x t1)) t2) H Q.
Proof using.
  introv M. applys rule_let_val. intros F EF.
  applys (rm M). clears H Q. intros X H Q.
  applys rule_app. auto.
Qed.



Lemma subst_cross : forall x1 x2 v1 v2 t,
  x1 <> x2 ->
  subst x2 v2 (subst x1 v1 t) = subst x1 v1 (subst x2 v2 t).
Proof using.
  introv N. induction t; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  repeat case_if; simpl; repeat case_if~.
Qed.
*)





(* ---------------------------------------------------------------------- *)
(** N-ary functions *)




(* not used
Definition trm_funcs (fopt:rec_var) (xs:vars) (t:trm) : trm :=
  match fopt with
  | None => trm_funs xs t
  | Some f => trm_fixs f xs t
  end.

Definition val_funcs (fopt:rec_var) (xs:vars) (t:trm) : trm :=
  match fopt with
  | None => val_funs xs t
  | Some f => val_fixs f xs t
  end.
*)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the [app] predicate *)

(** The proposition [app (f v) H Q] asserts that the application
    of [f] to [v] has [H] as pre-condition and [Q] as post-condition. *)

Definition app (t:trm) (H:hprop) (Q:val->hprop) :=
  triple t H Q.




(* ---------------------------------------------------------------------- *)
(* ** Instance of [app] for primitive operations *)

(* TODO: not needed *)
Lemma app_ref : forall v,
  app (val_ref v) \[] (fun r => Hexists l, \[r = val_loc l] \* l ~~> v).
Proof using. applys rule_ref. Qed.

Lemma app_get : forall v l,
  app (val_get (val_loc l)) (l ~~> v) (fun x => \[x = v] \* (l ~~> v)).
Proof using. applys rule_get. Qed.

Lemma app_set : forall w l v,
  app (val_set (val_loc l) w) (l ~~> v) (fun r => \[r = val_unit] \* l ~~> w).
Proof using. applys rule_set. Qed.




(* ---------------------------------------------------------------------- *)
(* todo: reuse Coq's notation for lsits *)
Notation "'[' x1 ']'" := (x1::nil) : list_scope.
Notation "'[' x1 ; x2 ']'" := (x1::x2::nil) : list_scope.
Notation "'[' x1 ; x2 ; x3 ']'" := (x1::x2::x3::nil) : list_scope.
Notation "'[' x1 ; x2 ; x3 ; x4 ']'" := (x1::x2::x3::x4::nil) : list_scope.
Open Scope list_scope.






red t2 v2 ->
red (t1 v2) r ->
red (t1 t2) r.

(* m2=m1 if pure*)
(red m2 t1' m3 r' -> red m1 t1 m3 r') ->
red m2 (t1' v2) m4 r ->
red m1 (t1 v2) m4 r ->
--right reduction first--




Lemma rule_frame' : forall H2 H1 Q1 t H Q,
  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv WH M WQ. applys rule_consequence WH WQ. applys rule_frame M.
Qed.

---




(* todo: already exist under different names

Lemma hexists_weaken : forall A (J J' : A -> hprop),
  J ===> J' ->
  hexists J ==> hexists J'.
Proof using. introv W. intros h (x&Hh). exists x. applys* W. Qed.

Lemma hforall_weaken : forall A (J J' : A -> hprop),
  J ===> J' ->
  hforall J ==> hforall J'.
Proof using. introv W. intros h Hh x. applys* W. Qed.

Lemma hwand_extend : forall H3 H1 H2,
  (H1 \--* H2) \* H3 ==> (H1 \--* (H2 \* H3)).
Proof using. intros. unfold hwand. hpull ;=> H4 M. hsimpl. hchanges M. Qed.

Arguments hwand_extend : clear implicits.

*)

(* false if H1 is not habited
Lemma hwand_same_part : forall H1 H2 H3,
  (H1 \* H2 \--* H1 \* H3) ==> (H2 \--* H3).
Proof using. intros. unfold hwand. hpull ;=> H4 M. hsimpl.


Lemma regular_regular_transformer : forall F,
  regular (regular_transformer F).
Proof using.
  intros F H Q Q' M.
  unfold regular_transformer.
  do 2 hchange hstar_hforall. rew_heap.
  unfolds hforall. simpl. intros h Hh H'.
  specializes Hh (H \* H'). hhsimpl.
  hchanges (hwand_cancel_part H (H' \* \Top) (F (Q \*+ (H \* H')))).
  rewrite (hstar_comm H' \Top).
  apply hwand_move_part_r.
  rewrite <- hstar_assoc. rewrite htop_hstar_htop.
  asserts_rewrite (Q \*+ (H \* H') = (fun x : val => (Q x \* H) \* H')).
  { apply fun_ext_1. intros x. rewrite~ hstar_assoc. }

  pattern \Top at 3; rewrite <-

  applys himpl_trans. Focus 2. applys hwand_move_part_l.

  hchanges (hwand_cancel_part \Top (H' \* \Top) (F (Q \*+ (H \* H')))).

  hchange (hwand_extend \Top (H' \* \Top) (F (Q \*+ (H \* H')))). rew_heap.


  hchanges (hwand_extend (H \* \Top) (H \* H' \* \Top) (F (Q \*+ (H \* H')))).
  hchanges (

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \--* H3) ==> (H2 \--* H3).


  do 2 hchange hstar_hforall. rew_heap.
  applys hforall_weaken. intros H'.
  hsimpl.
  unfold hforall.
  intros h Hh.
Qed.


Lemma regular_weaken : forall Q' F H Q,
  regular F ->
  H ==> F Q ->
  Q ===> Q' ->
  H ==> F Q'.
Proof using.
  introv R M W. hchanges M. forwards~ N: R \[] W. hchanges N.
Qed.

Lemma regular_frame_top : forall H1 H2 F H Q,
  regular F ->
  H ==> H1 \* H2 \* \Top ->
  H1 ==> F (fun x => H2 \--* Q x) -> (* todo: notation *)
  H ==> F Q.
Proof using.
  introv R W M. hchanges W. hchanges M.
  forwards~ N: R H2 (fun x : val => H2 \--* Q x). hsimpl. hchanges N.
  applys~ regular_weaken. intros x. hchanges (hwand_cancel H2).
Qed.

Lemma regular_frame : forall H1 H2 F H Q,
  regular F ->
  H ==> H1 \* H2 ->
  H1 ==> F (fun x => H2 \--* Q x) ->
  H ==> F Q.
Proof using.
  introv R W M. applys~ regular_frame_top H1 H2. { hchanges W. }
Qed.

*)


(* LATER
Lemma hpull_hforall : forall A H1 H2 H' (J:A->hprop),
  (exists x, H1 \* J x \* H2 ==> H') ->
  H1 \* (hforall J \* H2) ==> H'.
Proof using.
  introv (x&M). rewrite hstar_comm_assoc.
  applys himpl_trans. applys hstar_hforall.
  applys himpl_hforall_l. exists x.
  rewrite~ <- hstar_comm_assoc.
Qed.
*)

(* partial support for hforall
Ltac hpull_step tt ::=
  match goal with |- _ \* ?HN ==> _ =>
  match HN with
  | ?H \* _ =>
     match H with
     | \[] => apply hpull_empty
     | \[_] => apply hpull_hprop; intros
     | hexists _ => apply hpull_hexists; intros
     | hforall _ => apply hpull_hforall
     | _ \* _ => apply hpull_assoc
     | _ => apply hpull_keep
     end
  | \[] => fail 1
  | ?H => apply hpull_starify
  end end.
*)

(* LATER
Lemma xpull_hforall : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  SepBasicSetup.is_local F ->
  (exists x, F (H1 \* ((J x) \* H2)) Q) ->
   F (H1 \* (hforall J \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc. apply~ local_extract_hexists.
  intros. rewrite~ hstar_comm_assoc.
Qed.
*)


Lemma weaken_formula_trans : forall (F1 F2:formula),
  (forall H' Q', (H' ==> F1 Q') -> (H' ==> F2 Q')) ->
  F1 ===> F2.
Proof using. introv M. intros Q. applys~ M (F1 Q). Qed.





Definition sound_for (t:trm) (F:formula) :=
  forall H Q, (H ==> F Q) -> triple t H Q.

Lemma sound_for_local : forall t (F:formula),
  sound_for t F ->
  sound_for t (local F).
Proof using.
  unfold sound_for. introv SF. intros H Q M.
  rewrite is_local_triple. unfold SepBasicSetup.local.
  hchange M. unfold local. hpull ;=> Q'.
  hsimpl (F Q') ((Q' \---* Q \*+ \Top)) Q'. split.
  { applys~ SF. }
  { hchanges qwand_cancel. }
Qed.

Definition sound_for' (t:trm) (F:formula) :=
  forall Q, triple t (F Q) Q.

Lemma sound_for_eq_sound_for' :
  sound_for = sound_for'.
Proof using.
  applys pred_ext_2. intros t f.
  unfold sound_for, sound_for'. intros. iff M.
  { intros Q. applys M. auto. }
  { intros H Q N. applys* rule_consequence N M. }
Qed.

Lemma sound_for'_local : forall t (F:formula),
  sound_for' t F ->
  sound_for' t (local F).
Proof using. introv. rewrite <- sound_for_eq_sound_for'. applys sound_for_local. Qed.



(** Empty heap predicate, written [ \[] ]. *)

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

(** Separation Logic star, written [H1 \* H2]. *)

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

(** Notation for applying star to a post-condition,
  written [Q \*+ H], short for [fun x => (Q x \* H)]. *)

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

(** Existential lifted to heap predicates,
  written [Hexists x, H] *)

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
  (at level 39, x1 ident, H at level 50) : heap_scope.

(** Universal lifted to heap predicates
    (currently, no notation provided) *)

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'Hforall' x1 , H" := (hforall (fun x1 => H))
  (at level 39, x1 ident, H at level 50) : heap_scope.



Parameter hforall : forall (A : Type) (J : A -> hprop), hprop.

Parameter hexists : forall A (J:A->hprop), hprop.







(* ---------------------------------------------------------------------- *)
(** Definition of substitution of a set of bindings *)


Section LinearWp.

Definition ctx := list (var*val).

Definition ctx_empty : ctx :=
  nil.

Definition ctx_add (E:ctx) (x:var) (v:val) :=
  (x,v)::E.

Fixpoint ctx_lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E' => if eq_var_dec x y
                   then Some v
                   else ctx_lookup x E'
  end.

(*
Fixpoint ctx_subst (E:ctx) (t:trm) : trm :=
  let aux t := subst E t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => match ctx_lookup x E with
                 | None => t
                 | Some v => trm_val v
                 end
  | trm_fun x t1 => trm_fun x (aux_no_capture x t1)
  | trm_fix f x t1 => trm_fix f x (if eq_var_dec f y then t1 else
                                   aux_no_capture x t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capture x t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  end.
*)

Definition wp_def' wp (E:ctx) (t:trm) :=
  let w := wp E in
  match t with
  | trm_val v => wp_val v
  | trm_var x => match ctx_lookup x E with
                 | None => wp_fail
                 | Some v => wp_val v
                 end
  | trm_fun x t1 => wp_val (val_fun x t1)
  | trm_fix f x t1 => wp_val (val_fix f x t1)
  | trm_if t0 t1 t2 => wp_if (w t0) (w t1) (w t2)
  | trm_seq t1 t2 => wp_seq (w t1) (w t2)
  | trm_let x t1 t2 => wp_let (w t1) (fun X => wp (ctx_add E x X) t2)
  | trm_app t1 t2 => local (weakestpre (triple t))
  | trm_while t1 t2 => wp_while (w t1) (w t2)
  | trm_for x t1 t2 t3 => wp_for' (w t1) (w t2) (fun X => wp (ctx_add E x X) t3)
  end.

Definition wp' := FixFun2 wp_def'.

(*
Lemma wp'_unfold_iter : forall n t,
  wp' t = func_iter n wp_def' wp' t.
Proof using.
  applys~ (FixFun_fix_iter (measure trm_size)). auto with wf.
  intros f1 f2 t IH. unfold wp_def.
  destruct t; try solve [ fequals~ | fequals~; applys~ fun_ext_1 ].
Qed.
*)

Hint Extern 1 (measure2 _ _ _) => simpl; math.

Lemma wp'_unfold : forall E t,
  wp' E t = wp_def' wp' E t.
Proof using. (*applys (wp_unfold_iter 1). *)
  applys~ (FixFun2_fix (measure2 (fun (E:ctx) (t:trm) => trm_size t))). auto with wf.
  intros E t f1 f2 IH. unfold wp_def'. (* TODO inconsistent order of args with before *)
  destruct t; try solve [ fequals~ | fequals~; applys~ fun_ext_1 ].
Qed.

(*
Lemma wp'_eq_wp_ind : forall E t,
  wp' E t = wp (ctx_subst E t).
Proof using.
  admit.
Qed.
*)

Lemma wp_eq_wp' :
  wp = wp' ctx_empty.
Proof using.
  admit.
Qed.

End LinearWp.




(*
Lemma ctx_subst_add_rem : forall E x v t,
    ctx_subst (ctx_add x v (ctx_rem x E)) t
  = ctx_subst (ctx_add x v E) t.
Proof using.
  intros E. induction E as [|(y,w) E']; intros.
  { auto. }
  { simpl ctx_rem. unfold ctx_add. case_if.
    { subst y. admit. }
    { simpls. rewrite subst_subst_cross; [|auto]. apply IHE'. } }
Qed.
*)



Fixpoint substn (xs:vars) (vs:vals) (t:trm) : trm :=
  match xs, vs with
  | x::xs', v::vs' => substn xs' vs' (subst x v t)
  | _, _ => t
  end.

Lemma substs_eq_substs : forall xs vs t,
  length xs = length vs ->
  substs xs vs t = substn (LibList.combine xs vs) t.
Proof using.
  intros xs. induction xs as [|x xs']; introv N;
   destruct vs as [|v vs']; rew_list in N; tryfalse.
  { auto. }
  { simpl. rewrite~ IHxs'. }
Qed.

Lemma subst_substn : forall x v ys ws t,
  var_fresh x ys ->
  length ys = length ws ->
  subst x v (substn ys ws t) = substn ys ws (subst x v t).
Proof using.
  intros. gen t ws. induction ys as [|y ys']; introv L. simpls.
  { auto. }
  { destruct ws as [|w ws']; rew_list in *. { false; math. }
    simpls. case_if. rewrite~ IHys'. fequals. rewrite~ subst_subst_cross. }
Qed.























==now==



(* ===================


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt ::=
  applys local_erase; esplit; split.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Ltac xlet_core tt ::=
  applys local_erase; esplit; split.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xif] *)

Ltac xif_core tt ::=
  applys local_erase; esplit; splits;
  [ try reflexivity
  | xif_post tt
  | xif_post tt ].


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt ::=
  applys local_erase; unfold wp_fail.


(* ---------------------------------------------------------------------- *)
(* * [xapp] and [xapps] and [xapp as] *)

(** Basic [xapp] implementation

  Tactic Notation "xapp" constr(E) :=
    applys local_erase; xapplys E.

  Tactic Notation "xapp" :=
    try applys local_erase;
    xspec;
    let H := fresh "TEMP" in intros H;
    xapplys H;
    clear H.

*)

Ltac hpull_cont tt ::=
  try hpull.

Ltac hsimpl_cont tt ::=
  hsimpl.

Ltac xapp_let_cont tt ::=
  let X := fresh "X" in intros X;
  instantiate; try xpull; gen X.

Ltac xapp_as_let_cont tt ::=
  instantiate; try xpull.

Ltac xapps_let_cont tt ::=
  let X := fresh "X" in intros X;
  instantiate; try xpull;
  first [ intro_subst | gen X ].

Ltac xapp_template xlet_tactic xapp_tactic xlet_cont ::=
  match goal with
  | |- local (wp_let _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- local (wp_if _ _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- local (wp_seq _ _) _ _ => xseq; [ xapp_tactic tt | ]
  | _ => xapp_tactic tt
  end.

Ltac xapp_xapply E cont_post :=
  match goal with
  | |- ?F ?H ?Q => is_evar Q; xapplys E
  | |- ?F ?H (fun r => \[r = val_unit] \* ?H') => is_evar H'; xapplys E
    (* TODO: might not be needed *)
  | _ => xapply_core E ltac:(fun tt => hcancel) ltac:(cont_post)
  end.

Ltac xapp_basic_prepare tt ::=
  try match goal with |- local _ _ _ => apply local_erase end;
  rew_nary.

Ltac xapp_with_args E cont_xapply ::=
  match E with
  | __ => (* no spec provided *)
     let S := fresh "Spec" in
     xspec;
     intros S;
     cont_xapply S;
     clear S
  | _ =>
      match list_boxer_of E with
      | cons (boxer ltac_wild) ?E' => (* only args provided *)
         let S := fresh "Spec" in
         xspec;
         intros S;
         cont_xapply ((boxer S)::E');
         clear S
      | _ => (* spec and args provided *)
         cont_xapply E
      end
  end.

Ltac xapp_basic E cont_post tt ::=
  xapp_basic_prepare tt;
  xapp_with_args E ltac:(fun H =>
    xapp_xapply H cont_post).

(* TODO: xapps should do hsimpl if not in a let *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xval] and [xvals] *)

Ltac xval_nohtop_core tt :=
  applys local_erase; unfold wp_val.

Tactic Notation "xval_nohtop" :=
  xval_nohtop_core tt.

Lemma xval_htop_lemma : forall v H Q,
  H ==> Q v \* \Top ->
  local (wp_val v) H Q.
Proof using.
  intros v H Q M. unfold wp_val.
  applys~ local_htop_post (Q \*+ \Top).
  applys local_erase. intros x.
  hpull. intro_subst. hchanges~ M.
Qed.

Lemma xval_htop_as_lemma : forall v H Q,
  (forall x, x = v -> H ==> Q x \* \Top) ->
  local (wp_val v) H Q.
Proof using. intros v H Q M. applys~ xval_htop_lemma. Qed.

Ltac xval_template xlet_tactic xval_tactic xlet_cont :=
  match goal with
  | |- local (wp_let _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | |- local (wp_if _ _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | _ => xval_tactic tt
  end.

Ltac xval_basic tt :=
  match goal with
  | |- local ?F ?H ?Q => is_evar Q; applys local_erase; applys refl_rel_incl'
  | _ => applys xval_htop_lemma
  end.

Ltac xval_as_basic X EX :=
  match goal with
  | |- local ?F ?H ?Q => is_evar Q; applys local_erase; applys refl_rel_incl'
  | _ => applys xval_htop_as_lemma; intros X EX
  end.

Ltac xval_core tt ::=
  xval_template ltac:(fun tt => xlet) ltac:(xval_basic) ltac:(xapp_let_cont).

Ltac xval_as_core X ::=
  match goal with
  | |- local (wp_val _) _ _ => let EX := fresh "E" X in xval_as_basic X EX
  | _ => xval_template ltac:(fun tt => xlet as X) ltac:(xval_basic) ltac:(xapp_as_let_cont)
  end.

Ltac xvals_core tt ::=
  match goal with
  | |- local (wp_val _) _ _ => xval_basic tt; hsimpl
  | _ => xval_template ltac:(fun tt => xlet) ltac:(xval_basic) ltac:(xapps_let_cont)
  end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwhile] *)

(*
Ltac xwhile_template xwhile_tactic xseq_cont :=
  match goal with
  | |- local (wp_seq _ _) _ _ => xseq; [ xwhile_tactic tt | xseq_cont tt ]
  | _ => xwhile_tactic tt
  end.

Ltac xwhile_intros_all R LR HR ::=
  intros R LR; hnf; intros HR.

Ltac xwhile_intros R ::=
  let LR := fresh "L" R in
  let HR := fresh "H" R in
  xwhile_intros_all R LR HR.

Ltac xwhile_basic xwhile_intros_tactic ::=
  applys local_erase;
  xwhile_intros_tactic tt.

Ltac xwhile_core xwhile_tactic ::=
  xwhile_template ltac:(xwhile_tactic) ltac:(fun tt => xpull).


*)
*)




Definition sound_for t :=
  forall E Q, triple (substs E t) (wp E t Q) Q.

Lemma triple_wp_val : forall v,
  sound_for (trm_val v).
Proof using.
  intros. intros E Q. remove_local. rewrite substs_val. applys~ rule_val.
Qed.

Lemma triple_wp_fun : forall x t,
  sound_for (trm_fun x t).
Proof using.
  intros. intros E Q. remove_local. rewrite substs_fun. applys~ rule_fun.
Qed.

Lemma triple_wp_fix : forall f x t,
  sound_for (trm_fix f x t).
Proof using.
  intros. intros E Q. remove_local. rewrite substs_fix. applys~ rule_fix.
Qed.

Lemma triple_wp_var : forall x,
  sound_for (trm_var x).
Proof using.
  intros. intros E Q. remove_local.
  rewrite substs_var. destruct (ctx_lookup x E).
  { apply~ rule_val. }
  { xpull ;=> F. false. }
Qed.

Lemma triple_wp_if : forall t1 t2 t3,
  sound_for t1 ->
  sound_for t2 ->
  sound_for t3 ->
  sound_for (trm_if t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros E Q. remove_local.
  rewrite substs_if. applys rule_if.
  { applys* M1. }
  { intros b. simpl. remove_local ;=> b' M. inverts M. case_if.
    { applys* M2. }
    { applys* M3. } }
  { intros. applys~ wp_if_val_false. }
Qed.

Lemma triple_wp_seq : forall t1 t2,
  sound_for t1 ->
  sound_for t2 ->
  sound_for (trm_seq t1 t2).
Proof using.
  introv M1 M2. intros E Q. remove_local.
  rewrite substs_seq. applys rule_seq.
  { applys* M1. }
  { intros X. applys* M2. }
Qed.

Lemma triple_wp_let : forall x t1 t2,
  sound_for t1 ->
  sound_for t2 ->
  sound_for (trm_let x t1 t2).
Proof using.
  introv M1 M2. intros E Q. remove_local.
  rewrite substs_let. applys rule_let.
    { applys* M1. }
    { intros X. rewrite subst_substs_ctx_rem_same. applys M2. }
Qed.

Lemma triple_wp_app : forall t1 t2,
  sound_for t1 ->
  sound_for t2 ->
  sound_for (trm_app t1 t2).
Proof using.
  introv M1 M2. intros E Q. remove_local.
  rewrite substs_app. apply triple_weakestpre_pre.
Qed.




Lemma triple_wp_while : forall t1 t2,
  sound_for t1 ->
  sound_for t2 ->
  sound_for (trm_while t1 t2).
Proof using.
  introv M1 M2. intros E Q. remove_local.
  rewrite substs_while. applys rule_extract_hforall.


   set (R := weakestpre (triple (trm_while (substs E t1) (substs E t2)))). (* *)
  (* set (R := wp E (trm_while t1 t2)).*)
  exists R. simpl. applys rule_extract_hwand_hpure_l. (*todo rename *)
  { split.
    { (* applys is_local_wp *) applys is_local_weakestpre_triple. }
    { clears Q. applys qimpl_weakestpre_triple. intros Q.
(*
      set (t1' := substs E t1) in *.
      set (t2' := substs E t2) in *.
*)

 applys rule_while_raw. rewrite <- substs_while. rewrite <- substs_seq.
rewrite <- (substs_val E). rewrite <- substs_if.
applys triple_wp_if'. skip.
unfold we.
applys qimpl_weakestpre_triple. intros Q'.
applys triple_wp_seq'.
skip.
unfold R. unfold we. rewrite substs_while. auto.


 auto.

applys weakestpre_elim.
applys triple_wp_seq'.



forwards M: triple_wp_if'' E t1 (trm_seq t2 (trm_while t1 t2)) val_unit.
skip. skip. skip.
{ skip. }
{ hnf. intros Q'.
applys himpl_trans. applys triple_wp_seq'. skip.
 hnf. applys triple_wp_

intros E'. forwards: triple_wp_seq. skip. skip.

Search weakestpre. applys weakestpre_elim.
  applys triple_wp_if''.


      subst R. simpl. unfold wp_while at 2. apply local_erase'.
      apply himpl_hforall_r. intros R. applys hwand_move_l. hpull.
      intros (LR&MR).
Search hwand.
      applys rule_while_raw.
forwards M: triple_wp_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit.
auto.
applys triple_wp_seq.
(substs E t1) (trm_seq (substs E t2) (trm_while (substs E t1) (substs E t2))

      applys triple_wp_if.

Qed.






Lemma triple_wp : forall t E Q,
  triple (substs E t) (wp E t Q) Q.
Proof using.
  intros t. induction t; intros.
  { applys triple_wp_val. }
  { applys triple_wp_var. }
  { applys triple_wp_fun. }
  { applys triple_wp_fix. }
  { applys* triple_wp_if. }
  { applys* triple_wp_seq. }
  { applys* triple_wp_let. }
  { applys* triple_wp_app. }
  { applys* triple_wp_while. }
  { admit. }
Qed.




Lemma weakestpre_elim' : forall F H Q t,
  F ===> wp_triple t ->
  H ==> F Q ->
  triple t H Q.
Proof using.
  introv M N. lets G: triple_wp_triple t Q.
  applys~ rule_consequence G. hchanges N. applys M.
Qed.





(* ********************************************************************** *)
(* * Alternative definition of the CF generator *)

Module WP2.

(* ********************************************************************** *)
(* * Size of a term *)

(* ---------------------------------------------------------------------- *)
(** Size of a term, where all values counting for one unit. *)

Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fun x t1 => 1 + trm_size t1
  | trm_fix f x t1 => 1 + trm_size t1
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_seq t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_app t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  end.

Lemma trm_size_subst : forall t x v,
  trm_size (subst x v t) = trm_size t.
Proof using.
  intros. induction t; simpl; repeat case_if; auto.
Qed.

(** Hint for induction on size. Proves subgoals of the form
    [measure trm_size t1 t2], when [t1] and [t2] may have some
    structure or involve substitutions. *)

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_subst; math.

Hint Extern 1 (measure trm_size _ _) => solve_measure_trm_size tt.


(** The CF generator is a recursive function, defined using the
    optimal fixed point combinator (from TLC). [wp_def] gives the
    function, and [cf] is then defined as the fixpoint of [wp_def].
    Subsequently, the fixed-point equation is established. *)

Definition wp_def wp (t:trm) :=
  match t with
  | trm_val v => wp_val v
  | trm_var x => wp_fail (* unbound variable *)
  | trm_fun x t1 => wp_val (val_fun x t1)
  | trm_fix f x t1 => wp_val (val_fix f x t1)
  | trm_if t0 t1 t2 => wp_if (wp t0) (wp t1) (wp t2)
  | trm_seq t1 t2 => wp_seq (wp t1) (wp t2)
  | trm_let x t1 t2 => wp_let (wp t1) (fun X => wp (subst x X t2))
  | trm_app t1 t2 => local (wp_triple t)
  | trm_while t1 t2 => wp_while (wp t1) (wp t2)
  | trm_for x t1 t2 t3 => wp_for' (wp t1) (wp t2) (fun X => wp (subst x X t3))
  end.

Definition wp := FixFun wp_def.

(** Fixed point equations *)

Lemma wp_unfold_iter : forall n t,
  wp t = func_iter n wp_def wp t.
Proof using.
  applys~ (FixFun_fix_iter (measure trm_size)). auto with wf.
  intros f1 f2 t IH. unfold wp_def.
  destruct t; try solve [ fequals~ | fequals~; applys~ fun_ext_1 ].
Qed.

Lemma wp_unfold : forall t,
  wp t = wp_def wp t.
Proof using. applys (wp_unfold_iter 1). Qed.

(** All [wp] are trivially local by construction *)

Lemma is_local_cf : forall t,
  is_local (wp t).
Proof.
  intros. rewrite wp_unfold.
  destruct t; try solve [ apply is_local_local ].
  (* if no local on app : { simpl. applys is_local_wp_triple. } *)
Qed.

(** [remove_local] applies to goal of the form [triple t (local F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q],  then calls [xpull] *)

Ltac remove_local :=
  match goal with |- triple _ _ ?Q =>
    applys triple_local_pre; try (clear Q; intros Q); xpull end.

Lemma triple_wp : forall (t:trm) Q,
  triple t (wp t Q) Q.
Proof using.
  intros t. induction_wf: trm_size t. intros Q.
  rewrite wp_unfold. destruct t; simpl.
  { remove_local. applys~ rule_val. }
  { remove_local ;=> E. false. }
  { remove_local. applys~ rule_fun. }
  { remove_local. applys~ rule_fix. }
  { remove_local. applys rule_if.
    { applys* IH. }
    { intros b. simpl. remove_local ;=> b' E. inverts E. case_if.
      { applys* IH. }
      { applys* IH. } }
    { intros. applys~ wp_if_val_false. } }
  { remove_local. applys rule_seq. { applys* IH. } { intros X. applys* IH. } }
  { remove_local. applys rule_let. { applys* IH. } { intros X. applys* IH. } }
  { remove_local. apply triple_wp_triple. }
  { remove_local. set (R := weakestpre (triple (trm_while t1 t2))).
    apply rule_extract_hforall. exists R.
    apply rule_extract_hwand_hpure_l. split.
    { apply~ is_local_wp_triple. }
    { applys qimpl_wp_triple. clears Q; intros Q.
      applys rule_while_raw. remove_local. applys rule_if.
      { applys* IH. }
      { simpl. intros b. remove_local ;=> v' E. inverts E. case_if as C.
        { remove_local. applys rule_seq.
          { applys* IH. }
          { intros X. unfold R. apply triple_wp_triple. } }
        { remove_local. applys~ rule_val. } }
      { intros. applys~ wp_if_val_false. } }
    { apply triple_wp_triple. } }
  { rename v into x. remove_local. applys rule_for_trm.
    applys* IH. intros v1. esplit. split.
    applys* IH. intros v2. simpl.
    remove_local ;=> n1 n2 (E1&E2).
    invert E1. invert E2. intros _ _.
    set (S := fun i => weakestpre (triple (trm_for x i n2 t3))).
    apply rule_extract_hforall. exists S.
    apply rule_extract_hwand_hpure_l. split.
    { intros i. applys is_local_wp_triple. }
    { intros i. applys qimpl_wp_triple. clears Q; intros Q.
      applys rule_for_raw. case_if.
      { remove_local. applys rule_seq.
        { applys* IH. }
        { intros X. unfold S. apply triple_wp_triple. } }
      { remove_local. applys~ rule_val. } }
     { apply triple_wp_triple. } }
Qed.

Lemma triple_of_wp : forall (t:trm) H Q,
  H ==> wp t Q ->
  triple t H Q.
Proof using. introv M. xchanges M. applys triple_wp. Qed.

Lemma triple_trm_of_wp_iter : forall (n:nat) t H Q,
  H ==> func_iter n wp_def wp t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- wp_unfold_iter in M. applys* triple_of_wp.
Qed.

End WP2.



Module WP2Aux.
Import WP2.

Section LemmasCf.
Implicit Types n : nat.
Implicit Types F : val.
Implicit Types f x : var.

Lemma triple_apps_funs_of_wp_iter : forall n F (vs:vals) xs t H Q,
  F = val_funs xs t ->
  var_funs_exec (length vs) xs ->
  H ==> func_iter n wp_def wp (substn xs vs t) Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  applys* rule_apps_funs. applys* triple_trm_of_wp_iter.
Qed.

Lemma triple_apps_fixs_of_wp_iter : forall n f F (vs:vals) xs t H Q,
  F = val_fixs f xs t ->
  var_fixs_exec f (length vs) xs ->
  H ==> func_iter n wp_def wp (subst f F (substn xs vs t)) Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  applys* rule_apps_fixs. applys* triple_trm_of_wp_iter.
Qed.

End LemmasCf.

End WP2Aux.




Lemma triple_of_himpl_wp_triple : forall H Q t,
  H ==> wp_triple t Q ->
  triple t H Q.
Proof using.
  introv M. lets G: triple_wp_triple t Q.
  applys~ rule_consequence G.
Qed.


(** TODO: move somewhere else *)

Lemma rule_ramified_frame_htop_pre : forall t H Q Q',
  triple t H Q' ->
  triple t (H \* (Q' \---* Q \*+ \Top)) Q.
Proof using.
  introv M. applys local_ramified_frame_htop M.
  applys is_local_triple. hsimpl.
Qed.



Definition Weakestpre (T:forall `{Enc A},hprop->(A->hprop)->Prop) : Formula :=
  fun A (EA:Enc A) (Q:A->hprop) =>
    Hexists (H:hprop), H \* \[T H Q].


(* ********************************************************************** *)
(* * Size of a term *)

(* ---------------------------------------------------------------------- *)
(** Size of a term, where all values counting for one unit. *)

(* TODO: will be deprecated soon *)

Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fun x t1 => 1 + trm_size t1
  | trm_fix f x t1 => 1 + trm_size t1
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_seq t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_app t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  end.

Lemma trm_size_subst : forall t x v,
  trm_size (subst x v t) = trm_size t.
Proof using.
  intros. induction t; simpl; repeat case_if; auto.
Qed.

(** Hint for induction on size. Proves subgoals of the form
    [measure trm_size t1 t2], when [t1] and [t2] may have some
    structure or involve substitutions. *)

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_subst; math.

Hint Extern 1 (measure trm_size _ _) => solve_measure_trm_size tt.


(*
Fixpoint ctx_fresh (x:var) (E:ctx) : bool :=
  match E with
  | nil => true
  | (y,v)::E' => if var_eq x y then false else ctx_fresh x E'
  end.
*)



  (* deprecated
  | red_app_arg : forall m1 m2 m3 m4 t1 t2 v1 v2 r,
      (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_app v1 v2) m4 r ->
      red m1 (trm_app t1 t2) m4 r
  | red_app_fix : forall m1 m2 v1 v2 f x t r,
      red m1 (trm_app v1 v2) m2 r
   *)





(*
Definition trm_seq (t1:trm) (t2:trm) :=
  trm_let bind_anon t1 t2.

Definition trm_fun (x:var) (t1:trm) :=
  trm_fix bind_anon x t1.

Definition val_fun (x:var) (t1:trm) :=
  val_fix bind_anon x t1.
*)



(*
*)


(* todo deprecated
  Fixpoint trm_funs (xs:vars) (t:trm) : trm :=
    match xs with
    | nil => t
    | x::xs' => trm_fun x (trm_funs xs' t)
    end.

  Definition val_funs (xs:vars) (t:trm) : val :=
    match xs with
    | nil => arbitrary
    | x::xs' => val_fun x (trm_funs xs' t)
    end.
*)


Notation "'trm_seq' t1 t2" := (trm_let bind_anon t1 t2)
  (at level 69, t1 at level 0, t2 at level 0).

Notation "'trm_fun' x t1" := (trm_fix bind_anon x t1)
  (at level 69, x at level 0, t1 at level 0).

Notation "'val_fun' x t1" := (val_fix bind_anon x t1)
  (at level 69, x at level 0, t1 at level 0).

(* todo: deprecated
Lemma rule_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]) ->
  triple t2 (Q1 val_unit) Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  asserts E: (v1 = val_unit).
  { specializes M2 v1. applys not_not_inv. intros E.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange~ M2. hsimpl. }
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. }
    (* LATER: shorten this, and factorize with rule_if *)
  subst. forwards* (h2'&v2&R2&K2): (rm M3) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_seq R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.
*)


(** An alternative statement for [rule_seq]
todo deprecated

Lemma rule_seq' : forall t1 t2 H Q H1,
  triple t1 H (fun r => \[r = val_unit] \* H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_seq.
  { applys M1. }
  { intros v E. hpull; false. }
  { applys rule_extract_hprop. intros. applys M2. }
Qed.
*)


(* todo: deprecated *)
Definition is_val_unit (v:val) : Prop :=
  v = val_unit.

  (* LATER: introduce definitions

    is_post_unit Q :=
      (forall (v:val), v <> val_unit -> (Q1 v) ==> \[False]) ->

    is_post_bool Q :=
      (forall (v:val), v <> true -> v <> false -> (Q1 v) ==> \[False]) ->
  *)




Definition cf_seq (F1 F2:formula) : formula := fun H Q =>
  exists H1,
      F1 H (fun r => \[r = val_unit] \* H1)
   /\ F2 H1 Q.
(* TODO: TEMPORARY BROCKEN DUE TO SEMANTICS CHANGE *)

(* LATER: maybe use the following alternative, like in [LambdaCFLifted]:
  Definition cf_seq (F1 : formula) (F2 : formula) : formula := fun H Q =>
    exists Q1,
        F1 H Q1
     /\ F2 H1 Q
     /\  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]).
*)



Lemma substn_last : forall x xs v vs t,
  length xs = length vs ->
  substn (xs&x) (vs&v) t = subst1 x v (substn xs vs t).
Proof using.
  intros. unfold substn. rewrite~ combine_last.
  rew_ctx. rewrite~ subst_add. Qed.



(* DEPRECATED

Lemma subst_last : forall E x v t,
  subst (E & (x,v)) t = subst1 x v (subst E t).

Proof using.
  intros E. induction E as [|(x',v') E']; intros; rew_list.
  { rew_ctx. rewrite~ subst_empty. }
  {

 using list_ind_last; intros.
  { rew_ctx. rewrite~ subst_empty. }
  { destruct a as [x' v'].

 rew_list.  rew_list.
  { rewrite IHE'.

subst (rev (combine xs vs) & (x, v)) t =
subst (rev (combine xs vs)) (subst1 x v t)
*)

(* NEEDED in lambdawp:
subst (add x v E) t = subst1 x v (subst (rem x E) t)
*)

(*
Lemma subst1_subst_rem_same : forall E z v t,
    subst1 z v (subst (rem z E) t)
  = subst E (subst1 z v t).
Proof using.
  intros. rewrite <- subst_add.

  intros E. induction E as [|(y,w) E']; simpl; intros.
  { auto. }
  { rewrite var_eq_spec. case_if.
    { subst. rewrite IHE'. rewrite~ subst_subst_same. }
    { simpl. rewrite IHE'. rewrite~ subst_subst_neq. } }
Qed.

Admitted.

Lemma subst1_subst : forall x v E t,
  fresh x E ->
  subst1 x v (subst E t) = subst E (subst1 x v t).
Proof using.
  introv M. rewrite <- (@subst1_subst_rem_same E x v t).
  fequals. rewrite~ rem_fresh.
Qed.
*)

(*

  (** Substituting for [E] without [x] then substituting for [x]
      is equivalent to substituting for [x] then for [E]
      (even if [x] is bound in [E]). *)


  (** Substitutions for two distinct variables commute. *)

  Lemma subst1_subst1_neq : forall x1 x2 v1 v2 t,
    x1 <> x2 ->
    subst1 x2 v2 (subst1 x1 v1 t) = subst1 x1 v1 (subst1 x2 v2 t).
  Proof using.
    introv N. induction t; simpl; try solve [ fequals;
    repeat case_if; simpl; repeat case_if; auto ].
    repeat case_if; simpl; repeat case_if~.
    { false. destruct v; destruct x1; destruct x2; false. simpls.
      rewrite name_eq_spec in *. rew_bool_eq in *. false. }
  Qed. (* LATER: simplify *)

  (** Substituting for a variable that has just been substituted
      does not further modify the term. *)

  Lemma subst_subst_same : forall x v1 v2 t,
    subst1 x v2 (subst1 x v1 t) = subst1 x v1 t.
  Proof using.
    intros. induction t; simpl; try solve [ fequals;
    repeat case_if; simpl; repeat case_if; auto ].
  Qed.
*)




(** Auxiliary results for freshness of bindings w.r.t. combine *)


(*
Lemma fresh_combine : forall x ys vs,
  var_fresh x ys ->
  length ys = length vs ->
  Ctx.fresh x (LibList.combine ys vs).
Proof using.
  intros x ys. unfold Ctx.fresh.
  induction ys as [|y ys']; simpl; intros [|v vs] M L;
   rew_list in *; try solve [ false; math ].
  { auto. }
  { simpl. rewrite var_eq_spec in *. do 2 case_if. rewrite~ IHys'. }
Qed.

(* Permutation lemma for substitution and n-ary substitution *)

Lemma subst_substn : forall x v ys ws t,
  var_fresh x ys ->
  length ys = length ws ->
  subst1 x v (substn ys ws t) = substn ys ws (subst1 x v t).
Proof using.
  introv M L. unfold substn. rewrite~ subst1_subst.
  applys~ fresh_combine.
Qed.

*)

(*
Lemma red_app_fixs_val : forall xs (vs:vals) m1 m2 tf (vf:val) (f:var) t r,
  red m1 tf m1 vf ->
  vf = val_fixs f xs t ->
  red m1 (substn (f::xs) (vf::vs) t) m2 r ->
  var_fixs f (length vs) xs ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  introv M1 EQ M2 (F&L&N). gen tf t r m1 m2 F N. list2_ind~ xs vs; intros.
  (* LATER: replace list2_ind by list2_inv *)
  { false. }
  { rename xs1 into xs', x1 into x1, x2 into v1, xs2 into vs'. clear H0.
    simpl in F. rew_istrue in F. destruct F as (F1&F').
    tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'.
      simpls. applys* red_app. applys* red_val. applys* M2. }
    { subst vf. applys red_app. applys~ red_app_funs_val_ind.
      { applys red_val. eauto. applys* red_app_fix. do 2 rewrite~ subst_trm_funs. applys~ red_funs. }
      { rewrite~ subst_substn in M. { rewrite~ substn_cons in M.
        rewrite~ subst_subst_neq. } { simpl. case_if~. } }
      { splits*. } } }

do 2 rewrite substn_cons in M2. applys~ IH M2. applys* red_app.
      { applys* red_val. }
      { simpl. unfold subst2. simpl. rew_ctx.
        rewrite subst_add. rewrite subst_empty.
        rewrite~ subst_trm_funs. applys~ red_funs. } } }
Qed.
*)



Lemma rem_rem_neq : forall z1 z2 E,
  Ctx.rem z1 (Ctx.rem z2 E) = Ctx.rem z2 (Ctx.rem z1 E).
Proof using. (*

  introv M. unfold rem. induction E as [|(y,v) E'].
  { auto. }
  { simpls. lets (N1&N2): fresh_inv (rm M).
    rewrite var_eq_spec in *. case_if. rewrite~ IHE'. }
*) admit.
Qed.



  | red_add : forall m n1 n2 n',
      n' = n1 + n2 ->
      red m (val_add (val_int n1) (val_int n2)) m (val_int n')
  | red_sub : forall m n1 n2 n',
      n' = n1 - n2 ->
      red m (val_sub (val_int n1) (val_int n2)) m (val_int n')
  | red_ptr_add : forall l' m l n,
      (l':nat) = (l:nat) + n :> int ->
      red m (val_ptr_add (val_loc l) (val_int n)) m (val_loc l')
  | red_eq : forall m v1 v2,
      red m (val_eq v1 v2) m (val_bool (isTrue (v1 = v2)))




(*
Lemma hoare_consequence_post : forall t Q' H Q,
  hoare t H Q' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  intros. applys* hoare_consequence.
Qed.
*)




(** Tactic to apply hoare rules modulo consequence *)

Ltac hoare_apply_core M :=
  applys hoare_consequence M; try solve [ hsimpl.

Tactic Notation "hoare_apply" constr(M) :=
  hoare_apply_core M.
Tactic Notation "hoare_apply" "~" constr(M) :=
  hoare_apply_core M; auto_tilde.
Tactic Notation "hoare_apply" "*" constr(M) :=
  hoare_apply_core M; auto_star.



(** Derived rule integrating the case analysis on whether iterations
    are performed on not *)

Lemma rule_for : forall (x:var) (n1 n2:int) t3 H Q,
  (If (n1 <= n2) then
    (exists Q1,
      triple (subst1 x n1 t3) H Q1 /\
      (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q))
  else
    (H ==> Q val_unit)) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. case_if.
  { destruct M. applys* rule_for_le. }
  { xapplys* rule_for_gt. { math. } hchanges* M. }
Qed.







(** Rules for for-loop not in normal form *)

Lemma rule_for_trm : forall (x:var) (t1 t2 t3:trm) H (Q:val->hprop) (Q1:val->hprop),
  triple t1 H Q1 ->
  (forall v1, exists Q2,
      triple t2 (Q1 v1) Q2
   /\ (forall v2, triple (trm_for x v1 v2 t3) (Q2 v2) Q)) ->
  triple (trm_for x t1 t2 t3) H Q.
Proof using.
  introv M1 M2. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  lets (Q2&M2'&M3): ((rm M2) v1).
  forwards* (h2'&v2&R2&K2): (rm M2') h1'.
  rewrite <- (hstar_assoc \Top \Top) in K2. rewrite htop_hstar_htop in K2.
  forwards* (h'&v'&R'&K'): ((rm M3) v2) h2'.
  exists h' v'. splits~.
  { applys* red_for_arg. }
  { rewrite <- htop_hstar_htop. rew_heap~. }
Qed.

Definition is_val_int (v:val) :=
  exists n, v = val_int n.

(* full rule, too complex *)
Lemma rule_for_trm_int : forall (x:var) (t1 t2 t3:trm) H (Q:val->hprop) (Q1:val->hprop),
  triple t1 H Q1 ->
  (forall v, ~ is_val_int v -> (Q1 v) ==> \[False]) ->
  (forall (n1:int), exists Q2,
      triple t2 (Q1 (val_int n1)) Q2
   /\ (forall v, ~ is_val_int v -> (Q2 v) ==> \[False])
   /\ (forall (n2:int), triple (trm_for x n1 n2 t3) (Q2 (val_int n2)) Q)) ->
  triple (trm_for x t1 t2 t3) H Q.
Proof using. (* might be simplified using rule_for_trm *)
  introv M1 nQ1 M2. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  tests C1: (is_val_int v1).
  { destruct C1 as (n1&E). subst. lets (Q2&M2'&nQ2&M3): ((rm M2) n1).
    forwards* (h2'&v2&R2&K2): (rm M2') h1'.
    rewrite <- (hstar_assoc \Top \Top) in K2. rewrite htop_hstar_htop in K2.
    tests C2: (is_val_int v2).
    { destruct C2 as (n2&E). subst.
      forwards* (h'&v'&R'&K'): ((rm M3) n2) h2'.
      exists h' v'. splits~.
      { applys* red_for_arg. }
      { rewrite <- htop_hstar_htop. rew_heap~. } }
    { specializes nQ2 C2.
      asserts Z: ((\[False] \* \Top \* HF) h2').
      { applys himpl_trans K2. hchange nQ2. hsimpl. hsimpl. }
      repeat rewrite hfalse_hstar_any in Z.
      lets: hpure_inv Z. false*. } } (* LATER: shorten *)
  { specializes nQ1 C1.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange nQ1. hsimpl. hsimpl. }
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. } (* LATER: shorten *)
Qed.








(* DEPRECATEd
Lemma Triple_fun : forall x t1 H (Q:func->hprop),
  H ==> Q (val_fun x t1) ->
  Triple (trm_fun x t1) H Q.
Proof using.
  introv M. applys triple_fun. unfold Post. hsimpl*.
Qed.
*)





(* ********************************************************************** *)
(* * Tactics for progressing through proofs *)

(** Extends tactics defined in [LambdaCFTactics.v] *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_from_goal tt ::=
  match goal with |- triple ?t _ _ => xcf_get_fun_from_trm t end.

Ltac xcf_post tt :=
  simpl.

Ltac xcf_trm n ::= (* for WP2 *)
 (*  applys triple_trm_of_wp_iter n; [ xcf_post tt ]. *) fail.


Ltac xcf_basic_fun n f' ::= (* for WP2 *)
  let f := xcf_get_fun tt in
  match f with
(*
  | val_funs _ _ => (* TODO: use (apply (@..)) instead of applys? same in cflifted *)
      applys triple_apps_funs_of_wp_iter;
      [ reflexivity | reflexivity | xcf_post tt ]
*)
  | val_fixs _ _ _ =>
      applys triple_apps_fixs_of_wp_iter f';
      [ try unfold f'; rew_nary; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | reflexivity
      | xcf_post tt ]

  end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] *)

Ltac xlocal' :=
  try solve [ apply is_local_local ].
  (*   | apply is_local_wp_triple ]. *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Lemma xlet_lemma : forall Q1 (F1:formula) (F2:val->formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> wp_let F1 F2 Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.

Ltac xlet_core tt ::=
  applys xlet_lemma; [ xlocal' | | ].


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Lemma xapp_lemma : forall t H Q,
  triple t H Q ->
  H ==> (wp_app t) Q.
Proof using.
  introv M. applys local_erase'. unfold wp_triple, weakestpre. hsimpl~ H.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.


(* ---------------------------------------------------------------------- *)
(* ** Example proof of the [incr] function *)

Module Test.
Import NotationForVariables NotationForTerms.
Open Scope trm_scope.

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (val_incr p)
    (p ~~~> n)
    (fun r => p ~~~> (n+1)).
Proof using.
admit.
(*
  intros. xcf.
  xlet. { xapp. xapplys triple_get. }
  intros x. hpull ;=> E. subst.
  xlet. { xapp. xapplys triple_add. }
  intros y. hpull ;=> E. subst.
  xapp. xapplys triple_set.
*)
Qed.

End Test.



(* ---------------------------------------------------------------------- *)
(** ** Database of lemmas *)

(** We here use the notation [Register] and [Provide] from the TLC library.

  Usage of [RegisterSpecGoal], e.g.:

    Hint Extern 1 (RegisterSpecGoal (triple (trm_app2_val (val_prim val_eq) ?x ?y) ?H ?Q)) =>
      Provide triple_eq.

  Usage of [RegisterSpecApp], e.g.:

    Hint Extern 1 (RegisterSpecApp (trm_app2_val (val_prim val_eq) ?x ?y)) =>
      Provide triple_eq.

*)

Notation "'Register_rule' t" := (Register_goal (triple t _ _))
  (at level 69) : charac.

Notation "'Register_spec' f" := (Register_rule (trm_apps (trm_val f) _))
  (at level 69) : charac.


(* ---------------------------------------------------------------------- *)
(** ** Registering specification of primitive functions *)

Hint Extern 1 (Register_spec (val_prim val_ref)) => Provide triple_ref.
Hint Extern 1 (Register_spec (val_prim val_get)) => Provide triple_get.
Hint Extern 1 (Register_spec (val_prim val_set)) => Provide triple_set.
Hint Extern 1 (Register_spec (val_prim val_alloc)) => Provide triple_alloc.
Hint Extern 1 (Register_spec (val_prim val_eq)) => Provide triple_eq.
Hint Extern 1 (Register_spec (val_prim val_add)) => Provide triple_add.
Hint Extern 1 (Register_spec (val_prim val_sub)) => Provide triple_sub.
Hint Extern 1 (Register_spec (val_prim val_ptr_add)) => Provide triple_ptr_add.




(* ********************************************************************** *)
(* * Practical proofs using characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for computd WP *)

Notation "'`Val' v" :=
  ((wp_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  ((wp_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  ((wp_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;;; F2" :=
  ((wp_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((wp_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  ((wp_app t))
  (at level 68, t at level 0) : charac.

Notation "'`Fail'" :=
  ((wp_fail))
  (at level 69) : charac.

Notation "'`While' F1 'Do' F2 'Done'" :=
  ((wp_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' '`While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : charac.

(* TODO
Notation "'`For' x '=' v1 'To' v2 'Do' F3 'Done'" :=
  ((wp_for v1 v2 (fun x => F3)))
  (at level 69, x ident, (* t1 at level 0, t2 at level 0, *)
   format "'[v' '`For'  x  '='  v1  'To'  v2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : charac.
*)

Open Scope charac.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

(*
Lemma triple_apps_funs_of_wp_iter : forall F (vs:vals) xs t H Q,
  F = val_funs xs t ->
  var_funs_exec (length vs) xs ->
  H ==> wp (LibList.combine xs vs) t Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  lets (_&L&_): N. applys* triple_apps_funs.
  applys* triple_subst_of_wp.
Qed.
*)

Lemma triple_apps_fixs_of_wp_iter : forall (f:var) F (vs:vals) xs t H Q,
  F = val_fixs f xs t ->
  var_fixs_exec f (length vs) xs ->
  H ==> wp (LibList.combine (f::xs) (F::vs)) t Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  lets (D&L&_): N. simpl in D. rew_istrue in D. destruct D as [D1 D2].
Admitted.
(* todo
  applys* triple_apps_fixs. rewrite~ subst_substn.
  applys* triple_subst_of_wp M.
Qed.
*)





(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* LATER

Definition wp_for (F1 F2:formula) (F3:int->formula) : formula :=
  wp_let F1 (fun v1 => wp_let F2 (fun v2 => wp_for_val v1 v2 F3)).
Definition wp_for' (F1 F2:formula) (F3:int->formula) : formula := local (fun Q =>
  F1 (fun v1 => F2 (fun v2 => wp_for_val v1 v2 F3 Q))).
*)



(* ********************************************************************** *)
(* * Example proof *)



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Lemma xapp_lemma : forall t H Q,
  triple t H Q ->
  H ==> (wp_app t) Q.
Proof using.
  introv M. applys local_erase'. unfold wp_triple, weakestpre. hsimpl~ H.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.


(* ---------------------------------------------------------------------- *)
(* ** Example proof of the [incr] function *)

Module Test.
Import NotationForVariables NotationForTerms.
Open Scope trm_scope.

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (val_incr p)
    (p ~~~> n)
    (fun r => p ~~~> (n+1)).
Proof using.
admit.
(*
  intros. xcf.
  xlet. { xapp. xapplys triple_get. }
  intros x. hpull ;=> E. subst.
  xlet. { xapp. xapplys triple_add. }
  intros y. hpull ;=> E. subst.
  xapp. xapplys triple_set.
*)
Qed.

End Test.


(** Extends tactics defined in [LambdaCFTactics.v] *)





(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] demo

Lemma xlet_lemma : forall Q1 (F1:formula) (F2:val->formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> wp_let F1 F2 Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.

Ltac xlet_core tt ::=
  applys xlet_lemma; [ xlocal' | | ].

*)


