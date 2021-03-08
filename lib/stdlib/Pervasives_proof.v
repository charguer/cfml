Set Implicit Arguments.
Require Import CFLib.
Require Import Pervasives_ml.
Generalizable Variable A.


(* TODO: add PRE/POST notation *)

(************************************************************)
(** Boolean *)

Lemma not_spec : forall (a:bool),
  app not [a] \[] \[= !a ].
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

Parameter infix_eq_eq_loc_spec : curried 2%nat infix_eq_eq__ /\
  forall (a b:loc),
  app infix_eq_eq__ [a b] \[] \[= isTrue (a = b) ].

Parameter infix_eq_eq_gen_spec : curried 2%nat infix_eq_eq__ /\
  forall (A:Type) (a b:A),
  app infix_eq_eq__ [a b] \[] (fun r => \[r = true -> isTrue (a = b)]).

Hint Extern 1 (RegisterSpec infix_eq_eq__) => Provide infix_eq_eq_loc_spec.

Lemma infix_emark_eq_loc_spec : curried 2%nat infix_emark_eq__ /\
  forall (a b:loc),
  app infix_emark_eq__ [a b] \[] \[= isTrue (a <> b) ].
Proof using.
  xcf. xgo*. rew_isTrue; xauto*.
Qed.

Lemma infix_emark_eq_gen_spec : curried 2%nat infix_emark_eq__ /\
  forall (A:Type) (a b:A),
  app infix_emark_eq__ [a b] \[] (fun r => \[r = false -> isTrue (a = b)]).
Proof using.
  xcf. xapp_spec infix_eq_eq_gen_spec.
  introv E. xrets~.
Qed.

Hint Extern 1 (RegisterSpec infix_emark_eq__) => Provide infix_emark_eq_loc_spec.


(************************************************************)
(** Comparison *)

Parameter infix_eq_spec : curried 2%nat infix_eq__ /\
  forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  app infix_eq__ [a b] \[] \[= isTrue (a = b) ].

Hint Extern 1 (RegisterSpec infix_eq__) => Provide infix_eq_spec.

Parameter infix_neq_spec : curried 2%nat infix_eq__ /\
  forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  app infix_lt_gt__ [a b] \[] \[= isTrue (a <> b) ].

Hint Extern 1 (RegisterSpec infix_lt_gt__) => Provide infix_neq_spec.

Lemma min_spec : forall (n m:int),
  app min [n m] \[] \[= Z.min n m ].
Proof using.
  xcf. xgo*.
  { rewrite~ Z.min_l. }
  { rewrite~ Z.min_r. math. }
Qed.

Lemma max_spec : forall (n m:int),
  app max [n m] \[] \[= Z.max n m ].
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
  app infix_bar_bar__ [a b] \[] \[= a && b ].

Parameter infix_amp_amp_spec : forall (a b:bool),
  app infix_amp_amp__ [a b] \[] \[= a || b ].

Hint Extern 1 (RegisterSpec infix_bar_bar__) => Provide infix_bar_bar_spec.
Hint Extern 1 (RegisterSpec infix_amp_amp__) => Provide infix_amp_amp_spec.


(************************************************************)
(** Integer *)

Parameter infix_tilde_minus_spec : curried 1%nat infix_tilde_minus__ /\
  forall (n:int),
  app infix_tilde_minus__ [n] \[] \[= Z.opp n ].

Parameter infix_plus_spec : curried 2%nat infix_plus__ /\
  forall (n m:int),
  app infix_plus__ [n m] \[] \[= Z.add n m ].

Parameter infix_minus_spec : curried 2%nat infix_minus__ /\
  forall (n m:int),
  app infix_minus__ [n m] \[] \[= Z.sub n m ].

Parameter infix_star_spec : curried 2%nat infix_star__ /\
  forall (n m:int),
  app infix_star__ [n m] \[] \[= Z.mul n m ].

Parameter infix_slash_spec : curried 2%nat infix_slash__ /\
  forall (n m:int),
  m <> 0 ->
  app infix_slash__ [n m] \[] \[= Z.quot n m ].

Parameter mod_spec : curried 2%nat Pervasives_ml.mod /\ forall (n m:int),
  m <> 0 ->
  app Pervasives_ml.mod [n m] \[] \[= Z.rem n m ].

Hint Extern 1 (RegisterSpec infix_tilde_minus__) => Provide infix_tilde_minus_spec.
Hint Extern 1 (RegisterSpec infix_plus__) => Provide infix_plus_spec.
Hint Extern 1 (RegisterSpec infix_minus__) => Provide infix_minus_spec.
Hint Extern 1 (RegisterSpec infix_star__) => Provide infix_star_spec.
Hint Extern 1 (RegisterSpec infix_slash__) => Provide infix_slash_spec.
Hint Extern 1 (RegisterSpec Pervasives_ml.mod) => Provide mod_spec.

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
  app succ [n] \[] \[= n+1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma pred_spec : forall (n:int),
  app pred [n] \[] \[= n-1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma abs_spec : forall (n:int),
  app Pervasives_ml.abs [n] \[] \[= Z.abs n ].
Proof using.
  xcf. xgo.
  { rewrite~ Z.abs_eq. }
  { rewrite~ Z.abs_neq. math. }
Qed.

Hint Extern 1 (RegisterSpec succ) => Provide succ_spec.
Hint Extern 1 (RegisterSpec pred) => Provide pred_spec.
Hint Extern 1 (RegisterSpec abs) => Provide abs_spec.


(************************************************************)
(** Bit-level Integer *)

(* TODO: check *)

Parameter land_spec : curried 2%nat land /\ forall (n m:int),
  app land [n m] \[] \[= Z.land n m ].

Parameter lor_spec : curried 2%nat lor /\ forall (n m:int),
  app lor [n m] \[] \[= Z.lor n m ].

Parameter lxor_spec : curried 2%nat lxor /\ forall (n m:int),
  app lxor [n m] \[] \[= Z.lxor n m ].

Definition Zlnot (x : Z) : Z := -(x + 1).

Parameter lnot_spec : curried 1%nat lnot /\ forall (n:int),
  app lnot [n] \[] \[= Zlnot n ].

Parameter lsl_spec : curried 2%nat lsl /\ forall (n m:int),
  0 <= m ->   (* y < Sys.word_size -> *)
  app lsl [n m] \[] \[= Z.shiftl n m ].

  (* TODO We temporarily? restrict [lsr] to nonnegative integers,
     so it behaves like [asr]. Anyway, [lsr] really operates
     on unsigned integers, and this notion is missing in CFML. *)

Parameter lsr_spec : curried 2%nat lsr /\ forall (n m:int),
  0 <= n ->
  0 <= m ->
  (* m < Sys.word_size -> *)
  app lsr [n m] \[] \[= Z.shiftr n m ].

Parameter asr_spec : curried 2%nat asr /\ forall (n m:int),
  0 <= m ->
  (* m < Sys.word_size -> *)
  app asr [n m] \[] \[= Z.shiftr n m ].

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

Definition Ref {A} (v:A) (r:loc) :=
  r ~> `{ contents' := v }.

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

Notation "r '~~>' v" := (hdata (Ref v) r)
  (at level 32, no associativity) : heap_scope.

Lemma affine_Ref : forall A r (v: A), affine (r ~~> v).
Proof. intros. unfold Ref, hdata. affine. Qed.

Hint Resolve affine_Ref : affine.

(* Expose that [ref_ A] (defined in Pervasives_ml) is defined as [loc] *)
Hint Transparent ref_ : affine.

Lemma ref_spec : forall A (v:A),
  app ref [v]
    PRE \[]
    POST (fun r => r ~~> v).
Proof using. xcf_go~. Qed.

Lemma infix_emark_spec : forall A (v:A) r,
  app infix_emark__ [r]
    INV (r ~~> v)
    POST \[= v].
Proof using. xunfold @Ref. xcf_go~. Qed.

Lemma infix_colon_eq_spec : forall A (v w:A) r,
  app infix_colon_eq__ [r w] (r ~~> v) (# r ~~> w).
Proof using. xunfold @Ref. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ref) => Provide ref_spec.
Hint Extern 1 (RegisterSpec infix_emark__) => Provide infix_emark_spec.
Hint Extern 1 (RegisterSpec infix_colon_eq__) => Provide infix_colon_eq_spec.

Notation "'App'' `! r" := (App infix_emark__ r;)
  (at level 69, no associativity, r at level 0,
   format "'App''  `! r") : charac.

Notation "'App'' r `:= x" := (App infix_colon_eq__ r x;)
  (at level 69, no associativity, r at level 0,
   format "'App''  r  `:=  x") : charac.

Lemma incr_spec : forall (n:int) r,
  app incr [r]
    PRE (r ~~> n)
    POST (# r ~~> (n+1)).
Proof using. xcf_go~. Qed.

Lemma decr_spec : forall (n:int) r,
  app decr [r]
    PRE (r ~~> n)
    POST (# r ~~> (n-1)).
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.
Hint Extern 1 (RegisterSpec decr) => Provide decr_spec.



(************************************************************)
(** Group of References *)

Axiom ref_spec_group : forall A (M:map loc A) (v:A),
  app Pervasives_ml.ref [v]
    PRE (Group Ref M)
    POST (fun (r:loc) => Group Ref (M[r:=v]) \* \[r \notindom M]).
(* TODO: proof *)

Lemma infix_emark_spec_group : forall `{Inhab A} (M:map loc A) r,
  r \indom M ->
  app Pervasives_ml.infix_emark__ [r]
    INV (Group Ref M)
    POST (fun x => \[x = M[r]]).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. xsimpl~.
Qed.

Lemma infix_colon_eq_spec_group : forall `{Inhab A} (M:map loc A) (v:A) r,
  r \indom M ->
  app Pervasives_ml.infix_colon_eq__ [r v]
    PRE (Group Ref M)
    POST (# Group Ref (M[r:=v])).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. intros tt.
  hchanges~ (Group_add' r M).
Qed.


(************************************************************)
(** Pairs *)

Lemma fst_spec : forall A B (x:A) (y:B),
  app fst [(x,y)]
    PRE \[]
    POST \[= x].
Proof using. xcf_go~. Qed.

Lemma snd_spec : forall A B (x:A) (y:B),
  app snd [(x,y)]
    PRE \[]
    POST \[= y].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec fst) => Provide fst_spec.
Hint Extern 1 (RegisterSpec snd) => Provide snd_spec.


(************************************************************)
(** Unit *)

Lemma ignore_spec :
  app ignore [tt]
    PRE \[]
    POST \[= tt].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ignore) => Provide ignore_spec.


(************************************************************)
(** Float *)

(* TODO *)





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



