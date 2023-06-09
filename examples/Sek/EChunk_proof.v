Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib Array_proof.
From TLC Require Import LibListZ.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

Require Import EChunk_ml.



(* Copy-paste of earlier definitions to work around a notation bug in Coq *)

Notation "<[ e ]>" :=
 e
 (at level 0, e custom wp at level 99) : wp_scope.

Notation "'Pay' F" :=
 ((*Wptag*) (Wpgen_pay F))
 (in custom wp at level 69, F at level 0) : wp_scope.

Notation "'Fail'" :=
 ((*Wptag*) (Wpgen_fail))
 (in custom wp at level 69) : wp_scope.

Notation "'Done'" :=
 ((*Wptag*) (Wpgen_done))
 (in custom wp at level 69) : wp_scope.

Notation "'Match' V F1" :=
 ((*Wptag*) (Wpgen_match V F1))
 (in custom wp at level 69,
  V custom wp at level 0,
  F1 custom wp at level 69,
  format "'[v' 'Match'  V  '/' '['   F1 ']' ']' " ) : wp_scope.

Notation "'Assert' F" :=
 ((*Wptag*) (Wpgen_assert F))
 (in custom wp at level 69,
  F custom wp at level 99) : wp_scope.

Notation "'Val' v" :=
 ((*Wptag*) (Wpgen_val v))
 (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
 ((*Wptag*) (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetVal' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_let_val V (fun x => F1)))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'LetVal'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Alias' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_alias (Wpgen_let_val V (fun x => F1))))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Alias'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Seq' F1 ; F2" :=
 ((*Wptag*) (Wpgen_seq F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' f x1 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) .. (cons (Dyn xn) nil) ..)))
  (in custom wp at level 68,
   f constr at level 0,
   x1 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.

(* TODO: why need both? *)
Notation "'App' f x1 x2 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..))))
  (in custom wp at level 68,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_if v F1 F2))
 (in custom wp at level 69,
  v constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
 ((*Wptag*) (Wpgen_while F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  format "'[v' '[' 'While'  F1  'Do'  ']' '/' '['   F2 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'To' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'To'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'Downto' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_downto_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'Downto'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'LetFun' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  f ident,
  B1 constr at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.




(*************************************************)
(** EChunks *)

Notation "'K'" := capacity.

Definition Wrap_up i := If i >= K then i - K else i.
Definition Wrap_down i := If i < 0 then i + K else i.

Record EChunk_inv A {IA: Inhab A} (L: list A) (D: list A) (front: int) (size: int) (default: A) : Prop :=
	mkEChunk_inv {
		echunk_in : forall (i: int), 0 <= i < size -> D[Wrap_up (front + i)] = L[i];
		echunk_out : forall (i: int), size <= i < K -> D[Wrap_up (front + i)] = default;
		echunk_length : length L = size;
		echunk_capa : length D = K;
		echunk_front : 0 <= front < K;
		echunk_size : 0 <= size <= K }.

Definition EChunk A {IA: Inhab A} {EA: Enc A} (L: list A) (c: echunk_ A) : hprop :=
  \exists (data: loc) (D: list A) (front: int) (size: int) (default: A),
  	c ~~~> `{ data' := data; front' := front; size' := size; default' := default }
 		\* data ~> Array D
  	\* \[EChunk_inv L D front size default].

Lemma haffine_Echunk : forall A (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
    haffine (c ~> EChunk L).
Proof.
  intros.
  xunfold EChunk. (* Later : géré par xaffine *)
  xaffine.
Qed.

Lemma haffine_repr_Echunk : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@EChunk A IA EA).
Proof. intros. intros ? ?. apply haffine_Echunk. Qed.

Hint Resolve haffine_Echunk haffine_repr_Echunk : haffine.

Lemma EChunk_eq : forall c A {IA: Inhab A} {EA: Enc A} (L: list A),
  c ~> EChunk L =
  \exists (data: loc) (D: list A) (front: int) (size: int) (default: A),
    c ~~~> `{ data' := data; front' := front; size' := size; default' := default }
  	\* data ~> Array D
  	\* \[EChunk_inv L D front size default].
Proof. auto. Qed.

Hint Extern 1 (RegisterOpen EChunk) => Provide EChunk_eq.

Lemma echunk_inv_length : forall A (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
  c ~> EChunk L ==+> \[0 <= length L <= K].
Proof.
  intros.
  xopen c. introv Hc. lets []: Hc.
  xclose* c. xsimpl*.
Qed.

Definition IsFull A (c:list A) : Prop :=
  length c = K.

Lemma capacity_spec :
  capacity > 0.
Proof. rewrite capacity_cf__; math. Qed.

Lemma NotFull_of_nil : forall A,
  ~ IsFull (@nil A).
Proof.
  hint capacity_spec.
  intros. unfold IsFull. rew_list*.
Qed.

Hint Extern 1 (@le _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@lt _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@ge _ _ capacity _) => hint capacity_spec; math.
Hint Extern 1 (@gt _ _ capacity _) => hint capacity_spec; math.

(*************************************************)
(** Specifications *)

Lemma wrap_up_spec : forall (n: int),
	SPEC (wrap_up n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_up n]).
Proof.
	xcf. unfold Wrap_up.
	xpay.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_up) => Provide wrap_up_spec.

Lemma wrap_down_spec : forall (n: int),
	SPEC (wrap_down n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_down n]).
Proof.
	xcf. unfold Wrap_down.
	xpay.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_down) => Provide wrap_down_spec.

Lemma echunk_create_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (a: A),
  SPEC (echunk_create a)
    PRE (\$(K + 1))
    POST (fun c => c ~> EChunk (@nil A)).
Proof.
  xcf. xpay. xapp*. intros d L Hd.
  xapp*. intros r.
  xunfolds* EChunk.
  { constructors*; subst*; intros.
    { false. math. }
    { rew_listp*. unfolds Wrap_up. case_if*. }
    { rew_listp*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_is_empty_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_empty c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[ b = isTrue (L = nil)]).
Proof.
  xcf*.
  xopen c; introv Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. xvals*. subst*.
  now rewrite* length_zero_eq_eq_nil. (* now? *)
Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_is_full_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_full c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[b = isTrue (IsFull L)]).
Proof.
  xcf*.
	xopen c; introv Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. xvals*.
Qed.

Hint Extern 1 (RegisterSpec echunk_is_full) => Provide echunk_is_full_spec.

Lemma plus_minus : forall a b c,
	a + (b - c) = a + b - c.
Proof using. math. Qed.

(** [rew_maths] rewrite any lemma in the base [rew_maths].
    The goal should not contain any evar, otherwise tactic might loop. *)

#[global]
Hint Rewrite plus_minus: rew_maths.

Lemma echunk_peek_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  L <> nil ->
  SPEC (echunk_peek_back c)
    PRE (\$2)
    INV (c ~> EChunk L)
    POST (fun x => \exists L', \[L = L' & x]).
Proof.	
  introv HL.
  xcf*.
	lets (x & q & ->): list_neq_nil_inv_last L HL.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xpay. xappn*.
	{ unfolds* Wrap_up. }
	{ rew_list in *.
		xsimpl.
		{ fequals_rec.
			forwards* E: Iin (size - 1).
			rew_array in E. case_if; try math. rew_maths. auto. }
		{ xclose* c.
			xsimpl. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_peek_back) => Provide echunk_peek_back_spec.

Lemma echunk_pop_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  L <> nil -> 
  SPEC (echunk_pop_back c)
    PRE (\$4 \* c ~> EChunk L)
    POST (fun x => \exists L', c ~> EChunk L' \* \[L = L' & x]).
Proof.
  introv HL.
  xcf.
	lets (x & q & ->): list_neq_nil_inv_last L HL.
	xpay. xapp*. introv E. apply last_eq_last_inv in E as [E_q E_x]. rewrites <- E_x.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xapp*. xlets. xappn*.
	{ unfolds* Wrap_up. }
	{ rew_list in *.
		xvals*. xclose* c q.
		{ constructors*; intros i Hi.
			{ applys_eq* Iin; list_cases*.
				{ false.
					unfold Wrap_up in C.
					case_if* in C; case_if* in C. rew_maths. math. }
				{ unfolds* Wrap_up. } }
			{ list_cases*.
				{ applys_eq Iout.
					unfold Wrap_up in C.
					case_if* in C; case_if* in C. }
				{ unfolds* Wrap_up. } } }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_pop_back) => Provide echunk_pop_back_spec.

Lemma echunk_push_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (x: A) (L: list A),
  ~ (IsFull L) ->
  SPEC (echunk_push_back c x)
    PRE (\$2 \* c ~> EChunk L)
    POSTUNIT (c ~> EChunk (L & x)).
Proof.
  introv HL. unfolds IsFull.
  xcf.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
  xpay. xappn*.
	{ unfolds* Wrap_up. }
	{ xclose* c (L & x).
		{ constructors*; intros i Hi.
			{ list_cases*; unfolds* Wrap_up; false.
				{ case_if* in C0; case_if* in C0; rew_maths. }
				{ case_if* in C1; case_if* in C1; rew_maths. } }
			{ list_cases*; unfolds* Wrap_up; false.
				{ case_if* in C; case_if* in C; rew_maths. } } }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_push_back) => Provide echunk_push_back_spec.

Axiom Array_copy_spec : forall (A:Type) (EA:Enc A) (a:array A) (xs:list A),
  SPEC (Array_ml.copy a)
    PRE (\$(length xs))
    INV (a ~> Array xs)
    POST (fun a' => a' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide Array_copy_spec.

Lemma echunk_copy_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (c:echunk_ A) (L:list A),
  SPEC (echunk_copy c)
    PRE (\$(1 + K))
    INV (c ~> EChunk L)
    POST (fun c' => c' ~> EChunk L).
Proof.
  intros.
  xcf. xpay_pre; xsimpl.
  xopen c; introv Inv.
  xappn. intros.
  xappn*. intros c'.
  xclose* c. xclose_repr* EChunk_eq c'.
  destruct Inv.
  xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec echunk_copy) => Provide echunk_copy_spec.

Global Instance Heapdata_echunk : forall A {IA} {EA}, Heapdata (@EChunk A IA EA).
Proof.
  intros.
  apply Heapdata_intro; intros x L1 L2.
  do 2 (xopen_repr EChunk_eq x; intros).
  xchange* (Heapdata_record x).
Qed.

Hint Resolve Heapdata_echunk : core.

(*Ltac clever T :=
  intros; match goal with
    H: context [ T[_] ] |- context [ ?U[?i] ] => forwards: H i; try math end;
  list_cases in *; rew_int in *; auto_star; try congruence.*)
