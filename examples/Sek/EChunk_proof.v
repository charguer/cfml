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

Record EChunk_inv A {IA:Inhab A} (L:list A) (D:list A) (top:int) (default:A) : Prop :=
  mkEChunk_inv
    { echunk_front : forall (i:int), 0 <= i < top -> D[i] = L[top - 1 - i];
      echunk_tail : forall (i:int), top <= i < K -> D[i] = default;
      echunk_length : length L = top;
      echunk_capa : length D = K;
      echunk_top : 0 <= top <= K }.

Definition EChunk A {IA:Inhab A} {EA:Enc A} (L:list A) (c:echunk_ A) : hprop :=
  \exists (data:loc) (D:list A) (top:int) (default:A),
      c ~~~> `{ data' := data; top' := top; default' := default }
   \* data ~> Array D
   \* \[EChunk_inv L D top default].

Lemma haffine_Echunk : forall A (IA:Inhab A) (EA:Enc A) (L:list A) (c:echunk_ A),
    haffine (c ~> EChunk L).
Proof.
  intros.
  xunfold EChunk.
  xaffine.
Qed.

Lemma haffine_repr_Echunk : forall A (IA:Inhab A) (EA:Enc A),
    haffine_repr (@EChunk A IA EA).
Proof. intros. intros ? ?. apply haffine_Echunk. Qed.

Hint Resolve haffine_Echunk haffine_repr_Echunk : haffine.

Lemma EChunk_eq : forall c A {IA:Inhab A} {EA:Enc A} (L:list A),
  c ~> EChunk L =
  \exists (data:loc) (D:list A) (top:int) (default:A),
      c ~~~> `{ data' := data; top' := top; default' := default }
   \* data ~> Array D
   \* \[EChunk_inv L D top default].
Proof. auto. Qed.

Hint Extern 1 (RegisterOpen EChunk) => Provide EChunk_eq.

Lemma echunk_inv_length : forall A (IA:Inhab A) (EA:Enc A) (c:echunk_ A) (L:list A),
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
Hint Extern 1 (@ge _ _ capacity _) => hint capacity_spec; math.

(*************************************************)
(** Specifications *)

Lemma echunk_is_full_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (L:list A) (c:echunk_ A),
  SPEC (echunk_is_full c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[b = isTrue (IsFull L)]).
Proof.
  xcf*. xopen c.  (* xopen_repr EChunk_eq c. *) (* xopen_echunk c. *)
  intros a s d T Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. (* xclose_repr* EChunk_eq c L. *) (* xclose_echunk* c L.*)
  xvals*.
Qed.

Hint Extern 1 (RegisterSpec echunk_is_full) => Provide echunk_is_full_spec.

Lemma echunk_is_empty_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (L:list A) (c:echunk_ A),
  SPEC (echunk_is_empty c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[ b = isTrue (L = nil)]).
Proof.
  xcf*.
  xopen c; introv Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. xvals*. subst*.
  now rewrite* length_zero_eq_eq_nil.
Qed.

Hint Extern 1 (RegisterSpec echunk_is_empty) => Provide echunk_is_empty_spec.

Lemma echunk_create_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (a:A),
  SPEC (echunk_create a)
    PRE (\$(K+1))
    POST (fun c => c ~> EChunk (@nil A)).
Proof.
  xcf. xpay. xapp*. intros t L Hl.
  xapp. intros r.
  xunfolds EChunk.
  { constructors*; subst*; intros.
    { false. math. }
    { rew_listp*. }
    { rew_listp*. } }
  hint capacity_spec. (* TODO: not needed *)
  math.
Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_peek_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (L:list A) (c:echunk_ A),
  L <> nil ->
  SPEC (echunk_peek c)
    PRE (\$2)
    INV (c ~> EChunk L)
    POST (fun x => \exists L', \[L = x::L']).
Proof.
  introv HL.
  destruct L as [|x L']; tryfalse.
  xcf. xpay. xassert_cost 1.
  { xgo*. subst. now rewrite istrue_isTrue_eq. } (* TODO: rewrite* *)
    xopen c. (*xopen_echunk c;*) intros t s d T Inv. lets [Ifr Itl IL IC IS]: Inv.
  rew_list* in *. xgo*.
  { fequals*. rewrite Ifr.
    list_cases*. rew_list*. }
  { xclose* c. (*  xclose_echunk* c (x::L'). *)  xsimpl. }
Qed.

Hint Extern 1 (RegisterSpec echunk_peek) => Provide echunk_peek_spec.

Lemma echunk_pop_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (L:list A) (c:echunk_ A),
  L <> nil -> 
  SPEC (echunk_pop c)
    PRE (\$3 \* c ~> EChunk L)
    POST (fun x => \exists L', c ~> EChunk L' \* \[L = x::L']).
Proof.
  introv HL.
  xcf. xpay. xapp*; intros x L' HL'.
  xopen c; intros t s d T Inv.
  lets [Ifr Itl IL IC IS]: Inv.
  rew_list in *.
  xapp. xlets.
  xappn*. 
  rew_list* in *.
  xclose* c L'.
  { constructors*.
    { (* clever T. *) intros i Hi.
      forwards* E: Ifr i. list_cases* in *. list_cases*. rewrite* E. subst.
      list_cases*. fequals*. }
    { intros. list_cases*. }
    { subst*. rew_list* in *. } }
  { xvals*. }
Qed.

Hint Extern 1 (RegisterSpec echunk_pop) => Provide echunk_pop_spec.

Lemma echunk_push_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (c:echunk_ A) (x:A) (L:list A),
  ~ (IsFull L) ->
  SPEC (echunk_push c x)
    PRE (\$1 \* c ~> EChunk L)
    POSTUNIT (c ~> EChunk (x::L)).
Proof.
  introv HL. unfolds IsFull.
  xcf. xopen c. (* xopen_echunk c;*) intros t s d T Inv.
  lets [Ifr Itl IL IC IS]: Inv.
  xpay. xappn*.
  xclose* c (x::L). (*   xclose_echunk* c (x::L).*)
  { constructors*.
    { intros i Hi. (* clever T. *)
      list_cases*. forwards* E: Ifr i. list_cases*. rewrite E. fequals*. }
    { intros i Hi. list_cases*. } }
  { xsimpl. }
Qed.

Hint Extern 1 (RegisterSpec echunk_push) => Provide echunk_push_spec.

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
