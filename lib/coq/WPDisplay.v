Set Implicit Arguments.
From CFML Require Export WPHeader. (* WPTactics WPBuiltin.*)
From CFML Require Import WPBuiltin SepBase SepLifted WPLifted.

Declare Scope cf_scope.
Declare Custom Entry cf.
Open Scope cf_scope.


(* ********************************************************************** *)
(** * Additional notation for more concise Specifications at scale. *)


(************************************************************)
(** Additional notation for heap predicates *)

(** The following notation is only used for parsing. *)

(** [\[= v]] is short for [fun x => \[x = v]].
    It typically appears in a postcondition, after then [POST] keyword. *)

Notation "\[= v ]" := (fun x => \[x = v])
  (at level 0, only parsing) : triple_scope.

(** [H1 ==+> H2] is short for [H1 ==> (H1 \* H2)].
    Typical usage is for extracting a pure fact from a heap predicate. *)

Notation "H1 ==+> H2" := (himpl H1 (hstar H1 H2))
  (at level 55, only parsing) : triple_scope.


(************************************************************)
(** Additional notation for triples *)

Notation "'SPEC' t 'INV' H 'POST' Q" :=
  (Triple t H (Q \*+ H))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'INV'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'POSTUNIT' H2" :=
  (Triple t H1 (fun (_:unit) => H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'PRE'  H1  '/' 'POSTUNIT'  H2 ']'") : triple_scope.

Notation "'SPEC' t 'INV' H1 'POSTUNIT' H2" :=
  (Triple t H1 (fun (_:unit) => H2 \* H1))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'INV'  H1  '/' 'POSTUNIT'  H2 ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'INV' H2 'POST' Q" :=
  (Triple t (H1 \* H2) (Q \*+ H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t '/' 'PRE'  H1 '/' 'INV'  H2  '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'INV' H2 'POSTUNIT' H3" :=
  (Triple t (H1 \* H2) (fun (_:unit) => H3 \* H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t '/' 'PRE'  H1 '/' 'INV'  H2  '/' 'POSTUNIT'  H3 ']'") : triple_scope.

Notation "'SPEC_PURE' t 'POST' Q" :=
  (Triple t \[] Q)
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC_PURE'  t  '/'  'POST'  Q ']'") : triple_scope.

(* DEPRECATED

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

*)



(* ********************************************************************** *)
(** Embedding of the custom grammar *)

Notation "x" :=
 x
 (in custom cf at level 0,
  x constr at level 0) : cf_scope.

Notation "( x )" :=
 x
 (in custom cf,
  x at level 99) : cf_scope.


(* ********************************************************************** *)
(** Notations for triples *)

Notation "'SPEC' t 'INV' H 'POST' Q" :=
  (Triple t H (Q \*+ H))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'INV'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'POSTUNIT' H2" :=
  (Triple t H1 (fun (_:unit) => H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'PRE'  H1  '/' 'POSTUNIT'  H2 ']'") : triple_scope.

Notation "'SPEC' t 'INV' H1 'POSTUNIT' H2" :=
  (Triple t H1 (fun (_:unit) => H2 \* H1))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t  '/' 'INV'  H1  '/' 'POSTUNIT'  H2 ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'INV' H2 'POST' Q" :=
  (Triple t (H1 \* H2) (Q \*+ H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t '/' 'PRE'  H1 '/' 'INV'  H2  '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'PRE' H1 'INV' H2 'POSTUNIT' H3" :=
  (Triple t (H1 \* H2) (fun (_:unit) => H3 \* H2))
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC'  t '/' 'PRE'  H1 '/' 'INV'  H2  '/' 'POSTUNIT'  H3 ']'") : triple_scope.

Notation "'SPEC_PURE' t 'POST' Q" :=
  (Triple t \[] Q)
  (at level 39, t custom Trm_apps at level 0,
  format "'[v' 'SPEC_PURE'  t  '/'  'POST'  Q ']'") : triple_scope.


(* ********************************************************************** *)
(** Notations for triples with monotonicity *)

Class MonType (B:Type) : Type := make_MonType {
  MonTypeInv : B -> hprop;
  MonTypeExt : B -> B -> Prop; }.

Definition TripleMon (B:Type) {MB:MonType B} (A:Type) {EA:Enc A} (t:trm) (M:B) (H:hprop) (Q:B->A->hprop) :=
  Triple t
    (MonTypeInv M \* H)
    (fun x => \exists M',\[MonTypeExt M M'] \* MonTypeInv M' \* Q M' x).

Notation "'SPEC' t 'MONO' M 'PRE' H 'POST' Q" :=
  (TripleMon t M H Q)
  (at level 39, M at level 0, t custom Trm_apps at level 0,
   format "'[v' 'SPEC'  t  '/' 'MONO'  M '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'MONO' M 'PRE' H 'INV' I 'POST' Q" :=
  (TripleMon t M (H \* I) (fun M' => Q M' \*+ I))
  (at level 39, M at level 0, t custom Trm_apps at level 0,
   format "'[v' 'SPEC'  t  '/' 'MONO'  M '/' 'PRE'  H  '/' 'INV'  I '/' 'POST'  Q ']'") : triple_scope.

Notation "'SPEC' t 'MONO' M 'PRE' H 'POSTUNIT' Q" :=
  (TripleMon t M H (fun M' (_:unit) => Q M'))
  (at level 39, M at level 0, t custom Trm_apps at level 0,
   format "'[v' 'SPEC'  t  '/' 'MONO'  M '/' 'PRE'  H  '/' 'POSTUNIT'  Q ']'") : triple_scope.

Global Instance MonType_prod (B C:Type) (MB:MonType B) (MC:MonType C) : MonType (B * C) :=
  make_MonType
    (fun '(b,c) => (MonTypeInv b \* MonTypeInv c))
    (fun '(b1,c1) '(b2,c2) => MonTypeExt b1 b2 /\ MonTypeExt c1 c2).


(* ********************************************************************** *)
(** Notations for characteristic formulae *)


Delimit Scope cf_scope with cf.

Notation "'`' F" :=
  ((Wptag F))
  (in custom cf at level 69,
   F custom cf at level 99,
   format "'`' F") : cf_scope.

(*
Notation"'`' F" :=
  ((Wptag F%cf))
  (in custom cf at level 0,
   only printing,
   F custom cf) : cf_scope.*)

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (@Wptag F) _ _ Q)
  (at level 8,
   H at level 0,
   F custom cf at level 0,
   Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : cf_scope.

(*
Notation "<[ e ]>" :=
 e
 (at level 0, e custom cf at level 99) : cf_scope.
*)


(* ********************************************************************** *)
(** Notations for characteristic formulae constructs *)

Notation "'Pay' F" :=
 ((*Wptag*) (Wpgen_pay F))
 (in custom cf at level 69, F at level 0) : cf_scope.

Notation "'Fail'" :=
 ((*Wptag*) (Wpgen_fail))
 (in custom cf at level 69) : cf_scope.

Notation "'Done'" :=
 ((*Wptag*) (Wpgen_done))
 (in custom cf at level 69) : cf_scope.

Notation "'Match' V F1" :=
 ((*Wptag*) (Wpgen_match V F1))
 (in custom cf at level 69,
  V constr at level 0,
  F1 custom cf at level 69,
  format "'[v' 'Match'  V  '/' '['   F1 ']' ']' " ) : cf_scope.

Notation "'Assert' F" :=
 ((*Wptag*) (Wpgen_assert F))
 (in custom cf at level 69,
  F custom cf at level 99) : cf_scope.

Notation "'Val' v" :=
 ((*Wptag*) (Wpgen_val v))
 (in custom cf at level 69,
  v constr) : cf_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
 ((*Wptag*) (Wpgen_let_trm F1 (fun x => F2)))
 (in custom cf at level 69,
  x ident,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  right associativity,
 format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetVal' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_let_val V (fun x => F1)))
 (in custom cf at level 69,
  x ident,
  V constr at level 69,
  F1 custom cf at level 99,
  right associativity,
 format "'[v' '[' 'LetVal'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : cf_scope.

Notation "'Alias' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_alias (Wpgen_let_val V (fun x => F1))))
 (in custom cf at level 69,
  x ident,
  V constr at level 69,
  F1 custom cf at level 99,
  right associativity,
 format "'[v' '[' 'Alias'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : cf_scope.

Notation "'Seq' F1 ; F2" :=
 ((*Wptag*) (Wpgen_seq F1 F2))
 (in custom cf at level 68,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : cf_scope.

Notation "'App' f x1 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) .. (cons (Dyn xn) nil) ..)))
  (in custom cf at level 68,
   f constr at level 0,
   x1 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : cf_scope.

(* TODO: why need both? *)
Notation "'App' f x1 x2 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..))))
  (in custom cf at level 68,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : cf_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_if v F1 F2))
 (in custom cf at level 69,
  v constr at level 69,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
 ((*Wptag*) (Wpgen_while F1 F2))
 (in custom cf at level 68,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  format "'[v' '[' 'While'  F1  'Do'  ']' '/' '['   F2 ']' '/' 'Done' ']'") : cf_scope.

Notation "'For' i '=' n1 'To' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_int n1 n2 (fun i => F1)))
 (in custom cf at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom cf at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'To'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : cf_scope.

Notation "'For' i '=' n1 'Downto' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_downto_int n1 n2 (fun i => F1)))
 (in custom cf at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom cf at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'Downto'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : cf_scope.

Notation "'LetFun' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom cf at level 69,
  f ident,
  B1 constr at level 69,
  F1 custom cf at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : cf_scope.



(* ********************************************************************** *)
(* ** Function Body *)

(** Body is not in 'custom cf', on purpose *)

Notation "'Body' f v1 ':=' F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  v3 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f v1 v2 v3 v4 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 v3 v4 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::(@dyn_make _ _ v4)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  v3 ident,
  v4 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  v3  v4  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

(** Polymorphic variants of body-- TODO: only up to 3 polymorphic variables supported *)

Notation "'Body' f v1 ':=' { B1 [ EB1 ] } F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall B1 (EB1:Enc B1) v1 H A (EA:Enc A) Q,
   (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
   @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)) )
 (at level 69,
  f constr at level 0,
  v1 ident,
  right associativity,
  F1 at level 99,
  format "'[v' '[' 'Body'  f  v1  ':='  { B1  [ EB1 ] }  '/'  '[' F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ] } v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  v3 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  v3 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ]  }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 ident,
  v2 ident,
  v3 ident,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : cf_scope.

(* TODO: work on recursive notations for Body *)

(* TODO: generalize let-fun to recursive functions *)


(* ********************************************************************** *)
(* ** Polymorphic let *)

(* LetPoly 0 *)

Notation "'LetPoly' x : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall B1 (EB1:Enc B1), H ==> F1 T _ (fun r => \[P1 r] \* H1))
   /\ (forall x, (P1 x) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  :  T  ':='  { B1 [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetPoly' x : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun r => \[P1 r] \* H1))
   /\ (forall x, (P1 x) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  :  T  ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

(* LetPoly 1 *)

Notation "'LetPoly' x { A1 } : T ':=' F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1, H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A1 (x A1)) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetPoly' x { A1 } : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 B1 (EB1:Enc B1), H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A1 (x A1)) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  { B1  [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetPoly' x { A1 } : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A (x A1)) -> H1 ==> F2 Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

(* LetPoly 2 *)

Notation "'LetPoly' x { A1 A2 } : T ':=' F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2, H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetPoly' x { A1 A2 } : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2 B1 (EB1:Enc B1), H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A1 A2 (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  { B1 [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

Notation "'LetPoly' x { A1 A2 } : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2 B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A1 A2 (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom cf at level 69,
   only printing,
   x ident,
   T constr,
   F1 custom cf at level 99,
   F2 custom cf at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : cf_scope.

(* ********************************************************************** *)
(* ** Pattern Matching Cases *)

(* Notation for Case is not reversible, but that's fine because we know that
   the argument P is always in practice the negation of a test that is visible in F1. *)

(* TODO generic notation for arities that are not supported *)

Notation "'Case' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case F1 _ F2))
 (in custom cf at level 69,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity, (* TODO: could be right? *)
  format "'[v' '[' 'Case' ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p { x1 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  x1 ident,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p { x1 x2 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  x1 ident, x2 ident,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p { x1 x2 x3 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p { x1 x2 x3 x4 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3 x4, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident, x4 ident,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3  x4 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

Notation "'Case' v 'is' p { x1 x2 x3 x4 x5 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3 x4 x5, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom cf at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident, x4 ident, x5 ident,
  p constr at level 0,
  F1 custom cf at level 99,
  F2 custom cf at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3  x4  x5 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : cf_scope.

(* TODO: do not attempt to currify the assumption associated with the when clause?
    this could simplify the tactic that handles the case *)


(* ********************************************************************** *)
(* ** Notation for Primitive Operations. *)

(* needed?

Notation "'ref' t" :=
  (Wpgen_app _(val_prim val_ref) ((Dyn t)::nil))
  (in custom cf at level 68): cf_scope.

Notation "'free' t" :=
  (Wpgen_app _(val_prim val_free) ((Dyn t)::nil))
  (in custom cf at level 68): cf_scope.

Notation "'not' t" :=
  (Wpgen_app _(val_prim val_neg) ((Dyn t)::nil))
  (in custom cf at level 68): cf_scope.

Notation "! t" :=
  (Wpgen_app _(val_prim val_get) ((Dyn t)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 := t2" :=
  (Wpgen_app _(val_prim val_set) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 + t2" :=
  (Wpgen_app _(val_prim val_add) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "'- t" :=
  (Wpgen_app _(val_prim val_opp) ((Dyn t)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 - t2" :=
  (Wpgen_app _(val_prim val_sub) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 * t2" :=
  (Wpgen_app _(val_prim val_mul) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 / t2" :=
  (Wpgen_app _(val_prim val_div) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 'mod' t2" :=
  (Wpgen_app _(val_prim val_mod) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 = t2" :=
  (Wpgen_app _(val_prim val_eq) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 <> t2" :=
  (Wpgen_app _(val_prim val_neq) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 <= t2" :=
  (Wpgen_app _(val_prim val_le) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 < t2" :=
  (Wpgen_app _(val_prim val_lt) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 >= t2" :=
  (Wpgen_app _(val_prim val_ge) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.

Notation "t1 > t2" :=
  (Wpgen_app _(val_prim val_gt) ((Dyn t1)::(Dyn t2)::nil))
  (in custom cf at level 68): cf_scope.


*)