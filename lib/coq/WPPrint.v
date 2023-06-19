(*DEPRECATED

From TLC Require Export LibTactics LibCore LibListZ LibInt LibSet LibMap.
From CFML Require Export WPHeader WPTactics WPBuiltin WPArray.
From CFML Require Export WPRecord. (* needs to be last *)


(*********************************************************************** *)
(** * Grammar set up *)

(* TODO: there is a problem if moving this out to WPPrint, due to a Coq bug on custom entry *)

(** Custom grammar for the display of characteristic formulae. *)

(*Declare Custom Entry wp.*)

(* TODO NOT NEEDED?
Notation "<[ e ]>" :=
 e
 (at level 0, e custom wp at level 99) : wp_scope.
*)

(** Display [Wptag] as just a quote *)

Notation "'`' F" :=
  ((Wptag F%wp))
  (at level 69, F custom wp at level 100, format "'`' F") : wp_scope.

(* TODO: is it posssible to declare the fact that Wptag should not be printed,
   without this conflicting with the notation that says that 'x' by itself in
   [custom wp] can be interpreted as a [constr].

Notation "F" :=
  (Wptag F)
  (at level 100, only printing) : wp_scope.
*)

(** Display characteristic formulae goal in a nice way,
    with current state at the front. *)

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (@Wptag F) _ _ Q)
  (at level 8,
   H at level 0,
   F custom wp at level 0,
   Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "( x )" :=
 x
 (in custom wp,
  x at level 99) : wp_scope.

Notation "{ x }" := (* TODO: NOT NEEDED? *)
 x
 (in custom wp at level 0,
  x constr,
  only parsing) : wp_scope.

Notation "x" :=
 x
 (in custom wp at level 0,
  x constr at level 0) : wp_scope.

(* ********************************************************************** *)
(* ** Simple Constructors *)

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




(* ********************************************************************** *)
(* ** Simple Constructors for printing with tags *)

Notation "'Fail'" :=
 (Wptag (Wpgen_fail))
 (in custom wp at level 69,
  only printing) : wp_scope.

Notation "'Done'" :=
 (Wptag (Wpgen_done))
 (in custom wp at level 69,
  only printing) : wp_scope.

Notation "'Match' V F1" :=
 (Wptag (Wpgen_match V F1))
 (in custom wp at level 69,
  only printing,
  V custom wp at level 0,
  F1 custom wp at level 69,
  format "'[v' 'Match'  V  '/' '['   F1 ']' ']' " ) : wp_scope.

Notation "'Assert' F" :=
 (Wptag (Wpgen_assert F))
 (in custom wp at level 69,
  only printing,
  F custom wp at level 99) : wp_scope.

Notation "'Val' v" :=
 (Wptag (Wpgen_val v))
 (in custom wp at level 69,
  only printing) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
 (Wptag (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  only printing,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetVal' x ':=' V 'in' F1" :=
 (Wptag (Wpgen_let_val V (fun x => F1)))
 (in custom wp at level 69,
  only printing,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'LetVal'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Alias' x ':=' V 'in' F1" :=
 (Wptag (Wpgen_alias (Wpgen_let_val V (fun x => F1))))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Alias'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.


Notation "'Seq' F1 ; F2" :=
 (Wptag (Wpgen_seq F1 F2))
 (in custom wp at level 68,
  only printing,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' f x1 .. xn" :=
 (Wptag (Wpgen_app _ f (cons (Dyn x1) .. (cons (Dyn xn) nil) ..)))
  (in custom wp at level 68,
  only printing,
   f constr at level 0,
   x1 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.


(* TODO: why need both? *)
Notation "'App' f x1 x2 .. xn" :=
 (Wptag (Wpgen_app _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..))))
  (in custom wp at level 68,
   only printing,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
 (Wptag (Wpgen_if v F1 F2))
 (in custom wp at level 69,
  only printing,
  v constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
 (Wptag (Wpgen_while F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  format "'[v' '[' 'While'  F1  'Do'  ']' '/' '['   F2 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'To' n2 'Do' F1 'Done'" :=
 (Wptag (Wpgen_for_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  only printing,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'To'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'Downto' n2 'Do' F1 'Done'" :=
 (Wptag (Wpgen_for_downto_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  only printing,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'Downto'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'LetFun' f ':=' B1 'in' F1" :=
 (Wptag (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  only printing,
  f ident,
  B1 constr at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.



(* ********************************************************************** *)
(* ** Function Body *)

(** Body is not in 'custom wp', on purpose *)

Notation "'Body' f v1 ':=' F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  v3 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f v1 v2 v3 v4 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall v1 v2 v3 v4 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::(@dyn_make _ _ v4)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  v3 constr,
  v4 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  v1  v2  v3  v4  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

(** Polymorphic variants of body-- TODO: only up to 3 polymorphic variables supported *)

Notation "'Body' f v1 ':=' { B1 [ EB1 ] } F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall B1 (EB1:Enc B1) v1 H A (EA:Enc A) Q,
   (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
   @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)) )
 (at level 69,
  f constr at level 0,
  v1 at level 0,
  right associativity,
  F1 at level 99,
  format "'[v' '[' 'Body'  f  v1  ':='  { B1  [ EB1 ] }  '/'  '[' F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ] } v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 v2 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 v2 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  v2  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 [ EB1 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  v3 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  [ EB1 ] }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 [ EB1 EB2 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  v3 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  [ EB1  EB2 ]  }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

Notation "'Body' f { B1 B2 B3 [ EB1 EB2 EB3 ] } v1 v2 v3 ':=' F1" :=
 ((*Wptag*) (Wpgen_body (forall B1 EB1 B2 EB2 B3 EB3 v1 v2 v3 H A EA Q,
               (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
               @Triple (Trm_apps f ((@dyn_make _ _ v1)::(@dyn_make _ _ v2)::(@dyn_make _ _ v3)::nil)) A EA H Q)))
 (at level 69,
  f constr at level 0,
  v1 constr,
  v2 constr,
  v3 constr,
  F1 at level 99,
  right associativity,
  format "'[v' '[' 'Body'  f  { B1  B2  B3  [ EB1  EB2  EB3 ] }  v1  v2  v3  ':=' '/' '['   F1 ']' ']' ']'" ) : wp_scope.

(* TODO: work on recursive notations for Body *)

(* TODO: generalize let-fun to recursive functions *)


(* ********************************************************************** *)
(* ** Polymorphic let *)

(* LetPoly 0 *)

Notation "'LetPoly' x : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall B1 (EB1:Enc B1), H ==> F1 T _ (fun r => \[P1 r] \* H1))
   /\ (forall x, (P1 x) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  :  T  ':='  { B1 [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetPoly' x : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun r => \[P1 r] \* H1))
   /\ (forall x, (P1 x) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  :  T  ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

(* LetPoly 1 *)

Notation "'LetPoly' x { A1 } : T ':=' F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1, H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A1 (x A1)) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetPoly' x { A1 } : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 B1 (EB1:Enc B1), H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A1 (x A1)) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  { B1  [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetPoly' x { A1 } : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun x => \[P1 A1 x] \* H1))
   /\ (forall x, (forall A1, P1 A (x A1)) -> H1 ==> F2 Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1 }  :  T  ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

(* LetPoly 2 *)

Notation "'LetPoly' x { A1 A2 } : T ':=' F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2, H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetPoly' x { A1 A2 } : T ':=' { B1 [ EB1 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2 B1 (EB1:Enc B1), H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A1 A2 (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  { B1 [ EB1 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetPoly' x { A1 A2 } : T ':=' { B1 B2 [ EB1 EB2 ] } F1 'in' F2" :=
  (Wpgen_let_trm_poly (fun A (EA:Enc A) Q H => exists P1 H1,
     (forall A1 A2 B1 (EB1:Enc B1) B2 (EB2:Enc B2), H ==> F1 T _ (fun x => \[P1 A1 A2 x] \* H1))
   /\ (forall x, (forall A1 A2, P1 A1 A2 (x A1 A2)) -> H1 ==> F2 _ _ Q) ))
  (in custom wp at level 69,
   only printing,
   x ident,
   F1 custom wp at level 99,
   F2 custom wp at level 99,
   right associativity,
   format "'[v' '[' 'LetPoly'  x  { A1  A2 }  :  T ':='  { B1 B2 [ EB1 EB2 ] } '/' '['   F1 ']'  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

(* ********************************************************************** *)
(* ** Pattern Matching Cases *)

(* Notation for Case is not reversible, but that's fine because we know that
   the argument P is always in practice the negation of a test that is visible in F1. *)

(* TODO generic notation for arities that are not supported *)

Notation "'Case' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case F1 _ F2))
 (in custom wp at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity, (* TODO: could be right? *)
  format "'[v' '[' 'Case' ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p { x1 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  x1 ident,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p { x1 x2 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  x1 ident, x2 ident,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p { x1 x2 x3 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p { x1 x2 x3 x4 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3 x4, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident, x4 ident,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3  x4 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'Case' v 'is' p { x1 x2 x3 x4 x5 } 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_case (fun A EA Q => \forall x1 x2 x3 x4 x5, \[v = p] \-* F1 A EA Q) _ F2))
 (in custom wp at level 69,
  v constr at level 0,
  x1 ident, x2 ident, x3 ident, x4 ident, x5 ident,
  p constr at level 0,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'Case'  v  'is'  p  { x1  x2  x3  x4  x5 }  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

(* TODO: do not attempt to currify the assumption associated with the when clause?
    this could simplify the tactic that handles the case *)


*)