

(*=============*)

Declare Custom Entry body.

Notation "'Body' f v1 ':=' { B1 [ EB1 ] } F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall B1 (EB1:Enc B1) v1 H A (EA:Enc A) Q,
   (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
   @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)) )
 (in custom body at level 69,
  f constr at level 0,
  v1 at level 0,
  right associativity,
  F1 custom body at level 99,
  format "'[v' '[' 'Body'  f  v1  ':='  { B1  [ EB1 ] }  '/'  '[' F1 ']' ']' ']'" ) : wp_scope.


Notation "'LetFun' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  f ident,
  B1 custom body at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.


Notation "x" :=
 x
 (in custom body at level 0,
  x constr at level 0) : wp_scope.

Notation "( x )" :=
 x
 (in custom body,
  x at level 99) : wp_scope.




(*
Declare Custom Entry body.

Notation "'Body' f v1 ':=' { B1 [ EB1 ] } F1" := (* ok *)
 ((*Wptag*) (Wpgen_body (forall B1 (EB1:Enc B1) v1 H A (EA:Enc A) Q,
   (H ==> (*Wptag*) (F1 A EA (Q \*+ \GC))) ->
   @Triple (Trm_apps f ((@dyn_make _ _ v1)::nil)) A EA H Q)) )
 (in custom body at level 69,
  f constr at level 0,
  v1 at level 0,
  right associativity,
  F1 custom body at level 99,
  format "'[v' '[' 'Body'  f  v1  ':='  { B1  [ EB1 ] }  '/'  '[' F1 ']' ']' ']'" ) : wp_scope.


Notation "'LetFun' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  f ident,
  B1 custom body at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.


Notation "x" :=
 x
 (in custom body at level 0,
  x constr at level 0) : wp_scope.

Notation "( x )" :=
 x
 (in custom body,
  x at level 99) : wp_scope.

(*
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
*)
Open Scope wp_scope.
*)

Notation "'LetFunX' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  f ident,
  B1 custom body at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFunX'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.

Open Scope wp_scope.
Lemma let_poly_p2_spec : (* body *)
  SPEC (let_poly_p2 tt)
    PRE \[]
    POST \[= tt].
Proof using. Print Scopes.
  xcf. xlet. xlet.
  { xlet (fun B (r:option B) => r = None).
    { xapp. xvals*. }
    { xvals*. } }
  { xvals~. }
Qed.

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

Notation "'Body' f { B1 B2 B3  [ EB1 EB2 EB3 ] } v1 ':=' F1" :=
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

Notation "'Body' f { B1 B2 B3  [ EB1 EB2 EB3 ] } v1 v2 ':=' F1" :=
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

Notation "'Body' f { B1 B2 B3  [ EB1 EB2 EB3 ] } v1 v2 v3 ':=' F1" :=
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
