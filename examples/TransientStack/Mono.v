Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.

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
