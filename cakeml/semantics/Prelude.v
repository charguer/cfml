
Require Export String.
Require Export Coq.Numbers.BinNums.

Axiom COQ_HOLE : forall {X:Type} (msg:string), X.

Axiom classicT : forall (P : Prop),
  {P} + {~ P}.

Notation "'If_' P 'then' v1 'else' v2" :=
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) (* : type_scope *).

Parameter char : Type.
Parameter word8 : Type.
Parameter word64 : Type.
