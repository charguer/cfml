
Axiom classicT : forall (P : Prop),
  {P} + {~ P}.

Notation "'If' P 'then' v1 'else' v2" :=
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.
