Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Debug_ml.

(*Close Scope wp_scope.

Notation "'LetX' x ':=' F1 'in' F2" :=
 ( (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  only printing,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetX'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'").
*)


(********************************************************************)
(** ** Function calls: [xapp] *)

Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.


Definition f_cf__ :=
  CFML.WPLifted.Wpgen_body (
    forall r : Pervasives_ml.ref_ Coq.ZArith.BinInt.Z,
    forall n : Coq.ZArith.BinInt.Z,
    forall H : CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop,
    forall A : Type,
    forall EA : CFML.SepLifted.Enc A,
    forall Q : A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop,
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl H (
      @CFML.WPLifted.Wptag (
        (
          CFML.WPLifted.Wpgen_let_trm (
            @CFML.WPLifted.Wptag (
              (
                CFML.WPLifted.Wpgen_app Coq.ZArith.BinInt.Z Pervasives_ml.infix_emark__ (
                  Coq.Lists.List.cons (
                    @CFML.SepLifted.dyn_make (
                      Pervasives_ml.ref_ Coq.ZArith.BinInt.Z
                    ) _ r
                  ) Coq.Lists.List.nil
                )
              )
            )
          ) (
            fun x0__ : Coq.ZArith.BinInt.Z =>
            @CFML.WPLifted.Wptag (
              (
                CFML.WPLifted.Wpgen_app Coq.Init.Datatypes.unit Pervasives_ml.infix_colon_eq__ (
                  Coq.Lists.List.cons (
                    @CFML.SepLifted.dyn_make (
                      Pervasives_ml.ref_ Coq.ZArith.BinInt.Z
                    ) _ r
                  ) (
                    Coq.Lists.List.cons (
                      @CFML.SepLifted.dyn_make Coq.ZArith.BinInt.Z _ (
                        Coq.ZArith.BinInt.Z.add x0__ n
                      )
                    ) Coq.Lists.List.nil
                  )
                )
              )
            )
          )
        )
      ) _ _ (
        fun res__ : _ =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (Q res__) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hgc
      )
    ) ->
    CFML.SepLifted.Triple (
      CFML.SepLifted.Trm_apps f (
        Coq.Lists.List.cons (
          @CFML.SepLifted.dyn_make (Pervasives_ml.ref_ Coq.ZArith.BinInt.Z) _ r
        ) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make Coq.ZArith.BinInt.Z _ n) Coq.Lists.List.nil
        )
      )
    ) H Q
  ).



(*
let f r n =
  let x = !r in
  r := x + n

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)

