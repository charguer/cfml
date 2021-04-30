From CFML Require Export WPLibCommon.

Parameter use_credits_false :
  use_credits = false.

Ltac xcredits_activated tt ::=
  constr:(use_credits_false).
