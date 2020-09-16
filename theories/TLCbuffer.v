(**

This file contains temporary definitions that will eventually
get merged into the various files from the TLC library.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
(*
From TLC Require Import LibTactics LibLogic LibList.
From TLC Require Import LibReflect.
From TLC Require LibListZ LibWf LibMultiset LibInt.
*)
From TLC Require Import LibInt.
Generalizable Variables A B.

Global Opaque Z.mul.
Global Opaque Z.add.

From TLC Require Import LibLogic.
Hint Mode Inhab + : typeclass_instances.
