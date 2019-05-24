(**

Separation Logic Foundations

Chapter: "Intro".

Author: Arthur Charguéraud.
License: MIT.

*)

(* ####################################################### *)
(** * Structure *)

(** The "Separation Logic Foundations" course includes the following chapters,
    one file per chapter.


    - [SLFIntro]: the present introduction, which lists the chapters.

    - [SLFHprop]: definition of the core operators of Separation Logic, 
                  and of Hoare triples and Separation Logic triples.

    - [SLFHimpl]: definition, properties, and tactics for the entailment relation
                  between heap predicates.

    - [SLFRules]: reasoning rules for Separation Logic triples, and
                  examples of program verification proofs.

    - [SLFWand]: introduction of the magic wand operator, and of the 
                 ramified frame rule.

    - [SLFWPsem]: definition of the notion of weakest precondition (semantically),
                  and statement of reasoning rules in weakest-precondition style.

    - [SLFWPgen]: presents an effective function to compute weakest preconditions,
                  and the techniques for obtaining concise verification proofs.

    The course is completed with two summary chapters.

    - [SLFDirect]: provides the minimal set of definitions and lemmas required
                   to build an effective program verification tool, without detour.
                   This file is mostly self-contained; it depends on variables
                   defined in [Var.v], on finite maps defined in [Fmap.v] and on the
                   implementation of the SL simplification tactic from [Hsimpl.v].

    - [SLFExtra]: recaps all the definition and lemmas from the course that are
                  not included in [SLFDirect]. This file only depends on [SLFDirect].

*)

(* ####################################################### *)
(** * Future work *)

(** There are three future chapters, planned but not yet written:

    - [SLFLift]: presentation of a technique for writing postconditions that
                 directly bind a Coq value rather than a value from the deeply 
                 embedded language.

    - [SLFRich]: presentation of the techniques for handling a source language 
                 with more features.

    - [SLFExt]: examples of two extensions of Separation Logic, one with time 
                credits, and one with read-only permissions.

*)

(* ####################################################### *)
(** * TLC tactics and library *)

(** The proofs are carried out using TLC tactics, which greatly help.
    Most of the tactics used are described in the SF chapter [UseTactics]
    from the "Programming Language Foundations" course.

    The proofs also rely occasionnally on lemmas from the TLC library,
    for example extensionality properties.

*)


(* ####################################################### *)
(** * Organization of each chapter *)

(** Each chapter has a short first part entitled "the chapter in a rush"
    that presents the main take away messages.

    The course is organized so that reading only the "in a rush" parts
    of every chapter should make sense.

*)

(* ####################################################### *)
(** * Imports between chapters *)

(** Some chapters import the definitions from the previous chapter.
    Other chapters restart from a clean slate instead, and import
    the definitions from the files [SLFDirect] and [SLFExtra].

    All definitions and lemmas are compatible, no which imports are
    used should be totally transparent to the reader. With one notable
    exception, though: the definition of the core operators of Separation
    Logic are, at one point, set "Opaque", for the benefits of abstraction.
    One may no longer "unfold" their definitions, and must work exclusively
    using the lemmas about the definitions---this is done on purpose.

*)