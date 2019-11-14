(**

Separation Logic Foundations

Chapter: "Intro".

Author: Arthur Charguéraud.
License: MIT.

*)

(* ####################################################### *)
(** * Foreword *)

(** Welcome to the course on the theoretical foundations of Separation Logic,
at the heart of the implementation of the CFML tool.

This course on the theoretical foundation consists of the files named [SLF*.v].
For the course on the practice of proofs with CFML, see files named [CF*.v].

*)


(* ####################################################### *)
(** * Structure *)

(** The "Separation Logic Foundations" course includes the following chapters,
    one file per chapter.

    - [SLFIntro]: the present introduction, which lists the chapters.

    - [SLFBasic]: present verification proofs on basic imperative programs.

    - [SLFMList]: presents verification proofs on mutable lists.

    - [SLFHprop]: definition of the core operators of Separation Logic,
                  and of Hoare triples and Separation Logic triples.

    - [SLFHimpl]: definition, properties, and tactics for the entailment relation
                  between heap predicates.

    - [SLFRules]: reasoning rules for Separation Logic triples, and
                  examples of program verification proofs.

    - [SLFWPsem]: definition of the notion of weakest precondition (semantically),
                  and statement of reasoning rules in weakest-precondition style.

    - [SLFWPgen]: presents an effective function to compute weakest preconditions,
                  and the techniques for obtaining concise verification proofs.


    Bonus chapters:

    - [SLFWand]: introduction of the magic wand operator, and of the
                 ramified frame rule.

    - [SLFLift]:  presents a technique for writing postconditions that directly
                  bind a Coq value rather than a value from the deeply embedded language.

    - [SLFAffine]: describes how to make the logic affine or partially affine
                   instead of linear.

    - [SLFRich]:  describes how to handle more advanced language constructs,
                  such as arrays, records, and structures with sharing.


    Special chapters:

    - [SLFSummary]: provides a brief summary of all the contents of this course.
                    It is intended as support for a 1-hour technical course to
                    experts with prior knowledge of Separation Logic. It also
                    serves as a summary of the present course, as a target for
                    readers who, by the end of the course, presumably have become
                    experts in Separation Logic.

    - [SLFDirect]: provides the minimal set of definitions and lemmas required
                   to build an effective program verification tool, without detour.
                   Note that it does not cover [SLFLift] nor [SLFRich].
                   This file is mostly self-contained; it depends on variables
                   defined in [Var.v], on finite maps defined in [Fmap.v] and on the
                   implementation of the SL simplification tactic from [SepSimpl.v].
                   Note that this file contains a minimal amount of comments,
                   as they would be redundant with the other course files.

    - [SLFExtra]: recaps all the definition and lemmas from the course that are
                  not included in [SLFDirect]. This file only depends on [SLFDirect].
                  This file serves as reference, and a priori there is no reason
                  to read through it.

*)


(* ####################################################### *)
(** * TLC tactics and library *)

(** The proofs are carried out using TLC tactics, which greatly help.
    Most of the tactics used are described in the SF chapter [UseTactics]
    from the "Programming Language Foundations" course.

    The proofs also rely occasionally on lemmas from the TLC library,
    for example extensionality properties.

*)


(* ####################################################### *)
(** * Organization of each chapter *)

(** Each chapter begins with a first part entitled "the chapter in a rush"
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