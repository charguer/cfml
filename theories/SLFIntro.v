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

    This course consists of the files named [SLF*.v]. *)


(* ####################################################### *)
(** * Structure *)

(** The "Separation Logic Foundations" course includes the following chapters,
    one file per chapter.

    - [SLFIntro]: the present introduction, which lists the chapters.

    - [SLFBasic]: verification proofs on basic imperative programs.

    - [SLFList]: representation predicate and verification proofs for mutable lists
                 and for mutable stacks.

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


    Bonus chapters (NOT YET READY):

    - [SLFWand]: introduction of the magic wand operator, and of the
                 ramified frame rule.

    - [SLFAffine]: describes how to make the logic affine or partially affine
                   instead of linear.

    - [SLFLift]:  presents a technique for writing postconditions that directly
                  bind a Coq value rather than a value from the deeply embedded
                  language.

    - [SLFRich]:  describes how to handle more advanced language constructs,
                  such as arrays, records, and structures with sharing.


    Special chapters:

    - [SLFSummary]: provides a brief summary of all the contents of this course,
                    including [SLFWAnd] and [SLFLift].

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
(** * Organization of each chapter *)

(** Each chapter contains three parts:
    - "the chapter in a rush" that presents the main take-away messages,
    - "detailed contents" with presentation of important technical results,
    - "optional contents" for those who seek a deeper understanding or find
       additional exercises.

    The course is organized so that:
    - reading only the "in a rush" parts of every chapter should make some sense,
    - all the "optional contents" parts may be read or skipped, independently
      for each chapter.

*)


(* ####################################################### *)
(** * Imports between chapters *)

(** The first two chapters, "SLFBasic" and "SLFList", describe practical
    proofs using the CFML tool. They import the file [Example.v].
    The other chapters describe the "fundational" construction of a Separation
    Logic from scratch. They are essentially independent from the CFML tool.
    They just share a few common files ([Fmap.v] for states, [Var.v] for
    variables, and [SepSimpl.v] for the Separation Logic simplification
    tactic).

    These fundational chapters introduce the material layer by layer.
    Several chapters import definitions from the previous layer.
    Other chapters instead import definitions from the files [SLFDirect.v]
    and [SLFExtra.v], which summarize all the definitions of the course. Which
    definitions are imported should be essentially transparent to the reader.

    There is one notable exception: the definition of the core operators
    of Separation Logic are set [Opaque] in [SLFDirect]. Doing so benefits
    to abstraction: one may no longer "unfold" the core definitions.
    Instead, one must work exclusively using the high-level lemmas that
    characterize the useful properties of the definitions. *)


(* ####################################################### *)
(** * TLC tactics and library *)

(** The proofs are carried out using TLC tactics, which greatly help.
    Most of the tactics used are described in the SF chapter [UseTactics]
    from the "Programming Language Foundations" course. The first two
    chapters, [SLFBasic] and [SLFList], are careful to use as few TLC
    tactics as possible, and to explain the ones that are used.

    Note that a few proofs also rely occasionally on lemmas from the
    TLC library, for example extensionality properties, or results on lists.
    Such lemmas are commented whenever they are important to the proof.
*)

