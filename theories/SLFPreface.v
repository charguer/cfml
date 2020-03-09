(** * Preface *)

(** Warning! Beta release! *)

(* ########################################################### *)
(** * Welcome *)

(** This electronic book is Volume 5 of the _Software Foundations_
    series, which presents the mathematical underpinnings of reliable
    software.

    In this volume, you will learn about the foundations of Separation
    Logic, which is a practical approach for the modular verification
    of imperative programs.

    You are assumed to understand the material in Software Foundations
    Volume 1 (Logic Foundations), and the two chapters on Hoare Logic
    (Hoare and Hoare2) from Software Foundations Volume 2 (PL
    Foundations).

    The exposition here is intended for a broad range of readers, from
    advanced undergraduates to PhD students and researchers.  *)


(* ########################################################### *)
(** * About Separation Logic *)

(** Separation Logic is a "program logic": it enables one to establish
    that a program satisfies its specification.

    Specifications are expressed using triples, of the form [{H} t {Q}].
    Whereas in Hoare logic the precondition [H] and the postcondition
    [Q] describe the whole of the memory state, in Separation Logic,
    [H] and [Q] describe only a fragment of the memory state. This fragment
    includes the resources necessary to the execution of [t].

    Central to Separation Logic is the frame rule, which is key to the
    modularity of the verification proofs. Its statement is as follows.

[[
         { H } t { Q }
    -------------------------
     { H * H' } t { Q * H' }
]]

    The above rule asserts that if a term [t] executes correctly with the
    resources [H] and produces [Q], then the term [t] admits the same
    behavior in a larger memory state, described by the union of [H]
    with a disjoint union [H'], producing the postcondition [Q] extended
    with that same resource [H'] unmodified.

    Separation Logic can be exploited in three kind of tools.

    - Automated proofs: the user provides only the code, and the tool
      locates sources of potential bugs. A good automated tool provides
      feedback that, most of time, is relevant.
    - Semi-automated proofs: the user provides not just the code,
      but also specifications and invariants; the tool then leverages
      automated solvers (e.g., SMT solvers) to discharge proof obligations.
    - Interactive proofs: the user provides not just the code and its
      specifications, but also a detailed proof script justifying the
      correctness of the code; such proofs are developed interactively
      using a proof assistant such as Coq.

    The present course focuses on the third approach, that is, the integration
    of Separation Logic in an interactive proof assistant. This approach
    has been successfully put to practice throughout the world, using
    various proof assistants (Coq, Isabelle/HOL, HOL), targeting different
    languages (Assembly, C, SML, OCaml, Rust...), for verifying various
    kind of programs, ranging from low-level operating system kernels
    to high-level data structures and algorithms.

    The benefits of exploiting Separation Logic in a proof assistant
    include at least four major points:

    - higher-order logic provides virtually-unlimited expressiveness
      that enables formulating arbitrarily-complex specifications and
      invariants;
    - a proof assistant provides a unified framework to prove both
      the implementation details of the code and the underlying
      mathematical results form, e.g., results from  theory or graph
      theory;
    - proof scripts may be easily maintained to reflect on a change
      to the source code;
    - the fact that Separation Logic is formalized in the proof
      assistant provides high confidence in the correctness of the tool.

    Pretty much all the tools that leverage Separation Logic in a proof
    assistant are constructed following the same schema:

    - A formalization of the syntax and semantics of the source language
      (This is called a "deep embedding" of the programming language).
    - A definition of Separation Logic predicates as predicates from
      higher-order logic. (This is called a "shallow embedding" of the
      program logic.)
    - A definition of Separation Logic triples as a predicate, the
      statements of the reasoning rules as lemmas, and the proof of
      these reasoning rules with respect to the semantics.
    - An infrastructure that consists of lemmas, tactics and notation,
      allowing for verification proof to be carried out through
      relatively concise proof scripts.

    The purpose of this course is to explain how to set up such as
    construction. To that end, we consider in this course:

    - a minimalistic imperative programming language: a lambda-calculus
      with references (mini-ML), which admits a simple semantics and avoids
      in particular the need to distinguish between stack variables and
      heap-allocated variables;
    - the simplest possible variant of Separation Logic.

    For this mini-ML language and this core Separation Logic, we present
    in full the construction of a Separation Logic framework, up to the
    presentation of a concise verification proof script for a function
    that performs in-place concatenation of two mutable linked lists.

*)

(* ########################################################### *)
(** ** Summaries for the course *)

(** Before diving into the Coq files, the reader might be interested in
    reading high-level summaries of the contents of the course:

    - [SLFSummary.v] contains material for a 1-hour summary of the key
      ingredients involved in the course.

    - [SLFSummary.pdf] contains LaTeX-formatted slides presenting the
      most important definitions from [SLFSummary.v].

    - [SeqSepLogic.pdf] is a LaTeX-formatted paper that gives a summary
      of the definitions involved in the course, but not covering the
      chapters [SLFBasic] and [SLFWPgen], which involve the characteristic
      formula generator.

*)


(* ########################################################### *)
(** * Organization of the chapters *)

(* ########################################################### *)
(** ** Chapters *)

(** The "Foundations of Separation Logic" course includes the following chapters.

    - [SLFPreface]: the present introduction.

    - [SLFBasic]:  introduction to Separation Logic through practical examples
                   of specifications and verification proofs, on basic programs.

    - [SLFHprop]:  definition of the core operators of Separation Logic,
                   of Hoare triples, and of Separation Logic triples.

    - [SLFHimpl]:  definition of the entailment relation, statement and proof
                   of its fundamental properties, and description of the
                   simplification tactic for entailment.

    - [SLFRules]:  statement and proofs of the reasoning rules of Separation Logic,
                   and examples of complete verification proofs.

    - [SLFWPsem]:  definition of the semantic notion of weakest precondition,
                   and statement of reasoning rules in weakest-precondition style.

    - [SLFWPgen]:  presentation of a function that effectively computes weakest
                   preconditions, and description of the construction of a set up
                   that leads to concise verification proofs.

    - [SLFWand]:   introduction of the magic wand, of the ramified frame rule,
                   and recursive computation of weakest precondition inside functions.

    - [SLFStruct]: representation predicate for records and arrays.

    - [SLFRich]:   treatment of additional language constructs, including loops,
                   assertions, and n-ary functions.

    - [SLFAffine]: description of a generalized Separation Logic that supports the
                   ability to freely discard certain types of heap predicates.

*)

(* ########################################################### *)
(** ** Special chapters *)

(**

    - [SLFMinimal]:This file contains a minimal proof of soundness of Separation
                   Logic for sequential programs.

    - [SLFSummary]:This file contains the material for a one-hour talk that
                   introduces, at a high level, the most important ideas from the
                   course. This material is accompanied by LaTeX-generated slides
                   to be found in the file [SLFSummary.pdf].

    - [SLFDirect]: This file provides the minimal set of definitions and lemmas
                   required to build a practical program verification tool,
                   without detour. This file is mostly self-contained; it depends
                   only on the representation of variables, of finite maps, and
                   on the implementation of the entailment simplification tactic
                   (i.e., auxiliary files [Var.v], [Fmap.v], and [SepSimpl.v]).
                   Note that the file [SLFDirect] contains a minimal amount of
                   comments; explanations are given in the main course chapters.

    - [SLFExtra]:  This file recaps the definition and lemmas that are presented
                   in the main course chapters but that are not included in the
                   file [SLFDirect]. Again, this file serves as a reference, and
                   does not contain further explanations.

*)

(* ########################################################### *)
(** * Organization of each chapters *)

(* ########################################################### *)
(** ** Three levels of reading *)

(** Each chapter contains three parts:
    - the "chapter in a rush" part, which presents the main take-away messages,
    - the "detailed contents" part, with presentation of important technical results,
    - the "optional contents" part, intended for those who seek a deeper understanding,
      or wish so work on additional exercises.

    The course is organized so that:
    - reading only the "in a rush" parts of every chapter should make sense,
    - all the "optional contents" parts are independent: they may be read,
      partially read, or skipped, without consequences on the other chapters.

    For the first two chapters, the "detailed contents" material consists of
    exercises that are interleaved with the "chapter in a rush" material.
    For the other chapters, the tree parts are consecutive (i.e., not interleaved).

*)

(* ########################################################### *)
(** ** Exercises *)

(** Each chapter includes numerous exercises.  The star rating scheme in
    use is described in the Preface of Volume 1. *)


(* ########################################################### *)
(** * Practicalities *)

(* ########################################################### *)
(** ** System Requirements *)

(** The Preface of Volume 1 describes the Coq installation you will
    need. This edition was built with $(COQVERSION). *)

(* ########################################################### *)
(** ** Note for CoqIDE users *)

(** CoqIDE works better with its "asynchronous" proof mode disabled.
    To load all the course files in CoqIDE, use the following command line.

[[
	coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLF*.v &
]]

*)

(* ########################################################### *)
(** ** TLC: tactics and libraries *)

(** The proofs are carried out using tactics from the TLC library.
    These tactics greatly help. Most of the tactics used are described
    in the chapter [UseTactics] from the "Programming Language Foundations"
    (PLF) course.

    The first two chapters, [SLFBasic] and [SLFList], are careful to use as
    few TLC tactics as possible, and to explain the ones that are used.
    In the other chapters, TLC tactics are used in proof scripts to improve
    conciseness, however familiarity with these tactics should not be
    necessary to follow through the proofs. All exercises can be carried
    out without using TLC tactics.

    Note that a few proofs also rely occasionally on lemmas from the
    TLC library, for example extensionality properties, or results on lists.
    Such lemmas are described whenever they are relevant to a proof. *)


(* ########################################################### *)
(** ** CFML: a practical verification tool *)

(** CFML is a program verification framework based on Separation
    Logic and embedded in Coq. The present course presents, among
    other things, the foundations of the CFML tool.

    The first two chapters, [SLFBasic] and [SLFList], present
    verification proofs that are conducted using CFML.

    The other chapters build a mini-CFML from scratch, and present
    practical verification proofs based on that mini-CFML. *)


(* ########################################################### *)
(** ** Imports between files *)

(** To simplify the compilation process, copies of the source files from
    the TLC and the CFML libraries are included in the present folder.
    There is no need to look at these files. *)

(** The first two chapters, [SLFBasic] and [SLFList], leverage the
    CFML tool, by importing the CFML library file [Example.v].

    The other chapters are independent from the CFML library. They only
    exploit a few generic library files ([Var.v] for variables, [Fmap.v]
    for finite maps, and [SepSimpl.v] for the hi-tech Separation Logic
    simplification tactic). *)

(** The chapters introduce Separation Logic definitions and lemmas
    layer by layer.

    Several chapters import definitions from the previous layer.
    Other chapters instead import definitions from the files [SLFDirect.v]
    and [SLFExtra.v], which summarize all the definitions of the course.
    Which definitions are imported should be essentially transparent to
    the reader.

    There is one notable exception: the definition of the core operators
    of Separation Logic are set [Opaque] in [SLFDirect]. Doing so benefits
    to abstraction: one may no longer "unfold" the core definitions.
    Instead, one must work exclusively using the high-level lemmas that
    characterize the useful properties of the definitions. *)

(* ########################################################### *)
(** * Dissemination *)

(* LATER:

    Downloading the Coq Files

    A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at https://softwarefoundations.cis.upenn.edu.

    (If you are using the book as part of a class, your teacher may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.) *)

(* ########################################################### *)
(** ** Recommended citation format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:
[[
   @book            {$FIRSTAUTHOR:SF$VOLUMENUMBER,
   author       =   {$AUTHOR},
   title        =   "$VOLUMENAME",
   series       =   "Software Foundations",
   volume       =   "$VOLUMENUMBER",
   year         =   "$VOLUMEYEAR",
   publisher    =   "Electronic textbook",
   note         =   {Version $VERSION, \URL{http://softwarefoundations.cis.upenn.edu} },
   }
]]
*)

(* ########################################################### *)
(** ** For instructors and contributors *)

(** If you intend to use this course for teaching, please notify
    Arthur Charguéraud. *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the \CHAPV1{Preface}
    to _Logical Foundations_ for instructions.

    In particular, please do not hesitate to improve the formulation
    of the English sentences throughout this volume. *)


(* ########################################################### *)
(** * Thanks *)

(** The development of the technical infrastructure for the _Software
    Foundations_ series has been supported, in part, by the National Science
    Foundation under the NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)
