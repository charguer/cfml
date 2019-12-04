(** * Preface *)

(** *** Warning! Beta release! *)

(** This textbook is in beta release.

    If you intend to use this course as a teacher, please notify
    Arthur Charguéraud. *)

(** * Welcome *)

(** This electronic book is Volume 5 of the _Software Foundations_
    series, which presents the mathematical underpinnings of reliable
    software.

    In this volume, you will learn about the foundations of Separation
    Logic, which is a successful technique for the modular verification
    of imperative programs.

    You are assumed to understand the material in Software Foundations
    Volume 1 (Logic Foundations), and the two chapters on Hoare Logic
    (Hoare and Hoare2) from Software Foundations Volume 2 (PL
    Foundations).

    The exposition here is intended for a broad range of readers, from
    advanced undergraduates to PhD students and researchers.  *)

(** * Organization of the files *)

(** ** Chapters *)

(** The "Separation Logic Foundations" course includes the following chapters,
    one file per chapter.

    - [SLFPreface]: the present introduction, which lists the chapters.

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

*)

(** ** Organization of each chapter *)

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

(** ** Special chapters *)

(**
    - [SLFDirect]: provides the minimal set of definitions and lemmas required
                   to build an effective program verification tool, without detour.
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


(** ** Imports between files *)

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


(** ** TLC tactics and libraries *)

(** The proofs are carried out using TLC tactics, which greatly help.
    Most of the tactics used are described in the SF chapter [UseTactics]
    from the "Programming Language Foundations" course.

    The first two chapters, [SLFBasic] and [SLFList], are careful to use as
    few TLC tactics as possible, and to explain the ones that are used.
    In the other chapters, TLC tactics are used in proof scripts for
    conciseness, however familiarity with these tactics should not be
    necessary to follow through the proofs. Exercises can be carried out
    without using TLC tactics.

    Note that a few proofs also rely occasionally on lemmas from the
    TLC library, for example extensionality properties, or results on lists.
    Such lemmas are described whenever they are relevant to a proof. *)


(** * Practicalities *)

(** ** System Requirements *)

(** The Preface of Volume 1 describes the Coq installation you will
    need. This edition was built with $(COQVERSION). *)

(** ** TLC and CFML libraries *)

(** To simplify the compilation process, copies of the source files from
    the TLC and the CFML libraries are included in the present folder.
    There is no need to look at these files. *)

(** ** Note for CoqIDE users *)

(** CoqIDE works better with its "asynchronous" proof mode disabled.
    To load all the course files in CoqIDE, use the following command line.

[[
	coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLF*.v &
]]

*)

(** ** Exercises *)

(** Each chapter includes numerous exercises.  The star rating scheme in
    use is described in the Preface of Volume 1. *)

(* LATER:

    Downloading the Coq Files

    A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at https://softwarefoundations.cis.upenn.edu.

    (If you are using the book as part of a class, your teacher may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.) *)

(** ** Recommended Citation Format *)

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

(** ** For instructors and contributors *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the \CHAPV1{Preface}
    to _Logical Foundations_ for instructions.

    In particular, please do not hesitate to improve the formulation
    of the English sentences throughout this volume. *)


(** * Thanks *)

(** The development of the technical infrastructure for the _Software
    Foundations_ series has been supported, in part, by the National Science
    Foundation under the NSF Expeditions grant 1521523, _The Science of Deep
    Specification_. *)

