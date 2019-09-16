(**

Separation Logic: Verification with Characteristic Formulae

Chapter: "Intro".

Author: Arthur Charguéraud.
License: MIT.

*)

(* ####################################################### *)
(** * Structure *)

(** The "Separation Logic Foundations" course includes the following chapters,
    one file per chapter.


    - [CFIntro]: the present introduction, which lists the chapters.

    - [CFList]:

    - [CFTree]:

    - [CFQueue]:

    - [CFQueueOf]:

    - [CFPairingHeap]:

    - [CF_UF_Pointer]

*)

(* ####################################################### *)
(** * Future work *)

(** There are three future chapters, planned but not yet written:

    - [CFArray]: quicksort

    - [CFVector]:

    - [CF_UF_Array]

    - [CFLoops]:

    - [CFIterators]:

    - [CFFirstClass]:  CPS and counter

*)

(* ####################################################### *)
(** * With OCaml-to-CF generator *)

(**
    - Sized stack

    - Batched queue

    - Hahstable

    - Fixed capacity buffer

    - Chunked stack

    - Chunked sequence

    - Doubly-linked list

    - Erathostenes Sieve

    - Okasaki numeric representation

    - LambdaBytecodeCompiler

*)




(* ####################################################### *)
(** * TLC tactics and library *)

(** The proofs are carried out using TLC tactics, which greatly help.
    Most of the tactics used are described in the SF chapter [UseTactics]
    from the "Programming Language Foundations" course.

    The proofs also rely occasionnally on lemmas from the TLC library,
    for example extensionality properties.

*)

