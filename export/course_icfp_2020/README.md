
#############################################################
# Relevant files

  - paper_with_appendix.pdf
    Includes the 10-page appendix

  - SLFMinimal.v
    The minimal soundness proof of Separation Logic for sequential programs

  - SLFHprop.v
    Heap predicates

  - SLFHimpl.v
    Entailment

  - SLFRules.v
    Reasoning rules
   
  - SLFWPsem.v
    Formalization of the wp predicate

  - SLFWand.v
    Magic wand operator

  - SLFAffine.v
    Generalization to a partially-affine logic



#############################################################
# Other files

  - Files SLF*.v (except SLFBasic, SLFSummary, and SLFWPgen, which are not covered by the paper)
    Contents of the course

  - index.html
    The navigation starting point for html browsing

  - Files Lib*.v 
    Contents of the TLC library (a general-purpose Coq library)

  - Other *.v files
    Auxiliary implementation files



#############################################################
# Compilation

The theories should compile with any version of Coq from 8.8 to 8.11.

```
   tar -xzf slf.tar.gz
   cd slf
   make

   # alternative: make -j4
```


#############################################################
# Interactive session


To play the files in CoqIDE, execute the following command:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLF*.v
```

Remark: the options provided to CoqIDE makes its use much smoother.


To load SLFMinimal.v in CoqIDE, use the command:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLFMinimal.v
```
