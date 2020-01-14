#############################################################
# Contents

  - toc.html
    The navigation starting point

  - Files SLF*.v 
    Contents of the course

  - Files Lib*.v 
    Contents of the TLC library

  - Other *.v files
    Implementation of CFML



#############################################################
# Compilation

The theories compile with Coq 8.8 and Coq 8.9.

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


For material associated with the seminar at the "Collège de France", execute:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF CollegeDeFrance.v
```
