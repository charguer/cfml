#############################################################
# Version of Coq

The theories compile with Coq 8.8 and Coq 8.9.


#############################################################
# Compilation


```
   git clone https://gitlab.inria.fr/charguer/cfml2_ejcp2019
   cd cfml2_ejcp2019/theories
   make -j2
```

If your machine features more than 2 cores, adjust the number after "-j" accordingly.


#############################################################
# Interactive session


To use CoqIDE, execute:

```
   ./open.sh
```

This script executes the following command:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off EJCPTuto.v EJCPExo.v EJCPImplem.v ExampleList.v ExampleListOf.v ExamplePairingHeap.v
```

The options to CoqIDE makes its use much smoother.


