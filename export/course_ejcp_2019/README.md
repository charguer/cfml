#############################################################
# Version of Coq

The theories compile with Coq 8.8 and they probably also compile 
with more recent versions. (Let me know otherwise.)



#############################################################
# Compilation


```
   git clone https://gitlab.inria.fr/charguer/cfml2_ejcp2019
   cd cfml2_ejcp2019/theories
   make
```


#############################################################
# Interactive session


To use CoqIDE, execute:

```
   ./open.sh
```

This script executes the following command:

```
   coqide -async-proofs off -async-proofs-command-error-resilience off EJCPTuto.v EJCPExo.v EJCPImplem.v ExampleStack.v ExampleList.v ExamplePairingHeap.v
```

The options to CoqIDE makes its use much smoother.


