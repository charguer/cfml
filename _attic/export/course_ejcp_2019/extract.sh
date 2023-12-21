#!/bin/bash

##############################################################################
# Configuration

TARGET=~/shared/cfml2_ejcp2019
THEORIES_TARGET=${TARGET}/theories
DOC_TARGET=${TARGET}/doc

CFML_FOLDER=~/cfml2/theories
TLC_FOLDER=~/tlc/src
DOC_FOLDER=~/cfml2/doc

CP="cp -u"

##############################################################################
# File list

CFML_IMPORTS="Example.v ExampleList.v ExampleListOf.v ExampleStack.v ExamplePairingHeap.v TLCbuffer.v Fmap.v Var.v SepSimpl.v Bind.v Semantics.v SepFunctor.v SepBase.v WPBase.v SepLifted.v WPLifted.v WPTactics.v WPRecord.v WPLib.v EJCPTuto.v EJCPExo.v EJCPImplem.v SLFIntro.v SLFDirect.v SLFExtra.v SLFHprop.v SLFHimpl.v SubstExec.v SLFRules.v SLFWand.v SLFWPsem.v SLFWPgen.v"

TLC_IMPORTS="LibAxioms.v LibTactics.v LibEqual.v LibLogic.v LibOperation.v LibBool.v LibReflect.v LibProd.v LibSum.v LibRelation.v LibOrder.v LibNat.v LibEpsilon.v LibInt.v LibMonoid.v LibContainer.v LibOption.v LibWf.v LibList.v LibListZ.v LibMin.v LibSet.v LibChoice.v LibUnit.v LibCore.v LibFun.v LibFix.v LibMap.v LibString.v LibMultiset.v Makefile.coq"

DOC_IMPORTS="cheatlist.pdf"


##############################################################################
# Create target folder

mkdir -p ${THEORIES_TARGET}
mkdir -p ${DOC_TARGET}


##############################################################################
# Import local files

cp README.md ${TARGET}

cp Makefile ${THEORIES_TARGET}

cp open.sh ${THEORIES_TARGET}


##############################################################################
# Import CFML

for i in ${CFML_IMPORTS} ; do
  ${CP} ${CFML_FOLDER}/$i ${THEORIES_TARGET} ;
done


##############################################################################
# Import TLC

for i in ${TLC_IMPORTS} ; do
  ${CP} ${TLC_FOLDER}/$i ${THEORIES_TARGET} ;
done


##############################################################################
# Import DOC

for i in ${DOC_IMPORTS} ; do
  ${CP} ${DOC_FOLDER}/$i ${DOC_TARGET} ;
done


##############################################################################
# Remove "From TLC" and "From Sep"

cd ${THEORIES_TARGET}
sed -i -e 's/^From[[:space:]]TLC[[:space:]]//' *.v
sed -i -e 's/^From[[:space:]]Sep[[:space:]]//' *.v


##############################################################################
# Remove solutions

cd ${THEORIES_TARGET}
perl -i -pe 'BEGIN{undef $/;} s/\(\* SOLUTION \*\).*?\(\* \/SOLUTION \*\)/ (* FILL *) /smg' EJCPExo.v
