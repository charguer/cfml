#!/bin/bash

##############################################################################
# Configuration

TARGET=~/shared/coq-9.8.1/sfdev/slf

CFML_FOLDER=../../theories
DOC_FOLDER=../../doc
TLC_FOLDER=~/shared/coq-9.8.1/tlc/src

CP="cp -u"


##############################################################################
# File list

CFML_IMPORTS="TLCbuffer.v Fmap.v Var.v SepSimpl.v Bind.v Semantics.v SepFunctor.v SepBase.v WPBase.v SepLifted.v WPLifted.v WPTactics.v WPRecord.v WPLib.v Example.v"

SLF_IMPORTS="SLFIntro.v SLFDirect.v SLFExtra.v SLFSummary.v SLFBasic.v SLFList.v SLFHprop.v SLFHimpl.v SLFRules.v SLFWPsem.v SLFWPgen.v"

TLC_IMPORTS="LibAxioms.v LibTactics.v LibEqual.v LibLogic.v LibOperation.v LibBool.v LibReflect.v LibProd.v LibSum.v LibRelation.v LibOrder.v LibNat.v LibEpsilon.v LibInt.v LibMonoid.v LibContainer.v LibOption.v LibWf.v LibList.v LibListZ.v LibMin.v LibSet.v LibChoice.v LibUnit.v LibCore.v LibFun.v LibFix.v LibMap.v LibString.v LibMultiset.v"

DOC_IMPORTS="cheatlist.pdf"


##############################################################################
# Import local files

${CP} cheatlist.pdf ${TARGET}/cfml_tlc_cheatlist.pdf


##############################################################################
# Import TLC

for i in ${TLC_IMPORTS} ; do
  ${CP} ${TLC_FOLDER}/$i ${TARGET} ;
  sed -i -e 's/^From[[:space:]]TLC[[:space:]]/From SLF/' ${TARGET}/$i ;
done


##############################################################################
# Import CFML

for i in ${CFML_IMPORTS} ; do
  ${CP} ${CFML_FOLDER}/$i ${TARGET} ;
  sed -i -e 's/^From[[:space:]]Sep[[:space:]]/From SLF/' ${TARGET}/$i ;
done


##############################################################################
# Import SLF

if [[ -z "${EXPORT_SLF}" ]]; then

  echo "Skipping import of SLF files"

else

  echo "Performing import of SLF files"

  for i in ${SLF_IMPORTS} ; do
    ${CP} ${SLF_FOLDER}/$i ${TARGET} ;
    sed -i -e 's/^From[[:space:]]Sep[[:space:]]/From SLF/' ${TARGET}/$i ;
  done

fi
