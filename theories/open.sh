#!/bin/bash

pwd
COQBIN=
if [ -f ./settings.sh ]
then
    source settings.sh
fi
COQIDE_OPTIONS="-async-proofs off -async-proofs-command-error-resilience off -w -implicits-in-term,-redundant-canonical-projection,-several-object-files,-ambiguous-paths,-implicit-core-hint-db"
echo "${COQBIN}coqide ${COQIDE_OPTIONS}  `cat _CoqProject` $*"
${COQBIN}coqide ${COQIDE_OPTIONS} `cat _CoqProject` $*

#-dont-load-proofs  -async-proofs-j 1
