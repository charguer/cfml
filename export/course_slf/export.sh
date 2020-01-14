#!/bin/bash

##############################################################################
# Configuration

SOURCE=~/versions/coq-8.9.1/sfdev/slf/full
TARGET=slf

CP="cp -u"


##############################################################################
# Create target folder

rm -Rf ${TARGET}
mkdir -p ${TARGET}


##############################################################################
# Import local files

cp README.md ${TARGET}


##############################################################################
# Import SLF files

${CP} -R ${SOURCE}/common ${TARGET}

${CP} *.v *.html *.gif _CoqProject Makefile LICENSE ${TARGET}

for i in ${CFML_IMPORTS} ; do
   ${CFML_FOLDER}/$i ${THEORIES_TARGET} ;
done


##############################################################################
# Create archive

echo "Creating $TARGET.tar.gz with contents:"
tar ${TAROPTIONS} -cvzf $TARGET.tar.gz $TARGET


##############################################################################
# Test archive

exit
cd ${TARGET}
make -j8
coqide -async-proofs off -async-proofs-command-error-resilience off CollegeDeFrance.v
