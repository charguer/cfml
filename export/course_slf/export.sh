#!/bin/bash

##############################################################################
# Configuration

SOURCE=~/versions/coq-8.9.1/sfdev/slf/full
TARGET=slf
WEBSITE=website

CP="cp -u"


##############################################################################
# Create target folder

rm -Rf ${TARGET}
mkdir -p ${TARGET}

rm -Rf ${WEBSITE}


##############################################################################
# Import Website files

${CP} -R ${SOURCE}/common ${TARGET}

${CP} ${SOURCE}/*.html ${SOURCE}/*.gif ${TARGET}

# bypass index
${CP} ${TARGET}/toc.html ${TARGET}/index.html

${CP} -R ${TARGET} ${WEBSITE}


##############################################################################
# Import Dev files

${CP} README.md ${TARGET}

${CP} ${SOURCE}/*.v ${SOURCE}/_CoqProject ${SOURCE}/Makefile ${SOURCE}/LICENSE ${TARGET}


##############################################################################
# Create archive

echo "Creating $TARGET.tar.gz"
tar ${TAROPTIONS} -czf $TARGET.tar.gz $TARGET


##############################################################################
# Test archive

cd ${TARGET}
make -j8
chromium-browser index.html &
coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLFPreface.v SLFSummary.v
