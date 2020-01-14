#!/bin/bash

##############################################################################
# Configuration

SOURCE=~/versions/coq-8.9.1/sfdev/slf/full
TARGET=slf
SOURCE_COLLEGE=../../theories/CollegeDeFrance.v

CP="cp -u"


##############################################################################
# Create target folder

rm -Rf ${TARGET}
mkdir -p ${TARGET}


##############################################################################
# Import local files

${CP} README.md ${TARGET}


##############################################################################
# Import SLF files

${CP} -R ${SOURCE}/common ${TARGET}

${CP} ${SOURCE}/*.v ${SOURCE}/*.html ${SOURCE}/*.gif ${SOURCE}/_CoqProject ${SOURCE}/Makefile ${SOURCE}/LICENSE ${TARGET}


##############################################################################
# Tweaks

# bypass index
${CP} ${TARGET}/toc.html ${TARGET}/index.html

# add college de France seminar
${CP} ${SOURCE_COLLEGE} ${TARGET}
sed -i -e 's/^From[[:space:]]Sep[[:space:]]/From SLF (* Sep *) /' ${TARGET}/CollegeDeFrance.v


##############################################################################
# Create archive

echo "Creating $TARGET.tar.gz"
tar ${TAROPTIONS} -czf $TARGET.tar.gz $TARGET


##############################################################################
# Test archive

cd ${TARGET}
make -j8
chromium-browser index.html &
coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF CollegeDeFrance.v
