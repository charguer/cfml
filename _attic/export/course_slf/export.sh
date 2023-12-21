#!/bin/bash

##############################################################################
# Configuration

SOURCE=~/versions/coq-8.13/sfdev/_built/slf/full
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
rm ${TARGET}/common/media/image/{vc*,qc*,vfa*,lf*,plf*}

${CP} ${SOURCE}/*.html ${TARGET}
#${SOURCE}/*.gif

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

# Move the archive into folder to ease upload
cp $TARGET.tar.gz $TARGET


##############################################################################
# Test archive

cd ${TARGET}
make
chromium-browser index.html &
coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF Preface.v Basic.v Repr.v
