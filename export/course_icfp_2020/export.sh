#!/bin/bash

##############################################################################
# Configuration

PDF=~/work/sep/main_with_appendix.pdf
SOURCE=~/versions/coq-8.9.1/sfdev/slf/full
TARGET=slf

CP="cp -u"


##############################################################################
# Create target folder

rm -Rf ${TARGET}
mkdir -p ${TARGET}


##############################################################################
# Import local files

${CP} README.md ${TARGET}


echo "Copy appendix"
${CP} ${PDF} ${TARGET}/paper_with_appendix.pdf


##############################################################################
# Import SLF files

${CP} -R ${SOURCE}/common ${TARGET}

${CP} ${SOURCE}/*.v ${SOURCE}/*.html ${SOURCE}/*.gif ${SOURCE}/_CoqProject ${SOURCE}/Makefile ${SOURCE}/LICENSE ${TARGET}


##############################################################################
# Tweaks

# bypass index
${CP} ${TARGET}/toc.html ${TARGET}/index.html

# anonymize
FILES=`ls ${TARGET}/*.v ${TARGET}/*.html`
for i in ${FILES}; do
   sed -i'' 's/Arthur\ Charguéraud/Anonymous/g;s/Chargueraud/Anonymous/g;' $i;
done

# fix star symbol
FILES=`ls ${TARGET}/*.html`
for i in ${FILES}; do
   sed -i'' 's/×/*/g;' $i;
done



##############################################################################
# Create archive

echo "Creating $TARGET.tar.gz"
tar ${TAROPTIONS} -czf $TARGET.tar.gz $TARGET


##############################################################################
# Test archive

cd ${TARGET}
make -j8
chromium-browser index.html &
coqide -async-proofs off -async-proofs-command-error-resilience off -Q . SLF SLFMinimal.v
