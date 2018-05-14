#!/bin/bash

set -euo pipefail

# This script creates a self-contained archive containing TLC and
# the directory CFML/model.

# A command to get the current git hash.
HASH="git log -1 --pretty=%H"
# A command to get the current date.
DATE="/bin/date +%Y%m%d"
# The absolute name of the archive directory.
ARCHIVE=`pwd`/seplogics
if [ ! -z ${ARTHUR+x} ]; then
  TLC=~/tlc/src
  # Where to find CFML.
  CFML=~/cfml
else
  # Where to find TLC.
  TLC=`coqc -where`/user-contrib/TLC
  # Where to find CFML.
  CFML=`coqc -where`/user-contrib/CFML
fi

# Wipe out a previous archive.
rm -rf $ARCHIVE $ARCHIVE.tar.gz

# Create the archive.
mkdir $ARCHIVE
$DATE > $ARCHIVE/DATE

# Copy TLC into the archive.
echo "Copying TLC..."
mkdir $ARCHIVE/TLC
(cd $TLC && $HASH) > $ARCHIVE/TLC/HASH
(cd $TLC && cp *.v Makefile Makefile.coq $ARCHIVE/TLC)

# Copy a subset of CFML into the archive.
echo "Copying CFML/model..."
mkdir $ARCHIVE/model
if [ ! -z ${ARTHUR+x} ]; then
  FILES_FROM_MAKEFILE=`sed -n -e '/SRC := TLCbuffer/p' Makefile`
  FILES=$(echo $FILES_FROM_MAKEFILE| cut -d'=' -f 2)
  # FILES="TLCbuffer Fmap SepFunctor SepTactics LambdaSemantics LambdaSep LambdaCF LambdaStruct LambdaSepLifted LambdaCFLifted LambdaStructLifted ExampleBasic ExampleHigherOrder ExampleList ExampleBasicLifted ExampleListLifted ExampleUnionFind"
else
  FILES=`grep -v -e "^ *#" FILES` ;
fi
for i in ${FILES} ; do
  cp $CFML/model/$i.v $ARCHIVE/model/ ;
done


(cd $CFML && $HASH) > $ARCHIVE/model/HASH

# Copy Makefile.model into the archive as model/Makefile.
cp $CFML/model/Makefile.model $ARCHIVE/model/Makefile
# Copy Makefile.root into the archive as Makefile.
cp $CFML/model/Makefile.root $ARCHIVE/Makefile

# Copy README and INSTALL into the archive.
cp $CFML/model/README.md $ARCHIVE/README.md
cp $CFML/model/INSTALL.export $ARCHIVE/INSTALL

# Create a .tar file, filtering out the files that we do not wish or
# need to publish. (TEMPORARY.)
echo "Creating archive..."
(
  cd `dirname $ARCHIVE` &&
  ARCHIVE=`basename $ARCHIVE` &&
  tar \
  -X $CFML/.gitignore \
  --exclude=.git \
  --exclude=.gitignore \
  --exclude=attic \
  --exclude=open.sh \
  -cvz -f $ARCHIVE.tar.gz $ARCHIVE
)

# Remove the archive directory, and re-create it from the .tar file.
rm -rf $ARCHIVE
(
  cd `dirname $ARCHIVE` &&
  ARCHIVE=`basename $ARCHIVE` &&
  tar xfz $ARCHIVE.tar.gz
)
# Try to compile.
echo "Testing installation..."
make -C $ARCHIVE -j4
echo "OK."


