#!/bin/bash

set -euo pipefail

# This script creates a self-contained archive containing a subset
# of the directory CFML/model related to the Iris proof mode.

#############################################################

# The list of files to export
FILES="TLCbuffer Fmap SepFunctor SepTactics LambdaSemantics LambdaSepRO ExampleROProofMode LambdaSep LambdaCF LambdaCFTactics LambdaStruct ExampleListProofMode"

# The name of the archive to create
TARGET="cfml2_iris"

# The absolute name of the archive directory.
ARCHIVE=`pwd`/$TARGET

# The absolute name of the current /model folder.
SOURCES=`pwd`

# Wipe out a previous archive.
rm -rf $ARCHIVE $ARCHIVE.tar.gz

# Create the archive folder
mkdir $ARCHIVE

# Copy a subset of CFML/model into the archive.
echo "Copying CFML/model selected files into $ARCHIVE..."
for i in ${FILES} ; do
  cp $SOURCES/$i.v $ARCHIVE ;
done

# Copy Makefile.iris into the archive as Makefile
cp $SOURCES/Makefile.iris $ARCHIVE/Makefile

# Copy README.iris into the archive as README.md
# TODO --- cp $SOURCES/README.iris $ARCHIVE/README.iris

# Add a HASH (current git hash) and DATE file to record the version
HASH="git log -1 --pretty=%H"
DATE="/bin/date +%Y%m%d"
(cd $SOURCES && $HASH) > $ARCHIVE/HASH
$DATE > $ARCHIVE/DATE

# Create a .tar.gz file
echo "Creating archive..."
tar -cvzf $TARGET.tar.gz $TARGET

# Try to compile.
exit
echo "Testing installation..."
make -C $ARCHIVE -j4
echo "OK."


