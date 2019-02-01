#!/bin/bash

set -euo pipefail

# This script creates a self-contained archive containing a subset
# of the root directory related to the Iris proof mode.

#############################################################

# The name of the archive to create must be set, e.g.
# TARGET="credits_sep"

if [ -z "$TARGET" ]; then
   echo "TARGET not set";
   exit 1
fi

#############################################################


# The absolute name of the archive directory.
ARCHIVE=`pwd`/$TARGET

# The absolute name to the source directory.
THEORIES=${ARCHIVE}/theories

# The absolute name of the local folder.
LOCAL=`pwd`

# The absolute name of the root folder.
SOURCES=`pwd`/../../theories

# Wipe out a previous archive.
rm -rf $ARCHIVE $ARCHIVE.tar.gz

# Create the archive folder
mkdir $ARCHIVE
mkdir -p $THEORIES
echo "Copying files into $ARCHIVE"

# Copy Makefile from the root as Makefile.main in the archive
cp $SOURCES/Makefile $THEORIES/Makefile.main

# Copy local Makefiles and README.md and extra files in the archive
cp $LOCAL/Makefile $ARCHIVE/Makefile
cp $LOCAL/Makefile.theories $THEORIES/Makefile
cp $LOCAL/README.md $ARCHIVE
if [ ! -z "${EXTRAFILES:-}" ]; then
  for i in ${EXTRAFILES} ; do
    cp $LOCAL/$i $ARCHIVE ;
  done
fi

# The list of files to export is read from the local Makefile
FILES_FROM_MAKEFILE=`sed -n -e '/SRC_FORCE := /p' Makefile.theories`
FILES=$(echo $FILES_FROM_MAKEFILE| cut -d'=' -f 2)

# Copy a subset of CFML/model into the archive.
for i in ${FILES} ; do
  cp $SOURCES/$i.v $THEORIES ;
done

# Anonymize if requested
TAROPTIONS=""
if [ ! -z "${ANONYMIZE:-}" ]; then
  TAROPTIONS="--owner=0 --group=0"
  echo "Anonymizing files..."
  for i in ${FILES} ; do
    sed -i'' 's/Arthur\ Charguéraud/Anonymous/g;s/François\ Pottier/Anonymous/g;s/Armaël\ Guéneau\ Pottier/Anonymous/g;s/Jacques-Henri\ Jourdan/Anonymous/g;' $THEORIES/$i.v
  done
fi

# Include TLC files if requested
if [ ! -z "${INCLUDETLC}" ]; then
  echo "Including TLC files..."
  mkdir -p ${ARCHIVE}/TLC
  TLCSRC=`ls ${INCLUDETLC}/*.v`
  for i in ${TLCSRC} ; do
    cp $i $ARCHIVE/TLC ;
  done
  cp $INCLUDETLC/Makefile.coq $ARCHIVE/TLC ;
  cp $INCLUDETLC/Makefile $ARCHIVE/TLC ;
fi

# Add a HASH (current git hash) and DATE file to record the version
HASH="git log -1 --pretty=%H"
DATE="/bin/date +%Y%m%d"
(cd $SOURCES && $HASH) > $ARCHIVE/HASH
$DATE > $ARCHIVE/DATE

# Create a .tar.gz file
echo "Creating $TARGET.tar.gz with contents:"
tar ${TAROPTIONS} -cvzf $TARGET.tar.gz $TARGET

# Try to compile (unless disabled).
if [ -z "${NO_TEST:-}" ]; then
    echo "Testing installation..."
    make -C $TARGET -j4
    echo "---Success!---"
    read -n 1 -p "Press ENTER to delete test folder, or Ctrl+C to keep the files."
    rm -Rf $TARGET
    echo "Cleared $TARGET."
fi
