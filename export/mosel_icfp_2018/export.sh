#!/bin/bash

set -euo pipefail

# This script creates a self-contained archive containing a subset
# of the root directory related to the Iris proof mode.

#############################################################

# The name of the archive to create
TARGET="cfml2_iris"

# The absolute name of the archive directory.
ARCHIVE=`pwd`/$TARGET

# The absolute name of the local folder.
LOCAL=`pwd`

# The absolute name of the root folder.
SOURCES=`pwd`/../..

# Wipe out a previous archive.
rm -rf $ARCHIVE $ARCHIVE.tar.gz

# Create the archive folder
mkdir $ARCHIVE
echo "Copying files into $ARCHIVE"

# Copy Makefile from the root as Makefile.main in the archive
cp $SOURCES/Makefile $ARCHIVE/Makefile.main

# Copy local Makefile and README.md in the archive
cp $LOCAL/Makefile $ARCHIVE
cp $LOCAL/README.md $ARCHIVE

# The list of files to export is read from the local Makefile
FILES_FROM_MAKEFILE=`sed -n -e '/SRC_FORCE := /p' Makefile`
FILES=$(echo $FILES_FROM_MAKEFILE| cut -d'=' -f 2)

# Copy a subset of CFML/model into the archive.
for i in ${FILES} ; do
  cp $SOURCES/$i.v $ARCHIVE ;
done

# Add a HASH (current git hash) and DATE file to record the version
HASH="git log -1 --pretty=%H"
DATE="/bin/date +%Y%m%d"
(cd $SOURCES && $HASH) > $ARCHIVE/HASH
$DATE > $ARCHIVE/DATE

# Create a .tar.gz file
echo "Creating $TARGET.tar.gz with contents:"
tar -cvzf $TARGET.tar.gz $TARGET

# Try to compile.
echo "Testing installation..."
make -C $ARCHIVE -j4
echo "OK."



