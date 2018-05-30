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

# The absolute name of the local folder.
LOCAL=`pwd`

# The absolute name of the root folder.
SOURCES=`pwd`/../../theories

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

# Try to compile (unless disabled).
if [ -z "${NO_TEST:-}" ]; then
    echo "Testing installation..."
    make -C $TARGET -j4
    echo "---Success!---"
    read -n 1 -p "Press ENTER to delete test folder, or Ctrl+C to keep the files."
    rm -Rf $TARGET
    echo "Cleared $TARGET."
fi
