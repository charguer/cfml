#!/bin/bash

export FOLDER=`pwd`

ARGS="$@"
if [ -z ${ARGS} ]; then
  ARGS=libcoq
fi

cd ../..
make -f Makefile ${ARGS}

# -d
