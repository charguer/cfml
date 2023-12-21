#!/bin/bash

export FOLDER=`pwd`

cd ../..
ARGS="$@"
if [ -z ${ARGS} ]; then
  ARGS=stdlib
fi

make -f Makefile ${ARGS}
