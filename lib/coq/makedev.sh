#!/bin/bash

export VERBOSE=1

export ARG_EXAMPLEINCLUDE=EMPTY
export DONT_INCLUDE_ALL_STDLIB_V=true
cd ../..
ARGS="$@"
if [ -z ${ARGS} ]; then
  ARGS=libcoq
fi

make -f Makefile.dev ${ARGS}

# -d