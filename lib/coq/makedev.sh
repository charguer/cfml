#!/bin/bash

export ARG_EXAMPLEINCLUDE=EMPTY
export DONT_INCLUDE_ALL_STDLIB_V=true

ARGS="$@"
if [ -z ${ARGS} ]; then
  ARGS=libcoq
fi

cd ../..
make -f Makefile.dev ${ARGS}

# -d