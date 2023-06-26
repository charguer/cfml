#!/bin/bash

if [ -z ${FOLDER} ]; then
  export FOLDER=`pwd`
fi

make -f Makefile.dev $*
