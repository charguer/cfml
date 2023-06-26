#!/bin/bash

export CFMLC_FLAGS="-credits"
export FOLDER=`pwd`
cd ../..
make -f Makefile.dev $@
