#!/bin/bash

export CFMLC_FLAGS="-credits"
# "-deep_embedding -def_encoders"
export FOLDER=`pwd`
cd ../..
make -f Makefile.dev $@
