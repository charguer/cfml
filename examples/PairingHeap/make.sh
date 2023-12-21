#!/bin/bash

export CFMLC_FLAGS="-deep_embedding -def_encoders"
export FOLDER=`pwd`
cd ../..
make -f Makefile $@
