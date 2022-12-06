#!/bin/bash

# Usage: ./pretty_print_coq_file.sh Demo.v
# Generates: Demo_printed.v
# with the result of calling "Print" on every definitions (or inductive, or parameter)

FILENAME="$1"
BASE=`basename ${FILENAME} .v`

grep -Po "(Definition|Inductive|Parameter\|Fixpoint) [^\s]*" ${BASE}.v > ${BASE}_print.v
sed "s/\(Definition\|Inductive\|Parameter\|Fixpoint\)/Print/g" -i ${BASE}_print.v
sed "s/$/./g" -i ${BASE}_print.v
sed -i "1 i\Require Import Prelude ${BASE} String." ${BASE}_print.v
coqc ${BASE}_print.v > ${BASE}_printed.v
sed -i /^Arguments/d ${BASE}_printed.v
#echo "Generated ${BASE}_printed.v"
