# usage: ./go.sh

# For development purposes
# make sure to first recompile your local TLC

make -C ../../generator
make -f Makefile.dev _CoqProject
make -C ../../lib/coq -f Makefile.dev depend
make -j4 -C ../../lib/coq -f Makefile.dev
make -C ../../lib/stdlib -f Makefile.dev depend
make -j4 -C ../../lib/stdlib -f Makefile.dev
make -f Makefile.dev depend

ARG=$1
if [[ ${ARG} = "" ]]; then
  ARG="Debug_ml.vo"
fi
make -f Makefile.dev ${ARG}

# only for generation:
# ./go.sh Debug_ml.v

#coqide Debug_ml.v Debug_proof.v
