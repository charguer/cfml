# usage: ./go.sh

# For development purposes
# make sure to first recompile your local TLC

make -C ../../generator
make -f Makefile.dev _CoqProject
make -C ../../lib/coq -f Makefile.dev depend
make -C ../../lib/coq -f Makefile.dev
make -C ../../lib/stdlib -f Makefile.dev depend
make -C ../../lib/stdlib -f Makefile.dev
make -f Makefile.dev depend
make -f Makefile.dev

#coqide Debug_ml.v Debug_proof.v
