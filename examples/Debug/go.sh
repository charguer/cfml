# For development purposes

make -C ../../generator
make -f Makefile.dev _CoqProject
make -j4 -f Makefile.dev $1

#coqide Debug_ml.v Debug_proof.v
