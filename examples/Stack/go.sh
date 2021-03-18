rm *.cmj *.vo *_ml.v
make -C ../.. install \
&& make -f ../Makefile.dev _CoqProject \
&& make -f ../Makefile.dev
# && make -f ../Makefile.dev ML=`pwd`/StackSized.ml
# FILE=`basename \`pwd\``
coqide -async-proofs off -async-proofs-command-error-resilience off StackSized_proof.v Stack_proof.v StackSized_ml.v Stack_ml.v  &


# make -f ../Makefile.dev `pwd`/UnitTests_ml.v
