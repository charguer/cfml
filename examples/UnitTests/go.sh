# make -C ../../generator \
# && make -C../../lib/coq -j3 \
# && make -C ../../lib/stdlib \
make -C ../.. install \
&& make -f ../Makefile.dev _CoqProject \
&& make -f ../Makefile.dev
coqide -async-proofs off -async-proofs-command-error-resilience off UnitTests_ml.v &


# make -f ../Makefile.dev `pwd`/UnitTests_ml.v
