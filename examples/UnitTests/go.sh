make -C ../../generator \
&& make -C../../lib/coq -j3 \
&& make -C ../../lib/stdlib \
&& make -f ../Makefile.dev


# make -f ../Makefile.dev `pwd`/UnitTests_ml.v