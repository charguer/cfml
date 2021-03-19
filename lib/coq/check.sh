REGEN=
# REGEN="rm *.cmj *_ml.v *.vo"

make -C ../.. install || exit 1
cd ../../examples/Stack
${REGEN}
make -f ../Makefile.dev || exit 1
cd ../UnitTests
${REGEN}
make -f ../Makefile.dev || exit 1


