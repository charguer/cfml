# usage:
# ./go.sh
# ./go.sh mlv


ARG=$1
if [[ ${ARG} = "" ]]; then
  ARG="Debug_ml.vos"
fi


# For development purposes
# make sure to first recompile your local TLC

make -C ../../generator
make -f Makefile.dev _CoqProject

if [[ ${ARG} = "mlv" ]]; then

  make -C ../../lib/stdlib -f Makefile.dev depend
  make -j4 -C ../../lib/stdlib -f Makefile.dev Pervasives_ml.v
  make -f Makefile.dev ${ARG}

else

  make -C ../../lib/coq -f Makefile.dev depend
  make -j4 -C ../../lib/coq -f Makefile.dev vos
  make -C ../../lib/stdlib -f Makefile.dev depend
  if [[ ${ARG} = "Debug_ml.vos" ]]; then
    make -j4 -C ../../lib/stdlib -f Makefile.dev Pervasives_proof.vos
  else
    make -j4 -C ../../lib/stdlib -f Makefile.dev vos
  fi
  make -f Makefile.dev depend
  make -f Makefile.dev ${ARG}
  # make -j4 -C ../../lib/stdlib -f Makefile.dev vos

fi


#coqide Debug_ml.v Debug_proof.v
