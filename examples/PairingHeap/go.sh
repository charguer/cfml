
# usage:
# ./go.sh
# ./go.sh mlv


ARG=$1
if [[ ${ARG} = "" ]]; then
  ARG="PairingHeap_ml.vos"
fi

if [[ ${ARG} = "clean" ]]; then

make -j4 -C ../../lib/coq -f Makefile.dev clean
make -C ../../lib/stdlib -f Makefile.dev clean
make -f Makefile.dev clean

exit

fi

# For development purposes
# make sure to first recompile your local TLC

make -C ../../generator
make -f Makefile.dev _CoqProject

if [[ ${ARG} = "mlv" ]]; then

  make -C ../../lib/stdlib -f Makefile.dev depend
  make -j4 -C ../../lib/stdlib -f Makefile.dev depend
  make -j4 -C ../../lib/stdlib -f Makefile.dev Pervasives_ml.v
  make -f Makefile.dev depend
  make -f Makefile.dev ${ARG}

else

  make -C ../../lib/coq -f Makefile.dev depend
  make -j4 -C ../../lib/coq -f Makefile.dev vos
  make -C ../../lib/stdlib -f Makefile.dev depend
  make -j4 -C ../../lib/stdlib -f Makefile.dev vos
  make -f Makefile.dev depend
  make -f Makefile.dev MList_proof.vos
  make -f Makefile.dev ${ARG}
  # make -j4 -C ../../lib/stdlib -f Makefile.dev vos

fi


#coqide Debug_ml.v Debug_proof.v



exit



# usage:
# ./go.sh
# ./go.sh mlv


make V= -f Makefile.dev -C ../../lib/coq depend
make V= -f Makefile.dev -C ../../lib/coq
make V= -f Makefile.dev -C ../../lib/stdlib depend
make V= -f Makefile.dev -C ../../lib/stdlib

make V= -f Makefile.dev depend
make V= -f Makefile.dev MList_ml.v
make V= -f Makefile.dev MList_ml.vo
make V= -f Makefile.dev MList_proof.vo
make V= -f Makefile.dev PairingHeap_ml.vo
make V= -f Makefile.dev PairingHeap_proof.vo

exit

BASE=PairingHeap

ARG=$1
if [[ ${ARG} = "" ]]; then
  ARG="${BASE}_ml.vo"
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
  make -j4 -C ../../lib/coq -f Makefile.dev
    make -C ../../lib/stdlib -f Makefile.dev depend
if [[ ${ARG} = "${BASE}_ml.vo" ]]; then
  make -j4 -C ../../lib/stdlib -f Makefile.dev Pervasives_proof.vo
else
  make -j4 -C ../../lib/stdlib -f Makefile.dev
fi
  make -f Makefile.dev depend
  make -f Makefile.dev ${ARG}
  make -j4 -C ../../lib/stdlib -f Makefile.dev

fi


#coqide Debug_ml.v Debug_proof.v
