make -C ../../generator \
&& make -C ../coq -j3 \
&& make

WID=`xdotool search --onlyvisible --class CoqIde | tail -1`

if [ -z "${WID}" ]; then
  coqide -async-proofs off -async-proofs-command-error-resilience off Pervasives_proof.v Array_proof.v List_proof.v Pervasives_ml.v Array_ml.v List_ml.v   &
else
  # xdotool windowactivate ${WID}
  exit 0
fi




