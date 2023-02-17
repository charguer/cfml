make

#cd ../examples/Debug/ && \
#rm Debug_ml.v && \
#./go.sh

#&& ../../generator/_build/default/generator/cfmlc.exe -deep_embedding Debug.ml \
#&& echo "Produced ../Debug_ml.v" \
#&& coqc -w -notation-overridden,-implicit-core-hint-db,-omega-is-deprecated,-ambiguous-paths,-irrelevant-format-only-parsing,-deprecated-hint-without-locality,-deprecated-ident-entry,-custom-entry-overriden -Q /home/charguer/tlc/src TLC -Q ../../lib/coq CFML -R ../../lib/stdlib CFML.Stdlib -R .. EXAMPLES Debug_ml.v

# ocamlbuild -I parsing -I typing -I utils cfmlc.byte