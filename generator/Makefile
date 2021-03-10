.PHONY: all clean

ML_DIRS    := lex parsing typing utils
OCAMLBUILD := ocamlbuild -j 4 -classic-display \
	      $(addprefix -I ,$(ML_DIRS)) \
	      -cflags "-g" -lflags "-g" \
	      -use-ocamlfind -package pprint

all: cfml_config.ml
	$(OCAMLBUILD) cfmlc.native 

cfml_config.ml:
	$(error Type 'make -C .. generator' to first generate cfml_config.ml)

clean:
	rm -rf _build
	rm -f *.native
	rm -f *~
