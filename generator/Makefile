.PHONY: all clean

ML_DIRS    := lex parsing typing utils
OCAMLBUILD := ocamlbuild -j 4 -classic-display \
	      $(addprefix -I ,$(ML_DIRS)) \
	      -cflags "-g" -lflags "-g" \
	      -use-ocamlfind -package pprint

all:
	$(OCAMLBUILD) cfml.native 

clean:
	rm -rf _build
	rm -f *.native
	rm -f *~
