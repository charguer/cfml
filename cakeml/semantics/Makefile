#####################################################
# Configuration

# User-defined file to store path to directories
-include settings.sh

# Default paths used in case settings.sh is missing
# and the environment variables are undefined.

HOLDIR ?= ~/softs/cakeml_semantics/HOL
CAKEMLDIR ?= ~/softs/cakeml_semantics/cakeml


#####################################################
# Global

GENERATOR=../../generator
TRANS_LIBRARY=coq.ml print_coq.ml coq_from_hol.ml

all: demo cakeml

#####################################################
# Library

coq.ml:
	ln -s $(GENERATOR)/coq.ml coq.ml

print_coq.ml:
	ln -s $(GENERATOR)/print_coq.ml print_coq.ml



#####################################################
# Generic rules

%.vo: %.v
	coqc $<


#####################################################
# Rules for "demo" (unit tests)

demo: Demo.vo Demo_proofs.vo Demo_printed.v

demo.ml:
	ln -s demo_sample.ml $@

demo.byte: demo.ml $(TRANS_LIBRARY)
	ocamlbuild -package pprint $@

Demo.v Demo_obligations.v: demo.byte demo.ml 
	./demo.byte

Demo_printed.v: Demo.v ./pretty_print_coq_file.sh
	./pretty_print_coq_file.sh Demo.v

Demo.vo: Prelude.vo
Demo_proofs.vo: Demo_obligations.vo Demo.vo

demo_ide:
	coqide Demo.v Demo_obligations.v Demo_proofs.v &


#####################################################
# Rules for "cakeml" (real semantics)

cakeml: Cakeml.vo

# Temporary rule for producing a basic `cakeml.ml`
cakeml_from_sample:
	cp cakeml_sample.ml $@

# Real rule for producing `cakeml.ml`
cakeml.ml: sampleScript.sml
	CAKEMLDIR=$(CAKEMLDIR) $(HOLDIR)/bin/Holmake

cakeml.byte: cakeml.ml $(TRANS_LIBRARY)
	ocamlbuild -package pprint $@

Cakeml.vo: Prelude.vo

Cakeml.v: cakeml.byte cakeml.ml 
	./cakeml.byte

cakeml_ide:
	coqide Cakeml.v &

# LATER: proof obligations 


#####################################################
# Cleanup 

clean:
	rm -Rf _build
	rm -f coq.ml print_coq.ml
	rm -f Cakeml.v Demo.v Demo_obligations.v *.vo
	rm -f *_print.v *_printed.v


#####################################################
# Debug 

show_path:
	@echo $(HOLDIR)
	@echo $(CAKEMLDIR)
