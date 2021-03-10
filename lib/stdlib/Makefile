##############################################################################
# CFML setup.

CFML := $(shell cd ../.. && pwd)

include $(CFML)/Makefile.common

##############################################################################
# Compilation.

# The line "-R $(TLC) TLC" is required only if we wish to write just
# "LibFoo", as opposed to "TLC.LibFoo". In the long run, I believe it
# would be preferable to explicitly use the TLC prefix.

PWD := $(shell pwd)
export
COQINCLUDE := \
  -Q $(TLC) TLC \
  -Q $(CFML)/lib/coq CFML \
  -Q $(PWD) CFML.Stdlib

##############################################################################
# Files.

PWD    := $(shell pwd)
LIBCOQ := $(shell cd ../coq && pwd)

ML     := $(wildcard $(PWD)/*.ml)
CMJ    := $(patsubst %.ml,%.cmj,$(ML))

V      := $(patsubst %.ml,%_ml.v,$(ML)) \
	  $(patsubst %.ml,%_proof.v,$(ML)) \
	  Stdlib.v

ifdef INCLUDE_TLC_AS_DEPENDENCIES
# encompass TLC in the scope of the dependency graph.
# This allows us to recompile part of TLC, if it has changed.
V_AUX  := $(wildcard $(TLC)/*.v) \
          $(wildcard $(LIBCOQ)/*.v)
else
V_AUX  := $(wildcard $(LIBCOQ)/*.v)
endif

##############################################################################
# Targets.

.PHONY: all

all: $(CMJ)
# Must run in two successive phases, as coqdep must not run until the
# files %_ml.v have been generated. So, we create the files %.cmj and
# %_ml.v first (above), then compile every .v file.
	@ $(MAKE) -f $(TLC)/Makefile.coq $@

_CoqProject:
	@ $(MAKE) -f $(TLC)/Makefile.coq $@

##############################################################################
# Generating %.cmj and %_ml.v.

CFML_FLAGS :=
  # can use:
  # -only_cmj
  # and OCaml flags

# Note: we must delete the .cmj file if the construction of the _ml.v file
# has failed. (Maybe the generator itself should take care of that!)

# Note: at the moment, we do not run ocamldep, and assume that there no
# inter-module dependencies. Every module is allowed to implicitly depend
# on Pervasives.

ifndef CFMLC
  # This should happen only if "make" is run in lib/stdlib.
  # DEPRECATED: CFMLC := cfmlc
  CFMLC=$(CFML)/generator/cfmlc.native
endif

$(PWD)/Pervasives_ml.v $(PWD)/Pervasives.cmj: $(PWD)/Pervasives.ml $(CFMLC)
	$(CFMLC) $(CFML_FLAGS) -nostdlib -nopervasives -I . $< || (rm -f $@; exit 1)

$(PWD)/%_ml.v $(PWD)/%.cmj: $(PWD)/%.ml $(PWD)/Pervasives.cmj $(CFMLC)
	$(CFMLC) $(CFML_FLAGS) -nostdlib -I . $< || (rm -f $@; exit 1)

##############################################################################
# Cleanup.

clean::
	rm -rf *.cmj *_ml.v _output
	@ $(MAKE) -f $(TLC)/Makefile.coq $@

