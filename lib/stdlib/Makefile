# DISCLAIMER: WON'T WORK WITH MAKE-J

##############################################################################
# CFML setup.

CFML := $(shell cd ../.. && pwd)

include $(CFML)/Makefile.common

##############################################################################
# Compilation.

# The line "-R $(PWD) CFML.Stdlib" currently does not use "-Q" because 
# it's tricky in the *_ml.v files to generate "Require" with the precise 
# package name (here, CFML.Stdlib, but in general it could be more complex)

PWD := $(shell pwd)
export
COQINCLUDE := \
  -Q $(TLC) TLC \
  -Q $(CFML)/lib/coq CFML \
  -R $(PWD) CFML.Stdlib


##############################################################################
# Files.

PWD    := $(shell pwd)
LIBCOQ := $(shell cd ../coq && pwd)


ML     := $(wildcard $(PWD)/*.ml)

# TODO We would need the following dependency to be taken into account by Makefile.coq in the "all" target,
# instead of hard coding the fact that pervasives must be compiled first
# NONPERVASIVES_MLVO_FILES=$(patsubst %.ml,%_ml.vo,$(filter-out $(PWD)/Pervasives.ml,$(ML)))
# $(NONPERVASIVES_MLVO_FILES): $(PWD)/Pervasives_ml.vo

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
	 echo $(COQINCLUDE)
	 $(MAKE) -f $(TLC)/Makefile.coq $(PWD)/Pervasives_ml.vo
	 $(MAKE) -f $(TLC)/Makefile.coq $@

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

