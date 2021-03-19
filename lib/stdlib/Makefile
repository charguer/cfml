.PHONY: all clean install uninstall

##############################################################################

# We run in two successive phases. In the first phase, we create the
# files %.cmj and %_ml.v. In the second phase, we run coqdep and coqc.

# Phase 2 comes first in this Makefile because we want the target [all]
# to be the default target.

##############################################################################

# Phase 2. Run Coq.

# The dependency on the target [cmj] triggers phase 1 first.

# The recipes in Makefile.generic rely on coq_makefile.

# The name of the library, CFML.Stdlib, is specified in the file _CoqProject.

all: cmj
	@ $(MAKE) -f ../make/Makefile.generic $@

clean install uninstall:: all
	@ $(MAKE) -f ../make/Makefile.generic $@

##############################################################################

# Phase 1. Run CFML.

ML     := $(wildcard *.ml)

CMJ    := $(patsubst %.ml,%.cmj,$(ML))

MLV    := $(patsubst %.ml,%_ml.v,$(ML))

.PHONY: cmj
cmj: $(CMJ)

Pervasives_ml.v Pervasives.cmj: Pervasives.ml
	@ echo "CFMLC Pervasives.ml"
	@ cfmlc -nostdlib -nopervasives -I . $< || (rm -f $@; exit 1)

%_ml.v %.cmj: %.ml Pervasives.cmj
	@ echo "CFMLC $<"
	@ cfmlc -nostdlib -I . $< || (rm -f $@; exit 1)

clean::
	@ rm -f $(CMJ) $(MLV)
	@ rm -rf _output

##############################################################################

# Installation of the %.cmj files.

LIBDIR := $(shell cfmlc -where)

install:: all
	@ mkdir -p $(LIBDIR)/stdlib
	@ for f in $(CMJ) ; do \
	  echo "INSTALL $$f $(LIBDIR)/stdlib/" ; \
	  install $$f $(LIBDIR)/stdlib/ ; \
	done

uninstall::
	@ echo "RM $(LIBDIR)/stdlib"
	@ rm -rf $(LIBDIR)/stdlib
