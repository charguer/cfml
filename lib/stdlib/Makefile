.PHONY: all clean install uninstall

##############################################################################

# We run in two successive phases. In the first phase, we create the
# files %.cmj and %_ml.v. In the second phase, we run coqdep and coqc.

# Phase 2 comes first in this Makefile because we want the target [all]
# to be the default target.

##############################################################################

# Phase 2. Run Coq.

# The dependency on the target [cmj] triggers phase 1 first.

# The recipes in Makefile.stage2 rely on coq_makefile.

# The name of the library, CFML.Stdlib, is specified in the file _CoqProject.

all: cmj
	@ $(MAKE) -f Makefile.stage2 $@

clean install uninstall::
	@ $(MAKE) -f Makefile.stage2 $@

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

# Determine where to install the files %.cmj.

# We implement the same methods as the CFML tool (see cfml_config.ml).
# Method 1: if the path to cfmlc ends in [/bin/cfmlc], replace it with
#           [/lib/cfml].
# Method 2: run [opam config var prefix] and append [/lib/cfml].

define compute_libdir
  CFMLC=$$(command -v cfmlc) && \
  case $${CFMLC} in \
  */bin/cfmlc) \
    echo "$${CFMLC%%/bin/cfmlc}/lib/cfml" ;; \
  *) \
    if command -v opam >/dev/null ; then \
      echo "$$(opam config var prefix)/lib/cfml" ; \
    else \
      echo "undefined" ; \
    fi ;; \
  esac
endef

LIBDIR := $(shell $(compute_libdir))

ifeq ($(LIBDIR),undefined)
  $(error Cannot determine where to install *.cmj)
endif

install::
	@ mkdir -p $(LIBDIR)/stdlib
	@ for f in $(CMJ) ; do \
	  echo "INSTALL $$f $(LIBDIR)/stdlib/" ; \
	  install $$f $(LIBDIR)/stdlib/ ; \
	done

uninstall::
	@ echo "RM $(LIBDIR)/stdlib"
	@ rm -rf $(LIBDIR)/stdlib
