.PHONY: all coqlib generator examples doc clean install uninstall reinstall

CFML := $(shell pwd)


##############################################################################
# Installation destinations.

DEFAULT_PREFIX := $(shell opam config var prefix)
ifeq ($(DEFAULT_PREFIX),)
	DEFAULT_PREFIX := /usr/local
endif

PREFIX ?= $(DEFAULT_PREFIX)
BINDIR ?= $(PREFIX)/bin
LIBDIR ?= $(PREFIX)/lib/cfml

COQ_WHERE   ?= $(shell $(COQBIN)coqc -where)
COQ_CONTRIB := $(COQ_WHERE)/user-contrib

##############################################################################
# Targets.

all: coqlib generator
	$(MAKE) CFMLC=$(CFML)/generator/cfmlc.native -C lib/stdlib

coqlib:
	$(MAKE) CFML=$(CFML) -C lib/coq proof

generator:
	rm -f generator/cfml_config.ml
	sed -e 's|@@LIBDIR@@|$(LIBDIR)|' \
	    generator/cfml_config.ml.in > generator/cfml_config.ml
	$(MAKE) -C generator

examples: all
	$(MAKE) CFML=$(CFML) -C examples

##############################################################################
# Documentation.

DOC := README.html lib/coq/README.html generator/README.html

doc: $(DOC)

%.html: %.md
	pandoc -o $@ $<

##############################################################################
# Cleanup.

clean:
	$(MAKE) -C lib/coq $@
	$(MAKE) -C lib/stdlib $@
	$(MAKE) -C generator $@
	rm -f generator/cfml_config.ml
	rm -f $(DOC)

##############################################################################
# Installation.

# As install depends on all, the file generator/cfml_config.ml is regenerated
# when `make install` is run; this ensures LIBDIR cannot be inconsistent.

install: all
	# Install the generator binary
	install -m755 $(CFML)/generator/_build/cfmlc.native $(BINDIR)/cfmlc
#	install -m755 $(CFML)/generator/_build/makecmj.native $(BINDIR)/cfml_cmj

	# Cleanup LIBDIR
	rm -rf $(LIBDIR)

	# Install the stdlib .cmj files
	mkdir -p $(LIBDIR)/stdlib
	install $(CFML)/lib/stdlib/*.cmj $(LIBDIR)/stdlib

	# Install the auxiliary makefiles
	mkdir -p $(LIBDIR)/make
	install $(CFML)/lib/make/Makefile.cfml $(LIBDIR)/make
	install -m755 $(CFML)/lib/make/ocamldep.post $(LIBDIR)/make

	# Cleanup COQ_CONTRIB/CFML
	rm -rf $(COQ_CONTRIB)/CFML

	# Install the CFML core coq library
	mkdir -p $(COQ_CONTRIB)/CFML
	install $(CFML)/lib/coq/*.vo $(COQ_CONTRIB)/CFML

	# Install the CFML stdlib coq library
	mkdir -p $(COQ_CONTRIB)/CFML/Stdlib
	install $(CFML)/lib/stdlib/*.vo $(COQ_CONTRIB)/CFML/Stdlib

	# "Installation completed."

uninstall:
	rm -f $(BINDIR)/cfmlc
#	rm -f $(BINDIR)/cfml_cmj
	rm -rf $(LIBDIR)
#	rm -rf $(DOCDIR)
	rm -rf $(COQ_CONTRIB)/CFML

reinstall: uninstall
	@ $(MAKE) install
