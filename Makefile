.PHONY: all coqlib generator examples doc clean install uninstall reinstall

CFML := $(shell pwd)


##############################################################################
# Installation destinations.

DEFAULT_PREFIX := $(shell opam config var prefix)
ifeq ($(DEFAULT_PREFIX),)
	DEFAULT_PREFIX := /usr/local
endif

PREFIX ?= $(DEFAULT_PREFIX)
LIBDIR ?= $(PREFIX)/lib/cfml

COQ_WHERE   ?= $(shell $(COQBIN)coqc -where)
COQ_CONTRIB := $(COQ_WHERE)/user-contrib

##############################################################################
# Targets.

all: coqlib generator
	$(MAKE) CFMLC=$(CFML)/generator/_build/default/cfmlc.exe -C lib/stdlib

coqlib:
	$(MAKE) -C lib/coq

generator:
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
	rm -f $(DOC)

##############################################################################
# Installation.

install: all
	# Install the generator binary
	make -C generator install

	# Cleanup LIBDIR
	rm -rf $(LIBDIR)

	# Install the stdlib .cmj files
	mkdir -p $(LIBDIR)/stdlib
	install $(CFML)/lib/stdlib/*.cmj $(LIBDIR)/stdlib

	# Install the auxiliary makefiles
	mkdir -p $(LIBDIR)/make
	install $(CFML)/lib/make/Makefile.cfml $(LIBDIR)/make
	install -m755 $(CFML)/lib/make/ocamldep.post $(LIBDIR)/make

	# Install the CFML core coq library
	make -C lib/coq install

	# Install the CFML stdlib coq library
	mkdir -p $(COQ_CONTRIB)/CFML/Stdlib
	install $(CFML)/lib/stdlib/*.vo $(COQ_CONTRIB)/CFML/Stdlib

	# "Installation completed."

uninstall:
	make -C generator $@
	make -C lib/coq $@
	rm -rf $(LIBDIR)

reinstall: uninstall
	@ $(MAKE) install
