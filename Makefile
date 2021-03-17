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

##############################################################################
# Targets.

all: coqlib generator
	$(MAKE) -C lib/stdlib

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
	make -C generator $@
	make -C lib/coq $@
	make -C lib/stdlib $@
	# Install the auxiliary makefiles
	mkdir -p $(LIBDIR)/make
	install $(CFML)/lib/make/Makefile.cfml $(LIBDIR)/make
	install -m755 $(CFML)/lib/make/ocamldep.post $(LIBDIR)/make

uninstall:
	make -C generator $@
	make -C lib/coq $@
	make -C lib/stdlib $@

reinstall: uninstall
	@ $(MAKE) install
