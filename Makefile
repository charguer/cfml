SHELL := bash
export CDPATH=

.PHONY: all coqlib generator examples doc clean install uninstall

CFML := $(shell pwd)


# -------------------------------------------------------------------------
# Installation destinations.

DEFAULT_PREFIX := $(shell opam config var prefix)
ifeq ($(DEFAULT_PREFIX),)
	DEFAULT_PREFIX := /usr/local
endif

PREFIX ?= $(DEFAULT_PREFIX)
LIBDIR ?= $(PREFIX)/lib/cfml

# -------------------------------------------------------------------------
# Targets.

all: coqlib generator
	$(MAKE) -C lib/stdlib

coqlib:
	$(MAKE) -C lib/coq

generator:
	$(MAKE) -C generator

examples: all
	$(MAKE) CFML=$(CFML) -C examples

# -------------------------------------------------------------------------
# Documentation.

DOC := README.html lib/coq/README.html generator/README.html

doc: $(DOC)

%.html: %.md
	pandoc -o $@ $<

# -------------------------------------------------------------------------
# Cleanup.

clean:
	$(MAKE) -C lib/coq $@
	$(MAKE) -C lib/stdlib $@
	$(MAKE) -C generator $@
	rm -f $(DOC)

# -------------------------------------------------------------------------
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

# -------------------------------------------------------------------------

.PHONY: pin
pin: unpin
	@ opam pin add cfmlc .
	@ opam pin add coq-cfml-basis .
	@ opam pin add coq-cfml-stdlib .

.PHONY: unpin
unpin:
	@ opam remove cfmlc coq-cfml-basis coq-cfml-stdlib

.PHONY: reinstall
reinstall:
	@ opam reinstall cfmlc coq-cfml-basis coq-cfml-stdlib

# -------------------------------------------------------------------------

# Distribution.

# The version number is automatically set to the current date,
# unless DATE is defined on the command line.
DATE     := $(shell /bin/date +%Y%m%d)

# The repository's name on gitlab.
PROJECT  := cfml2
# The repository URL (https).
REPO     := https://gitlab.inria.fr/charguer/$(PROJECT)
# The archive URL (https).
ARCHIVE  := $(REPO)/repository/$(DATE)/archive.tar.gz
# The local repository directory.
PWD      := $(shell pwd)

# -------------------------------------------------------------------------

# Simulating the creation of an archive by git.

.PHONY: archive
archive:
	@ git archive HEAD --format=tar.gz -o $(DATE).tar.gz --prefix=$(PROJECT)/
	@ tar tvfz $(DATE).tar.gz

# -------------------------------------------------------------------------

# Publish a release. (Remember to commit everything first!)

.PHONY: release
release:
# Check if everything has been committed.
	@ if [ -n "$$(git status --porcelain)" ] ; then \
	    echo "Error: there remain uncommitted changes." ; \
	    git status ; \
	    exit 1 ; \
	  else \
	    echo "Now making a release..." ; \
	  fi
# Create a git tag.
	@ git tag -a $(DATE) -m "Release $(DATE)."
# Upload. (This automatically makes a .tar.gz archive available on gitlab.)
	@ git push
	@ git push --tags

# -------------------------------------------------------------------------

# Updating the opam package.

# This entry assumes that "make package" and "make export"
# have just been run (on the same day).

# You need opam-publish:
#   sudo apt-get install libssl-dev
#   opam install tls opam-publish

# In fact, you need a version of opam-publish that supports --subdirectory:
#   git clone git@github.com:fpottier/opam-publish.git
#   cd opam-publish
#   git checkout 1.3
#   opam pin add opam-publish `pwd` -k git

# The following command should have been run once:
#   opam-publish repo add opam-coq-archive coq/opam-coq-archive

PUBLISH_OPTIONS := \
  --repo opam-coq-archive \
  --subdirectory released \

.PHONY: opam
opam:
	@ opam lint
	@ opam-publish prepare $(PUBLISH_OPTIONS) $(PACKAGE).$(DATE) $(ARCHIVE)

.PHONY: submit
submit:
	@ opam-publish submit $(PUBLISH_OPTIONS) $(PACKAGE).$(DATE)
