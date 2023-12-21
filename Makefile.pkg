SHELL := bash
export CDPATH=

# -------------------------------------------------------------------------

# [make all] rebuilds the tool [cfmlc] and the basis library.
# It is fast and can be used while developing these components.

# If you wish to work on the examples, then it is recommended to pin
# the packages first, by running [make pin]. If, while working on the
# examples, you find that you need to modify one of the packages, you
# should commit your changes and run [make reinstall].

.PHONY: all
all: coq-cfml-basis generator
	@ echo "Okay, I have compiled the generator and the library lib/coq."
	@ echo "If you want to go further, you will need to install them:"
	@ echo
	@ echo "  opam pin add cfml ."
	@ echo "  opam pin add coq-cfml-basis ."
	@ echo
	@ echo "You should then be able to install also the standard library:"
	@ echo
	@ echo "  opam pin add coq-cfml-stdlib ."
	@ echo
	@ echo "You can then work on the examples:"
	@ echo
	@ echo "  make -C examples"

.PHONY: coq-cfml-basis
coq-cfml-basis:
	$(MAKE) -C lib/coq

.PHONY: generator
generator:
	$(MAKE) -C generator

# -------------------------------------------------------------------------
# Cleanup.

.PHONY: clean
clean:
	$(MAKE) -C lib/coq $@
	$(MAKE) -C lib/stdlib $@
	$(MAKE) -C generator $@
	if command -v cfmlc >/dev/null ; then $(MAKE) -C examples $@ ; fi

# -------------------------------------------------------------------------

# Compiling under various versions of Coq.

# This assumes that the opam switches coq813, coq814, etc. exist and the
# packages that we need (menhir, coq-tlc, etc.) are installed in them.

VERSIONS := \
  coq814 \
  coq813 \

.PHONY: versions
versions:
	for v in $(VERSIONS) ; do \
	  opam switch $$v && eval $$(opam env) && make clean && \
          make -j && \
          (opam remove cfml coq-cfml-basis coq-cfml-stdlib --yes || true) && \
	  opam pin add cfml . --yes && \
	  opam pin add coq-cfml-basis . --yes && \
	  opam pin add coq-cfml-stdlib . --yes && \
	  true ; \
	done

# -------------------------------------------------------------------------
# Installation.

# These commands perform direct installation, without going through opam.

install: all
	$(MAKE) -C generator $@
	$(MAKE) -C lib/coq $@
	$(MAKE) -C lib/stdlib $@

uninstall:
	$(MAKE) -C generator $@
	$(MAKE) -C lib/coq $@
	$(MAKE) -C lib/stdlib $@

# -------------------------------------------------------------------------

# These commands ask opam to install the packages, based on the package
# description files *.opam.

# Note that [opam pin] uses the last committed version of the code, so
# you should commit your changes before using [make pin].

# Use [OPAMYES=1 make pin] to automatically answer "yes" to every
# question asked by opam.

PACKAGES := cfml coq-cfml-basis coq-cfml-stdlib coq-cfml

.PHONY: pin
pin: unpin
	@ for p in $(PACKAGES) ; do opam pin add $$p . ; done

.PHONY: unpin
unpin:
	@ opam pin remove $(PACKAGES)

.PHONY: reinstall
reinstall:
	@ opam reinstall $(PACKAGES)

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
ARCHIVE  := $(REPO)/-/archive/$(DATE)/archive.tar.gz
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
# Message.
	@ echo "Done. Now (if happy) type make opam."

.PHONY: undo
undo:
# Undo the last release (assuming it was done on the same date).
	@ git tag -d $(DATE)
	@ git push -u origin :$(DATE)

# -------------------------------------------------------------------------

# Updating the opam package.

# This entry assumes that [make release] has been run on the same day.

# The publication command.
PUBLISH := \
  opam publish -v $(DATE)

# The publication command, for a Coq package.
COQPUBLISH := \
  $(PUBLISH) \
  --repo coq/opam-coq-archive \
  --packages-directory released/packages \

.PHONY: opam
opam:
# Check the current package descriptions.
	@ opam lint
# Publish the OCaml package.
	@ $(PUBLISH) cfml.opam $(ARCHIVE)
# Publish the Coq packages.
# Each package description file is patched on the fly:
#   we replace the string DATEDASH with $(DATEDASH).
	@ rm -f *.patched.opam
	@ \
	for package in coq-cfml coq-cfml-basis coq-cfml-stdlib ; do \
	  cat $$package.opam \
	  | sed -e 's/DATEDASH/$(DATEDASH)/g' \
	  > $$package.patched.opam ; \
	done
	@ $(COQPUBLISH) *.patched.opam $(ARCHIVE)
	@ rm -f *.patched.opam
