SHELL := bash
export CDPATH=

# -------------------------------------------------------------------------
# Targets.

.PHONY: all
all: coq-cfml-basis generator
	@ echo "Okay, I have compiled the generator and the library lib/coq."
	@ echo "If you want to go further, you will need to install them first:"
	@ echo
	@ echo "  opam pin add cfml ."
	@ echo "  opam pin add coq-cfml-basis ."
	@ echo
	@ echo "You should then be able to install also the standard library:"
	@ echo
	@ echo "  opam pin add coq-cfml-stdlib ."
	@ echo
	@ echo "You will then be able to work on the examples:"
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
	$(MAKE) -C examples $@ || exit 0

# -------------------------------------------------------------------------
# Installation.

install: all
	make -C generator $@
	make -C lib/coq $@
	make -C lib/stdlib $@

uninstall:
	make -C generator $@
	make -C lib/coq $@
	make -C lib/stdlib $@

# -------------------------------------------------------------------------

.PHONY: pin
pin: unpin
	@ opam pin add cfml .
	@ opam pin add coq-cfml-basis .
	@ opam pin add coq-cfml-stdlib .

.PHONY: unpin
unpin:
	@ opam remove cfml coq-cfml-basis coq-cfml-stdlib

.PHONY: reinstall
reinstall:
	@ opam reinstall cfml coq-cfml-basis coq-cfml-stdlib

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
