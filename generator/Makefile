# -------------------------------------------------------------------------

# Compilation and installation rules.

.PHONY: all install uninstall clean

all:
	@ dune build @all

byte:
	@ dune build cfmlc.bc

clean:
	@ dune clean

install:
	@ cd .. && dune build -p cfml && dune install cfml

uninstall:
	@ cd .. && dune uninstall cfml


# For some reason, running [dune install] or [dune uninstall] in the
# current directory causes it to create a [dune-project] file in this
# directory, even though there is one in the parent directory. To
# avoid this, we move up to the parent directory first.

# For some reason, running [dune install -p cfml] does not work; dune
# complains about the presence of other packages, which it does not
# know how to install. Fortunately, [dune install cfml] seems to work.

# -------------------------------------------------------------------------

# [make versions] compiles CFML with several versions of OCaml.

VERSIONS := \
  4.08.1 \
  4.09.1 \
  4.10.0 \
  4.11.1 \
  4.12.0 \
  4.13.0 \

.PHONY: versions
versions:
	@(echo "(lang dune 2.0)" && \
	  for v in $(VERSIONS) ; do \
	    echo "(context (opam (switch $$v)))" ; \
	  done) > dune-workspace.versions
	@ dune build --workspace dune-workspace.versions @all
	@ rm -f dune-workspace.versions
