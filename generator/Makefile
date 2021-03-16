# -------------------------------------------------------------------------

# Compilation and installation rules.

.PHONY: all install uninstall clean

all:
	@ dune build @all

clean:
	@ dune clean

install: all
	@ dune install

uninstall:
	@ dune uninstall

# -------------------------------------------------------------------------

# [make versions] compiles CFML with several versions of OCaml.

VERSIONS := \
  4.08.1 \
  4.09.1 \
  4.10.0 \
  4.11.1 \
  4.12.0 \

.PHONY: versions
versions:
	@(echo "(lang dune 2.0)" && \
	  for v in $(VERSIONS) ; do \
	    echo "(context (opam (switch $$v)))" ; \
	  done) > dune-workspace.versions
	@ dune build --workspace dune-workspace.versions @all
	@ rm -f dune-workspace.versions
