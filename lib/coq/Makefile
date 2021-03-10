##############################################################################
# CFML setup.

CFML := $(shell cd ../.. && pwd)

include $(CFML)/Makefile.common

##############################################################################
# Compilation.

PWD   := $(shell pwd)
V     := $(wildcard $(PWD)/*.v)
COQFLAGS=-w -notation-overridden,-implicit-core-hint-db,-omega-is-deprecated,-ambiguous-paths


ifdef INCLUDE_TLC_AS_DEPENDENCIES
# For Arthur: encompass TLC in the scope of the dependency graph.
# This allows us to recompile part of TLC, if it has changed.
V_AUX := $(wildcard $(TLC)/*.v)
endif

# The line "-R $(TLC) TLC" is required only if we wish to write just
# "LibFoo", as opposed to "TLC.LibFoo". In the long run, I believe it
# would be preferable to explicitly use the TLC prefix.

COQINCLUDE := \
  -Q $(TLC) TLC \
  -Q $(PWD) CFML

include $(TLC)/Makefile.coq
