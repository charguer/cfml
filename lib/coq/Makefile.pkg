# The _CoqProject file is generated.

# Test that TLC is installed

TLC := $(shell $(COQBIN)coqc -where)/user-contrib/TLC
ifeq ($(findstring $(MAKECMDGOALS),clean),)
  ifeq ($(wildcard $(TLC)),)
    $(error $(TLC) does not exist. Please install TLC first)
  endif
endif


COQINCLUDE := "-Q . CFML"

COQWARNINGS := "-w -notation-overridden,-implicit-core-hint-db,-omega-is-deprecated,-ambiguous-paths,-irrelevant-format-only-parsing,-deprecated-hint-without-locality,-deprecated-ident-entry,-custom-entry-overriden"

include ../make/Makefile.generic
include ../make/Makefile.coqproject
