#
# This Makefile is a wrapper for the generic Makefile provided by TLC
#


##############################################################################
# Certain custom settings can be defined in settings.sh.

# To specify the location of the Coq binaries, define COQBIN (with a
# trailing slash), e.g. COQBIN=/var/tmp/coq/bin/.
# If COQBIN is undefined, then "coqc" is used.

-include settings.sh

export COQBIN


############################################################################
# We assume that TLC has been installed.
# (Note: this definition can be overriden from outside.)

ifndef TLC
	TLC := $(shell $(COQBIN)coqc -where)/user-contrib/TLC
endif

ifeq ($(wildcard $(TLC)),)
  $(error $(TLC) does not exist. \
          Please install TLC first)
endif

export TLC


##############################################################################
# List of files


SRC_EXAMPLES := Example ExampleQueue ExampleList ExampleListIndir ExampleListNull ExampleListOf ExampleStack ExamplePairingHeap

SRC_COMMON := LibSepTLCbuffer LibSepFmap LibSepVar LibSepSimpl

SRC_NOW := SepCreditsNew SepCredits 

SRC_CFML := LibSepBind Semantics LibSepFunctor SepBase WPBase SepLifted WPLifted WPTactics 

SRC_CFML_PLUS := WPRecord WPArrayNonLifted WPArray WPLib 

# $(SRC_EXAMPLES) WPExamples WPExamplesDetails WPUnitTests 

SRC_MORE := SepBaseAltProofs SepCredits SepRO SepRONew SepROMode SubstExec 

# SRC_EXAMPLES := Example ExampleBasicNonlifted ExampleListNonlifted ExampleQueueNonlifted ExampleBasic ExampleTrees ExampleUnionFind ExampleHigherOrder ExampleListNull ExampleListIndir ExampleRO 

SRC_CF := CFCrashCourse

# SRC_MOSEL := SepMoselFunctor SepBaseMosel SepROMosel ExampleROMosel ExampleListMosel

SRC := $(SRC_COMMON) $(SRC_NOW) $(SRC_CFML) $(SRC_MORE) $(SRC_CFML_PLUS) $(SRC_EXAMPLES) 

# using the variable SRC_FORCE, one can modify the compilation targets and/or their order.

ifdef SRC_FORCE 
	SRC := $(SRC_FORCE)
endif



##############################################################################
# Compilation settings

PWD := $(shell pwd)

LIBCOQ := $(PWD)/../lib/coq

V := $(addprefix $(PWD)/,$(SRC:=.v))

ifndef COQFLAGS
	ifdef SLF
		COQFLAGS:=-w -implicits-in-term,-redundant-canonical-projection,-several-object-files,-ambiguous-paths,-implicit-core-hint-db
	else
		COQFLAGS:=-w -implicits-in-term,-redundant-canonical-projection,-several-object-files,-ambiguous-paths,-implicit-core-hint-db
	endif
endif

# -notation-overridden,

COQINCLUDE := \
  -Q $(LIBCOQ) CFML \
  -Q $(TLC) TLC \
  -Q $(PWD) Sep


include $(TLC)/Makefile.coq

all: _CoqProject


##############################################################################
# Compilation of files from the course on Foundations of Separation Logic

# TODO: import_slf needs to be updated

# usage: make import_slf && make SLF=1

SLF_FILES := $(SRC_SF:=.v)

ifndef SLF_FOLDER
	SLF_FOLDER := /home/charguer/versions/coq-8.12/sfdev/slf
endif

import_slf:
	cp $(addprefix $(SLF_FOLDER)/,$(SLF_FILES)) .
	sed -i -e 's/^From[[:space:]]SLF[[:space:]]LibSep/From CFML LibSep/' $(SLF_FILES)
	sed -i -e 's/^From[[:space:]]SLF[[:space:]]Lib/From TLC Lib/' $(SLF_FILES)
	sed -i -e 's/^From[[:space:]]SLF/From Sep/' $(SLF_FILES)

clean_slf:
	rm SLF*.v


##############################################################################

# TODO: still needed?

required_vos:
	touch $@

