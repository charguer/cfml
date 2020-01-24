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


SRC_EXAMPLES := Example ExampleList ExampleListNull ExampleListIndir ExampleQueue ExampleListOf ExampleStack ExamplePairingHeap
SRC_CORE := TLCbuffer Fmap Var SepSimpl Bind Semantics SepFunctor SepBase WPBase SepLifted WPLifted WPTactics WPRecord $(SRC_EXAMPLES) WPExamples WPExamplesDetails WPLib WPUnitTests 

SRC_MORE := SepBaseAltProofs SepCredits SepRO SubstExec CollegeDeFrance

SRC_EXAMPLES := Example ExampleBasicNonlifted ExampleListNonlifted ExampleQueueNonlifted ExampleBasic ExampleTrees ExampleUnionFind ExampleHigherOrder ExampleListNull ExampleListIndir ExampleRO 

SRC_CF := CFCrashCourse

SRC_SF := SLFPreface SLFDirect SLFExtra SLFBasic SLFHprop SLFHimpl SLFRules SLFWPsem SLFWPgen SLFSummary SLFWand SLFAffine

# SLFLift SLFRicher SLFExt

SRC_MOSEL := SepMoselFunctor SepBaseMosel SepROMosel ExampleROMosel ExampleListMosel

SRC := $(SRC_CORE) $(SRC_CF) $(SRC_SF) $(SRC_MORE)
# $(SRC_EXAMPLES)  $(SRC_MOSEL)

# using the variable SRC_FORCE, one can modify the compilation targets and/or their order.

ifdef SRC_FORCE 
	SRC := $(SRC_FORCE)
endif


##############################################################################
# Compilation settings

PWD := $(shell pwd)

V := $(addprefix $(PWD)/,$(SRC:=.v))

COQFLAGS:=-w -implicits-in-term,-redundant-canonical-projection,-several-object-files

# -notation-overridden,

COQINCLUDE := \
  -Q $(TLC) TLC \
  -Q $(PWD) Sep


include $(TLC)/Makefile.coq

all: _CoqProject


##############################################################################
# File transfer

SLF_FILES := $(SRC_SF:=.v)

ifndef SLF_FOLDER
	SLF_FOLDER := /home/charguer/versions/coq-8.9.1/sfdev/slf
endif

import_slf:
	cp $(addprefix $(SLF_FOLDER)/,$(SLF_FILES)) .
	sed -i -e 's/^From[[:space:]]SLF[[:space:]]Require[[:space:]]Export[[:space:]]LibCore/From TLC Require Export LibCore/' $(SLF_FILES)
	sed -i -e 's/^From[[:space:]]SLF[[:space:]]/From Sep /' $(SLF_FILES)


