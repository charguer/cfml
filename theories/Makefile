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

SRC_CORE := TLCbuffer Fmap Var SepSimpl Bind Semantics SepFunctor SepBase WPBase SepLifted WPLifted WPTactics WPRecord Example ExampleList ExampleStack WPExamples WPExamplesDetails WPLib 

#ExamplePairingHeap2

SRC_MORE := SepBaseAltProofs SepCredits SepRO

# WPArray

SRC_EXAMPLES := Example ExampleBasicNonlifted ExampleListNonlifted ExampleQueueNonlifted ExampleBasic ExampleTrees ExampleUnionFind ExampleHigherOrder ExampleList ExampleRO 

SRC_SF := SLFIntro SLFDirect SLFExtra SLFHprop SLFHimpl SubstExec SLFRules SLFWand SLFWPsem SLFWPgen 
 #  SLFLift SLFRicher SLFExt

SRC_MOSEL := SepMoselFunctor SepBaseMosel SepROMosel ExampleROMosel ExampleListMosel

SRC := $(SRC_CORE) $(SRC_SF) $(SRC_MORE)
# $(SRC_EXAMPLES)  $(SRC_MOSEL)

# using the variable SRC_FORCE, one can modify the compilation targets and/or their order.

ifdef SRC_FORCE 
	SRC := $(SRC_FORCE)
endif


##############################################################################
# Compilation settings

PWD := $(shell pwd)

V := $(addprefix $(PWD)/,$(SRC:=.v))

COQFLAGS:=-w -notation-overridden,-implicits-in-term,-redundant-canonical-projection,-several-object-files

COQINCLUDE := \
  -Q $(TLC) TLC \
  -Q $(PWD) Sep


include $(TLC)/Makefile.coq

all: _CoqProject



# (** [] *)