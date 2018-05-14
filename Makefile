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

SRC := TLCbuffer Fmap SepFunctor LambdaSemantics LambdaSep SLSemantics SLHprop SLHimpl SLRules SLWP LambdaCFTactics LambdaWP LambdaSepLifted LambdaWPLifted LambdaCF SepGPM LambdaSepProofMode LambdaStruct LambdaSepRO LambdaSepROProofMode ExampleROProofMode  LambdaSepCredits LambdaSepLifted LambdaCFLifted LambdaStructLifted Example ExampleBasicNonlifted ExampleListNonlifted ExampleQueueNonlifted ExampleBasic ExampleTrees ExampleUnionFind ExampleHigherOrder ExampleList LambdaCFCredits ExampleRO ExampleListProofMode


##############################################################################
# Compilation settings

PWD := $(shell pwd)

V := $(addprefix $(PWD)/,$(SRC:=.v))

COQFLAGS:=-w -notation-overridden,-implicits-in-term

COQINCLUDE := \
  -R $(TLC) TLC \
  -R $(PWD) Sep

include $(TLC)/Makefile.coq





