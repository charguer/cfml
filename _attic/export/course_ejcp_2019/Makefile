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


##############################################################################
# List of files

SRC_EXAMPLES := Example ExampleList ExampleListOf ExampleStack ExamplePairingHeap
SRC_CORE := TLCbuffer Fmap Var SepSimpl Bind Semantics SepFunctor SepBase WPBase SepLifted WPLifted WPTactics WPRecord $(SRC_EXAMPLES) WPLib 
SRC_COURSE := EJCPTuto EJCPImplem
# EJCPExo
SRC_SF := SLFIntro SLFDirect SLFExtra SLFHprop SLFHimpl SubstExec SLFRules SLFWand SLFWPsem SLFWPgen 

SRC_TLC := LibAxioms LibTactics LibEqual LibLogic LibOperation LibBool LibReflect LibProd LibSum LibRelation LibOrder LibNat LibEpsilon LibInt LibMonoid LibContainer LibOption LibWf LibList LibListZ LibMin LibSet LibChoice LibUnit LibCore LibFun LibFix LibMap LibString LibMultiset

SRC := $(SRC_TLC) $(SRC_CORE) $(SRC_SF) $(SRC_MORE) $(SRC_COURSE)


##############################################################################
# Compilation settings

PWD := $(shell pwd)

# V := $(addprefix $(PWD)/,$(SRC:=.v))
V := $(SRC:=.v)

COQFLAGS:=-w -notation-overridden,-implicits-in-term,-redundant-canonical-projection,-several-object-files

include Makefile.coq

all: _CoqProject

clean::
	rm -f _CoqProject


