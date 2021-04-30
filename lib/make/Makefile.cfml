SHELL := bash

.PHONY: all clean

###############################################################################
# Readme
#
# $(OCAML_INCLUDE) should contain -I directives.
# Optionally, $(CFML_FLAGS) can be set (e.g. to "-rectypes").
# Optionally, $(ML) can be used to specify the sources files (default: *.ml)
#
# For each %.ml file in $(ML), we create:
# - the files %.d      (dependency files)
# - the files %.cmj    (type information; .cmi files in disguise)
# - the files %_ml.v   (characteristic formulae)
# - the files %_ml.vo  (compiled characteristic formulae)
#
# Idea number 1:
# Because the CFML generator produces the files %_ml.v and %.cmj at
# the same time (in just one invocation), it is not necessary to
# tell "make" about both of these files. We adopt the convention
# that only the .cmj file is used as a target. This seems to help.
#
# Idea number 2:
# This Makefile deals only with the generation of %_ml.v and %.cmj.
# Running Coq on %_ml.v is the job of another Makefile, which is
# run in a second stage. This means we write fewer Makefiles, they
# are really independent, and dependency computations are simpler.

CFML ?= $(shell cfmlc -where)

############################################################################
# Verbosity control.

# Our commands can be pretty long. So, we hide them by default, and echo a
# short message instead. However, sometimes one wants to see the command.

# By default, VERBOSE is undefined, so the .SILENT directive is read, so no
# commands are echoed. If VERBOSE is defined by the user, then the .SILENT
# directive is ignored, so commands are echoed, unless they begin with an
# explicit @.

ifndef VERBOSE
.SILENT:
endif

###############################################################################
# Parameters

ifndef ML
  ML := $(wildcard *.ml)
endif

###############################################################################
# Definitions

CMJ   := $(patsubst %.ml,%.cmj,$(ML))
MLV   := $(patsubst %.ml,%_ml.v,$(ML))
D     := $(patsubst %.ml,%.d,$(ML))

OCAMLDEP  := $(OCAMLBIN)ocamldep
OCAMLPOST := $(CFML)/ocamldep.post

###############################################################################
# Targets

all: $(CMJ)

###############################################################################
# Dependencies

# As described by the recipe below, including the dependency files $(D)
# adds dependencies of the form:
#   A.cmj: B.cmj
# whenever module A depends on module B.

ifeq ($(findstring $(MAKECMDGOALS),clean),)
-include $(D)
endif

# We use ocamldep to find out which files A depends upon.

# ocamldep must be passed appropriate -I flags, as it searches the file system
# to find where each module is stored. We assume that these flags are given by
# $(OCAML_INCLUDE).

# ocamldep does not reliably print absolute path names -- its output depends
# on the current directory! it omits the absolute path if it coincides with
# the current directory. If absolute path names are desired, one can change
# the current directory to /tmp before invoking ocamldep. Of course, this
# requires $(OCAML_INCLUDE) and $< to contains absolute paths, too.

# ocamldep produces the following dependencies:
#   A.cmo: B.cmi (or B.cmo, depending on the existence of B.mli, I think)
#   A.cmx: B.cmx (or B.cmi, depending on obscure criteria)
# We keep only the second line and replace both .cmx and .cmi with .cmj in it.

# ocamldep sometimes produces a dependency A.cmx: A.cmi (not sure why).
# This leads us to produce a circular dependency A.cmj: A.cmj.
# The script $(OCAMLPOST) filters it out.

SED := $(shell if command -v gsed >/dev/null ; then echo gsed ; else echo sed ; fi)

%.d: %.ml
	$(OCAMLDEP) -one-line $(OCAML_INCLUDE) $< \
	  | grep cmx \
	  | $(SED) -e "s/\\.cm\\(x\\|i\\)/\\.cmj/g" \
	  | $(OCAMLPOST) \
	  > $@

###############################################################################
# Rules

# We use CFML's cmj generator to produce %_ml.v and %.cmj files out of %.ml.
# Only the %.cmj target is known to "make".

# We include a dependency on the executable [cfmlc]. This is not strictly
# required, but can be helpful for us (developers) who tend to frequently
# reinstall CFML and do not always remember to run [make clean] in every
# project that uses CFML.

%.cmj: %.ml $(shell command -v cfmlc)
	@ echo "CFMLC `basename $<`"
	cfmlc $(CFML_FLAGS) $(OCAML_INCLUDE) $<

###############################################################################
# Clean

clean:
	rm -f *.cmj *_ml.v *.d
	rm -rf _output
