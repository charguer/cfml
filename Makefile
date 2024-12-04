
VERBOSE:=1

# This Makefile deals with all dependencies between the
# CF generator, the Coq library files, and CFML stdlib,
# and the EXAMPLES developments.
#
# Dependencies must be computed first using the "make depend".
# The computation of these dependencies requires *_ml.v files to be
# generated succesfully. In other words, "make depend" will need
# to process '.ml' files, in order to generate '_ml.v' files, in
# which to look for dependencies for Coq compilation.

# Environment variables in use, e.g.:
#   OCAMLINCLUDE := -I . -I ../../lib/ocaml
#
# The "CFMLC_FLAGS" such as -deep_embedding -def_encoders
# are to be stored in a 'cfml.config' file in the folder
# on which the flags apply.
#
# Other variables that may be used
#   ARG_ML : the list of files for which to generate CF;
#         each .ml file should be accompanied by a _proof.v file.
#   ARG_V_AUX : the list of auxiliary local Coq library files to be compiled
#   FOLDER : names the folder where to look for auxiliary .v files automatically
#   TLC : the path to a local TLC installation
#   COQWARNINGS : custom -w flags for Coq
#   COQEXTRAFLAGS : other custom flags for Coq

# All variables named ARG_* may have the special value EMPTY.
# The purpose is to distinguish between an unset environment variables,
# which should be instantiated to a default value, and a variable that
# the caller purposely want to set to empty.

# This Makefile may be invoked with help of the scripts `./make.sh`,
# which provides a shortcut for `make -f Makefile $*`. Beware, however,
# that all paths should be relative to the root of the workspace.


##############################################################################
# Documentation
#
# $(LIBCOQ) contains:
# - %.v files
# - %.v.d generated files
#
# $(STDLIB) contains:
# - %.ml and %_proof.v files
# - %.cmj and %_ml.v
# - Stdlib.v wrapper file
#
# $(PWD) contains:
# - %.v auxiliary files
# - %.ml and %_proof.v files
# - %.cmj and %_ml.v generated files
#
# The %.cmj files of $(STDLIB) are compiled before other %.cmj files.
# The other %.cmj files are compiled in order thanks to dependencies in %.depend_ml
# The %_ml.v are generated at the same time as %.cmj.
# The %_proof.v.d can only be computed after the corresponding %_ml.v files exist.
# The %_proof.vo/vos/vok files can only be computed after loading the %_proof.v.d files.


##############################################################################
# Parameters

all: vo

############################
# All examples

EXAMPLE_FOLDERS=$(shell find examples -mindepth 1 -maxdepth 1 -type d)
EXAMPLES=$(subst examples/,,$(EXAMPLE_FOLDERS))

EXAMPLES_EXCLUDED=
#EXAMPLES_EXCLUDED=examples/wip_Sek/%

# SHORTHANDS
tuto: examples/Tutorial/Tutorial_proof.vo
stack: examples/Stack/Stack_proof.vo
pair: examples/PairingHeap/PairingHeap_proof.vo examples/PairingHeap/PairingHeap_valid.vo
debug: examples/Debug/Debug_proof.vo
units: examples/UnitTests/UnitTests_proof.vo exapples/UnitTestsCredits/UnitTestsCredits_proof.vo
# sek: examples/wip_Sek/PSek_proof.vo examples/wip_Sek/ESek_proof.vo
# todo: a function to gather all targeted .vo in a given folder


############################
# Folders

# CFML denotes the path to the root of the CFML folder.
# We assume that the current folder is the path to CFML.

PWD := $(shell pwd)

CFML = $(PWD)

GENERATOR := $(CFML)/generator
#LIBCOQ := $(CFML)/lib/coq
#STDLIB := $(CFML)/lib/stdlib
#LIBOCAML := $(CFML)/lib/ocaml

LIBCOQ := lib/coq
STDLIB := lib/stdlib
LIBOCAML := lib/ocaml


# FOLDER is the folder where to look for .v and .ml files by default


############################
# COQBIN denotes the path to the Coq binaries (final slash is added if necessary)

ifneq ($(COQBIN),)
	COQBINLASTCHAR=`echo "${$(COQBIN): -1}"`
	ifneq ($(COQBINLASTCHAR),/)
		COQBIN := $(COQBIN)/
	endif
endif

############################
# TLC denotes the path to the TLC library

ifndef TLC
	# Hack for Arthur
	ifeq ($(shell echo $$USER),charguer)
		TLC := /home/charguer/tlc/src
	endif
endif
ifdef TLC
	TLC_V := $(wildcard $(TLC)/*.v)
else
	TLC := $(shell $(COQBIN)coqc -where)/user-contrib/TLC
	TLC_V=
endif

############################
# COQWARNINGS, COQEXTRAFLAGS, COQFLAGS are lists of flags for Coq

# Warning flags

ifndef COQWARNINGS
	COQWARNINGS=-w -notation-overridden,-implicit-core-hint-db,-omega-is-deprecated,-ambiguous-paths,-irrelevant-format-only-parsing,-deprecated-hint-without-locality,-deprecated-ident-entry,-custom-entry-overriden,-deprecated-hint-rewrite-without-locality,-deprecated-instance-without-locality,-notation-incompatible-prefix,-automatic-prop-lowering
endif

# Other flags

ifndef COQEXTRAFLAGS
	COQEXTRAFLAGS:=
endif

# All flags for Coq

ifndef COQFLAGS
	COQFLAGS:=$(COQWARNINGS) $(COQEXTRAFLAGS)
endif

############################
# OCAMLINCLUDE gives the ocamldep include folder.

ifndef OCAMLINCLUDE
	OCAMLINCLUDE := -I lib/stdlib -I lib/ocaml $(addprefix -I examples/,$(EXAMPLES))
endif
$(info OCAMLINCLUDE=$(OCAMLINCLUDE))

############################
# ML lists the ML sources files to process. It is set using ARG_ML.

$(info ARG_ML=$(ARG_ML))
ifdef ARG_ML
	$(info ARG_ML defined)
   ifeq ($(ARG_ML),EMPTY)
      ML :=
   else
      ML := $(ARG_ML)
   endif
else
   #ifeq ($(FOLDER),$(LIBCOQ))
   #   ML :=
   #else
	 		ifeq ($(FOLDER),)
        $(info gathering all ml files)
        # TODO: SHOULD restrict to folder actually used
				PROOFV := $(shell find examples -name '*_proof.v')
        # -not -iwholename '*_output*'
	 			ML := $(PROOFV:_proof.v=.ml)
	 		else
        # DEPRECATED?
        $(info gathering local ml files)
    	  ML := $(wildcard $(FOLDER)/*.ml)
			endif
   #endif
endif

$(info ML=$(ML))



############################
# COQINCLUDE gives the -R/-Q Coq bindings for compiling files.

COQINCLUDE := \
  -Q $(LIBCOQ) CFML \
  -R $(STDLIB) CFML.Stdlib \
	-R examples EXAMPLES

#   -Q $(TLC) TLC \

############################
# Ocamlbuild options

# The variable $(ML_MAIN) is used to specify which source file is the
# starting point when compiling with ocamlbuild. It can remain undefined
# if there is only one .ml file.

ifndef ML_MAIN
	ML_MAIN := $(ML)
endif

# Options for OCAMLBUILD, by default ignore unused variables

ifndef OCAMLBUILD_FLAGS
	OCAMLBUILD_FLAGS := -cflags -w,-26
endif


############################
# COQIDE options

# Files to open in IDE when `make ide` is executed.
# By default, all the local proof files, sorted by last modification date

ifndef OPENINIDE
	OPENINIDE := $(shell ls -t $(FOLDER)*.v 2> /dev/null || echo "")
endif

# Options for CoqIDE. By default, disable parallel progress

ifndef COQIDEOPTIONS
	COQIDEOPTIONS := -async-proofs off -async-proofs-command-error-resilience off
endif


############################################################################
# Verbosity control.

# If VERBOSE is defined by the user, then commands are echoed, unless they
# begin with an explicit @.

ifndef VERBOSE
.SILENT:
endif


##############################################################################
# Binaries.

OCAMLDEP  := $(OCAMLBIN)ocamldep
OCAMLPOST := $(CFML)/lib/make/ocamldep.post

COQC := $(COQBIN)coqc $(COQFLAGS)
COQIDE := $(COQBIN)coqide $(COQFLAGS)
COQDEP := $(COQBIN)coqdep -vos

# OPTIONAL saving of error in a file, to open in the ide the error file first
SHELL := /bin/bash
COQERROR := .coq_error
COQSAVERROR := | tee $(COQERROR)

CFMLC := $(CFML)/_build/default/generator/cfmlc.exe

OCAMLBUILD := \
  ocamlbuild \
    -classic-display -use-ocamlfind \
    -cflags "-g" -lflags "-g" \
	 -X .coq-native


#################################
# Files.

DEPEND := .depend_lib .depend_ml .depend_v

GENERATOR_SRC := $(shell find $(GENERATOR) \( -name '*.ml' -o  -name '*.mli' \) !  -path '$(GENERATOR)/_build/*')

LIBCOQ_V := $(wildcard $(LIBCOQ)/*.v)

STDLIB_ML := $(wildcard $(STDLIB)/*.ml)
STDLIB_CMJ := $(patsubst %.ml,%.cmj,$(STDLIB_ML))
STDLIB_MLV := $(patsubst %.ml,%_ml.v,$(STDLIB_ML))
STDLIBMAIN := $(STDLIB)/Stdlib.v
STDLIB_PROOFV := $(patsubst %.ml,%_proof.v,$(STDLIB_ML))
STDLIB_V := $(STDLIB_MLV) $(STDLIB_PROOFV) $(STDLIBMAIN)

EXAMPLE_MLV := $(patsubst %.ml,%_ml.v,$(ML))
EXAMPLE_PROOFV := $(patsubst %.ml,%_proof.v,$(ML))
# TODO: SHOULD restrict to folder actually used
AUX_V := $(filter-out %_ml.v %_proof.v, $(shell find examples -name '*.v' -not -iwholename '*_output*'))
EXAMPLE_V := $(AUX_V) $(EXAMPLE_MLV) $(EXAMPLE_PROOFV)
EXAMPLE_EXE := $(patsubst %.ml,%.native,$(ML_MAIN))
EXAMPLE_MLD := $(patsubst %.ml,%.ml.d,$(ML))

MLV := $(STDLIB_MLV) $(EXAMPLE_MLV)
OTHERV := $(TLC_V) $(LIBCOQ_V) $(STDLIB)/Stdlib.v $(V_AUX)

V := $(TLC_V) $(LIBCOQ_V) $(STDLIB_V) $(EXAMPLE_V)

$(info V=$(V))

VQ := $(patsubst %.v,%.vq,$(V))
VO := $(patsubst %.v,%.vo,$(V))
VOS := $(patsubst %.v,%.vos,$(V))
VOK := $(patsubst %.v,%.vok,$(V))


##############################################################################
# Makefile configuration and shorthand targets

INTERMEDIATE=%_ml.v $(STDLIB)/%_ml.v
.SECONDARY: $(INTERMEDIATE)
.PRECIOUS: $(INTERMEDIATE)

.PHONY: all

vd: $(VD)
# TEMPORARY: filter out broken exp
vo: $(filter-out $(EXAMPLES_EXCLUDED), $(VO))
vos: $(VOS)
vok: $(VOK)

ocaml: $(EXAMPLE_EXE)

generator: $(CFMLC)
gen: generator

mlv: $(MLV)
mlvo: $(patsubst %.v,%.vo,$(MLV))

libcoq: $(patsubst %.v,%.vo,$(LIBCOQ_V))
libcoqs: $(patsubst %.v,%.vos,$(LIBCOQ_V))
libcoqk: $(patsubst %.v,%.vok,$(LIBCOQ_V))

stdlib: $(patsubst %.v,%.vo,$(STDLIB_V))
stdlibs: $(patsubst %.v,%.vos,$(STDLIB_V))
stdlibk: $(patsubst %.v,%.vok,$(STDLIB_V))

# $(info LIBCOQ_V=$(LIBCOQ_V))

mlv_show:
	echo $(MLV)

makefile_show:
	echo $(MAKEFILE_LIST)
	echo $(lastword $(MAKEFILE_LIST))

debug_infos:
	@echo "DONT_INCLUDE_ALL_STDLIB_V=$(DONT_INCLUDE_ALL_STDLIB_V)"
	@echo "LIBCOQ_V=$(LIBCOQ_V) "
	@echo "V=$(TLC_V) $(LIBCOQ_V) $(EXAMPLE_V)"


ifdef VERBOSE
	$(info DONT_INCLUDE_ALL_STDLIB_V=$(DONT_INCLUDE_ALL_STDLIB_V))
	$(info V=$(TLC_V) $(LIBCOQ_V) $(EXAMPLE_V))
endif


##############################################################################
# Execution of "make depend"

# Make depend performs recursive calls to the present Makefile in order
# to generate the dependency files:
# - .depend_lib: dependencies in TLC, lib/coq, and lib/stdlib
# - .depend_ml: dependencies between targeted $(ML) files
# - .depend_v.: dependencies between targeted *_ml.v, *_proof.v, and $(V_AUX) files
# These files must be generated in this specific order.

# It it important to export parameters to recursive calls for "make depend".
# Note that we purposely don't export the derived variables ML, V_AUX, EXAMPLEINCLUDE.
export CFML
export OCAMLINCLUDE
export COQBIN
export TLC
export COQWARNINGS
export COQEXTRAFLAGS
export COQFLAGS
export ARG_V_AUX
export ARG_ML
export ARG_EXAMPLEINCLUDE
export FOLDER

$(info FOLDER=$(FOLDER))
$(info LIBCOQ=$(LIBCOQ))

#ifeq ($(FOLDER),$(LIBCOQ))
#$(info FOLDER is LIBCOQ)
#
#depend: _CoqProject
#	$(MAKE) .depend_lib
#
#else

depend: _CoqProject
	$(MAKE) .depend_lib
	$(MAKE) .depend_ml
	$(MAKE) mlv
	$(MAKE) .depend_v

#endif


############################################################################
# Rule for building .depend_ml

# As described by the recipe below, including the dependency files $(D)
# adds dependencies of the form:
#   A.cmj: B.cmj
# whenever module A depends on module B.

# We use ocamldep to find out which files A depends upon.

# By using ocamldep in this way, we obtain dependencies that mention absolute
# path names, as desired. We cannot use ocamldep -modules because it does not
# perform this search and does not produce absolute path names.

# ocamldep does not reliably print absolute path names -- its output depends
# on the current directory! it omits the absolute path if it coincides with
# the current directory. So, we change the current directory to /tmp before
# invoking ocamldep.

# ocamldep produces the following dependencies:
#   A.cmo: B.cmi (or B.cmo, depending on the existence of B.mli, I think)
#   A.cmx: B.cmx (or B.cmi, depending on obscure criteria)
# We keep only the second line and replace both .cmx and .cmi with .cmj in it.

# ocamldep sometimes produces a dependency A.cmx: A.cmi (not sure why).
# This leads us to produce a circular dependency A.cmj: A.cmj.
# The script $(OCAMLPOST) filters it out.

SED := $(shell if command -v gsed >/dev/null ; then echo gsed ; else echo sed ; fi)

.depend_ml: $(ML)
	@echo "Computing $@"
	($(OCAMLDEP) -one-line $(OCAMLINCLUDE) $^) \
	  | grep cmx \
	  | $(SED) -e "s/\\.cm\\(x\\|i\\)/\\.cmj/g" \
	  > $@

# TEMPORARY WORKAROUND HACK
#$(CFML)/examples/PairingHeap/PairingHeap.cmj :
#    MList.cmo


############################################################################
# Rules for building .depend_lib and .depend_v

.depend_lib: $(LIBCOQ_V)
	@echo "Computing $@"
	$(COQDEP) $(COQINCLUDE) $(LIBCOQ_V) > $@

# Beware that 'make depend' needs to be redone if changing Coq files
.depend_v:
	@echo "Computing $@"
	$(COQDEP) $(COQINCLUDE) $(V) > $@

# Hardcoded constraints for $(STDLIBMAIN)

$(patsubst %.v,%.vo,$(STDLIBMAIN)): $(patsubst %.v,%.vo,$(STDLIB_MLV))
$(patsubst %.v,%.vos,$(STDLIBMAIN)) $(patsubst %.v,%.vok,$(STDLIBMAIN)): $(patsubst %.v,%.vos,$(STDLIB_MLV))

# The dependencies generated by coqdep at the point where the
# files *_ml.v don't exist yet are incomplete, because they lack dependencies
# on those files. We compensate for that by introducing the following dependency
# for %_proof.vo files, and by having .depend_v depend on al $(V) files,
# including $(MLV) files.

%_proof.vo %_proof.vos %_proof.vok: %_ml.v %_ml.vo


##############################################################################
# Building the generator

$(CFMLC): $(GENERATOR_SRC)
	make -C $(GENERATOR)


############################################################################
# Compiling OCaml code
#
# FOR FUTURE USE
# %.native: %.ml
#
#$(ML_MAIN:.ml=.native):
# $(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $@


############################################################################
# Include of generated dependency files

# If the Makefile target is one mentioned in the next two lines,
# we don't include dependency files
AUXGOALS := ocaml gen generator dev clean cleangen cleandep cleancoq cleandev cleanex
DEPENDGOALS := depend .depend_lib .depend_v .depend_ml
# Beware that this approach is fragile if goals could be substrings of the goal above

$(info MAKECMDGOALS=$(MAKECMDGOALS))

ifeq ($(findstring $(MAKECMDGOALS),$(AUXGOALS) $(DEPENDGOALS)),)

   ifeq ($(MAKECMDGOALS),libcoq)
      # Dependency files when building libcoq: only .depend_lib
      ifeq ($(wildcard .depend_lib),)
         $(error Missing .depend_lib; try 'make .depend_lib' first.)
      endif
      include .depend_lib
      $(info include .depend_lib)

	else
	ifeq ($(MAKECMDGOALS),mlv)
      # Dependency files when building mlv: only .depend_ml
      ifeq ($(wildcard .depend_ml),)
         $(error Missing .depend_ml; try 'make .depend_ml' first.)
      endif
      include .depend_ml
      $(info include .depend_ml)
   else

    $(info Regular compilation using all .depend files)
		ifeq ($(wildcard .depend_lib),)
      $(error Missing .depend_lib; try 'make depend' first.)
    endif
		ifeq ($(wildcard .depend_ml),)
      $(error Missing .depend_ml; try 'make depend' first.)
    endif
		ifeq ($(wildcard .depend_v),)
      $(error Missing .depend_v; try 'make depend' first.)
    endif
    include .depend_lib
    include .depend_ml
    include .depend_v

  endif
	endif

else
   $(info Special target, not including .depend files)
endif


##############################################################################
# Rules for building the Stdlib files

CFMLC_STDLIB_FLAGS :=
#-def_encoders -deep_embedding

$(STDLIB)/Pervasives_ml.v $(STDLIB)/Pervasives.cmj: $(STDLIB)/Pervasives.ml $(CFMLC)
	@echo "Processing stdlib $< with flags $(CFMLC_STDLIB_FLAGS)"
	$(CFMLC) $(CFMLC_STDLIB_FLAGS) -nostdlib -nopervasives -I $(STDLIB) $< || (rm -f $@; exit 1)

$(STDLIB)/%_ml.v $(STDLIB)/%.cmj: $(STDLIB)/%.ml $(STDLIB)/Pervasives.cmj $(CFMLC)
	@echo "Processing stdlib $< with flags $(CFMLC_STDLIB_FLAGS)"
	$(CFMLC) $(CFMLC_STDLIB_FLAGS) -nostdlib -I $(STDLIB) $< || (rm -f $@; exit 1)

# #lib/stdlib/Pervasives_ml.v lib/stdlib/Pervasives.cmj: $(STDLIB)/Pervasives.ml $(CFMLC)
# 	@echo "Processing stdlib $< with flags $(CFMLC_STDLIB_FLAGS)"
# 	$(CFMLC) $(CFMLC_STDLIB_FLAGS) -nostdlib -nopervasives -I $(STDLIB) $< || (rm -f $@; exit 1)

# lib/stdlib/%_ml.v lib/stdlib/%.cmj: $(STDLIB)/%.ml $(STDLIB)/Pervasives.cmj $(CFMLC)
# 	@echo "Processing stdlib $< with flags $(CFMLC_STDLIB_FLAGS)"
# 	$(CFMLC) $(CFMLC_STDLIB_FLAGS) -nostdlib -I $(STDLIB) $< || (rm -f $@; exit 1)


$(LIBOCAML)/%.cmj: $(STDLIB)/%.ml $(CFMLC)
	@echo "Processing ocaml lib $< with flags $(CFMLC_STDLIB_FLAGS)"
	$(CFMLC) $(CFMLC_STDLIB_FLAGS) -only_cmj -I $(STDLIB) $< || (rm -f $@; exit 1)


##############################################################################
# Generating %.cmj and %_ml.v files.

# Note: we must delete the .cmj file if the construction of the _ml.v file
# has failed. (Maybe the generator itself should take care of that!)

%_ml.v: %.cmj
	echo > /dev/null

%.cmj: %.ml $(STDLIB_CMJ) $(CFMLC)
	@echo "Generating $*_ml.v with options $(shell cat `dirname $<`/cfml.config  2>/dev/null | tr '\n' ' ' )"
	$(CFMLC) $(shell cat `dirname $<`/cfml.config 2>/dev/null | tr '\n' ' ') $(CFMLC_FLAGS) -I $(STDLIB) $(OCAMLINCLUDE) -I . $< || (rm -f $@; exit 1)

# Note: $(shell cat `dirname $<`/cfml.config | tr '\n' ' ')
# is used to grab the folder-specific CFML options, without line break


############################################################################
# Generating %.vo, %.vos, %.vok files

%.vo: %.v
	@echo "Compiling $<" $(COQSAVERROR)
	$(COQC) $(COQINCLUDE) $<

%.vos: %.v
	@echo "Digesting $<" $(COQSAVERROR)
	$(COQC) $(COQINCLUDE) -vos $<

%.vok: %.v
	@echo "Checking $<" $(COQSAVERROR)
	$(COQC) $(COQINCLUDE) -vok $<


##############################################################################
# Cleanup rules.

COQCLEAN := find . -type f \( -name '*.cmj' -o -name '*._ml.v' -o -name '*.vos' -o -name '*.vok' -o -name '*.vo' -o -name '*.glob' -o -name '*.native' \) -exec rm {} +; find . -type d -name '_output' -exec rm -Rf {} +

# [make cleangen] to clean only the generated files in the generator folder
cleangen:
	make -C $(GENERATOR) clean
	@echo "Clean up generator"

# [make cleandep] to clean only dependency  files
cleandep:
	rm -rf $(DEPEND)

# [make cleangen] to clean only the generated Coq files
cleancoq: cleandep
	$(COQCLEAN)
	@echo "Clean up Coq files"

# [make cleanex] to clean only the generated files in the examples folder
cleanex: cleandep
	cd examples; $(COQCLEAN)

# [make cleandev] to clean only the generated files local to the working folder
cleandev: cleandep
	cd $(FOLDER); $(COQCLEAN)

# [make clean] to clean all generated files
clean: cleangen cleancoq



##############################################################################
# DEPRECATED

# Rule for generating _CoqProject
# _CoqProject: .FORCE
# 	@echo $(COQINCLUDE) $(addprefix -arg ,$(COQWARNINGS)) > $@
# .FORCE:

# Rule for opening the file that fails to compile
# COQERRORGET := cat .coq_error | tail -n 1 | sed 's/Compiling \([^"]*\)$$/\1/'
# fix:
# code `$(COQERRORGET)`
