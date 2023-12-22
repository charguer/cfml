##############################################################################
# Folders

EXAMPLE_DIRS = \
	Stack \
	Tutorial \
	UnitTests \
	UnitTestsCredits \


# $(shell find . -type d -depth 1)

##############################################################################
# Targets

.PHONY: all seq clean

# "make all" and "make clean" can be run in parallel on all directories.

all clean: $(EXAMPLE_DIRS)

$(EXAMPLE_DIRS)::
	$(MAKE) -C $@ $(MAKECMDGOALS)

# "make seq" forces sequential compilation of the directories, and
# stops at the first error.

seq:
	for folder in $(EXAMPLE_DIRS); do make -C $${folder} || exit 1 ; done
