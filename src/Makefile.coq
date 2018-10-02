############################################################################
# Requirements.

# We need bash. We use the pipefail option to control the exit code of a
# pipeline.

SHELL := /usr/bin/env bash

############################################################################
# Configuration
#
#
# This Makefile relies on the following variables:
# ROOTDIR    (default: `pwd`)
# COQBIN     (default: empty)
# COQINCLUDE (default: empty)
# V          (default: *.v)
# V_AUX      (default: undefined/empty)
# VERBOSE    (default: undefined)
#            (if defined, commands are displayed)

# We usually refer to the .v files using relative paths (such as Foo.v)
# but [coqdep -R] produces dependencies that refer to absolute paths
# (such as /bar/Foo.v). This confuses [make], which does not recognize
# that these files are the same. As a result, [make] does not respect
# the dependencies.

# We fix this by using ABSOLUTE PATHS EVERYWHERE. The paths used in targets,
# in -R options, etc., must be absolute paths.

ifndef ROOTDIR
	ROOTDIR := $(shell pwd)
endif

ifndef V
	V := $(wildcard $(ROOTDIR)/*.v)
endif

# Typically, $(V) should list only the .v files that we are ultimately
# interested in checking. $(V_AUX) should list every other .v file in the
# project. $(VD) is obtained from $(V) and $(V_AUX), so [make] sees all
# dependencies and can rebuild files anywhere in the project, if needed, and
# only if needed.

ifndef VD
	VD  := $(patsubst %.v,%.v.d,$(V) $(V_AUX))
endif

VIO := $(patsubst %.v,%.vio,$(V))
VQ  := $(patsubst %.v,%.vq,$(V))
VO  := $(patsubst %.v,%.vo,$(V))
VOS  := $(patsubst %.v,%.vos,$(V))
VOK  := $(patsubst %.v,%.vok,$(V))

############################################################################
# Binaries

COQC   := $(COQBIN)coqc $(COQFLAGS)
COQDEP := $(COQBIN)coqdep
COQIDE := $(COQBIN)coqide $(COQFLAGS)
COQCHK := $(COQBIN)coqchk

############################################################################
# Targets

.PHONY: all depend proof interface vos vok

all: proof
depend: $(VD)
proof: $(VO)
vos: $(VOS)
vok: $(VOK)


############################################################################
# Verbosity control.

# Our commands are pretty long (due, among other things, to the use of
# absolute paths everywhere). So, we hide them by default, and echo a short
# message instead. However, sometimes one wants to see the command.

# By default, VERBOSE is undefined, so the .SILENT directive is read, so no
# commands are echoed. If VERBOSE is defined by the user, then the .SILENT
# directive is ignored, so commands are echoed, unless they begin with an
# explicit @.

ifndef VERBOSE
.SILENT:
endif

############################################################################
# Verbosity filter.

# Coq is way too verbose when using one of the -schedule-* commands.
# So, we grep its output and remove any line that contains 'Checking task'.

# We need a pipe that keeps the exit code of the *first* process. In
# bash, when the pipefail option is set, the exit code is the logical
# conjunction of the exit codes of the two processes. If we make sure
# that the second process always succeeds, then we get the exit code
# of the first process, as desired.

############################################################################
# Rules

# If B uses A, then the dependencies produced by coqdep are:
# B.vo:  B.v A.vo
# B.vio: B.v A.vio

%.v.d: %.v
	$(COQDEP) $(COQINCLUDE) $< > $@

%.vo: %.v
	@echo "Compiling `basename $*`..."
	$(COQC) $(COQINCLUDE) $<

%.vos: %.v
	@echo "Digesting `basename $*`..."
	$(COQC) $(COQINCLUDE) -vos $<

%.vok: %.v
	@echo "Checking `basename $*`..."
	$(COQC) $(COQINCLUDE) -vok $<

# DEPRECATED
# %.vo: %.vio
#	@echo "Compiling `basename $*`..."
#	set -o pipefail; ( \
#	  $(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* \
#	  2>&1 | (grep -v 'Checking task' || true))

_CoqProject: .FORCE
	@echo $(COQINCLUDE) > $@

.FORCE:

############################################################################
# Dependencies

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
-include $(VD)
endif

############################################################################
# IDE

.PHONY: ide

.coqide:
	@echo '$(COQIDE) $(COQINCLUDE) $$*' > .coqide
	@chmod +x .coqide

ide: _CoqProject
	$(COQIDE) $(COQINCLUDE)

############################################################################
# Clean

.PHONY: clean

# In a multi-directory setting, it is not entirely clear how to find the
# files that we wish to remove.

# One approach would be to view $(V) as the authoritative list of source files
# and remove just the derived files $(VO), etc.

# Another approach is to scan all subdirectories of $(ROOTDIR) and remove all
# object files in them. We follow this approach.

# Be careful to use regular expressions that work both with GNU find
# and with BSD find (MacOS).

clean::
	for d in `find $(ROOTDIR) -type d -not -regex ".*\\.git.*"` ; do \
	  (cd $$d && \
	     rm -f *~ && \
	     rm -f .*.aux && \
	     rm -f *.{vo,vos,vok,v.d,aux,glob,cache,crashcoqide} && \
	     rm -rf *.coq-native *.coqide && \
	     true) ; \
	done
