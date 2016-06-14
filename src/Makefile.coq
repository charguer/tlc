############################################################################
# Requirements.

# We need bash. We use the pipefail option to control the exit code of a
# pipeline.

SHELL := /bin/bash

############################################################################
# Configuration
#
#
# This Makefile relies on the following variables:
# COQBIN     (default: empty)
# COQINCLUDE (default: empty)
# V          (default: *.v)
# SERIOUS    (default: undefined)
#            (if defined, coqc is used to produce .vo files in the old way)

# We usually refer to the .v files using relative paths (such as Foo.v)
# but [coqdep -R] produces dependencies that refer to absolute paths
# (such as /bar/Foo.v). This confuses [make], which does not recognize
# that these files are the same. As a result, [make] does not respect
# the dependencies.
# We fix this, for the moment, by using absolute paths everywhere.
# Note that the paths specified by the user via -R options MUST be
# absolute paths, too!
# Not sure if this is quite right:

ifndef V
	PWD := $(shell pwd)
	V := $(wildcard $(PWD)/*.v)
endif

ifndef VD
	VD  := $(patsubst %.v,%.v.d,$(V))
endif

VIO := $(patsubst %.v,%.vio,$(V))
VQ  := $(patsubst %.v,%.vq,$(V))
VO  := $(patsubst %.v,%.vo,$(V))


############################################################################
# Binaries

COQC   := $(COQBIN)coqc
COQDEP := $(COQBIN)coqdep
COQIDE := $(COQBIN)coqide
COQCHK := $(COQBIN)coqchk

############################################################################
# Targets

.PHONY: all proof depend quick proof_vo proof_vq

all: proof
ifndef SERIOUS
proof: proof_vq
else
proof: proof_vo
endif
proof_vq: $(VQ)
depend: $(VD)
quick: $(VIO)
proof_vo: $(VO)

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
	@$(COQDEP) $(COQINCLUDE) $< > $@

ifndef SERIOUS

%.vo: %.vio
	@echo "Compiling `basename $*`..."
	@set -o pipefail; ( \
	  $(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* \
	  2>&1 | (grep -v 'Checking task' || true))

%.vio: %.v
	@echo "Digesting `basename $*`..."
	@$(COQC) $(COQINCLUDE) -quick $<

%.vq: %.vio
	@echo "Checking `basename $*`..."
	@set -o pipefail; ( \
	  $(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< \
	  2>&1 | (grep -v 'Checking task' || true))
	@touch $@

endif

ifdef SERIOUS

%.vo: %.v
	$(COQC) $(COQINCLUDE) $<

endif

_CoqProject: .FORCE
	echo $(COQINCLUDE) > $@

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

clean::
	rm -f *~
	rm -f *.vio *.v.d *.vo *.vq *.vk *.aux .*.aux *.glob *.cache *.crashcoqide
	rm -rf .coq-native .coqide
