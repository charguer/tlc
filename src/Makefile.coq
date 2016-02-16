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

ifndef V
	V := $(wildcard *.v)
endif

VD := $(patsubst %.v,%.v.d,$(V))
VIO := $(patsubst %.v,%.vio,$(V))
VQ := $(patsubst %.v,%.vq,$(V))
VO := $(patsubst %.v,%.vo,$(V))

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
# We need a pipe that keeps the exit code of the *first* process.
# We could program it by hand, but prefer to use mispipe, which is part
# of the package moreutils.

MISPIPE := $(shell if mispipe true cat ; then echo mispipe ; else echo failed ; fi)
ifeq ($(MISPIPE),failed)
  $(error Please install mispipe (part of the package "moreutils"))
endif

############################################################################
# Rules

# If B uses A, then the dependencies produced by coqdep are:
# B.vo:  B.v A.vo
# B.vio: B.v A.vio

%.v.d: %.v
	$(COQDEP) $(COQINCLUDE) $< > $@

ifndef SERIOUS

%.vo: %.vio
	@echo "Compiling $*..."
	@$(MISPIPE) \
	  "$(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* 2>&1" \
	  "grep -v 'Checking task'"

%.vio: %.v
	$(COQC) $(COQINCLUDE) -quick $<

%.vq: %.vio
	@echo "Checking $*..."
	@$(MISPIPE) \
	  "$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< 2>&1" \
	  "grep -v 'Checking task'"
	@touch $@

endif

ifdef SERIOUS

%.vo: %.v 
	$(COQC) $(COQINCLUDE) $<

endif

_CoqProject:
	echo $(COQINCLUDE) > $@

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

# Do not delete intermediate files.
.SECONDARY: %.v.d %.vio
.PRECIOUS: %.v.d %.vio

.PHONY: clean

clean::
	rm -f *~
	rm -f *.vio *.v.d *.vo *.vq *.vk *.aux .*.aux *.glob *.cache
	rm -rf .coq-native .coqide

