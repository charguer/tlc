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

.PHONY: proof depend quick proof_vo proof_vq

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
# Verbosity filter. (Remove when verbosity bug in Coq is fixed.)

QUIET := 2>&1 | (grep -v "Checking task" || true)

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
	@$(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* $(QUIET)

%.vio: %.v
	$(COQC) $(COQINCLUDE) -quick $<

%.vq: %.vio
	@echo "Checking $*..."
	@$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< $(QUIET)
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
	rm -f *.vio *.v.d *.vo *.vq *.vk *.aux .*.aux *.glob
	rm -rf .coq-native .coqide

############################################################################
############################################################################
# Notes

# Later: checking
#
# ifndef VK
# 	VK := $(patsubst %.v,%.vk,$(V))
# endif
#
# check: $(VK)
#
#%.vk: %.vo
#	$(COQCHK) $(COQINCLUDE) $<
#
#
# We patch coqdep using sed so that it returns dependencies from vo to vio (and not to vo).
# Used to replace dependency from vo to vio
# 	@sed -i -e "s/^\(.*\)\.vo\(.*\):/\1TEMPORARYvo\2:/g" -e "s/\.vo/.vio/g" -e "s/TEMPORARYvo/.vo/g" $@ 
