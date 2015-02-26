############################################################################
# Configuration
#
#
# This Makefile relies on the following variables:
# COQBIN     (default: empty)
# COQINCLUDE (default: empty)
# V          (default: *.v)

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

.PHONY: proof depend quick proof_vo

proof: $(VQ)
depend: $(VD)
quick: $(VIO)
proof_vo: $(VO)

############################################################################
# Verbosity filter. (Remove when verbosity bug in Coq is fixed.)

QUIET := 2>&1 | (grep -v "Checking task" || true)

############################################################################
# Rules

%.v.d: %.v
	$(COQDEP) $(COQINCLUDE) $< > $@

%.vo: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $* $(QUIET)

%.vio: %.v .coqide
	$(COQC) $(COQINCLUDE) -quick $<

%.vq: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< $(QUIET)
	@touch $@

# be careful dependencies not respected for vodirect
%.vodirect: %.v 
	$(COQC) $(COQINCLUDE) $<
	@touch $@

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

ide:
	$(COQIDE) $(COQINCLUDE)

############################################################################
# Clean

# Do not delete intermediate files.
.SECONDARY: %.v.d %.vio
.PRECIOUS: %.v.d %.vio

.PHONY: clean

clean::
	rm -f *.vio *.v.d *.vo *.vq *.vk *.aux .*.aux *.glob
	rm -rf .coq-native .coqide

############################################################################
############################################################################
# Notes

# Alternative for vo construction:
# %.vo: %.v
#	$(COQC) $(COQINCLUDE) $<
#
#
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
