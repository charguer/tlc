############################################################################
# Configuration
#
#
# Variables to bind for using this makefile:
# COQBIN
# COQINCLUDE
# (optional) V, VD, VIO, VQ, VO


############################################################################
# Binaries

COQC   := $(COQBIN)coqc
COQDEP := $(COQBIN)coqdep
COQIDE := $(COQBIN)coqide
COQCHK := $(COQBIN)coqchk


############################################################################
# Targets

ifndef V
	V := $(wildcard *.v)
endif

ifndef VD
	VD := $(patsubst %.v,%.v.d,$(V))
endif

ifndef VIO
	VIO := $(patsubst %.v,%.vio,$(V))
endif

ifndef VQ
	VQ := $(patsubst %.v,%.vq,$(V))
endif

ifndef VO
	VO := $(patsubst %.v,%.vo,$(V))
endif

depend: $(VD)
quick: $(VIO)
proof: $(VQ)
proof_vo: $(VO)


############################################################################
# Rules

# We patch coqdep using sed so that it returns dependencies from vo to vio (and not to vo).

%.v.d: %.v 
	$(COQDEP) $(COQINCLUDE) $< > $@

%.vo: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio2vo 1 $(patsubst .vio,,$<) > /dev/null 2>&1 

%.vio: %.v .coqide
	$(COQC) -quick $(COQINCLUDE) $<

%.vq: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< > /dev/null 2>&1 
	@touch $@

# ==> TODO remove when verbosity bug is fixed

%.vqdbg: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< 
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

clean::
	rm -f *.vio *.v.d *.vo *.vq *.vk *.aux .*.aux *.glob
	rm -Rf .coq-native .coqide


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
# Used to replace dependency from vo to vio
# 	@sed -i -e "s/^\(.*\)\.vo\(.*\):/\1TEMPORARYvo\2:/g" -e "s/\.vo/.vio/g" -e "s/TEMPORARYvo/.vo/g" $@ 
