############################################################################
# Configuration
#
#
# Variables to bind for using this makefile:
# COQBIN
# COQINCLUDE
# V (optional)


############################################################################
# Binaries

COQC   := $(COQBIN)coqc
COQDEP := $(COQBIN)coqdep
COQIDE := $(COQBIN)coqide


############################################################################
# Targets

ifndef V
	V      := $(wildcard *.v)
endif

VO     := $(patsubst %.v,%.vo,$(V))
VIO     := $(patsubst %.v,%.vio,$(V))
VD     := $(patsubst %.v,%.v.d,$(V))
VK     := $(patsubst %.v,%.vk,$(V))

verify: $(VO)
check: $(VK)
quick: $(VIO)


############################################################################
# Rules

%.v.d: %.v 
	$(COQDEP) $(COQINCLUDE) $< > $@

%.vo: %.v
	$(COQC) $(COQINCLUDE) $<

%.vio: %.v
	$(COQC) -quick $(COQINCLUDE) $<

%.vk: %.vio
	$(COQC) $(COQINCLUDE) -schedule-vio-checking 1 $< > /dev/null 2>&1 
	@touch $@


############################################################################
# Dependencies

ifeq ($(findstring $(MAKECMDGOALS),clean),)
-include $(VD)
endif

############################################################################
# IDE

ide:
	$(COQIDE) $(COQINCLUDE)


############################################################################
# Clean

clean:
	rm -f *.vio *.v.d *.vo *.vk *.aux .*.aux *.glob
	rm -Rf .coq-native
