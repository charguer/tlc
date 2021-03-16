##############################################################################
# Certain custom settings can be defined in settings.sh.

# To specify the location of the Coq binaries, define COQBIN (with a
# trailing slash), e.g. COQBIN=/var/tmp/coq/bin/
# If COQBIN is undefined, then "coqc" is used.

# To request creation of .vio files, as opposed to creation of .vo
# files, define SERIOUS=0.

-include settings.sh

############################################################################
# Compilation.

# By default, we compile and install only .vo files. We could compile
# and install both .vio and .vo files (by using the targets "quick"
# and "proof_vo" in succession), but would it be a good idea? A .vio
# file can be 80x larger than the corresponding .vo file.

export COQINCLUDE := -R $(shell pwd) TLC
export COQBIN
export COQFLAGS

ifndef COQFLAGS
COQFLAGS=-w -implicit-core-hint-db,-omega-is-deprecated
endif

.PHONY: all clean

all depend clean _CoqProject vo vod vos vok:
	$(MAKE) -f Makefile.coq $@

############################################################################
# Installation.

CONTRIB := $(shell $(COQBIN)coqc -where)/user-contrib
TARGET  := $(CONTRIB)/TLC

.PHONY: install uninstall

install:
	rm -rf $(TARGET)
	mkdir -p $(TARGET)
	install -m 644 *.v *.vo *.glob Makefile Makefile.coq $(TARGET)
ifeq ($(SERIOUS),0)
	install -m 644 *.vio $(TARGET)
endif

uninstall:
	rm -rf $(TARGET)
