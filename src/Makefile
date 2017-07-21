##############################################################################
# Certain custom settings can be defined in settings.sh.

# To specify the location of the Coq binaries, define COQBIN (with a
# trailing slash), e.g. COQBIN=/var/tmp/coq/bin/.
# If COQBIN is undefined, then "coqc" is used.

# To request installation via a symbolic link, as opposed to
# installation via a copy, define ARTHUR.

# To request creation of .vio files, as opposed to creation of .vo
# files, define SERIOUS=0.

SERIOUS := 1
-include settings.sh

############################################################################
# Files.

SRC :=\
   LibTactics \
	\
   LibAxioms \
   LibEqual \
   LibLogic \
	\
   LibOperation \
   LibBool \
   LibReflect \
	\
   LibNat \
   LibRelation \
   LibEpsilon \
   LibChoice \
   LibOperation \
   LibOrder \
   LibWf \
	\
   LibProd \
   LibSum \
   LibUnit \
   LibOption \
   LibString \
   LibInt \
   LibMonoid \
   LibList \
	\
	LibMin \
	LibFix \
	\
   LibContainer \
   LibSet

# V := $(addsuffix .v,$(SRC))


############################################################################
# Compilation.

# By default, we compile and install only .vo files. We could compile
# and install both .vio and .vo files (by using the targets "quick"
# and "proof_vo" in succession), but would it be a good idea? A .vio
# file can be 80x larger than the corresponding .vo file.

export COQINCLUDE := -R $(shell pwd) TLC
export SERIOUS
export COQBIN
export COQFLAGS

.PHONY: all clean

all depend clean _CoqProject:
	$(MAKE) -f Makefile.coq $@

#  V="$(V)" 

############################################################################
# Installation.

CONTRIB := $(shell $(COQBIN)coqc -where)/user-contrib
TARGET  := $(CONTRIB)/TLC

.PHONY: install uninstall

ifndef ARTHUR

install:
	rm -rf $(TARGET)
	mkdir -p $(TARGET)
	install -m 644 *.v *.vo *.glob Makefile Makefile.coq $(TARGET)
ifeq ($(SERIOUS),0)
	install -m 644 *.vio $(TARGET)
endif

else

install:
	rm -rf $(TARGET)
	mkdir -p $(CONTRIB)
	ln -s `pwd` $(TARGET)

endif

uninstall:
	rm -rf $(TARGET)
