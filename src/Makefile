############################################################################
# Compilation.

# As of now, we compile and install only .vo files.
# We could compile and install both .vio and .vo files (by using the targets
# "quick" and "proof_vo" in succession), but would it be a good idea?
# A .vio file can be 80x larger than the corresponding .vo file.

export COQINCLUDE := -R $(shell pwd) TLC
export SERIOUS    := 1 # request .vo files

.PHONY: all clean

all clean:
	$(MAKE) -f Makefile.coq $@

############################################################################
# Installation.

CONTRIB := $(shell $(COQBIN)coqc -where)/user-contrib
TARGET  := $(CONTRIB)/TLC

.PHONY: install uninstall

install:
	rm -rf $(TARGET)
	mkdir -p $(TARGET)
	install -m 644 *.v *.vo *.glob Makefile.coq $(TARGET)

uninstall:
	rm -rf $(TARGET)
