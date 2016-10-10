############################################################################
# Compilation

PWD := $(shell pwd)
COQINCLUDE := -R $(PWD) TLC
SERIOUS := 1 # request .vo files
include Makefile.coq

############################################################################
# Installation
# "make install" should be run with appropriate permissions.

.PHONY: install uninstall

CONTRIB := $(shell $(COQC) -where)/user-contrib
TARGET  := $(CONTRIB)/TLC

install:
	rm -rf $(TARGET)
	mkdir -p $(TARGET)
	install -m 644 *.v *.vo *.glob Makefile.coq $(TARGET)

uninstall:
	rm -rf $(TARGET)
