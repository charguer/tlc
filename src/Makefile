############################################################################
# To specify the location of the Coq binaries, create a file called
# settings.sh and define the variable COQBIN (with trailing slash),
# e.g.
#   COQBIN=/var/tmp/coq/bin/
# If this file is absent, then COQBIN is empty and "coqc" is used.

-include settings.sh

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
