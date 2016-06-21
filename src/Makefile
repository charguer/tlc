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
include Makefile.coq

############################################################################
# Installation
# "make install" should be run with appropriate permissions.

# As of now, it creates a symbolic link from Coq's user-contrib directory to
# this directory (src). This should be convenient for TLC developers, who have
# a working copy of the TLC git repository at hand. For end users, we might
# wish to copy this directory instead of creating a symbolic link to it.

.PHONY: install

install:
	mkdir -p `$(COQC) -where`/user-contrib
	ln -s `pwd` `$(COQC) -where`/user-contrib/TLC

# LATER: install could force creation of *.vo files, for end user
