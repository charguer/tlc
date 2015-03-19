############################################################################
# To specify the location of coq binaries, create a file  called
# "settings.sh" and define the variable COQBIN (with trailing slash), e.g.
#    COQBIN=/var/tmp/coq/bin/

-include settings.sh

############################################################################
# Compilation

all: proof
COQINCLUDE := -R . TLC
include Makefile.coq

