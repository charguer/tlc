
############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#     COQBIN=/var/tmp/charguer/v8.4/bin/
# Note the use of a leading slash.


COQBIN=

-include settings.sh


############################################################################
# Files

LIB :=\
	LibTactics.v \
	LibAxioms.v \
	LibEqual.v \
	LibLogic.v \
	LibEpsilon.v \
	LibFunc.v \
	LibChoice.v \
	LibOperation.v \
	LibBool.v \
	LibReflect.v \
	LibUnit.v \
	LibProd.v \
	LibSum.v \
	LibOption.v \
	LibStruct.v \
	LibRelation.v \
	LibOrder.v \
	LibWf.v \
	LibNat.v \
	LibInt.v \
	LibStruct.v \
	LibList.v \
	LibListSorted.v \
	LibListZ.v \
	LibBag.v \
	LibSet.v \
	LibMultiset.v \
	LibMap.v \
	LibArray.v \
	LibGraph.v \
	LibPer.v \
	LibString.v \
	LibFset.v \
	LibVar.v \
	LibEnv.v \
	LibLN.v \
	LibHeap.v \
	LibCore.v


MORE :=\
	LibFix.v \
	LibStream.v 

DEMO :=\
	LibTacticsDemos.v \
	LibFixDemos.v \
	LibOtherDemos.v 

#	LibCoreDemos.v \

TACTICS :=\
	LibTactics.v \
	LibTacticsDemos.v 

ALL := $(LIB) $(MORE) $(DEMO)


############################################################################
# Compilation

all: check

COQINCLUDE := -R . HERE
V := $(ALL)

include Makefile.coq

