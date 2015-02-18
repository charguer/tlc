
############################################################################
# To specify the location of coq binaries, create a file  called
# "settings.sh" and define the variable COQBIN (with trailing slash), e.g.
#    COQBIN=/var/tmp/coq/bin/

-include settings.sh


############################################################################
# Files

SRC :=\
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
	LibCore.v  \
	LibFix.v \
	LibStream.v  \
	LibTacticsDemos.v \
	LibFixDemos.v \
	LibOtherDemos.v 


############################################################################
# Compilation

all: check

COQINCLUDE := -R . TLC
V := $(SRC)

include Makefile.coq

