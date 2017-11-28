#!/bin/bash

pwd
COQBIN=
if [ -f ./settings.sh ]
then
    source settings.sh
fi
echo "${COQBIN}coqide ${COQIDE_OPTIONS} -R . TLC $*"
${COQBIN}coqide ${COQIDE_OPTIONS} -R . TLC $*


# COQIDE_OPTIONS="-async-proofs off -async-proofs-command-error-resilience off"
#-dont-load-proofs  -async-proofs-j 1
