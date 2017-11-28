#!/bin/bash

pwd
COQBIN=
if [ -f ./settings.sh ]
then
    source settings.sh
fi
echo "${COQBIN}coqide ${COQOPTIONS} -R . TLC $*"
${COQBIN}coqide ${COQOPTIONS} -R . TLC $*


#-dont-load-proofs  -async-proofs-j 1
# COQOPTIONS=-async-proofs off -async-proofs-command-error-resilience off