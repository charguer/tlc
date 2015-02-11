#!/bin/bash

pwd
COQBIN=
if [ -f ./settings.sh ]
then
    source settings.sh 
fi
echo coqbin=${COQBIN}
${COQBIN}coqide -R . TLC $*


#-dont-load-proofs  -async-proofs-j 1
