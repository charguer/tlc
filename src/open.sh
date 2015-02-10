COQBIN=
if [ -f settings.sh ]
then
    source settings.sh 
fi
${COQBIN}coqide -R . TLC $*

#-dont-load-proofs 
