
   COQBIN=~/softs/coq8.4/bin/
   export PATH="$COQBIN:$PATH"


   ~/softs/coq8.4/bin/coqc Ssrext.v 
   ~/softs/coq8.4/bin/coqide Ssrext.v &
   ~/softs/coq8.4/bin/coqide -R ~/softs/ssreflect-1.4/theories/ Ssreflect SsrextDemos.v &





not up to date


  git clone http://ssr.msr-inria.inria.fr/~gares/coqfinitgroup.git/.git
  git checkout wip
  export COQBIN=..../coq/bin/
  make theories/seq.vo
