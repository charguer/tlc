% The TLC library
% Arthur Charguéraud, with contributions from others.
% CeCILL B license (the French equivalent of the BSD license).


To view this file in html format, run:

    pandoc README.md -o README.html


Description
===========

TLC is a library for Coq based on classical logic and use of type classes.

Compilation
===========

The first plot we generate is a simple bar plot in which bars are
grouped together by arguments of `n` and apart by arguments o
`algo`. The y axis represents run time.

To compile everything:

    cd src
    make 

To compile only the developments, not the demos:

    make lib

To compile only the demos:

    make demo

