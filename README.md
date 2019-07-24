# The TLC Coq library

Description
===========

TLC is a general-purpose library that provides an alternative to Coq's standard library.

   - TLC relies on the axioms of
     functional extensionality,
     propositional extensionality,
     and indefinite description (also known as Hilbert's epsilon operator).
     The consequences of these axioms include
     the law of the excluded middle
     as well as proof irrelevance.
     Accepting these axioms often makes life significantly simpler.
   - TLC takes advantage of Coq's type class mechanism.
     In particular, this allows for common operators and lemma names
     for all container data structures and all order relations.
   - TLC includes the optimal fixed point combinator,
     which allows arbitrarily-complex recursive and co-recursive definitions.
   - TLC provides a collection of tactics that enhance the default tactics
     provided by Coq. These tactics help construct more concise and more
     robust proof scripts.

Status:

   - The master branch compiles with both Coq 8.8 and Coq 8.9.
     There is also a branch for Coq 8.10.

Compatibility:

   - Disclaimer: to allow improving the design of TLC, backward compatibility is not guaranteed.
   - TLC should not be incompatible with use of the standard library.

Compilation
===========

The released versions of TLC are available via `opam`:

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install -j4 coq-tlc

A working copy of TLC can also be compiled and installed as follows:

    # first clone this repository, then descend into it, and:
    make -j4
    make install

Documentation
=============

Some (partial) documentation can be found in the directory [doc](doc/).

License
=======

All files in TLC are distributed under the GNU-LGPL license.

If you need a more permissive license, please contact the author.

Authors: Arthur Charguéraud,
with contributions from Armaël Guéneau and François Pottier.
