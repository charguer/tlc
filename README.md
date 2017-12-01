# The TLC Coq library

Description
===========

TLC is a general purpose Coq library that provides an alternative to Coq's standard library.

   - TLC takes as axiom extensionality, classical logic and indefinite description (Hilbert's epsilon). These axioms allow for significantly simpler formal definitions in many cases.
   - TLC takes advantage of the type class mechanism. In particular, this allows for common operators and lemma names for all container data structures and all order relations.
   - TLC includes the optimal fixed point combinator, which can be used for building arbitrarily-complex recursive and co-recursive definitions.
   - TLC provides a collection of tactics that enhance the default tactics provided by Coq. These tactics help constructing more concise and more robust proof scripts.


Status:

   - TLC compiles with Coq v8.6 (tags are available for prior versions).
   - TLC 2.0 (beta) was released in November 2017, with a complete polishing phase.
 

Compatibility:

   - Disclaimer: to allow improving the design of TLC, backward compatibility is not guaranteed.
   - TLC should not be incompatible with use of the standard library.
 

License
=======

All the files from TLC are distributed under the GNU-LGPL license.

If you need a more permissive license, please contact the author.

Authors: Arthur Charguéraud, with contributions from François Pottier.


Documentation
=============

Some (partial) documentation can be found in subfolder "doc".


Compilation
===========

To compile everything:

    cd src
    make
    make install
    
    
