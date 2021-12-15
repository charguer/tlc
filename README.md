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

Compatibility:

   - Disclaimer: to allow improving the design of TLC, backward compatibility is not guaranteed.
   - TLC can be used, to some extent, in conjunction with Coq's standard library, however there are a few rough edges.


Using TLC
=========

The released versions of TLC are available via `opam`:

```
    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install coq-tlc
```

For a local checkout of TLC:

```
    # obtain the sources
    git clone git@github.com:charguer/tlc.git

    # compile the library files
    make -j

    # install the files in Coq's user-contrib folder
    make install
```


Documentation
=============

Some (partial) documentation can be found in the directory [doc](doc/).

   - `NamingConventions.txt` describe the naming scheme for definition and lemmas
   - `StableFiles.txt` lists the stable files and the work-in-progress files
   - `TacticsOverview.html` provides an overview of the tactics from `LibTactics.v`
   - `Overview.txt` describes the most important design choices of the library

License
=======

All files in TLC are distributed under the MIT X11 license. See the LICENSE file.

Authors
=======

See the AUTHORS file.
