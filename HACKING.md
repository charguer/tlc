# Developer Documentation

## How to release TLC

First, check the file `coq-tlc.opam`. Make sure the dependencies
and version constraints are correct. Run `opam lint`.

Then, make sure that the library can be compiled by Coq. Run `make -j`. To
compile the library under several versions of Coq, run `make versions`.
This assumes that a number of appropriate `opam` switches exist; see the
list in `GNUMakefile`, and, if necessary, update this list.

Once you are ready, run `make release`. This creates a git tag and pushes
it to the repository.

Finally, assuming `make release` has succeeded, run `make opam` and follow the
interactive instructions. (This requires `opam-publish`.) At the end, a pull
request on the [opam Coq archive](https://github.com/coq/opam) will be opened.
[You may need to create your own fork of this repository. You may also need to
create a GitHub authentication token for use by `opam publish`.]
