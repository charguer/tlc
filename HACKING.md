# Developer Documentation

## How to release TLC

### Declare constraint on supported versions

Check the file `coq-tlc.opam`.

Make sure the dependencies and version constraints are correct.
In particular the constraint of the form `"coq" { >= "8.17" }`.

Run `opam lint`.

### Check compilation for various versions

Open the file `GNUMakefile` and locate the definition of `VERSIONS :=`.
Each version listed there will be tested.

For each version in this list, ensure the existence of a corresponding
opam switch. To create one, use e.g.:
`opam switch create coq818 4.14.1; opam pin add -y coq 8.18.0`.

Optionally, run `make -j` to check compilation in the current switch.

Run `make versions` to check compilation for all listed versions.

### Create the release tag in the repo

Assuming `make versions` has succeeded.

Run `make release`. This creates a git tag and pushes it to the repository.

### Release the opam package

Assuming `make release` has succeeded.

Check that you have the package `opam-publish` in the current switch.
If not, `opam install opam-publish`.

[You may need to create your own fork of this repository. You may also need to
create a GitHub authentication token for use by `opam publish`.]

Run `make opam` and follow the interactive instructions.
At the end, a pull request on the [opam Coq archive](https://github.com/coq/opam)
will be opened.

