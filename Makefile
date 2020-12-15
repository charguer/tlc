.PHONY: all
all:
	@ dune build @all

.PHONY: clean
clean:
	@ dune clean

# At the time of writing (2020/12/15), [dune install] does not seem to
# work at all. It seems to install an empty OCaml library named TLC.
