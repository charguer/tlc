# This Makefile is used for releases.

include Makefile

# -------------------------------------------------------------------------

# The date becomes the version number.
DATE     := $(shell /bin/date +%Y%m%d)
DATEDASH := $(shell /bin/date +%Y-%m-%d)

# An abbreviation.
THIS     := coq-tlc

# The repository URL (https).
REPO     := https://github.com/charguer/tlc

# The archive URL (https).
ARCHIVE  := $(REPO)/archive/$(DATE).tar.gz

# -------------------------------------------------------------------------

.PHONY: pin
pin:
	opam pin add $(THIS) .

.PHONY: unpin
unpin:
	opam pin remove $(THIS)

# -------------------------------------------------------------------------

# Simulating the creation of an archive by git.

.PHONY: archive
archive:
	@ git archive HEAD --format=tar.gz -o $(DATE).tar.gz --prefix=$(THIS)/

# This creates an archive and checks that it can be compiled.

.PHONY: archive-check
archive-check: archive
	@ rm -rf $(THIS)
	@ tar xvfz $(DATE).tar.gz
	@ make -C $(THIS) -j
	@ rm -rf $(THIS) $(DATE).tar.gz

# -------------------------------------------------------------------------

# Making a release.

# It is recommended to pin the package first, so as to make sure that it
# can be compiled and installed.

.PHONY: release
release:
# Check the current package description.
	@ opam lint
# Check if everything has been committed.
	@ if [ -n "$$(git status --porcelain)" ] ; then \
	    echo "Error: there remain uncommitted changes." ; \
	    git status ; \
	    exit 1 ; \
	  else \
	    echo "Now making a release..." ; \
	  fi
# Create an archive and make sure that it compiles.
	make archive-check
# Create a git tag.
	@ git tag -a $(DATE) -m "Release $(DATE)."
# Upload. (This automatically makes a .tar.gz archive available on github.)
	@ git push
	@ git push --tags

# -------------------------------------------------------------------------

# Updating the opam package.

# This entry assumes that [make release] has been run on the same day.

.PHONY: opam
opam:
# Check the current package description.
	@ opam lint
# Patch coq-tlc.opam.
# We replace the string DATEDASH with $(DATEDASH).
# We replace the string DATE with $(DATE).
	@ cat $(THIS).opam \
	  | sed -e 's/DATEDASH/$(DATEDASH)/g' \
	  | sed -e 's/DATE/$(DATE)/g' \
	  > $(THIS).patched.opam
	@ opam publish \
	    -v $(DATE) \
	    --repo coq/opam-coq-archive \
	    --packages-directory released/packages \
	    $(THIS).patched.opam $(ARCHIVE)
	@ rm $(THIS).patched.opam
