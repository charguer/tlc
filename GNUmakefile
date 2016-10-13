# This Makefile is not shipped.

# -------------------------------------------------------------------------

# Delegate these commands.

.PHONY: all clean install uninstall

all clean install uninstall:
	@ $(MAKE) -C src $@

# -------------------------------------------------------------------------

# Utilities.

SED     := $(shell if hash gsed 2>/dev/null ; then echo gsed ; else echo sed ; fi)
CUT     := $(shell if hash gcut 2>/dev/null ; then echo gcut ; else echo cut ; fi)
MD5SUM  := $(shell if hash md5  2>/dev/null ; then echo "md5 -r" ; else echo md5sum ; fi)

# -------------------------------------------------------------------------

# Archive creation.

DATE     := $(shell /bin/date +%Y%m%d)
PACKAGE  := tlc-$(DATE)
PWD      := $(shell pwd)

.PHONY: package

package:
# Archive creation.
	rm -rf /tmp/$(PACKAGE)
	cp -r . /tmp/$(PACKAGE)
	cd /tmp && tar \
	  -X $(PWD)/.gitignore \
	  --exclude=.git \
	  --exclude=.gitignore \
	  --exclude=dev \
	  --exclude=doc \
	  --exclude=new \
	  --exclude=old \
	  --exclude=opam \
	  --exclude=open.sh \
	  --exclude=todo \
	  --exclude=GNUmakefile \
	  -cvz -f $(PACKAGE).tar.gz $(PACKAGE)
# Test the archive that we just created.
	rm -rf /tmp/$(PACKAGE)
	cd /tmp && tar xvfz $(PACKAGE).tar.gz
	cd /tmp/$(PACKAGE) && make -j4

# -------------------------------------------------------------------------

# Archive export.

# Our ssh upload command.
RSYNC   := scp -p -B -C
# Our Web site: ssh upload target. (With trailing slash.)
TARGET  := scm.gforge.inria.fr:/home/groups/tlc/htdocs/releases/
# Our Web site: public URL. (With trailing slash.)
WWW     := http://tlc.gforge.inria.fr/releases/

# The name of our opam package.
NAME    := coq-tlc
# Our forked copy of Coq's opam repository.
OPAM    := $(HOME)/dev/opam-coq-archive
# Our package subdirectory.
OPAMSUB := $(OPAM)/released/packages/$(NAME)
# Our package subsubdirectory.
OPAMSUBDATE := $(OPAMSUB)/$(NAME).$(DATE)
# Our checksum command.
CSUM     = $(shell $(MD5SUM) /tmp/$(PACKAGE).tar.gz | $(CUT) -d ' ' -f 1)

.PHONY: export opam

export:
	$(RSYNC) /tmp/$(PACKAGE).tar.gz $(TARGET)

opam:
# Update my local copy of the opam repository.
# This assumes that the following command has been run (once):
#   git remote add upstream git@github.com:coq/opam-coq-archive.git
	@ echo "Updating local opam repository..."
	@ cd $(OPAM) && \
	  git fetch upstream && \
	  git merge upstream/master
# Create a new package description, based on the last one.
	@ echo "Creating a new package description $(PACKAGE)..."
	cd $(OPAMSUB) && cp -r `ls | grep $(NAME) | tail -1` $(NAME).$(DATE)
# Update the file "url".
	@ cd $(OPAMSUBDATE) && \
	  rm -f url && \
	  echo 'archive: "$(WWW)$(PACKAGE).tar.gz"' >> url && \
	  echo 'checksum: "$(CSUM)"' >> url
# Copy the file "opam" from our repository to opam's.
	@ cp -f opam $(OPAMSUBDATE)
# Prepare a commit.
	@ echo "Preparing a new commit..."
	@ cd $(OPAMSUB) && \
	  git add $(NAME).$(DATE) && \
	  git status
# Ask for review.
	@ echo "If happy, please run:"
	@ echo "  cd $(OPAM) && git commit && git push && firefox https://github.com/"
	@ echo "and issue a pull request."
