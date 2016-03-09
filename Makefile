# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrEllipticCurves
SUBDIRS  :=
INCFLAGS := -R 3rdparty $(NAME) -R common $(NAME) -R src $(NAME)
COQFILES := \
	3rdparty/fraction.v \
	3rdparty/polyorder.v \
	common/ssrring.v \
	common/fracfield.v \
	common/polyall.v \
	common/polydec.v \
	common/polyfrac.v \
	common/xmatrix.v \
	common/xseq.v \
	src/ec.v \
	src/ecpoly.v \
	src/ecpolyfrac.v \
	src/ecorder.v \
	src/eceval.v \
	src/ecdiv.v \
	src/ecrr.v \
	src/ecdivlr.v \
	src/ecgroup.v

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f *.glob *.d *.vo

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = ellipttic-curves-ssr
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
     awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
