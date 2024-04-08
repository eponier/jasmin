# -*- Makefile -*-

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= \
	safety \
	CCT \
	x86-64-ATT \
	x86-64-Intel \
	x86-64-print \
	x86-64-nolea \
	arm-m4 \
	arm-m4-print \
	x86-64-stack-zero-loop \
	x86-64-stack-zero-unrolled \
	arm-m4-stack-zero-loop \
	arm-m4-stack-zero-unrolled

# --------------------------------------------------------------------
DESTDIR  ?=
PREFIX   ?= /usr/local
BINDIR   := $(PREFIX)/bin
INSTALL  ?= ../scripts/install-sh

# --------------------------------------------------------------------
DISTDIR ?= jasmin-compiler

# --------------------------------------------------------------------
OBELISK ?= obelisk

# --------------------------------------------------------------------
.PHONY: all build byte native CIL check check-ci
.PHONY: clean install uninstall dist

all: build
	@true

build: native

define do-build
	$(RM) jasminc jazz2tex jazzct
	dune build @check entry/jasminc.$(1) entry/jazz2tex.$(1) entry/jazzct.$(1)
	ln -sf "../_build/default/compiler/entry/jasminc.$(1)" jasminc
	ln -sf "../_build/default/compiler/entry/jazz2tex.$(1)" jazz2tex
	ln -sf "../_build/default/compiler/entry/jazzct.$(1)" jazzct
endef

byte:
	$(call do-build,bc)

native:
	$(call do-build,exe)

CIL:
	$(RM) -f src/CIL/*.ml src/CIL/*.mli
	$(MAKE) -C ../proofs extraction
	cp ../_build/default/proofs/extraction/*.ml  src/CIL/
	cp ../_build/default/proofs/extraction/*.mli src/CIL/
	for i in wsize BinNums Datatypes String0 eqtype utils0 Specif ssrbool ssrfun Bool BinInt BinNat BinPos BinPosDef Nat0 CMorphisms CRelationClasses Init finfun fintype ssrnat choice seq stack_zero_strategy; do \
	  mv -f "src/CIL/$$i.ml" "src/CIL/$$i.mli" src/pre_CIL; \
	done

check: build
	$(CHECK) --report=report.log $(CHECKCATS)

check-ci:
	$(CHECK) --report=- $(CHECKCATS)

clean:
	dune clean
	$(RM) jasminc jazz2tex jazzct

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T jasminc $(DESTDIR)$(BINDIR)/jasminc
	$(INSTALL) -m 0755 -T jazz2tex $(DESTDIR)$(BINDIR)/jazz2tex
	$(INSTALL) -m 0755 -T jazzct $(DESTDIR)$(BINDIR)/jazzct

uninstall:
	$(RM) $(DESTDIR)$(BINDIR)/jasminc
	$(RM) $(DESTDIR)$(BINDIR)/jazz2tex
	$(RM) $(DESTDIR)$(BINDIR)/jazzct

# --------------------------------------------------------------------
dist: $(DISTDIR).tgz

$(DISTDIR).tgz: MANIFEST
	$(RM) -r $(DISTDIR)
	../scripts/distribution $(DISTDIR) $<
	tar -czvf $(DISTDIR).tgz --owner=0 --group=0 $(DISTDIR)
	$(RM) -r $(DISTDIR)

# --------------------------------------------------------------------
jasmin.bnf: src/parser.mly
	$(OBELISK) -i -o $@ $<

jasmin.ebnf: scripts/expand-bnf jasmin.bnf
	@sed -f $^ > $@
