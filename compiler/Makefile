# -*- Makefile -*-

# --------------------------------------------------------------------
JSJOBS    ?= 2
CHECKPY   ?=
CHECK     := $(CHECKPY) scripts/runtest --jobs="$(JSJOBS)"
CHECK     += config/tests.config
CHECKCATS ?= \
	x86-64-ATT \
	x86-64-Intel \
	x86-64-print \
	x86-64-nolea \
	arm-m4 \
	arm-m4-print \
	x86-64-stack-zero-loop \
	x86-64-stack-zero-unrolled \
	arm-m4-stack-zero-loop \
	arm-m4-stack-zero-unrolled \
	risc-v \
	CCT CCT-DOIT SCT

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
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec
	dune build @check @install
	for p in _build/install/default/bin/*; do ln -sf $$p $$(basename $$p); done
endef

byte:
	$(call do-build,bc)

native:
	$(call do-build,exe)

CIL:
	$(RM) -f src/CIL/*.ml src/CIL/*.mli ../proofs/extraction.vo
	$(MAKE) -C ../proofs extraction
	cp ../proofs/lang/ocaml/*.ml  src/CIL/
	cp ../proofs/lang/ocaml/*.mli src/CIL/

check: build
	$(CHECK) --report=report.log $(CHECKCATS)

check-ci:
	$(CHECK) --report=- $(CHECKCATS)

clean:
	dune clean
	$(RM) jasminc jasmin2tex jasmin-ct jasmin2ec

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T jasminc $(DESTDIR)$(BINDIR)/jasminc
	$(INSTALL) -m 0755 -T jasmin2tex $(DESTDIR)$(BINDIR)/jasmin2tex
	$(INSTALL) -m 0755 -T jasmin-ct $(DESTDIR)$(BINDIR)/jasmin-ct
	$(INSTALL) -m 0755 -T jasmin2ec $(DESTDIR)$(BINDIR)/jasmin2ec

uninstall:
	$(RM) $(DESTDIR)$(BINDIR)/jasminc
	$(RM) $(DESTDIR)$(BINDIR)/jasmin2tex
	$(RM) $(DESTDIR)$(BINDIR)/jasmin2ec

# --------------------------------------------------------------------
dist: $(DISTDIR).tgz

$(DISTDIR).tgz: MANIFEST
	$(RM) -r $(DISTDIR)
	../scripts/distribution $(DISTDIR)/compiler $<
	cp -riv ../eclib $(DISTDIR)/
	cp ../Makefile.compiler $(DISTDIR)/Makefile
	tar -czvf $(DISTDIR).tgz --owner=0 --group=0 $(DISTDIR)
	$(RM) -r $(DISTDIR)

# --------------------------------------------------------------------
jasmin.bnf: src/parser.mly
	$(OBELISK) -i -o $@ $<

jasmin.ebnf: scripts/expand-bnf jasmin.bnf
	@sed -f $^ > $@
