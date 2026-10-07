# Build and check the proof of the main theorems.
#
#   make build    compile library/, theories/ and extension/ with JOBS
#                 parallel jobs
#   make theories/Foo.vo, make library/dir/foo.vo, make extension/Dir/Foo.vo
#                 compile one module and what it requires, not what
#                 depends on it: for iteration; it does not replace make check
#   make check    build, then run scripts/check_sources.py: the axioms of the
#                 main theorem are among those of check/assumptions.expected,
#                 the frozen files are unchanged, and library/ depends neither
#                 on the papers nor on Stdlib's reals; unless CITATIONS=no, it
#                 also runs scripts/stale_citations.py (see make citations)
#   make citations
#                 list the names that comments cite but that nothing defines
#                 (scripts/stale_citations.py), after a build
#   make clean    remove compiled files
#
# ROCQ_SWITCH names the opam switch with the toolchain of README.md. Set it
# empty to use the rocq on your PATH: make check ROCQ_SWITCH=
ROCQ_SWITCH ?= rocq-analysis
EXEC = $(if $(ROCQ_SWITCH),opam exec --switch=$(ROCQ_SWITCH) --,)
JOBS ?= 4
# CITATIONS=no makes "make check" skip scripts/stale_citations.py, which
# fails when a comment cites a name that nothing defines.
CITATIONS ?= yes

.PHONY: all build check citations clean FORCE

all: check

Makefile.rocq: _CoqProject
	$(EXEC) rocq makefile -f _CoqProject -o Makefile.rocq

build: Makefile.rocq
	$(EXEC) $(MAKE) -f Makefile.rocq -j $(JOBS)

theories/%.vo library/%.vo extension/%.vo: Makefile.rocq FORCE
	$(EXEC) $(MAKE) -f Makefile.rocq -j $(JOBS) $@

check: build
	mkdir -p build
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -o build/Assumptions.vo check/Assumptions.v > build/assumptions.txt
	python3 scripts/check_sources.py build/assumptions.txt
	$(if $(filter yes,$(CITATIONS)),$(EXEC) python3 scripts/stale_citations.py,@true)
	@echo "make check passed."

citations: Makefile.rocq
	$(EXEC) python3 scripts/stale_citations.py

clean:
	if [ -f Makefile.rocq ]; then $(EXEC) $(MAKE) -f Makefile.rocq clean; fi
	rm -rf build Makefile.rocq Makefile.rocq.conf
