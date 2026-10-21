# Build and check the proof of the main theorems.
#
#   make build    compile library/, theories/, extension/ and applications/
#                 with JOBS parallel jobs
#   make theories/Foo.vo, make library/dir/foo.vo, make extension/Dir/Foo.vo,
#   make applications/Foo.vo
#                 compile one module and what it requires, not what
#                 depends on it: for iteration; it does not replace make check
#   make check    run scripts/check_sources.py --before-build, which checks
#                 the sources before anything compiles; build; then run
#                 scripts/check_sources.py, which checks the sources again,
#                 starts scripts/run_checks.py to compile the check files of
#                 check/ with a run identifier it creates, then checks: the axioms
#                 of each theorem are among those of its expected list, and
#                 each theorem has its frozen statement as its type; the
#                 frozen files and the pinned sections are unchanged; the
#                 statement snapshots equal their references; library/ and
#                 applications/ depend neither on the papers nor on Stdlib's
#                 reals, and library/ not on applications/; the build
#                 configuration and the scripts are as fixed;
#                 make reads a GNUmakefile or a makefile before this file:
#                 the checker refuses both, but only make -f Makefile check
#                 runs the checker whatever files the tree holds;
#                 unless CITATIONS=no, it also runs
#                 scripts/stale_citations.py (see make citations)
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
# CHECK_JOBS check files compile at once in make check (each loads large
# libraries; raise it where memory allows).
CHECK_JOBS ?= 1
# The variables that can change what Rocq loads (an rc file, a load path, a
# plugin path), and every variable whose name starts with OCAML or CAML (the
# configuration of findlib and of the OCaml compiler): make build and make
# check run without them.
UNSAFE_ENV = ROCQPATH COQPATH ROCQLIB COQLIB OCAMLPATH CAML_LD_LIBRARY_PATH \
	ROCQRC COQRC XDG_CONFIG_HOME COQFLAGS COQEXTRAFLAGS OTHERFLAGS \
	COQ_SRC_SUBDIRS COQCHKEXTRAFLAGS
CLEAN_ENV = env $(addprefix -u ,$(sort $(UNSAFE_ENV) $(filter OCAML% CAML%,$(.VARIABLES))))
# CITATIONS=no makes "make check" skip scripts/stale_citations.py, which
# fails when a comment cites a name that nothing defines.
CITATIONS ?= yes


.PHONY: all build check citations clean FORCE

all: check

Makefile.rocq: _CoqProject
	$(EXEC) $(CLEAN_ENV) rocq makefile -f _CoqProject -o Makefile.rocq

build: Makefile.rocq
	$(EXEC) $(CLEAN_ENV) $(MAKE) -f Makefile.rocq -j $(JOBS)

theories/%.vo library/%.vo extension/%.vo applications/%.vo: Makefile.rocq FORCE
	$(EXEC) $(CLEAN_ENV) $(MAKE) -f Makefile.rocq -j $(JOBS) $@

check:
	$(EXEC) $(CLEAN_ENV) python3 -I -B scripts/check_sources.py --before-build
	$(MAKE) -f Makefile build
	$(EXEC) $(CLEAN_ENV) python3 -I -B scripts/check_sources.py --jobs $(CHECK_JOBS)
	$(if $(filter yes,$(CITATIONS)),$(EXEC) python3 -I -B scripts/stale_citations.py,@true)
	@echo "make check passed."

citations: Makefile.rocq
	$(EXEC) python3 -I -B scripts/stale_citations.py

clean:
	if [ -f Makefile.rocq ]; then $(EXEC) $(MAKE) -f Makefile.rocq clean; fi
	rm -rf build Makefile.rocq Makefile.rocq.conf
