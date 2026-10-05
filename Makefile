# Build and check the proof of the main theorems.
#
#   make build    compile theories/ with JOBS parallel jobs
#   make check    build, compare the axioms of the main theorem with
#                 check/assumptions.expected, and check that the frozen files
#                 are unchanged (scripts/check_sources.py)
#   make clean    remove compiled files
#
# ROCQ_SWITCH names the opam switch with the toolchain of README.md. Set it
# empty to use the rocq on your PATH: make check ROCQ_SWITCH=
ROCQ_SWITCH ?= rocq-analysis
EXEC = $(if $(ROCQ_SWITCH),opam exec --switch=$(ROCQ_SWITCH) --,)
JOBS ?= 4

.PHONY: all build check clean

all: check

Makefile.rocq: _CoqProject
	$(EXEC) rocq makefile -f _CoqProject -o Makefile.rocq

build: Makefile.rocq
	$(EXEC) $(MAKE) -f Makefile.rocq -j $(JOBS)

check: build
	mkdir -p build
	$(EXEC) rocq compile -noglob -Q theories EllipsoidFitting -o build/Assumptions.vo check/Assumptions.v > build/assumptions.txt
	diff -u check/assumptions.expected build/assumptions.txt
	python3 scripts/check_sources.py
	@echo "The main theorem is proved, uses only the axioms of check/assumptions.expected, and its statement is unchanged."

clean:
	if [ -f Makefile.rocq ]; then $(EXEC) $(MAKE) -f Makefile.rocq clean; fi
	rm -rf build Makefile.rocq Makefile.rocq.conf
