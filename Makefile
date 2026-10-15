# Build and check the proof of the main theorems.
#
#   make build    compile library/, theories/, extension/ and applications/
#                 with JOBS parallel jobs
#   make theories/Foo.vo, make library/dir/foo.vo, make extension/Dir/Foo.vo,
#   make applications/Foo.vo
#                 compile one module and what it requires, not what
#                 depends on it: for iteration; it does not replace make check
#   make check    build, then run scripts/check_sources.py: the axioms of the
#                 main theorem are among those of check/assumptions.expected,
#                 those of the universality theorem among those of
#                 check/universality_assumptions.expected, and likewise for
#                 every theorem of its table, one report each; the frozen
#                 files are unchanged; library/ and applications/ depend
#                 neither on the papers nor on Stdlib's reals, and library/
#                 not on applications/; check/ApplicationsDefinitions.v
#                 checks the characterizations of the library definitions
#                 that the frozen statements of applications/ unfold to;
#                 the reports are deleted and regenerated at every run;
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
# CITATIONS=no makes "make check" skip scripts/stale_citations.py, which
# fails when a comment cites a name that nothing defines.
CITATIONS ?= yes

# The axiom reports of the check target, one per theorem of the table of
# scripts/check_sources.py, in its order (REPORTS there).
REPORTS = build/assumptions.txt \
	build/universality_assumptions.txt \
	build/mixture_assumptions.txt \
	build/paired_assumptions.txt \
	build/latent_sign_assumptions.txt \
	build/countable_assumptions.txt \
	build/condition_assumptions.txt \
	build/latent_scope_assumptions.txt \
	build/robust_assumptions.txt \
	build/latent_tensor_assumptions.txt \
	build/continuous_latent_assumptions.txt \
	build/condition_endpoints_assumptions.txt \
	build/condition_robust_assumptions.txt \
	build/latent_tensor_upper_assumptions.txt \
	build/condition_kappa_curve_assumptions.txt \
	build/condition_kappa_assumptions.txt \
	build/condition_kappa_robust_assumptions.txt \
	build/matrix_series_assumptions.txt \
	build/tensor_packing_assumptions.txt \
	build/goe_edge_assumptions.txt \
	build/sk_gap_assumptions.txt \
	build/psd_splitting_assumptions.txt \
	build/perceptron_sign_assumptions.txt \
	build/sat_variance_assumptions.txt

.PHONY: all build check citations clean FORCE

all: check

Makefile.rocq: _CoqProject
	$(EXEC) rocq makefile -f _CoqProject -o Makefile.rocq

build: Makefile.rocq
	$(EXEC) $(MAKE) -f Makefile.rocq -j $(JOBS)

theories/%.vo library/%.vo extension/%.vo applications/%.vo: Makefile.rocq FORCE
	$(EXEC) $(MAKE) -f Makefile.rocq -j $(JOBS) $@

check: build
	mkdir -p build
	rm -f $(REPORTS) build/applications_definitions.txt build/phase13_definitions.txt
	$(EXEC) rocq compile -noglob -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-prefix -w -hiding-delimiting-key -Q library GaussianAnalysis -o build/ApplicationsDefinitions.vo check/ApplicationsDefinitions.v > build/applications_definitions.txt
	$(EXEC) rocq compile -noglob -w -notation-overridden -w -ambiguous-paths -w -notation-incompatible-prefix -w -hiding-delimiting-key -Q library GaussianAnalysis -o build/Phase13Definitions.vo check/Phase13Definitions.v > build/phase13_definitions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -o build/Assumptions.vo check/Assumptions.v > build/assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/UniversalityAssumptions.vo check/UniversalityAssumptions.v > build/universality_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/MixtureAssumptions.vo check/MixtureAssumptions.v > build/mixture_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/PairedAssumptions.vo check/PairedAssumptions.v > build/paired_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/LatentSignAssumptions.vo check/LatentSignAssumptions.v > build/latent_sign_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/CountableAssumptions.vo check/CountableAssumptions.v > build/countable_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionAssumptions.vo check/ConditionAssumptions.v > build/condition_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/LatentScopeAssumptions.vo check/LatentScopeAssumptions.v > build/latent_scope_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/RobustAssumptions.vo check/RobustAssumptions.v > build/robust_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/LatentTensorAssumptions.vo check/LatentTensorAssumptions.v > build/latent_tensor_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ContinuousLatentAssumptions.vo check/ContinuousLatentAssumptions.v > build/continuous_latent_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionEndpointsAssumptions.vo check/ConditionEndpointsAssumptions.v > build/condition_endpoints_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionRobustAssumptions.vo check/ConditionRobustAssumptions.v > build/condition_robust_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/LatentTensorUpperAssumptions.vo check/LatentTensorUpperAssumptions.v > build/latent_tensor_upper_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionKappaCurveAssumptions.vo check/ConditionKappaCurveAssumptions.v > build/condition_kappa_curve_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionKappaAssumptions.vo check/ConditionKappaAssumptions.v > build/condition_kappa_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q theories EllipsoidFitting -Q extension EllipsoidUniversality -o build/ConditionKappaRobustAssumptions.vo check/ConditionKappaRobustAssumptions.v > build/condition_kappa_robust_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/MatrixSeriesAssumptions.vo check/MatrixSeriesAssumptions.v > build/matrix_series_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/TensorPackingAssumptions.vo check/TensorPackingAssumptions.v > build/tensor_packing_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/GoeEdgeAssumptions.vo check/GoeEdgeAssumptions.v > build/goe_edge_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/SKGapAssumptions.vo check/SKGapAssumptions.v > build/sk_gap_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/PsdSplittingAssumptions.vo check/PsdSplittingAssumptions.v > build/psd_splitting_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/PerceptronSignAssumptions.vo check/PerceptronSignAssumptions.v > build/perceptron_sign_assumptions.txt
	$(EXEC) rocq compile -noglob -Q library GaussianAnalysis -Q applications GaussianApplications -o build/SatVarianceAssumptions.vo check/SatVarianceAssumptions.v > build/sat_variance_assumptions.txt
	python3 scripts/check_sources.py $(REPORTS)
	$(if $(filter yes,$(CITATIONS)),$(EXEC) python3 scripts/stale_citations.py,@true)
	@echo "make check passed."

citations: Makefile.rocq
	$(EXEC) python3 scripts/stale_citations.py

clean:
	if [ -f Makefile.rocq ]; then $(EXEC) $(MAKE) -f Makefile.rocq clean; fi
	rm -rf build Makefile.rocq Makefile.rocq.conf
