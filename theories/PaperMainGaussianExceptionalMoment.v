(* Quantitative expectation loss on a measurable exceptional event, using
   the actual Gaussian law and its proved second moments. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import numfun.
From EllipsoidFitting Require Import AnalysisBridge GaussianCoordinateDefinitions
  GaussianProductDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainGordonLipschitz
  PaperMainGaussianLipschitzApproximationLaw PaperMainGaussianLipschitzVariance.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_exceptional_young x a :
  0 < a -> x <= / (4*a) * (x*x) + a.
Proof.
intros Ha; apply (Rmult_le_reg_r (4*a)); [lra|].
replace ((/(4*a)*(x*x)+a)*(4*a)) with (x*x+4*a*a) by (field; lra).
pose proof (pow2_ge_0 (x-2*a)); nra.
Qed.
