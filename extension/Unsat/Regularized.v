(* Corollary 2.13 of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 1499-1601), at Stdlib's
   R: the universality of the ridge-regularized and of the unregularized
   least squares values on R_d^o = {R > 0, Tr R = d} (and, for (i), on the
   two-sided domain {m I < R < M I, Tr R = d}), for two sequences of laws
   of features with the same covariance Sigma_kappa.

   Setting. kappa > 1, K > 0, alpha > 0, n d / d^2 -> alpha
   (universality_density_tends_to). For every d, mu d and nu d are laws on
   'rV[R]_(d * d) that are (K, tau d)-regular features (regular_feature)
   with covariance unsat_cov kappa d (LeastSquares.v); W and G have laws
   tuple_prod (fun=> mu d) (n d) and tuple_prod (fun=> nu d) (n d). In the
   paper, mu d is the law of the quadratic feature of a point with
   independent coordinates (regular by Proposition 2.6, lane A) and nu d
   the Gaussian feature with the same covariance (regular by (2.10),
   convex/barrier_lindeberg.v); both are regular with tau d = O(d^(-1/2)).

   Planned results (stage 1 of phase 5):
   - Corollary 2.13 (i): there is C such that for every sequence
     0 < beta d <= 1 there are reals c d with
     P(|Phi_Z(D_d; beta d) - c d| > C (1 + 1 / beta d)^2 q d) -> 0 for
     Z = W and for Z = G, where q d = tau d + (ln d / d)^(1/3) and
     (D_d, B_d) is (R_d^o, -ln det) or the two-sided domain and barrier.
     The proof takes the reference point (I, 0), gamma = d^(-4/3)
     (ln d)^(-2/3) and eps = 1 / n in Lemma 2.11
     (convex/barrier_removal.v), and Theorem 2.9
     (convex/barrier_lindeberg.v) with c d = E Phi_G(D_d, B_d; beta d,
     gamma).
   - Corollary 2.13 (ii): if moreover tau d <= C0 (ln d)^-3 for large d,
     there are reals c d such that for every eps > 0,
     P(|unsat_value Z - c d| > eps) -> 0 for Z = W and for Z = G. The
     proof takes beta d = (q d / ln d)^(1/3) in (i) and removes the ridge
     with Lemma 2.12 (extension/Unsat/Ridge.v, lane C).
   With the identity Gamma_X = 2 unsat_value (unsat_features x)
   (LeastSquares.v), (ii) says that Gamma_X and the Gaussian Gamma_G
   converge in probability to the same deterministic sequence, which is
   what the proofs of Theorem 1.7 and Theorem 1.2 (ii) use
   (lines 1602-1635). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis Require Import euclidean opnorm lindeberg least_squares.
From GaussianAnalysis Require Import logdet_barrier.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions LeastSquares.

Local Open Scope ring_scope.
