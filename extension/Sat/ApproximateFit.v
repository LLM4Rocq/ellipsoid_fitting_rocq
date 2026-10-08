(* The approximate fit: Proposition 2.1 of Koehler and Sohn, "Universality
   and sharp thresholds for ellipsoid fitting" (arXiv 2608.27372, lines
   725-740, proof lines 4443-4596), at Stdlib's R. Item S1 of stage 3 of
   phase 5 (lane A).

   Setting. kappa > 1, K > 0, alpha > 0 and n d / d^2 -> alpha
   (universality_density_tends_to); for every d the coordinate laws
   nu d j (j < d) are universality_coordinate_law kappa K. The features of
   a sample x are W_i = (x_i x_i^T - I) / sqrt d, given as the rows
   mxvec W_i of unsat_features n d x (Unsat/LeastSquares), of law
   tuple_prod (fun=> data_feature_law (nu d) d) n.

   Hypothesis. gaussian_subcritical_fit kappa alpha is Proposition 1.4 (i)
   (Lemma 5.17, item G9 of lane B, Gaussian/Subcritical) in the form that
   requests/a-to-b.md asks for: there are 0 < m0 <= M0 such that, with
   probability tending to one under the Gaussian features of law
   gaussian_feature_law kappa d, some symmetric S has m0 I <= S <= M0 I,
   tr S = d and <G_i, S> = 0 for every i.

   Planned result (names come with the proofs):
   - approximate_fit: under gaussian_subcritical_fit kappa alpha, there are
     0 < m < 1 < M and C > 0, depending only on alpha, kappa and K, such
     that with probability tending to one some S with mxvec S in
     pd_slice2 d m M (m I < S < M I and tr S = d) and some real b satisfy
       sum_i (<W_i, S> - b)^2 <= C n / ln d   and
       |<W_i, S> - b| <= C ln d for every i.
     The paper's rates are (ln d / d)^(1/10) and (ln d)^2; any rates o(1)
     and o(sqrt d / (ln d)^4) suit Theorem 1.9 (Sat/Interpolation, lane C).

   Route (the paper's, with the barrier kept).
   1. Theorem 2.9 (barrier_lindeberg_concentration of
      convex/barrier_lindeberg.v) on the domain pd_slice2 d m M, with
      m = m0 / 2, M = 2 M0 and its 2d-self-concordant barrier
      logdet_barrier2 (Lemma 2.8, convex/logdet_barrier.v), and with
      beta = 1 / ln d and gamma = 1 / (d ln d), for the data features and
      for the Gaussian ones (both regular: uni_regular_data and
      uni_regular_gauss of Unsat/Universality). Both values Phi_W and Phi_G
      are within O(1 / ln d) of E Phi_G with probability tending to one.
   2. The Gaussian witness S of the hypothesis is in the domain, with
      b = 0: Phi_G <= beta lambda |S|_F^2 + gamma B(S) = O(1 / ln d).
      Hence E Phi_G and then Phi_W are O(1 / ln d) = O(beta).
   3. A minimizer (S, b) of the full objective (ls_barrier_minimizer of
      convex/minimizers.v) has sum_i (<W_i, S> - b)^2 <= 2 n Phi_W.
   4. The leave-one-out minimizers (S^(i), b^(i)) are measurable functions
      of the other rows (to prove in the library: the limit of the first
      minimizers over a countable dense subset of the domain), with
      beta (b^(i))^2 <= Phi_W, so |b^(i)| = O(1), and
      |<W_i, S> - b| <= |<W_i, S^(i)> - b^(i)| (add the two optimality
      inequalities). Given the other rows, <W_i, S^(i)> is subexponential
      with constant 252 K^2 M (Hanson-Wright, data_feature_subexponential
      of Features/Regular, as |S^(i)|_F <= M sqrt d), so a union bound over
      the n rows gives max_i |<W_i, S> - b| = O(ln d). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* Proposition 1.4 (i) for the Gaussian features, in the form that
   approximate_fit takes as its hypothesis. *)
Definition gaussian_subcritical_fit (kappa alpha : R) : Prop :=
  exists m0 M0 : R, [/\ 0 < m0, m0 <= M0 &
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
      forall v : 'rV[R]_d,
        m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
      \tr S = d%:R &
      forall i, mxdot (tnth Z i) (mxvec S) = 0]]].
