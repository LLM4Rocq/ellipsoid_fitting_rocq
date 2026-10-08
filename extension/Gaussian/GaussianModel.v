(* Proposition 1.4 of Koehler and Sohn (arXiv 2608.27372, lines 322-345 of
   arxiv_v1.tex), the Gaussian model, at Stdlib's R: the stage theorem
   universality_gaussian_model of stage 2 of phase 5.

   Let kappa > 1 and n / d^2 -> alpha > 0, and let Z = (G_1, ..., G_n) be
   n independent Gaussian features of law gaussian_feature_law kappa d
   (Features/Definitions). The paper's optimal squared fitting error
   Gamma_{G,kappa} is 2 unsat_value n d Z (Unsat/LeastSquares), and its
   map A_{G,kappa} is S |-> P_(1^perp) (<G_i, S>)_i.
   - (i) If alpha < alpha*(kappa), there are 0 < m0 <= M0 such that with
     probability tending to one some symmetric S with m0 I <= S <= M0 I and
     tr S = d satisfies <G_i, S> = 0 for every i, hence A_{G,kappa} S = 0:
     gaussian_fit_below_threshold (Gaussian/Subcritical, Lemma 5.17,
     item G9).
   - (ii) Gamma_{G,kappa} tends to e*(alpha, kappa) in probability
     (gaussian_fitting_error_limit of Gaussian/FittingError, item G8), and
     if alpha > alpha*(kappa), then e*(alpha, kappa) > 0 and
     Gamma_{G,kappa} > e*(alpha, kappa) / 2 with probability tending to one
     (gaussian_fitting_error_gap).
   "With probability tending to one" is written as in these inputs: for
   every eps > 0 and every large d, the property holds outside a measurable
   event of probability at most eps. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis Require Import euclidean measurable_matrix lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Threshold InProbability.
From EllipsoidUniversality.Gaussian Require Import FittingError Subcritical.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* Proposition 1.4: (i) below the threshold, (ii) the limit of the fitting
   error, and its positivity above the threshold. *)
Theorem universality_gaussian_model (kappa alpha : R) :
  1 < kappa -> 0 < alpha ->
  [/\ alpha < universality_alpha_star kappa ->
      exists m0 M0 : R, [/\ 0 < m0, m0 <= M0 &
      forall n : nat -> nat, universality_density_tends_to n alpha ->
      forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
      exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
        (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
        forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
          forall v : 'rV[R]_d,
            m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
          \tr S = d%:R &
          forall i, mxdot (tnth Z i) (mxvec S) = 0]]],
    forall n : nat -> nat, universality_density_tends_to n alpha ->
    forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
    exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
      (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
      forall Z, ~ E Z ->
        `|2 * unsat_value (n d) d Z - universality_e_star alpha kappa| <= eps]
    & universality_alpha_star kappa < alpha ->
      0 < universality_e_star alpha kappa /\
      forall n : nat -> nat, universality_density_tends_to n alpha ->
      forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
      exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
        (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
        forall Z, ~ E Z ->
          universality_e_star alpha kappa / 2 < 2 * unsat_value (n d) d Z]].
Proof.
move=> k1 a0; split.
- by move=> ha; exact: gaussian_fit_below_threshold.
- move=> n hn eps e0.
  have [D hD] := gaussian_fitting_error_limit alpha kappa a0 k1 n hn eps e0.
  exists D => d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split => // Z nEZ; rewrite leNgt; apply/negP => h.
  exact: nEZ (hE Z h).
- move=> ha; split; first by rewrite universality_e_star_gt0.
  move=> n hn eps e0.
  have [_ hneg] := gaussian_fitting_error_gap alpha kappa n a0 k1 hn ha.
  have [D hD] := hneg eps e0.
  exists D => d dD; have [E [mE PE hE]] := hD d dD.
  exists E; split => // Z nEZ; rewrite ltNge; apply/negP => h.
  exact: nEZ (hE Z h).
Qed.
