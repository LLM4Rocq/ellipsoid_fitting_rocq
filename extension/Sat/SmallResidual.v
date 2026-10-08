(* Theorem 1.9 of Koehler and Sohn (arXiv 2608.27372, lines 549-566 of
   arxiv_v1.tex), the small-residual interpolation, without hypothesis, at
   Stdlib's R. Item S10 of stage 3 of phase 5 (lane C).

   Proved here.
   - small_residual_interpolation_unconditional: for 1 < kappa,
     0 < alpha < 1/2 and coordinate laws as universality_coordinate_law
     kappa K, the conclusion of small_residual_interpolation_limit
     (Sat/Interpolation), with Proposition 3.4 given by
     light_tail_quotient (Sat/LightTailBound, lane B).
   - small_residual_interpolation_holds: the hypothesis
     small_residual_interpolation kappa K alpha of
     universality_statement_of_interpolation (Sat/Universality, lane A)
     for 1 < kappa and 0 < alpha < alpha*(kappa), since
     alpha*(kappa) < 1/2 (universality_alpha_star_lt of
     Gaussian/Threshold). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals Rstruct.
From mathcomp Require Import exp.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Sat Require Import Apriori Interpolation.
From EllipsoidUniversality.Sat Require Import LightTailBound Universality.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* Theorem 1.9: with probability tending to one, every residual y is
   matched up to a shift, <W_i, Delta> = y_i + b for every i, by a
   symmetric Delta with
   opnorm Delta <= C1 ((ln d)^4 / sqrt d max_i |y_i| + |y| / d). *)
Theorem small_residual_interpolation_unconditional (kappa K alpha : R) :
  1 < kappa -> 0 < alpha -> alpha < 2^-1 ->
  exists C1 : R, 0 < C1 /\
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_probability (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (y : 'rV[R]_(n d)) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y +
                frobenius y / d%:R)]].
Proof.
move=> k1 a0 ah.
exact: (small_residual_interpolation_limit kappa K alpha a0
  (light_tail_quotient kappa K alpha k1 a0 ah)).
Qed.

(* The hypothesis of universality_statement_of_interpolation. *)
Theorem small_residual_interpolation_holds (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  small_residual_interpolation kappa K alpha.
Proof.
move=> k1 _ a0 ha.
have /andP[_ h] := universality_alpha_star_lt _ k1.
exact: (small_residual_interpolation_unconditional kappa K alpha k1 a0
  (lt_trans ha h)).
Qed.
