(* Theorem 1.2 (i) of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 164-190, proof lines
   976-991), at Stdlib's R: below the threshold, with probability tending
   to one, the points have a positive definite fit of value 1 with a
   condition number bounded by a constant. Item S11 of stage 3 of phase 5
   (lane A).

   Hypothesis. small_residual_interpolation kappa K alpha is Theorem 1.9
   (Sat/Interpolation, item S10 of lane C) in the form that
   requests/a-to-c.md asks for: with probability tending to one, every y
   in R^n with |y_i| <= Y for every i is <W_i, Delta> = y_i + b for some
   symmetric Delta with opnorm Delta <= C1 ((ln d)^4 / sqrt d Y + |y| / d)
   and some real b, where W_i = sample_W x i = (x_i x_i^T - I) / sqrt d.
   This is interpolation_det of Sat/Interpolation on the event of Theorem
   2.3, with a = c sqrt d / (ln d)^4 and D = d.

   Plan (names come with the proofs).
   - The first conjunct of universality_statement from
     small_residual_interpolation. Let
     0 < m < 1 < M and C be the constants of approximate_fit (S1), and
     c = 4 M / m. Take delta with C1 sqrt (2 alpha delta) <= m / 4. On the
     intersection of the event of approximate_fit, the event of Theorem
     1.9 and the event that some point x_i is not zero, the residual
     y_i = b - <W_i, R> of the approximate fit R has |y_i| <= C ln d and
     |y| <= sqrt (delta n), so Theorem 1.9 gives Delta with
     opnorm Delta <= m / 2 for d large. Then S = R + Delta has all
     <W_i, S> equal and m / 2 I <= S <= (M + m / 2) I, so
     x_i^T S x_i = sqrt d <W_i, S> + tr S is a common value t, with
     t >= m / 2 |x_i|^2 > 0 for a point x_i != 0, and S / t is a fit of
     value 1 with lm = m / (2 t) and lm I <= S / t <= c lm I. The
     conditioned event is contained in the positive definite one.
   - All the points vanish with probability at most
     (1 - 1 / (4 kappa))^n: P(x_(i,0) != 0) >= 1 / (4 kappa) by
     Paley-Zygmund (paley_zygmund_sqr of probability/moments.v), and the
     coordinates x_(i,0) are independent (tuple_prod_box of
     probability/conditioning.v).
   - The events are measurable: measurable_pd_fit_event and
     measurable_conditioned_fit_event of Model/Measurability (U11).
   - The same without hypothesis, once Theorem 1.9 (lane C) proves
     small_residual_interpolation. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* Theorem 1.9 in the form that the assembly of Theorem 1.2 (i) takes as
   its hypothesis. *)
Definition small_residual_interpolation (kappa K alpha : R) : Prop :=
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
