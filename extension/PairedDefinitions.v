(* The glossary of the paired law: points of R^d whose coordinates come in
   independent pairs (2k, 2k + 1) with the Sarmanov density
   (1 + eps h(x) h(y)) / 12 on [-sqrt 3, sqrt 3]^2, h the rescaled Legendre
   polynomial P_4 (notes/paired-dependent-sat.md, (1); its exact fitting is
   a corollary of the finite-mixture theorem, notes/mixture-product-universality.md,
   section 5; the plan notes/paired-law-plan-v2.md, section 4.1). Every
   definition is concrete and is meant to be read by the reviewer; the
   comment of PairedStatement reads the statement.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope, as in PaperMainDefinitions. lebesgue_measure is Lebesgue
   measure on the line; universality_sample_law (fun=> mu) n d is the law
   of n * d independent coordinates of law mu (UniversalityDefinitions).

   1. The uniform law on [-sqrt 3, sqrt 3]: a law mu on the line that gives
      every Borel set A the measure int_A 1_{|x| <= sqrt 3} / (2 sqrt 3) dx.
      It is characterized rather than constructed, and the statement
      quantifies over such mu; uniform_prob of MathComp-Analysis is one.
   2. h(x) = P_4(x / sqrt 3), with P_4(t) = (35 t^4 - 30 t^2 + 3) / 8; on
      [-sqrt 3, sqrt 3], h takes its values in [-3/7, 1].
   3. The density of a pair against the product of two uniform laws,
      1 + eps h(x) h(y); it is nonnegative on the support exactly when
      -1 <= eps <= 7/3. The density of a sample of n points of R^d against
      the product of the n * d uniform laws is the product, over the points
      i and the pairs k < d / 2, of the pair density at the coordinates
      2k and 2k + 1 of point i; the last coordinate of an odd d has no
      factor, so it is uniform and independent of the others. Coordinate j
      of point i is coordinate i * d + j of the tuple, as in
      paper_main_point. The density is written without the indicator of
      the support: the reference law puts no mass outside it.
   4. paired_probability eps mu n d E is the probability of a set E of
      samples under the paired law: the integral over E of the sample
      density against the product of the uniform laws.

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. The uniform law on [-sqrt 3, sqrt 3], by its density against
   Lebesgue measure. *)
Definition paired_uniform_spec (mu : probability (measurableTypeR R) R) : Prop :=
  forall A : set (measurableTypeR R), measurable A ->
    mu A = (\int[lebesgue_measure]_(x in A)
              (if `|(x : R)| <= Num.sqrt 3%:R
               then (2%:R * Num.sqrt 3%:R)^-1 else 0)%:E)%E.

(* 2. h(x) = P_4(x / sqrt 3), P_4(t) = (35 t^4 - 30 t^2 + 3) / 8. *)
Definition paired_kernel (x : R) : R :=
  (35%:R * (x / Num.sqrt 3%:R) ^+ 4 - 30%:R * (x / Num.sqrt 3%:R) ^+ 2 + 3%:R)
  / 8%:R.

(* 3. The density of a pair, 1 + eps h(x) h(y), against the product of two
   uniform laws. *)
Definition paired_pair_density (eps x y : R) : R :=
  (1 + eps * paired_kernel x * paired_kernel y)%R.

(* The density of a sample of n points of R^d against the product of the
   n * d uniform laws: one factor for each point i < n and each pair of
   coordinates (2k, 2k + 1), k < d / 2. *)
Definition paired_sample_density (eps : R) (n d : nat)
    (x : paper_main_sample n d) : R :=
  \prod_(i < n) \prod_(k < d./2)
    paired_pair_density eps (List.nth (i * d + 2 * k)%nat (tval x) 0)
                            (List.nth (i * d + 2 * k + 1)%nat (tval x) 0).

(* 4. The probability of a set E of samples under the paired law. An
   extended real; it is in [0, 1] for a measurable E when
   -1 <= eps <= 7/3 and mu is the uniform law. *)
Definition paired_probability (eps : R) (mu : probability (measurableTypeR R) R)
    (n d : nat) (E : set (paper_main_sample n d)) : \bar R :=
  (\int[universality_sample_law (fun=> mu) n d]_(x in E)
     (paired_sample_density eps n d x)%:E)%E.
