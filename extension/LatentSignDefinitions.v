(* The glossary of the latent-sign law: points of R^d whose coordinates are
   coupled by one hidden sign. Given the sign, the d coordinates of a point
   are independent, all with law lam_s = (1 + s h) mu or all with law
   lam_(-s) = (1 - s h) mu, each sign with probability 1/2: the law of a
   point is (1/2) lam_s^(x) d + (1/2) lam_(-s)^(x) d. Here mu is the
   uniform law on [-sqrt 3, sqrt 3] and h the rescaled Legendre polynomial
   P_4 of PairedDefinitions. Its exact fitting is the third corollary of
   the finite-mixture theorem (MixtureStatement), with two components
   (the review of the phase 6 release; AGENTS.md, section "Phase 7", item
   3). Every definition is concrete and is meant to be read by the
   reviewer; the comment of LatentSignStatement reads the statement.

   Vocabulary. As in PairedDefinitions: Stdlib's R is the real field, read
   through MathComp's ring_scope; universality_sample_law (fun=> mu) n d is
   the law of n * d independent coordinates of law mu
   (UniversalityDefinitions); paired_uniform_spec mu says that mu is the
   uniform law on [-sqrt 3, sqrt 3], and paired_kernel is
   h(x) = P_4(x / sqrt 3), with values in [-3/7, 1] on [-sqrt 3, sqrt 3]
   (PairedDefinitions).

   1. The density of a sample of n points of R^d against the product of
      the n * d uniform laws: the product, over the points i, of
        (prod_j (1 + s h(x_(i,j))) + prod_j (1 - s h(x_(i,j)))) / 2,
      where x_(i,j), for j < d, is coordinate j of point i, coordinate
      i * d + j of the tuple, as in paper_main_point. For 0 <= s <= 1
      both products are nonnegative on the support, since -3/7 <= h <= 1.
      The density is written without the indicator of the support: the
      reference law puts no mass outside it.
   2. latent_probability s mu n d E is the probability of a set E of
      samples under the latent-sign law: the integral over E of the sample
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
From EllipsoidUniversality Require Import PairedDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. The density of a sample of n points of R^d against the product of
   the n * d uniform laws: for each point, the average of the products of
   1 + s h and of 1 - s h at its d coordinates. *)
Definition latent_sample_density (s : R) (n d : nat)
    (x : paper_main_sample n d) : R :=
  (\prod_(i < n)
     ((\prod_(j < d)
         (1 + s * paired_kernel (List.nth (i * d + j)%nat (tval x) 0)) +
       \prod_(j < d)
         (1 - s * paired_kernel (List.nth (i * d + j)%nat (tval x) 0)))
      / 2%:R))%R.

(* 2. The probability of a set E of samples under the latent-sign law. An
   extended real; it is in [0, 1] for a measurable E when 0 <= s <= 1 and
   mu is the uniform law. *)
Definition latent_probability (s : R) (mu : probability (measurableTypeR R) R)
    (n d : nat) (E : set (paper_main_sample n d)) : \bar R :=
  (\int[universality_sample_law (fun=> mu) n d]_(x in E)
     (latent_sample_density s n d x)%:E)%E.
