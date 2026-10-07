(* The threshold alpha*(kappa) and the cutoffs of Koehler and Sohn (arXiv
   2608.27372, lines 343-404 and section 5.3, lines 5115-5400 of
   arxiv_v1.tex), over the frozen definitions of UniversalityDefinitions.

   The semicircle law nu of density sqrt (2 - x^2)/pi is semicircle_prob
   (sqrt 2) of the library (probability/semicircle_law.v), and the functions
   m, s and E_kappa of the frozen definitions are the upper partial moments
   and the energy of the library's scalar variational problem
   (probability/variational.v) at c = c_kappa = (kappa - 3)/2. This file
   transports the library's results to the frozen definitions and adds what
   is specific to nu.

   Main results to prove (stage 1 of phase 5; names come with the proofs),
   for kappa > 1:
   - universality_semicircle_integral f is the integral of f against
     semicircle_prob (sqrt 2) whenever f times the density is integrable or
     f is nonnegative and measurable; hence universality_m, universality_s
     and universality_energy kappa are upper_moment nu 1, upper_moment nu 2
     and upper_energy nu c_kappa.
   - The semicircle facts: nu has mass one and second moment 1/2;
     m(-w) = m(w) + w and s(-w) + s(w) = 1/2 + w^2 (lines 5281-5283);
     m(w) > 0 for w < sqrt 2 and m(w) = s(w) = 0 for w >= sqrt 2; for
     w <= -sqrt 2, m(w) = -w, s(w) = w^2 + 1/2 and
     E_kappa(w) = (kappa - 1)/2 w^2 + 1/2 (lines 5384-5391).
   - The paper's unique solution (lines 373-376): omega_kappa =
     universality_cutoff kappa lies in [-sqrt 2, sqrt 2], satisfies
     omega_kappa = c_kappa m(omega_kappa), and is the only real number that
     does.
   - Proposition 5.10 (i) (lines 401-404): E_kappa is strictly decreasing on
     ]-oo, sqrt 2]; for alpha > 0, omega_{alpha,kappa} =
     universality_level_cutoff alpha kappa is < sqrt 2, satisfies
     E_kappa(omega_{alpha,kappa}) = alpha, and is the only w < sqrt 2 that
     does.
   - Proposition 5.10: for chi_kappa(z) = upper_value nu c_kappa z,
     z |-> chi_kappa(z) is nondecreasing and strictly increasing where it is
     positive; with z_{alpha,kappa} = c_kappa m(omega_{alpha,kappa}) -
     omega_{alpha,kappa}, chi_kappa(z_{alpha,kappa}) = alpha, and
     z_{alpha,kappa} > 0 if and only if alpha > alpha*(kappa).
   - Proposition 5.10 (ii): universality_alpha_star_variational kappa =
     universality_alpha_star kappa = chi_kappa(0): the two definitions of
     alpha*(kappa) agree.
   - Lemma 5.9, the scalar part: with kappa^vee = kappa_dual kappa and
     z^vee = -2 z/(kappa - 1), the cutoff of (kappa^vee, z^vee) is minus that
     of (kappa, z), and chi_kappa(z) + chi_{kappa^vee}(z^vee) =
     1/2 + 2 z^2/(kappa - 1). The claim of Lemma 5.9 that
     -G_{d,kappa}(z) and G_{d,kappa^vee}(z^vee) have the same law is about
     the Gaussian matrices of section 5.2 and goes with them (stage 2, G8).
   - Proposition 5.10 (iii): 0 <= alpha*(kappa) <= 1/2 and
     alpha*(kappa) + alpha*(kappa^vee) = 1/2.
   - Proposition 5.10 (i), line 188: for alpha > 0, e*(alpha, kappa) > 0 if
     and only if alpha > alpha*(kappa).
   - Line 377 and Corollary 1.3: universality_alpha_star 3 = 1/4, from
     omega_3 = 0 and s(0) = (1/2) int x^2 dnu = 1/4.

   Definitions:
     threshold_law            == semicircle_prob (sqrt 2), the law nu
   and, once nu is a probability: omega_{kappa,z}, the solution of
   w + z = c_kappa m(w) (eq:shifted-omega-eqn), and chi_kappa(z) =
   E_kappa(omega_{kappa,z}). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences trigo.
From GaussianAnalysis.probability Require Import semicircle_law variational.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition threshold_law : set (measurableTypeR R) -> \bar R :=
  semicircle_prob (Num.sqrt 2%:R).
