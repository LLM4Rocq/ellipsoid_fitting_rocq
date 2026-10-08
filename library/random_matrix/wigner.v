From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals ereal.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.

(**md**************************************************************************)
(* # Wigner's semicircle law for the GOE                                      *)
(*                                                                            *)
(* Let W = goe_mx a for a of law gauss (d * d) (random_matrix/goe.v). The     *)
(* empirical law of its eigenvalues spec W (matrix/von_neumann.v) converges   *)
(* in probability to the semicircle law of radius 2. This is the form of the  *)
(* semicircle law that Lemma 5.14 of Koehler and Sohn (arXiv 2608.27372, line *)
(* 5905) cites from Anderson, Guionnet and Zeitouni. This file completes item *)
(* G7 of phase 5.                                                             *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - Weierstrass's approximation theorem on a compact interval, by Bernstein  *)
(*   polynomials (not in MathComp-Analysis 1.16).                             *)
(* - wigner: for every continuous f and eps > 0, the probability that |(1 /   *)
(*   d) \sum_i f (spec W i) - \int f d(semicircle_prob 2)| > eps tends to 0   *)
(*   as d tends to infinity: for polynomials from the moments and the         *)
(*   variance bound of goe.v and Chebyshev's inequality, then on the event    *)
(*   opnorm W < 3 by uniform approximation.                                   *)
(* - The same uniformly over a family f_t, t in a compact interval, with |f_t *)
(*   x - f_s x| <= L |t - s| for all x, as Lemma 5.14 needs for the functions *)
(*   (x - t)_+ and (x - t)_+^2.                                               *)
(* - In particular (1 / d) \tr (W^2) tends to 1 in probability.               *)
(******************************************************************************)
