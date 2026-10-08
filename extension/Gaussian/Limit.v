(* The Gaussian model: Lemma 5.14, Proposition 5.15 (the shifted
   cone-projection limit), Lemma 5.16 and Proposition 1.4 (ii) of Koehler and
   Sohn (arXiv 2608.27372, lines 5880-6220 of arxiv_v1.tex), at Stdlib's R.
   Item G8 of stage 2 of phase 5 (lane C), with library/matrix/psd_part.v.

   Plan (names come with the proofs). For kappa > 1, alpha > 0 and n with
   n / d^2 -> alpha:
   - Lemma 5.14 (kappa >= 3): the value V_d of the shifted GOE against the
     cone reduces, by von Neumann's trace inequality (matrix/von_neumann.v,
     lane A), to the eigenvalues g_i = spec G_d i / sqrt d, then to the
     scalar problem of library/probability/variational.v (G5) for their
     empirical law; the optimizer is psd_part (G_d - sqrt d omega_d I).
   - Proposition 5.15: d^(-2) |proj_{S^d_kappa} (G_d + zeta sqrt (2 d /
     (kappa - 1)) I)|_F^2 -> chi_kappa (zeta) in probability; for
     kappa >= 3 from Lemma 5.14, Wigner's law (random_matrix/wigner.v) and
     Lemma 5.13 (random_matrix/goe_rotation.v); for 1 < kappa < 3 by
     Moreau's decomposition (library/convex/moreau.v), the polar cone of
     S^d_kappa (kappa_cone_polar of Gaussian/Cones) and the scalar shifted
     duality of G5 (Gaussian/Threshold).
   - Lemma 5.16: phihat_d -> zeta_{alpha,kappa} and Phi_d ->
     (zeta_{alpha,kappa})_+ in probability, from Lemma 5.6
     (Gaussian/Representation), |g| / d -> sqrt alpha, and the CGMT in mean
     and concentration form (G3, lane B).
   - Proposition 1.4 (ii), the form that Unsat/Universality (U10, lane A)
     uses: for Z of law tuple_prod (fun=> gaussian_feature_law kappa d)
     (n d) and every eps > 0, the probabilities of
     [set Z | eps < `|2 * unsat_value (n d) d Z - universality_e_star alpha kappa|]
     tend to 0 (paper_main_tends_to). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
