(* The Gaussian feature model as an i.i.d. Gaussian matrix acting on the cone
   S^d_kappa: Lemmas 5.4 to 5.6 of Koehler and Sohn (arXiv 2608.27372,
   lines 4992-5076 of arxiv_v1.tex), at Stdlib's R. Item G4 of stage 2 of
   phase 5 (lane C).

   Plan (names come with the proofs). For kappa > 1, let a_1, ..., a_n be
   independent of law gauss (d * d), Z_i = mxvec (gaussian_feature kappa
   (vec_mx a_i)) the Gaussian features (law gaussian_feature_law kappa d)
   and M the n x (d * d) matrix of rows a_i.
   - The identity behind Lemma 5.4: for R symmetric,
     <Z_i, mxvec R> = <a_i, mxvec (sqrt (2/d) T_kappa R)>
     (gaussian_feature_pairing of Gaussian/Cones), so the vector
     (<Z_i, mxvec R>)_i is sqrt (2/d) M mxvec (T_kappa R) exactly. No
     identification of S^d with R^(d (d + 1)/2) is needed: the Gaussian
     matrix acts on mxvec of symmetric matrices, and for Y symmetric
     <H, Y> = <(H + H^T)/2, Y>, which turns h of law gauss (d * d) into the
     paper's GOE matrix G_d.
   - The least squares value: 2 unsat_value n d Z is (1/n) times the
     infimum over R in R_d = {R >= 0, Tr R = d} of
     |P_{1^perp} (<Z_i, mxvec R>)_i|^2; the infimum over the closed slice
     equals the one over the open slice unsat_domain d (continuity). Hence
     2 unsat_value n d Z = (2 / (n d)) inf_{R in R_d} |P_{1^perp} M mxvec (T_kappa R)|^2.
   - Lemma 5.4 in law: for Q an n x (n - 1) matrix whose columns are an
     orthonormal basis of 1^perp, |P_{1^perp} v| = |Q^T v|, and Q^T M has
     the law of gauss ((n - 1) * (d * d)) read as a matrix (gauss_mulmx_law
     of comparison/gauss_law.v). Hence 2 unsat_value has the law of
     (2 d^2 / n) Phi_d^2 with Phi_d = d^(-3/2) inf_{R in R_d}
     |A mxvec (T_kappa R)| and A an (n - 1) x (d * d) standard Gaussian
     matrix.
   - Lemma 5.5 in the mean and concentration form of lane B's cgmt.v
     (requests/b-to-c.md): K = {mxvec (T_kappa R) | R in R_d} is a nonempty
     compact convex set of radius at most max (1, sqrt ((kappa - 1)/2)) d,
     so after the normalization by d^(3/2) the means of Phi_d and of
     (phihat_d)_+ differ by O(d^(-1/2)) and both concentrate at that
     scale, where phihat_d = d^(-3/2) inf_{R in R_d}
     (|g| |T_kappa R|_F - <G_d, T_kappa R>).
   - Lemma 5.6: phihat_d = sup {zeta | |proj_{S^d_kappa} (G_d +
     zeta sqrt (2 d / (kappa - 1)) I)|_F <= |g|}, by positive homogeneity,
     Tr R = sqrt (2 / (kappa - 1)) <I, T_kappa R> and cone_proj_support of
     library/convex/moreau.v for the closed convex cone mxvec S^d_kappa
     (kappa_cone_closed of Gaussian/Cones). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
