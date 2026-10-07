(* Removing the ridge: Lemma 2.12 of Koehler and Sohn (arXiv 2608.27372,
   lines 1476-1494 of arxiv_v1.tex, proof lines 4598-4833), in the
   vocabulary of lane B (library/convex/least_squares.v and
   Unsat/LeastSquares.v): features are row vectors of size d * d, the
   objective is ls_objective, the values are unsat_ridge_value and
   unsat_value, the domain is unsat_domain d = R_d^o, the positive definite
   matrices of trace d, and the ridge weight is unsat_lambda kappa d =
   opnorm (unsat_cov kappa d) = max (2, kappa - 1) / d.

   Main results to prove (stage 1 of phase 5; names come with the proofs).
   The constants depend only on kappa, K, L0 and alpha.
   - The covariance on symmetric matrices: theta (unsat_cov kappa d)
     theta^T is feature_cov kappa (vec_mx theta) (vec_mx theta) for
     vec_mx theta symmetric, which is at least min (2, kappa - 1) / d
     |theta|^2; opnorm (unsat_cov kappa d) <= max (2, kappa - 1) / d.
   - Lemma 4.3: for independent features Z_1, ..., Z_n with a law whose
     quadratic forms z |-> <z, mxvec (v^T v)> (|v| <= 1) are centered and
     subexponential with constant L0 / sqrt d, and every sign vector s,
       E sup over theta in R_d of |<sum_i s_i Z_i, theta>| / n
         <= C L0 (d / sqrt n + d sqrt d / n),
     which is bounded when n / d^2 -> alpha > 0; the paper has an extra
     sqrt (log d) from the matrix Bernstein inequality. Proof:
     matrix/random_opnorm.v, since <A, theta> <= tr theta opnorm (sym A)
     for theta positive semidefinite.
   - Localization, deterministic: if every theta in R_d and b with
     C_kappa(theta, theta) + b^2 >= s^2 satisfy
     (1/n) sum_i (<Z_i, theta> - b)^2 >= c (C_kappa(theta, theta) + b^2),
     and (1/n) sum_i <Z_i, I>^2 <= B with 2 B + 2 < c s^2, then for every
     beta >= 0,
       0 <= unsat_ridge_value kappa n d beta Z - unsat_value n d Z
         <= beta (max (2, kappa - 1) / min (2, kappa - 1) + 1) s^2.
     Near-minimizers are used, so no minimizer, compactness or density
     argument is needed.
   - Lemma 2.12, for features of regular laws mu d (regular_feature with
     covariance unsat_cov kappa d) whose quadratic forms are subexponential
     with constant L0 / sqrt d, n / d^2 -> alpha and beta d >= 0: there is
     C such that the probability under tuple_prod (fun=> mu d) (n d) that
     unsat_ridge_value - unsat_value exceeds C beta d ln d tends to 0. The
     statement is in requests/c-to-b.md. Proof: the small-ball method in
     Markov form (probability/small_ball_method.v) with scale
     s_d^2 = ln d, the class of the (<z, theta> - b) / sqrt
     (C_kappa(theta, theta) + b^2), the small-ball probability from (F1) and
     Paley-Zygmund, and Chebyshev's inequality for (1/n) sum_i <Z_i, I>^2
     around C_kappa(I, I) = kappa - 1; then the localization. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
