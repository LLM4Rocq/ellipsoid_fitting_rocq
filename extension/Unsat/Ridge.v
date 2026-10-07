(* Removing the ridge: Lemma 2.12 of Koehler and Sohn (arXiv 2608.27372,
   lines 1476-1494 of arxiv_v1.tex, proof lines 4598-4833), for the
   quadratic features of the data and for the Gaussian features.

   For features Z_1, ..., Z_n (symmetric d x d matrices), a domain D, a
   ridge weight beta >= 0 and lambda_d = ||Sigma_kappa||_op =
   max(2, kappa - 1)/d, the ridge-regularized least squares objective is
     F_Z(S, b; beta) = (1/(2n)) sum_i (b - <Z_i, S>)^2
                       + beta (lambda_d ||S||_F^2 + b^2)
   and Phi_Z(D; beta) its infimum over S in D and b real; Phi_Z(D) =
   Phi_Z(D; 0). The domain is R_d^o, the positive definite matrices of
   trace d (lines 1040-1058).

   Main results to prove (stage 1 of phase 5; names come with the proofs).
   The constants depend only on kappa, K and alpha.
   - Lemma 4.3 for the data: for points x_1, ..., x_n with independent
     coordinates of laws as in universality_coordinate_law kappa K, and
     W(x) = (x x^T - I)/sqrt d,
       E rademacher_mean (opnorm ((1/n) sum_i eps_i W(x_i)))
         <= C K^2 (1/sqrt n + sqrt d / n),
     which is O(1/d) when n/d^2 -> alpha > 0; the paper has sqrt (log d)/d
     from matrix Bernstein. Proof: the operator norm bound of
     matrix/random_opnorm.v, since v^T W(x) v = ((v^T x)^2 - |v|^2)/sqrt d
     is centered and subexponential with constant C K^2/sqrt d.
   - Lemma 4.3 for the Gaussian features: the same bound, with a constant
     depending on kappa, for n independent features of law
     gaussian_feature kappa (Gaussian/Cones.v), since v^T G v is normal with
     variance C_kappa(v v^T, v v^T) <= max(2, kappa - 1)/d.
   - Localization (deterministic, from the small-ball event): if every S in
     R_d and b with C_kappa(S, S) + b^2 >= s^2 satisfies
     (1/n) sum_i (<Z_i, S> - b)^2 >= c (C_kappa(S, S) + b^2), and
     (1/n) sum_i <Z_i, I>^2 <= B with B < c s^2, then for every beta >= 0,
       0 <= Phi_Z(R_d^o; beta) - Phi_Z(R_d^o)
         <= beta (max(2, kappa - 1)/min(2, kappa - 1)) s^2.
     Near-minimizers are used, so no minimizer, compactness or density
     argument is needed.
   - Lemma 2.12 for the data: for kappa > 1, K > 0 and alpha > 0 there is C
     such that for every family of coordinate laws as in
     universality_statement and every n with n/d^2 -> alpha, there are
     measurable sets of samples E_d with probability tending to one on which
       0 <= Phi_{W(X)}(R_d^o; beta) - Phi_{W(X)}(R_d^o) <= C beta
     for every beta >= 0. The paper's bound C beta log d follows for d >= 3.
     Proof: the small-ball bound for linear classes of
     probability/small_ball_method.v with D = R_d, N(Z) = d opnorm Z and s^2
     a large constant, the covariance E <W, S>^2 = C_kappa(S, S) and the
     bound E <W, S>^4 <= C C_kappa(S, S)^2 (condition (F1); lane A,
     Features/Regular.v), Chebyshev's inequality for
     (1/n) sum_i <W_i, I>^2 around C_kappa(I, I) = kappa - 1, then the
     localization.
   - Lemma 2.12 for the Gaussian features: the same for n independent
     Gaussian features of covariance C_kappa.

   Definitions:
     feature_scale kappa d        == lambda_d = max(2, kappa - 1)/d
     ridge_objective l beta Z S b == F_Z(S, b; beta) with lambda_d = l
     ridge_value l beta Z D       == Phi_Z(D; beta)
     pd_trace_slice d             == R_d^o, the positive definite matrices of
                                     trace d *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.
From EllipsoidUniversality.Gaussian Require Import Cones.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition feature_scale (kappa : R) (d : nat) : R :=
  Num.max 2%:R (kappa - 1) / d%:R.

Definition ridge_objective {n d : nat} (l beta : R) (Z : 'I_n -> 'M[R]_d)
    (S : 'M[R]_d) (b : R) : R :=
  (\sum_(i < n) (b - paper_main_pairing (Z i) S) ^+ 2) / (2%:R * n%:R)
  + beta * (l * paper_main_pairing S S + b ^+ 2).

Definition ridge_value {n d : nat} (l beta : R) (Z : 'I_n -> 'M[R]_d)
    (D : set 'M[R]_d) : R :=
  inf [set ridge_objective l beta Z S b | S in D & b in [set: R]].

Definition pd_trace_slice (d : nat) : set 'M[R]_d :=
  [set S | paper_main_pd S /\ paper_main_trace S = d%:R].
