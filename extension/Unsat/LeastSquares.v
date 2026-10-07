(* The least squares problem of the unsatisfiable phase of Koehler and Sohn,
   "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, section 2.2, lines 1004-1086), at Stdlib's R: the quadratic
   features of a sample, their covariance Sigma_kappa, the domain
   R_d^o = {R > 0, Tr R = d}, and the values Phi_Z(R_d^o; beta) and
   Phi_Z(R_d^o) of the library's least squares problem
   (convex/least_squares.v) for a tuple Z of features.

   Matrices are row vectors of size d * d through mxvec, so that the
   Frobenius product <A, B> is mxdot (mxvec A) (mxvec B). The feature of a
   point x is W(x) = (x x^T - I) / sqrt d; the features of a sample are
   W(x_1), ..., W(x_n). Their covariance is
   C_kappa(A, B) = (1/d) (2 <A, B> + (kappa - 3) <diag A, diag B>) on
   symmetric matrices (paper, lines 268-280); on all matrices it is
   C_kappa of the symmetric parts, and unsat_cov is its matrix in the mxvec
   coordinates. The ridge regularization uses
   lambda = opnorm (unsat_cov kappa d), the operator norm of Sigma_kappa.

   Planned results (stage 1 of phase 5):
   - For every sample x of n points of R^d,
     universality_fitting_error n d x = 2 * unsat_value (unsat_features x)
     (eq:unregularized-affine-energy-value, lines 1054-1058): the
     constraint r >= 0 of Gamma_X is inactive because x_i^T S x_i >= 0, and
     the infimum over S >= 0 of trace d is the infimum over S > 0 of trace
     d, by continuity, since (1 - t) S + t I is positive definite for t > 0.
   - R_d^o is convex and relatively open with directions the symmetric
     matrices of trace 0, and -ln det is a d-self-concordant barrier on it,
     nonnegative with value 0 at the identity (convex/logdet_barrier.v at
     Stdlib's R). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis Require Import euclidean opnorm least_squares.
From GaussianAnalysis Require Import logdet_barrier.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope ring_scope.

(* The quadratic feature W(x) = (x x^T - I) / sqrt d of a point x of R^d,
   as a row vector of size d * d. *)
Definition unsat_feature d (x : 'cV[R]_d) : 'rV[R]_(d * d) :=
  mxvec ((Num.sqrt d%:R)^-1 *: (x *m x^T - 1%:M)).

(* The features W(x_1), ..., W(x_n) of a sample. *)
Definition unsat_features n d (x : paper_main_sample n d) :
    n.-tuple 'rV[R]_(d * d) :=
  [tuple unsat_feature d (paper_main_point x i) | i < n].

(* C_kappa of the symmetric parts of A and B. *)
Definition unsat_cov_form (kappa : R) d (A B : 'M[R]_d) : R :=
  d%:R^-1 * (mxdot A B + mxdot A B^T +
             (kappa - 3%:R) * \sum_(j < d) A j j * B j j).

(* Sigma_kappa, the matrix of C_kappa in the mxvec coordinates. *)
Definition unsat_cov (kappa : R) d : 'M[R]_(d * d) :=
  \matrix_(p, q)
    unsat_cov_form kappa d (vec_mx (delta_mx 0 p : 'rV[R]_(d * d)))
                           (vec_mx (delta_mx 0 q : 'rV[R]_(d * d))).

(* The paper's lambda, the operator norm of Sigma_kappa. *)
Definition unsat_lambda (kappa : R) d : R := opnorm (unsat_cov kappa d).

(* R_d^o = {R > 0, Tr R = d}. *)
Definition unsat_domain d : set 'rV[R]_(d * d) := pd_slice d d%:R.

(* Phi_Z(R_d^o; beta), with the ridge weight unsat_lambda kappa d. *)
Definition unsat_ridge_value (kappa : R) n d (beta : R)
    (Z : n.-tuple 'rV[R]_(d * d)) : R :=
  ls_value Z (unsat_lambda kappa d) beta (unsat_domain d).

(* Phi_Z(R_d^o), without regularization. *)
Definition unsat_value n d (Z : n.-tuple 'rV[R]_(d * d)) : R :=
  ls_value Z 0 0 (unsat_domain d).
