(* The rescaled positive semidefinite cones of Koehler and Sohn (arXiv
   2608.27372, section 5, lines 4848-4950 of arxiv_v1.tex), and the
   covariance of the quadratic features.

   For kappa > 1, c_kappa = (kappa - 3)/2, the map T_kappa multiplies the
   diagonal of a matrix by sqrt ((kappa - 1)/2) and keeps the rest, and the
   cone S^d_kappa = T_kappa(S^d_+) is the image of the positive semidefinite
   cone. The feature covariance is
   C_kappa(A, B) = (1/d) (2 <A, B> + (kappa - 3) <A_diag, B_diag>)
   = (2/d) <T_kappa A, T_kappa B> (eq:gaussian-section-covariance): the
   covariance E <W, A> <W, B> of the quadratic feature W = (x x^T - I)/sqrt d
   of a point with independent coordinates of mean 0, variance 1 and fourth
   moment kappa, and of the Gaussian feature G = sqrt (2/d) T_kappa
   ((A + A^T)/2) of a square matrix A with independent standard normal
   entries ((A + A^T)/2 is the paper's GOE matrix: diagonal entries N(0, 1),
   entries above the diagonal N(0, 1/2), all independent).

   Main results to prove (stage 1 of phase 5; names come with the proofs),
   for kappa > 1:
   - kappa^vee = 1 + 4/(kappa - 1) is an involution of ]1, +oo[ with fixed
     point 3, exchanging ]1, 3[ and ]3, +oo[, and
     c_{kappa^vee} = -c_kappa/(1 + c_kappa).
   - T_{kappa^vee} = T_kappa^{-1}; T_3 is the identity; T_kappa preserves
     symmetry and is self-adjoint for the Frobenius pairing.
   - C_kappa(A, B) = (2/d) <T_kappa A, T_kappa B>; for A symmetric,
     min(2, kappa - 1)/d ||A||_F^2 <= C_kappa(A, A) <= max(2, kappa - 1)/d
     ||A||_F^2 (eq:feature-covariance-coercivity); C_kappa(I, I) = kappa - 1.
   - Y is in S^d_kappa if and only if T_{kappa^vee} Y >= 0; S^d_3 is the
     positive semidefinite cone.
   - Lemma 5.2: within the symmetric matrices, the dual cone of S^d_kappa is
     S^d_{kappa^vee} and its polar cone is -S^d_{kappa^vee}, from the
     self-duality of the positive semidefinite cone (a symmetric Y is >= 0
     if and only if <Y, S> >= 0 for every S >= 0).
   - S^d_kappa is a closed convex cone.
   - For A with law gauss (d * d), read as a d x d matrix by vec_mx, and B
     symmetric, <G, B> has law normal_prob 0 (sqrt C_kappa(B, B)).

   Definitions, at Stdlib's R read through MathComp's ring_scope as in
   UniversalityDefinitions:
     cone_shift kappa      == c_kappa = (kappa - 3)/2
     kappa_dual kappa      == kappa^vee = 1 + 4/(kappa - 1)
     diag_part S           == the diagonal part S_diag of S
     cone_map kappa S      == T_kappa S = S - S_diag
                              + sqrt ((kappa - 1)/2) S_diag
     kappa_cone kappa d    == S^d_kappa, the image of the positive semidefinite
                              d x d matrices under T_kappa
     feature_cov kappa A B == C_kappa(A, B)
     sym_dual_cone K       == the symmetric Y with <Y, S> >= 0 for S in K
     sym_polar_cone K      == the symmetric Y with <Y, S> <= 0 for S in K
     goe_part A            == (A + A^T)/2
     gaussian_feature kappa A == sqrt (2/d) T_kappa ((A + A^T)/2) *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition cone_shift (kappa : R) : R := (kappa - 3%:R) / 2%:R.

Definition kappa_dual (kappa : R) : R := 1 + 4%:R / (kappa - 1).

Definition diag_part {d : nat} (S : 'M[R]_d) : 'M[R]_d :=
  \matrix_(i, j) (if i == j then S i j else 0).

Definition cone_map {d : nat} (kappa : R) (S : 'M[R]_d) : 'M[R]_d :=
  S - diag_part S + Num.sqrt ((kappa - 1) / 2%:R) *: diag_part S.

Definition kappa_cone (kappa : R) (d : nat) : set 'M[R]_d :=
  [set cone_map kappa S | S in [set S : 'M[R]_d | paper_main_psd S]].

Definition feature_cov (kappa : R) {d : nat} (A B : 'M[R]_d) : R :=
  (2%:R * paper_main_pairing A B + (kappa - 3%:R) * \sum_(i < d) A i i * B i i)
  / d%:R.

Definition sym_dual_cone {d : nat} (K : set 'M[R]_d) : set 'M[R]_d :=
  [set Y | paper_main_symmetric Y /\
    forall S, K S -> 0 <= paper_main_pairing Y S].

Definition sym_polar_cone {d : nat} (K : set 'M[R]_d) : set 'M[R]_d :=
  [set Y | paper_main_symmetric Y /\
    forall S, K S -> paper_main_pairing Y S <= 0].

Definition goe_part {d : nat} (A : 'M[R]_d) : 'M[R]_d := (2%:R)^-1 *: (A + A^T).

Definition gaussian_feature (kappa : R) {d : nat} (A : 'M[R]_d) : 'M[R]_d :=
  Num.sqrt (2%:R / d%:R) *: cone_map kappa (goe_part A).
