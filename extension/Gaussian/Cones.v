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

   Proved, for kappa > 1:
   - cone_shiftE, cone_shiftD1, kappa_dualE: c_kappa = (kappa - 3)/2,
     1 + c_kappa = (kappa - 1)/2 and kappa^vee = 1 + 4/(kappa - 1), with
     MathComp's operations (the definitions, at Stdlib's R, unfold to
     Stdlib's); cone_shift_gtN1: c_kappa > -1; cone_shift3: c_3 = 0.
   - kappa_dual_gt1, kappa_dualK, kappa_dual3, kappa_dual_lt3,
     kappa_dual_gt3: kappa^vee is an involution of ]1, +oo[ with fixed point
     3, exchanging ]1, 3[ and ]3, +oo[; cone_shift_dual:
     c_{kappa^vee} = -c_kappa/(1 + c_kappa).

   Main results to prove (stage 1 of phase 5; names come with the proofs),
   for kappa > 1:
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
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

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

Section kappa_dual.

Lemma cone_shiftE (kappa : R) : cone_shift kappa = (kappa - 3%:R) / 2%:R.
Proof. by rewrite /cone_shift RdivE RminusE. Qed.

Lemma cone_shiftD1 (kappa : R) : 1 + cone_shift kappa = (kappa - 1) / 2%:R.
Proof. by rewrite cone_shiftE; field. Qed.

Lemma cone_shift_gtN1 (kappa : R) : 1 < kappa -> -1 < cone_shift kappa.
Proof. by move=> k1; rewrite cone_shiftE; lra. Qed.

Lemma cone_shift3 : cone_shift 3%:R = 0.
Proof. by rewrite cone_shiftE subrr mul0r. Qed.

Lemma kappa_dualE (kappa : R) : kappa_dual kappa = 1 + 4%:R / (kappa - 1).
Proof. by rewrite /kappa_dual RplusE RdivE RminusE !R1E. Qed.

Lemma kappa_dual_gt1 (kappa : R) : 1 < kappa -> 1 < kappa_dual kappa.
Proof. by move=> k1; rewrite kappa_dualE ltrDl divr_gt0// subr_gt0. Qed.

Lemma kappa_dualK (kappa : R) : 1 < kappa ->
  kappa_dual (kappa_dual kappa) = kappa.
Proof.
move=> k1; have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
rewrite !kappa_dualE addrAC subrr add0r.
by field.
Qed.

Lemma kappa_dual3 : kappa_dual 3%:R = 3%:R.
Proof. by rewrite kappa_dualE; field. Qed.

Lemma kappa_dual_lt3 (kappa : R) : 3%:R < kappa -> kappa_dual kappa < 3%:R.
Proof.
move=> k3; rewrite kappa_dualE -ltrBrDl ltr_pdivrMr; last by lra.
by lra.
Qed.

Lemma kappa_dual_gt3 (kappa : R) : 1 < kappa -> kappa < 3%:R ->
  3%:R < kappa_dual kappa.
Proof.
move=> k1 k3; rewrite kappa_dualE -ltrBlDl ltr_pdivlMr; last by lra.
by lra.
Qed.

Lemma cone_shift_dual (kappa : R) : 1 < kappa ->
  cone_shift (kappa_dual kappa) = - cone_shift kappa / (1 + cone_shift kappa).
Proof.
move=> k1; have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
rewrite cone_shiftD1 !cone_shiftE kappa_dualE.
by field.
Qed.

End kappa_dual.
