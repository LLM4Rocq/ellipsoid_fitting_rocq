(* Symmetric bilinear coefficients for the Gaussian operator tail: the
   deterministic bridge from the bilinear form u^T W v of the public Gaussian
   feature row W to a linear form in the Gaussian coordinates.

   For column vectors u, v put B = (u v^T + v u^T) / 2
   (paper_main_symmetric_bilinear). B is symmetric, <Z, B> = u^T Z v for
   symmetric Z, and |B|_F^2 = (|u|^2 |v|^2 + (u^T v)^2) / 2 <= |u|^2 |v|^2.
   With c_k the coordinates of B in the orthonormal goe_basis
   (paper_main_symmetric_bilinear_coefficients), Parseval gives
   sum_k c_k^2 = |B|_F^2, and for the public row W = paper_main_public_gaussian_row n 0 xs
   (dimension n + 1, D = paper_main_symmetric_dimension n):
     u^T W v = goe_scale n * sum_(k < D) c_k xs_k
   (paper_main_symmetric_bilinear_gaussian_row). So W / goe_scale n has
   bilinear form exactly sum_k c_k xs_k, with sum_k c_k^2 <= 1 for unit u, v.
   paper_main_symmetric_column maps a list-coordinate vector nat -> R to a
   public column whose squared norm is its Gordon dot product. Sums are the
   Gordon finite sums (paper_main_gordon_dot) of the existing Gaussian
   modules. No probability is used. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Matrix.Definitions Tensor.Definitions Goe.Definitions PaperMainDefinitions
  Geometry.Psd Geometry.Gram Geometry.Homogeneous Spectral.Transport
  Spectral.Duality Gordon.ProcessCovariance Gaussian.FeatureCoordinates
  Gaussian.PublicFeature Geometry.HeadFrobenius Geometry.HeadCoefficients
  Cone.ConditionOperator.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* B = (u v^T + v u^T) / 2. *)
Definition paper_main_symmetric_bilinear {d : nat} (u v : 'cV[R]_d) : 'M[R]_d :=
  2^-1 *: (u *m v^T + v *m u^T).

Section Bilinear.
Variable d : nat.
Implicit Types (Z : 'M[R]_d) (a b c e u v : 'cV[R]_d).

Lemma pmsb_pairing_outer Z a b :
  paper_main_pairing Z (a *m b^T) = (a^T *m Z *m b) 0 0.
Proof.
rewrite /paper_main_pairing mxE.
under eq_bigr do under eq_bigr do rewrite mxE big_ord1 mxE.
under [RHS]eq_bigr do rewrite mxE mulr_suml.
rewrite exchange_big /=; apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite mxE; ring.
Qed.

Lemma pmsb_pairing_outer_outer a b c e :
  paper_main_pairing (a *m b^T) (c *m e^T) = (c^T *m a) 0 0 * (b^T *m e) 0 0.
Proof.
by rewrite pmsb_pairing_outer mulmxA -(mulmxA (c^T *m a)) paper_main_mx11_mul.
Qed.

Theorem paper_main_symmetric_bilinear_symmetric u v :
  paper_main_symmetric (paper_main_symmetric_bilinear u v).
Proof. by move=> i j; rewrite !mxE !big_ord1 !mxE; ring. Qed.

Theorem paper_main_symmetric_bilinear_pairing Z u v :
  paper_main_symmetric Z ->
  paper_main_pairing Z (paper_main_symmetric_bilinear u v) = (u^T *m Z *m v) 0 0.
Proof.
move=> HZ.
have HZt : Z^T = Z by exact/paper_main_symmetricP.
rewrite /paper_main_symmetric_bilinear paper_main_pairing_scale pmh_pairingDr.
rewrite !pmsb_pairing_outer (paper_main_cross_sym _ Z v u HZt).
have H2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
by rewrite -mulr2n -(mulr_natl ((u^T *m Z *m v) 0 0) 2) mulrA (mulVf H2) mul1r.
Qed.

Theorem paper_main_symmetric_bilinear_frobenius_eq u v :
  paper_main_pairing (paper_main_symmetric_bilinear u v) (paper_main_symmetric_bilinear u v) =
  2^-1 * ((u^T *m u) 0 0 * (v^T *m v) 0 0 + (u^T *m v) 0 0 ^+ 2).
Proof.
rewrite /paper_main_symmetric_bilinear paper_main_pairing_scale pmh_pairingZl.
rewrite !pmh_pairingDl !pmh_pairingDr !pmsb_pairing_outer_outer.
rewrite (paper_main_inner_sym _ v u).
have H2 : (2%:R : R)^-1 * 2%:R = 1 by rewrite mulVf // pnatr_eq0.
transitivity (2^-1 * ((2^-1 * 2) *
    ((u^T *m u) 0 0 * (v^T *m v) 0 0 + (u^T *m v) 0 0 ^+ 2))); first by ring.
by rewrite H2 mul1r.
Qed.

Theorem paper_main_symmetric_bilinear_frobenius u v :
  paper_main_pairing (paper_main_symmetric_bilinear u v) (paper_main_symmetric_bilinear u v) <=
  (u^T *m u) 0 0 * (v^T *m v) 0 0.
Proof.
rewrite paper_main_symmetric_bilinear_frobenius_eq.
have CS := pmco_vec_cauchy_schwarz _ u v.
have H2p : 0 < (2%:R : R) by rewrite ltr0n.
rewrite mulrC (ler_pdivrMr _ _ H2p).
lra.
Qed.

End Bilinear.

(* The coordinates of B in the orthonormal goe_basis. *)
Definition paper_main_symmetric_bilinear_coefficients n (u v : 'cV[R]_(S n)) : nat -> R :=
  paper_main_symmetric_coordinates n
    (paper_main_matrix_from_public n (paper_main_symmetric_bilinear u v)).

Section GaussianRow.
Variable n : nat.
Implicit Types (u v : 'cV[R]_(S n)).

Lemma pmsb_internal_symmetric u v :
  symmetric_matrix n (paper_main_matrix_from_public n (paper_main_symmetric_bilinear u v)).
Proof.
apply: paper_main_matrix_internal_symmetric.
exact: paper_main_symmetric_bilinear_symmetric.
Qed.

(* Parseval: sum_k c_k^2 = |B|_F^2. *)
Theorem paper_main_symmetric_bilinear_coefficients_sqr u v :
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v)
    (paper_main_symmetric_bilinear_coefficients n u v) =
  paper_main_pairing (paper_main_symmetric_bilinear u v) (paper_main_symmetric_bilinear u v).
Proof.
have HBi := pmsb_internal_symmetric u v.
rewrite /paper_main_symmetric_bilinear_coefficients paper_main_symmetric_coordinate_pairing //.
by rewrite paper_main_matrix_public_pairing // paper_main_matrix_public_roundtrip.
Qed.

Corollary paper_main_symmetric_bilinear_coefficients_le u v :
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v)
    (paper_main_symmetric_bilinear_coefficients n u v) <=
  (u^T *m u) 0 0 * (v^T *m v) 0 0.
Proof.
rewrite paper_main_symmetric_bilinear_coefficients_sqr.
exact: paper_main_symmetric_bilinear_frobenius.
Qed.

(* The bilinear form of the public Gaussian row in the coefficients. *)
Theorem paper_main_symmetric_bilinear_gaussian_row u v xs :
  (u^T *m paper_main_public_gaussian_row n 0 xs *m v) 0 0 =
  goe_scale n * paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v) (fun k => List.nth k xs 0).
Proof.
have HW := paper_main_public_gaussian_row_symmetric n 0 xs.
have HBi := pmsb_internal_symmetric u v.
have HF := paper_main_gaussian_feature_row_symmetric n 0 xs.
rewrite -(paper_main_symmetric_bilinear_pairing _ _ u v HW).
rewrite /paper_main_public_gaussian_row.
rewrite -[paper_main_symmetric_bilinear u v]paper_main_matrix_public_roundtrip.
rewrite -paper_main_matrix_public_pairing //.
rewrite -paper_main_symmetric_coordinate_pairing //.
rewrite /paper_main_gordon_dot -RmultE -finite_sum_scale.
apply: finite_sum_ext => k Hk.
have Hk' : (k < paper_main_symmetric_dimension n)%coq_nat.
  by apply List.in_seq in Hk; lia.
rewrite (paper_main_gaussian_feature_row_coordinate n 0 xs k Hk').
rewrite Nat.mul_0_l Nat.add_0_l /paper_main_symmetric_bilinear_coefficients.
by rewrite !RmultE; ring.
Qed.

Lemma pmsb_goe_scale_gt0 : 0 < goe_scale n.
Proof.
rewrite /goe_scale RsqrtE sqrtr_gt0 RdivE INRE.
apply: divr_gt0; last by rewrite ltr0n.
by apply/RltP; exact: Rlt_0_2.
Qed.

(* The unit-covariance row W / goe_scale n has bilinear form exactly
   sum_k c_k xs_k. *)
Corollary paper_main_symmetric_bilinear_unit_row u v xs :
  (u^T *m ((goe_scale n)^-1 *: paper_main_public_gaussian_row n 0 xs) *m v) 0 0 =
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v) (fun k => List.nth k xs 0).
Proof.
rewrite -scalemxAr -scalemxAl mxE paper_main_symmetric_bilinear_gaussian_row mulrA.
by rewrite (mulVf (lt0r_neq0 pmsb_goe_scale_gt0)) mul1r.
Qed.

Corollary paper_main_symmetric_bilinear_coefficients_unit u v :
  (u^T *m u) 0 0 = 1 -> (v^T *m v) 0 0 = 1 ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_symmetric_bilinear_coefficients n u v)
    (paper_main_symmetric_bilinear_coefficients n u v) <= 1.
Proof.
move=> Hu Hv; have := paper_main_symmetric_bilinear_coefficients_le u v.
by rewrite Hu Hv mulr1.
Qed.

(* List-coordinate vectors as public columns. *)
Definition paper_main_symmetric_column (f : nat -> R) : 'cV[R]_(S n) := \col_i f i.

Lemma paper_main_symmetric_column_norm (f : nat -> R) :
  ((paper_main_symmetric_column f)^T *m paper_main_symmetric_column f) 0 0 =
  paper_main_gordon_dot (S n) f f.
Proof.
rewrite pmh_vec_dot /paper_main_gordon_dot finite_sum_seqE.
by apply: eq_bigr => i _; rewrite !mxE RmultE.
Qed.

End GaussianRow.
