(* Exact coefficient and GOE-covariance bridges for matrices 'M[R]_(S n). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages Matrix.Definitions
  Tensor.Definitions PaperMainDefinitions Geometry.Psd Geometry.Homogeneous
  Spectral.Transport Spectral.Duality Gaussian.FeatureCoordinates
  Gordon.ProcessCovariance Data.FeatureMoments Projection.Stein
  Projection.Variance Projection.Algebra Projection.Product
  Projection.Independent.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_projection_public_coeff n (T : 'M[R]_(S n)) i j :=
  matrix_entry n (paper_main_matrix_from_public n T) i j.
Definition paper_main_projection_goe_loading n (T : 'M[R]_(S n)) k :=
  sqrt 2*paper_main_symmetric_coordinates n (paper_main_matrix_from_public n T) k.

Lemma paper_main_projection_public_matrix n T :
  paper_main_projection_matrix (S n) (paper_main_projection_public_coeff n T)=T.
Proof.
apply/matrixP => i j; rewrite /paper_main_projection_matrix mxE /paper_main_projection_public_coeff.
apply paper_main_matrix_from_public_entry.
Qed.

Lemma paper_main_projection_public_symmetric n T : paper_main_symmetric T ->
  forall i j, (i<=n)%coq_nat -> (j<=n)%coq_nat ->
    paper_main_projection_public_coeff n T i j=paper_main_projection_public_coeff n T j i.
Proof.
intro HT; exact(paper_main_matrix_internal_symmetric n T HT).
Qed.

Lemma paper_main_projection_public_pairing n T U :
  paper_main_projection_pairing (S n) (paper_main_projection_public_coeff n T)
    (paper_main_projection_public_coeff n U)=paper_main_pairing T U.
Proof.
unfold paper_main_projection_pairing,paper_main_pairing.
rewrite finite_sum_seqE; apply: eq_bigr => i _.
rewrite finite_sum_seqE; apply: eq_bigr => j _.
rewrite /paper_main_projection_public_coeff !paper_main_matrix_from_public_entry; reflexivity.
Qed.

Lemma paper_main_projection_public_square n T :
  paper_main_projection_square_coefficients (S n) (paper_main_projection_public_coeff n T)=paper_main_frobenius T^2.
Proof.
rewrite paper_main_projection_square_pairing paper_main_projection_public_pairing.
symmetry; apply paper_main_frobenius_squared.
Qed.

Lemma paper_main_projection_public_quadratic n T xs :
  paper_main_projection_quadratic (S n) (paper_main_projection_public_coeff n T) xs=pmdf_quad n T xs.
Proof. rewrite paper_main_projection_quad_matrix paper_main_projection_public_matrix; reflexivity. Qed.

Theorem paper_main_projection_goe_covariance n T U :
  paper_main_symmetric T -> paper_main_symmetric U ->
  paper_main_projection_covariance (paper_main_symmetric_dimension n)
    (paper_main_projection_goe_loading n T) (paper_main_projection_goe_loading n U)=
    2*paper_main_projection_pairing (S n) (paper_main_projection_public_coeff n T)
      (paper_main_projection_public_coeff n U).
Proof.
intros HT HU; rewrite paper_main_projection_public_pairing.
transitivity (2*paper_main_gordon_dot (paper_main_symmetric_dimension n)
  (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n T))
  (paper_main_symmetric_coordinates n (paper_main_matrix_from_public n U))).
- unfold paper_main_projection_covariance,paper_main_projection_goe_loading,paper_main_gordon_dot.
  rewrite <- finite_sum_scale; apply finite_sum_ext; intros k Hk.
  pose proof(sqrt_sqrt 2 ltac:(lra)) as Hsq.
  transitivity ((sqrt 2*sqrt 2)*(paper_main_symmetric_coordinates n (paper_main_matrix_from_public n T) k*
    paper_main_symmetric_coordinates n (paper_main_matrix_from_public n U) k)); [ring|].
  rewrite Hsq; reflexivity.
- rewrite (paper_main_symmetric_coordinate_pairing n _ _
    (paper_main_matrix_internal_symmetric n T HT) (paper_main_matrix_internal_symmetric n U HU)).
  rewrite (paper_main_matrix_public_pairing n _ _ (paper_main_matrix_internal_symmetric n U HU)).
  rewrite !paper_main_matrix_public_roundtrip; reflexivity.
Qed.
