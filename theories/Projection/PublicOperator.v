(* The bilinear operator bound implies the coefficient action bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages Matrix.Definitions
  Spectral.Transport Spectral.Duality PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadCoefficients Cone.ConditionOperator
  Gaussian.SmoothCovariance Gaussian.FeatureCoordinates Data.FeatureMoments
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Projection.Stein Projection.Image Projection.Variance Projection.Product
  Projection.Independent Projection.Public.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Theorem paper_main_projection_public_operator n (T : 'M[R]_(S n)) eps :
  paper_main_cone_opnorm_le T eps ->
  paper_main_projection_operator_bound (S n) (paper_main_projection_public_coeff n T) eps.
Proof.
intros HO z.
pose (v := ((\col_i z i)%R) : 'cV[R]_(S n)).
pose (w := (T *m v)%R).
pose (X := (w^T *m w)%R ord0 ord0).
pose (Y := (v^T *m v)%R ord0 ord0).
assert (HX : 0<=X) by (apply/RleP; apply pmh_vec_sqr_ge0).
assert (HY : 0<=Y) by (apply/RleP; apply pmh_vec_sqr_ge0).
pose proof(HO w v) as HH.
rewrite -mulmxA in HH.
change ((X^+2 <= eps^+2*(X*Y))%R = true) in HH.
move/RleP: HH => HH.
rewrite -!RpowE -!RmultE in HH.
change (X^2<=eps^2*(X*Y)) in HH.
assert (HXY : X<=eps^2*Y).
{ destruct(Req_dec X 0) as [->|Hne].
  - apply Rmult_le_pos; [apply pow2_ge_0|exact HY].
  - assert (Hpos : 0<X) by lra.
    apply (Rmult_le_reg_l X); [exact Hpos|]; nra. }
assert (EW : forall i : 'I_(S n),
  finite_sum (fun j => paper_main_projection_public_coeff n T i j*z j) (List.seq 0 (S n))=w i ord0).
{ intro i; unfold w; rewrite mxE finite_sum_seqE.
  apply: eq_bigr => j _.
  rewrite /paper_main_projection_public_coeff paper_main_matrix_from_public_entry /v mxE; reflexivity. }
assert (EX : finite_sum (fun i => (finite_sum (fun j => paper_main_projection_public_coeff n T i j*z j)
  (List.seq 0 (S n)))^2) (List.seq 0 (S n))=X).
{ unfold X; rewrite pmh_vec_dot finite_sum_seqE.
  apply: eq_bigr => i _; rewrite EW.
  change ((w i ord0)^2=w i ord0*w i ord0); ring. }
assert (EY : finite_sum (fun j => z j^2) (List.seq 0 (S n))=Y).
{ unfold Y; rewrite pmh_vec_dot finite_sum_seqE; apply: eq_bigr => j _.
  rewrite /v !mxE; change (z j^2=z j*z j); ring. }
rewrite EX EY; exact HXY.
Qed.

Theorem paper_main_projection_public_comparison n K (T : nat -> 'M[R]_(S n)) F DF D2F C eps S :
  paper_main_gaussian_smooth_test K F DF D2F C 0 ->
  (forall a, (a<K)%coq_nat -> paper_main_symmetric (T a)) ->
  (forall a, (a<K)%coq_nat -> paper_main_cone_opnorm_le (T a) eps) ->
  (forall a, (a<K)%coq_nat -> paper_main_frobenius (T a)^2<=S^2) ->
  0<=eps -> 0<=S ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => F(paper_main_projection_image K (fun a => pmdf_quad n (T a)) xs))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => F(paper_main_projection_image K
      (fun a => linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T a))) xs)))<=
    INR K*(INR K*(2*C*eps*S)).
Proof.
intros HF HT HO HN Heps HS.
pose proof(paper_main_projection_independent_comparison n (paper_main_symmetric_dimension n) K
  (fun a => paper_main_projection_public_coeff n (T a))
  (fun a => paper_main_projection_goe_loading n (T a)) F DF D2F C eps S HF
  ltac:(intros a i j Ha Hi Hj; apply paper_main_projection_public_symmetric; [apply HT; exact Ha|exact Hi|exact Hj])
  ltac:(intros a Ha; apply paper_main_projection_public_operator; apply HO; exact Ha)
  ltac:(intros a Ha; rewrite paper_main_projection_public_square; apply HN; exact Ha)
  ltac:(intros a b Ha Hb; apply paper_main_projection_goe_covariance; apply HT; assumption)
  Heps HS) as H.
assert (HE : gaussian_iterated_expectation (Datatypes.S n)
  (fun xs => F(paper_main_projection_image K (fun a => paper_main_projection_quadratic (Datatypes.S n)
    (paper_main_projection_public_coeff n (T a))) xs))=
  gaussian_iterated_expectation (Datatypes.S n) (fun xs => F(paper_main_projection_image K (fun a => pmdf_quad n (T a)) xs))).
{ apply gaussian_iterated_expectation_ext; intros xs Hxs; f_equal.
  unfold paper_main_projection_image; apply map_ext; intro a; apply paper_main_projection_public_quadratic. }
rewrite HE in H; exact H.
Qed.
