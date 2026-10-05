(* A Gaussian Hanson-Wright tail for a real symmetric matrix under the
   public product law gaussian_product_law d. For B : 'M[R]_d symmetric and
   a sample x, the centered statistic is
     paper_main_gaussian_quadratic_statistic B (tval x)
       = x^T B x - trace B,   x = paper_main_symmetric_column (tval x),
   the public column of the d coordinates. It is continuous, so its level
   sets are measurable. The real orthogonal diagonalization and the bridge
   of PaperMainSymmetricDiagonalizationBridge rewrite it, pointwise, as the
   A13 weighted square of an image with orthonormal rows, with
   sum_i a_i^2 = paper_main_pairing B B and |a_i| <= b under the public
   bilinear bound paper_main_cone_opnorm_le B b. The A13 tail then gives,
   for 0 <= b, 0 < u and 0 < |B|_F^2 + b u,
     P[u <= |x^T B x - trace B|] <= 2 exp (- u^2 / (4 |B|_F^2 + 4 b u)),
   where |B|_F^2 = paper_main_pairing B B. For B <> 0 the last hypothesis
   always holds. For B = 0 the event is empty when u > 0. This is the
   Gaussian Hanson-Wright helper, not a main phase theorem. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianCoordinateDefinitions
  GaussianCoordinateTopology GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity GaussianCovarianceDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainConeConditionOperator PaperMainGaussianSmoothTail PaperMainGaussianWeightedSquare
  PaperMainGaussianWeightedSquareLaw PaperMainGaussianOrthogonal
  PaperMainGaussianOrthogonalTail PaperMainSymmetricDiagonalization
  PaperMainSymmetricDiagonalizationBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_quadratic_statistic {d : nat} (B : 'M[R]_d)
    (xs : list R) : R :=
  paper_main_quadratic_form B (paper_main_symmetric_column xs) - paper_main_trace B.

(* Continuity and measurability. *)

Lemma paper_main_gaussian_quadratic_continuous d (B : 'M[R]_d) :
  paper_main_symmetric B ->
  finite_joint_continuous d (paper_main_gaussian_quadratic_statistic B).
Proof.
move=> HB.
have [L [c [_ [Hid _]]]] := paper_main_symmetric_quadratic_list _ _ HB.
apply: (finite_joint_continuous_ext d
  (fun xs => paper_main_weighted_square d c (gaussian_covariance_image d d L xs))).
  by move=> xs _; rewrite /paper_main_gaussian_quadratic_statistic RminusE Hid.
exact: paper_main_gaussian_orthogonal_square_continuous.
Qed.

Theorem paper_main_gaussian_quadratic_abs_measurable d (B : 'M[R]_d) u :
  paper_main_symmetric B ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_quadratic_statistic B (tval x)))].
Proof.
move=> HB.
exact: (paper_main_gaussian_smooth_ge_measurable d _ u
  (finite_joint_continuous_abs d _ (paper_main_gaussian_quadratic_continuous d B HB))).
Qed.

Theorem paper_main_gaussian_quadratic_ge_measurable d (B : 'M[R]_d) u :
  paper_main_symmetric B ->
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle u (paper_main_gaussian_quadratic_statistic B (tval x))].
Proof.
move=> HB.
exact: (paper_main_gaussian_smooth_ge_measurable d _ u
  (paper_main_gaussian_quadratic_continuous d B HB)).
Qed.

(* The tail. *)

Theorem paper_main_gaussian_quadratic_tail d (B : 'M[R]_d) (b u : R) :
  paper_main_symmetric B -> 0 <= b -> paper_main_cone_opnorm_le B b -> 0 < u ->
  0 < paper_main_pairing B B + b * u ->
  (gaussian_product_law d
    [set x | Rle u (Rabs (paper_main_gaussian_quadratic_statistic B (tval x)))]
    <= (2 * exp (- u ^ 2 / (4 * paper_main_pairing B B + 4 * b * u)))%:E)%E.
Proof.
move=> HB Hb HBb Hu Hden.
have [L [c [HL [Hid [Hfr Hbd]]]]] := paper_main_symmetric_quadratic_list _ _ HB.
have Hb' : (0 <= b)%R by exact/RleP.
have Hc : forall i, (i < d)%coq_nat -> Rabs (c i) <= b.
  by move=> i Hi; apply/RleP; exact: (Hbd b Hb' HBb i Hi).
have Hden' : 0 < finite_sum (fun i => c i ^ 2) (List.seq 0 d) + b * u.
  by rewrite Hfr.
have H := paper_main_gaussian_orthogonal_square_two_sided_tail d L c b u HL Hc Hb Hu Hden'.
rewrite Hfr in H.
have -> : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_quadratic_statistic B (tval x)))] =
  [set x | Rle u (Rabs (paper_main_weighted_square d c
    (gaussian_covariance_image d d L (tval x))))].
  by apply/seteqP; split=> x /=; rewrite /paper_main_gaussian_quadratic_statistic RminusE Hid.
exact: H.
Qed.

Corollary paper_main_gaussian_quadratic_tail_nonzero d (B : 'M[R]_d) (b u : R) :
  paper_main_symmetric B -> B != 0%R -> 0 <= b -> paper_main_cone_opnorm_le B b -> 0 < u ->
  (gaussian_product_law d
    [set x | Rle u (Rabs (paper_main_gaussian_quadratic_statistic B (tval x)))]
    <= (2 * exp (- u ^ 2 / (4 * paper_main_pairing B B + 4 * b * u)))%:E)%E.
Proof.
move=> HB HB0 Hb HBb Hu.
apply: (paper_main_gaussian_quadratic_tail d B b u HB Hb HBb Hu).
have Hp : 0 < paper_main_pairing B B.
  by apply/RltP; exact: (paper_main_pairing_self_gt0 d B HB0).
have Hbu : 0 <= b * u by apply: Rmult_le_pos; lra.
lra.
Qed.

Theorem paper_main_gaussian_quadratic_zero_tail d u :
  0 < u ->
  gaussian_product_law d
    [set x | Rle u (Rabs (paper_main_gaussian_quadratic_statistic (0%R : 'M[R]_d) (tval x)))]
    = 0%E.
Proof.
move=> Hu.
have Hz : forall xs, paper_main_gaussian_quadratic_statistic (0%R : 'M[R]_d) xs = 0.
  move=> xs; rewrite /paper_main_gaussian_quadratic_statistic.
  have -> : paper_main_quadratic_form (0%R : 'M[R]_d) (paper_main_symmetric_column xs) = 0.
    rewrite /paper_main_quadratic_form big1 // => i _; rewrite big1 // => j _.
    by rewrite !mxE mulr0 mul0r.
  have -> : paper_main_trace (0%R : 'M[R]_d) = 0.
    by rewrite /paper_main_trace big1 // => i _; rewrite mxE.
  by rewrite Rminus_0_r.
have -> : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_gaussian_quadratic_statistic (0%R : 'M[R]_d) (tval x)))] = set0.
  apply/seteqP; split=> x //=.
  by rewrite Hz Rabs_R0; lra.
exact: measure0.
Qed.
