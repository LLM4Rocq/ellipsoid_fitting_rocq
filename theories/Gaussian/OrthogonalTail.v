(* Tails of a weighted centered Gaussian square after a loading with
   orthonormal rows, under the law gaussian_product_law d. Write
   O x = gaussian_covariance_image d d O x and
   Q d a xs = sum_(i < d) a_i (x_i^2 - 1), with coefficients of either sign.
   The map x |-> Q d a (O x) is continuous
   (paper_main_gaussian_orthogonal_square_continuous). Since O x has the law
   of x (paper_main_covariance_equal_law, with the identity loading), the
   tails of Q (O x) are those of Q x (Gaussian.WeightedSquareLaw):
   for v = sum_(i < d) a_i^2, |a_i| <= L, 0 < u and 0 < v + L u,
     P[u <= |Q(O x)|] <= 2 exp (- u^2 / (4 v + 4 L u))
   (paper_main_gaussian_orthogonal_square_two_sided_tail). *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  GaussianProbabilityProductDefinitions Gaussian.CovarianceDefinitions
  Gaussian.WeightedSquare Gaussian.WeightedSquareLaw Gaussian.Orthogonal
  Gaussian.OrthogonalLaw Gaussian.CovarianceBounds Gaussian.CovarianceMarginals.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_orthogonal_square_continuous d O (a : nat -> R) :
  finite_joint_continuous d
    (fun xs => paper_main_weighted_square d a (gaussian_covariance_image d d O xs)).
Proof.
exact: (paper_main_gaussian_orthogonal_continuous d O _
  (paper_main_weighted_square_continuous d a)).
Qed.

Theorem paper_main_gaussian_orthogonal_square_two_sided_tail d O (a : nat -> R) L u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d
    [set x | Rle u (Rabs (paper_main_weighted_square d a
      (gaussian_covariance_image d d O (tval x))))]
    <= (2 * exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) +
      4 * L * u)))%:E)%E.
Proof.
move=> HO Ha HL Hu Hden.
have mS : measurable [set y : measurableTypeR R | Rle u y].
  have -> : [set y : measurableTypeR R | Rle u y] = `[u, +oo[%classic.
    apply/seteqP; split => y /=; rewrite in_itv/= andbT.
      by move/RleP.
    by move=> /RleP.
  exact: measurable_itv.
have cg := finite_joint_continuous_abs d _ (paper_main_weighted_square_continuous d a).
have Hcov i j : (i < d)%coq_nat -> (j < d)%coq_nat ->
    gaussian_covariance_entry d O i j =
    gaussian_covariance_entry d paper_main_gaussian_identity i j.
  by move=> Hi Hj; rewrite HO // paper_main_gaussian_identity_covariance.
rewrite (paper_main_covariance_equal_law d d d O paper_main_gaussian_identity _
  [set y | Rle u y] Hcov cg mS).
have -> : [set t : d.-tuple (measurableTypeR R) | Rle u (Rabs (paper_main_weighted_square d a
    (gaussian_covariance_image d d paper_main_gaussian_identity (tval t))))] =
    [set x | Rle u (Rabs (paper_main_weighted_square d a (tval x)))].
  apply/seteqP; split => t /=;
    by rewrite (paper_main_gaussian_identity_image d (tval t) (size_tuple t)).
exact: paper_main_weighted_square_two_sided_tail.
Qed.
