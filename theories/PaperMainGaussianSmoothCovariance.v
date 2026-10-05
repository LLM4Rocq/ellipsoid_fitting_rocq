(* A weighted covariance inequality from Gaussian interpolation.
   The test f(x)g(y) must have the displayed C2 polynomial bounds. A
   pointwise upper bound for its mixed Hessian is transported through
   the coupling using the unchanged right Gaussian marginal. The
   specialization to g = exp(t f) is not supplied in this module. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateSteinDomains
  GaussianCovarianceDefinitions GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCovariancePath GaussianCovarianceDomains GaussianCovarianceEndpoints
  GaussianCovarianceComparison PaperMainGaussianCovarianceBounds
  PaperMainGaussianCovarianceMarginals PaperMainGaussianCovarianceCoupling.
Import ListNotations.
Open Scope R_scope.

Record paper_main_gaussian_smooth_test d F DF D2F C r : Prop := {
  pmgs_continuous : finite_joint_continuous d F;
  pmgs_derivative : forall a, (a < d)%coq_nat ->
    finite_coordinate_derivative d a F (DF a);
  pmgs_derivative_continuous : forall a, (a < d)%coq_nat ->
    finite_joint_continuous d (DF a);
  pmgs_second_derivative : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_coordinate_derivative d b (DF a) (D2F a b);
  pmgs_second_continuous : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_joint_continuous d (D2F a b);
  pmgs_bound : finite_polynomial_bound d C r F;
  pmgs_derivative_bound : forall a, (a < d)%coq_nat ->
    finite_polynomial_bound d C r (DF a);
  pmgs_second_bound : forall a b, (a < d)%coq_nat -> (b < d)%coq_nat ->
    finite_polynomial_bound d C r (D2F a b)
}.

Definition paper_main_gaussian_coupling_path d t :=
  gaussian_covariance_path (d + d)%coq_nat d (d + d)%coq_nat
    (paper_main_gaussian_duplicate d) paper_main_gaussian_identity t.

Definition paper_main_gaussian_right_loading d t (a k : nat) :=
  gaussian_covariance_coef d (d + d)%coq_nat
    (paper_main_gaussian_duplicate d) paper_main_gaussian_identity t (d + a)%coq_nat k.

Lemma paper_main_gaussian_image_right_block d p P xs :
  List.skipn d (gaussian_covariance_image (d + d)%coq_nat p P xs) =
  gaussian_covariance_image d p (fun a k => P (d + a)%coq_nat k) xs.
Proof.
apply (nth_ext _ _ 0 0).
- unfold gaussian_covariance_image; rewrite length_skipn !length_map_seq; lia.
- intros a Ha; unfold gaussian_covariance_image in *.
  rewrite length_skipn length_map_seq in Ha.
  assert (Had : (a < d)%coq_nat) by lia.
  rewrite nth_skipn_add.
  rewrite (nth_map_seq _ (d + d)%coq_nat (d + a)%coq_nat ltac:(lia)).
  rewrite (nth_map_seq _ d a Had); reflexivity.
Qed.

Lemma paper_main_gaussian_coupling_right_image d t xs :
  List.skipn d (paper_main_gaussian_coupling_path d t xs) =
  gaussian_covariance_image d (d + (d + d))%coq_nat
    (paper_main_gaussian_right_loading d t) xs.
Proof.
unfold paper_main_gaussian_coupling_path.
rewrite gaussian_covariance_path_linear.
change (List.skipn d (gaussian_covariance_image (d + d)%coq_nat (d + (d + d))%coq_nat
  (gaussian_covariance_coef d (d + d)%coq_nat
    (paper_main_gaussian_duplicate d) paper_main_gaussian_identity t) xs) =
  gaussian_covariance_image d (d + (d + d))%coq_nat
    (paper_main_gaussian_right_loading d t) xs).
apply paper_main_gaussian_image_right_block.
Qed.

Lemma paper_main_gaussian_coupling_right_covariance d t a b :
  0 <= t <= 1 -> (a < d)%coq_nat -> (b < d)%coq_nat ->
  gaussian_covariance_entry (d + (d + d))%coq_nat
    (paper_main_gaussian_right_loading d t) a b = paper_main_gaussian_identity b a.
Proof.
intros Ht Ha Hb.
change (gaussian_covariance_entry (d + (d + d))%coq_nat
  (gaussian_covariance_coef d (d + d)%coq_nat (paper_main_gaussian_duplicate d)
    paper_main_gaussian_identity t) (d + a)%coq_nat (d + b)%coq_nat =
  paper_main_gaussian_identity b a).
rewrite (paper_main_gaussian_path_covariance d (d + d)%coq_nat
  (paper_main_gaussian_duplicate d) paper_main_gaussian_identity t
  (d + a)%coq_nat (d + b)%coq_nat Ht).
pose proof (paper_main_gaussian_coupling_right d a b Ha Hb) as Heq.
unfold paper_main_gaussian_coupling_difference in Heq.
pose proof (paper_main_gaussian_duplicate_covariance d (d + a)%coq_nat (d + b)%coq_nat ltac:(lia)) as Hdup.
rewrite !paper_main_gaussian_fold_right in Hdup.
rewrite Hdup in Heq; rewrite Hdup.
nra.
Qed.

Theorem paper_main_gaussian_coupling_right_marginal d g Dg D2g C r t :
  paper_main_gaussian_smooth_test d g Dg D2g C r ->
  0 <= t <= 1 ->
  gaussian_iterated_integrable (d + (d + d))%coq_nat
    (fun xs => g (List.skipn d (paper_main_gaussian_coupling_path d t xs))) /\
  gaussian_iterated_expectation (d + (d + d))%coq_nat
    (fun xs => g (List.skipn d (paper_main_gaussian_coupling_path d t xs))) =
  gaussian_iterated_expectation d g.
Proof.
intros [Hc HD HDc HD2 HD2c Hb HDb HD2b] Ht.
assert (He : (fun xs => g (List.skipn d (paper_main_gaussian_coupling_path d t xs))) =
  (fun xs => g (gaussian_covariance_image d (d + (d + d))%coq_nat
    (paper_main_gaussian_right_loading d t) xs))).
{ apply FunctionalExtensionality.functional_extensionality; intros xs.
  rewrite paper_main_gaussian_coupling_right_image; reflexivity. }
rewrite He; split.
- exact (proj1 (gaussian_covariance_image_domain d (d + (d + d))%coq_nat
    (paper_main_gaussian_right_loading d t) g C r Hc Hb)).
- apply (paper_main_gaussian_standard_covariance_expectation d g Dg D2g C r
    Hc HD HDc HD2 HD2c Hb HDb HD2b).
  intros a b Ha Hb'; apply paper_main_gaussian_coupling_right_covariance; assumption.
Qed.

Theorem paper_main_gaussian_weighted_covariance_bound d (f g : list R -> R)
    DF D2F C r Dg D2g Cg rg B :
  paper_main_gaussian_smooth_test (d + d)%coq_nat
    (fun zs => f (List.firstn d zs) * g (List.skipn d zs)) DF D2F C r ->
  paper_main_gaussian_smooth_test d g Dg D2g Cg rg ->
  gaussian_iterated_integrable d f ->
  (forall zs, List.length zs = (d + d)%coq_nat ->
    finite_sum (fun a => D2F a (d + a)%coq_nat zs + D2F (d + a)%coq_nat a zs)
      (List.seq 0 d) <= 2 * B * g (List.skipn d zs)) ->
  gaussian_iterated_expectation d (fun xs => f xs * g xs) -
    gaussian_iterated_expectation d f * gaussian_iterated_expectation d g <=
  B * gaussian_iterated_expectation d g.
Proof.
intros HF Hg Hif Hbound.
destruct HF as [HFc HFD HFDc HFD2 HFD2c HFb HFDb HFD2b].
assert (Hig : gaussian_iterated_integrable d g).
{ destruct Hg as [Hgc HgD HgDc HgD2 HgD2c Hgb HgDb HgD2b].
  exact (proj1 (gaussian_coordinate_polynomial_domain d g Cg rg Hgc Hgb)). }
set (F := fun zs => f (List.firstn d zs) * g (List.skipn d zs)).
assert (Hend : gaussian_iterated_expectation d (fun xs =>
  F (gaussian_covariance_image (d + d)%coq_nat d (paper_main_gaussian_duplicate d) xs)) -
  gaussian_iterated_expectation (d + d)%coq_nat (fun ys =>
    F (gaussian_covariance_image (d + d)%coq_nat (d + d)%coq_nat paper_main_gaussian_identity ys)) <=
  B * gaussian_iterated_expectation d g).
{ apply (paper_main_covariance_expected_hessian_bound (d + d)%coq_nat F DF D2F C r
    HFc HFD HFDc HFD2 HFD2c HFb HFDb HFD2b).
  intros t Ht.
  assert (HiH : forall a b, (a < (d + d)%coq_nat)%coq_nat -> (b < (d + d)%coq_nat)%coq_nat ->
    gaussian_iterated_integrable (d + (d + d))%coq_nat
      (fun zs => D2F a b (paper_main_gaussian_coupling_path d t zs))).
  { intros a b Ha Hb.
    exact (proj1 (gaussian_covariance_path_domain (d + d)%coq_nat d (d + d)%coq_nat
      (paper_main_gaussian_duplicate d) paper_main_gaussian_identity
      (D2F a b) C r t ltac:(lra) (HFD2c a b Ha Hb) (HFD2b a b Ha Hb))). }
  destruct (gaussian_covariance_pairing_expectation (d + d)%coq_nat d (d + d)%coq_nat
    (paper_main_gaussian_duplicate d) paper_main_gaussian_identity D2F t HiH) as [Hi HE].
  rewrite HE.
  destruct (paper_main_gaussian_coupling_right_marginal d g Dg D2g Cg rg t Hg ltac:(lra))
    as [Him HEm].
  pose proof (gaussian_iterated_scale (d + (d + d))%coq_nat
    (fun xs => g (List.skipn d (paper_main_gaussian_coupling_path d t xs))) (2 * B) Him)
    as [His HEs].
  assert (Hmono : gaussian_iterated_expectation (d + (d + d))%coq_nat
    (fun zs => gaussian_covariance_pairing (d + d)%coq_nat d (d + d)%coq_nat
      (paper_main_gaussian_duplicate d) paper_main_gaussian_identity
      (fun a b => D2F a b (paper_main_gaussian_coupling_path d t zs))) <=
    gaussian_iterated_expectation (d + (d + d))%coq_nat
      (fun xs => 2 * B * g (List.skipn d (paper_main_gaussian_coupling_path d t xs)))).
  { apply gaussian_iterated_monotone; [exact Hi|exact His|].
    intros zs Hzs; rewrite paper_main_gaussian_coupling_pairing.
    apply Hbound; unfold paper_main_gaussian_coupling_path, gaussian_covariance_path.
    apply length_map_seq. }
  rewrite HEs HEm in Hmono.
  rewrite <- Rmult_assoc; exact Hmono. }
assert (Hone : gaussian_iterated_expectation d (fun xs =>
  F (gaussian_covariance_image (d + d)%coq_nat d (paper_main_gaussian_duplicate d) xs)) =
  gaussian_iterated_expectation d (fun xs => f xs * g xs)).
{ apply gaussian_iterated_expectation_ext; intros xs Hxs; unfold F.
  rewrite (paper_main_gaussian_duplicate_image d xs Hxs).
  rewrite <- Hxs; rewrite firstn_app_exact skipn_app_exact; reflexivity. }
assert (Hzero : gaussian_iterated_expectation (d + d)%coq_nat (fun ys =>
  F (gaussian_covariance_image (d + d)%coq_nat (d + d)%coq_nat paper_main_gaussian_identity ys)) =
  gaussian_iterated_expectation (d + d)%coq_nat F).
{ apply gaussian_iterated_expectation_ext; intros ys Hys.
  rewrite (paper_main_gaussian_identity_image (d + d)%coq_nat ys Hys); reflexivity. }
rewrite Hone Hzero in Hend.
unfold F in Hend; rewrite (paper_main_gaussian_independent_product d f g Hif Hig) in Hend.
exact Hend.
Qed.
