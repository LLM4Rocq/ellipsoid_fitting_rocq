(* Exchange of two blocks of coordinates in the iterated Gaussian
   expectation of Gaussian.Iterated.Definitions. For F continuous in d + e
   coordinates (finite_joint_continuous) and polynomially bounded
   (finite_polynomial_bound), the expectation of F can be computed by
   integrating the last e coordinates first or the first d coordinates
   first (gaussian_block_exchange_signed). gaussian_block_exchange adds the
   same identities for Rabs (F zs), the integrability of every function
   integrated on the way (gaussian_list_domain), and the continuity and
   polynomial bounds of both partial expectations. The expectations are
   iterated Lebesgue integrals. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Gaussian.Iterated.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions
  Gaussian.Iterated.SuffixMarginalDefinitions Joint.Definitions
  Gaussian.Iterated.BlockRotation.
From EllipsoidFitting Require Import Gaussian.Iterated.Expectation
  Gaussian.Iterated.LastIntegration Analysis.CoordinateTopology
  Gaussian.Iterated.PolynomialGrowth Gaussian.Iterated.SuffixAlgebra
  Gaussian.Iterated.SuffixRegularity Analysis.CoordinatePermutationContinuity.
From EllipsoidFitting Require Gaussian.Coordinate.Weights.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_list_domain_of_integrable d F :
  gaussian_iterated_integrable d F -> gaussian_iterated_absolutely_integrable d F ->
  gaussian_list_domain d F.
Proof.
  intros HI HA; split; [exact HI|]; split; [exact HA|]; split;
    apply gaussian_iterated_has_expectation_correct; assumption.
Qed.

Theorem gaussian_list_domain_polynomial d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_list_domain d F.
Proof.
  intros HC HB; apply gaussian_list_domain_of_integrable.
  - exact (gaussian_iterated_polynomial_integrable d F C p HC HB).
  - exact (gaussian_iterated_polynomial_absolutely_integrable d F C p HC HB).
Qed.

Lemma gaussian_list_domain_ext d F G :
  (forall xs, length xs = d -> F xs = G xs) ->
  gaussian_list_domain d F -> gaussian_list_domain d G.
Proof.
  intros HE [HI [HA _]]; apply gaussian_list_domain_of_integrable.
  - eapply gaussian_iterated_integrable_ext; [exact HE|exact HI].
  - eapply gaussian_iterated_integrable_ext; [|exact HA].
    intros xs Hxs; simpl; rewrite HE by exact Hxs; reflexivity.
Qed.

Theorem gaussian_block_suffix_domains d e F C p :
  finite_joint_continuous (d+e) F -> finite_polynomial_bound (d+e) C p F ->
  (forall xs, length xs = d -> gaussian_list_domain e (fun ys => F (xs++ys))) /\
  gaussian_list_domain d (gaussian_suffix_marginal e F) /\
  finite_joint_continuous d (gaussian_suffix_marginal e F) /\
  finite_polynomial_bound d (C*gaussian_coordinate_weight_moment p^e) p
    (gaussian_suffix_marginal e F).
Proof.
  intros HC HB.
  destruct (gaussian_suffix_marginal_regular d e F C p HC HB) as [HMC HMB].
  split.
  - intros xs Hxs; apply (gaussian_list_domain_polynomial e _ (C*gaussian_coordinate_product_weight p xs) p).
    + apply finite_joint_continuous_prefix; rewrite Hxs; exact HC.
    + apply finite_polynomial_bound_prefix; rewrite Hxs; exact HB.
  - split.
    + exact (gaussian_list_domain_polynomial d _ _ p HMC HMB).
    + split; assumption.
Qed.

Lemma finite_polynomial_bound_suffix d F C p ys :
  finite_polynomial_bound (d+length ys) C p F ->
  finite_polynomial_bound d (C*gaussian_coordinate_product_weight p ys) p
    (fun xs => F (xs++ys)).
Proof.
  intros [HC HB]; split.
  - apply Rmult_le_pos; [exact HC|apply Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_nonnegative].
  - intros xs Hxs; specialize (HB (xs++ys) ltac:(rewrite length_app, Hxs; reflexivity)).
    rewrite Gaussian.Coordinate.Weights.gaussian_coordinate_product_weight_append in HB.
    replace (C*gaussian_coordinate_product_weight p ys*gaussian_coordinate_product_weight p xs)
      with (C*(gaussian_coordinate_product_weight p xs*gaussian_coordinate_product_weight p ys)) by ring.
    exact HB.
Qed.

Lemma gaussian_block_rotation_append e (xs ys : list R) : length ys = e ->
  skipn e (ys++xs) ++ firstn e (ys++xs) = xs++ys.
Proof.
  intros H; subst e.
  rewrite skipn_app, firstn_app, skipn_all, firstn_all, Nat.sub_diag.
  simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma gaussian_block_reverse_marginal d e F ys : length ys = e ->
  gaussian_suffix_marginal d (fun zs => F (skipn e zs ++ firstn e zs)) ys =
  gaussian_iterated_expectation d (fun xs => F (xs++ys)).
Proof.
  intro Hys; unfold gaussian_suffix_marginal.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  rewrite gaussian_block_rotation_append by exact Hys; reflexivity.
Qed.

Theorem gaussian_block_prefix_domains d e F C p :
  finite_joint_continuous (d+e) F -> finite_polynomial_bound (d+e) C p F ->
  (forall ys, length ys = e -> gaussian_list_domain d (fun xs => F (xs++ys))) /\
  gaussian_list_domain e (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))) /\
  finite_joint_continuous e (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))) /\
  finite_polynomial_bound e (C*gaussian_coordinate_weight_moment p^d) p
    (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))).
Proof.
  intros HC HB.
  assert (HCr : finite_joint_continuous (e+d) F) by (rewrite Nat.add_comm; exact HC).
  assert (HBr : finite_polynomial_bound (e+d) C p F) by (rewrite Nat.add_comm; exact HB).
  destruct (gaussian_suffix_marginal_regular e d
    (fun zs => F (skipn e zs ++ firstn e zs)) C p
    (gaussian_block_rotation_continuous d e F HCr)
    (gaussian_block_rotation_polynomial_bound d e C p F HBr)) as [HMC HMB].
  assert (HCm : finite_joint_continuous e
    (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys)))).
  { eapply finite_joint_continuous_ext; [|exact HMC].
    intros ys Hys; apply gaussian_block_reverse_marginal; exact Hys. }
  assert (HBm : finite_polynomial_bound e (C*gaussian_coordinate_weight_moment p^d) p
    (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys)))).
  { eapply finite_polynomial_bound_ext; [|exact HMB].
    intros ys Hys; apply gaussian_block_reverse_marginal; exact Hys. }
  split.
  - intros ys Hys; apply (gaussian_list_domain_polynomial d _ (C*gaussian_coordinate_product_weight p ys) p).
    + apply finite_joint_continuous_suffix; rewrite Hys; exact HC.
    + apply finite_polynomial_bound_suffix; rewrite Hys; exact HB.
  - split.
    + exact (gaussian_list_domain_polynomial e _ _ p HCm HBm).
    + split; assumption.
Qed.

Theorem gaussian_block_exchange_signed d e F C p :
  finite_joint_continuous (d+e) F -> finite_polynomial_bound (d+e) C p F ->
  gaussian_iterated_expectation (d+e) F =
    gaussian_iterated_expectation d (fun xs => gaussian_iterated_expectation e (fun ys => F (xs++ys))) /\
  gaussian_iterated_expectation (d+e) F =
    gaussian_iterated_expectation e (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))).
Proof.
  intros HC HB; split.
  - apply gaussian_iterated_suffix_expectation.
  - rewrite (Nat.add_comm d e).
    assert (HCr : finite_joint_continuous (e+d) F) by (rewrite Nat.add_comm; exact HC).
    assert (HBr : finite_polynomial_bound (e+d) C p F) by (rewrite Nat.add_comm; exact HB).
    transitivity (gaussian_iterated_expectation (e+d) (fun zs => F (skipn e zs ++ firstn e zs))).
    + exact (gaussian_iterated_block_rotation d e F C p HCr HBr).
    + rewrite gaussian_iterated_suffix_expectation.
      apply gaussian_iterated_expectation_ext; intros ys Hys.
      apply gaussian_block_reverse_marginal; exact Hys.
Qed.

Theorem gaussian_block_exchange d e F C p :
  finite_joint_continuous (d+e) F -> finite_polynomial_bound (d+e) C p F ->
  gaussian_list_domain (d+e) F /\
  (forall xs, length xs = d -> gaussian_list_domain e (fun ys => F (xs++ys))) /\
  (forall ys, length ys = e -> gaussian_list_domain d (fun xs => F (xs++ys))) /\
  List.Forall (gaussian_list_domain d)
    [gaussian_suffix_marginal e F; gaussian_suffix_marginal e (fun zs => Rabs (F zs))] /\
  List.Forall (gaussian_list_domain e)
    [(fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys)));
     (fun ys => gaussian_iterated_expectation d (fun xs => Rabs (F (xs++ys))))] /\
  finite_joint_continuous d (gaussian_suffix_marginal e F) /\
  finite_polynomial_bound d (C*gaussian_coordinate_weight_moment p^e) p (gaussian_suffix_marginal e F) /\
  finite_joint_continuous e (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))) /\
  finite_polynomial_bound e (C*gaussian_coordinate_weight_moment p^d) p
    (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))) /\
  gaussian_iterated_expectation (d+e) F =
    gaussian_iterated_expectation d (fun xs => gaussian_iterated_expectation e (fun ys => F (xs++ys))) /\
  gaussian_iterated_expectation (d+e) F =
    gaussian_iterated_expectation e (fun ys => gaussian_iterated_expectation d (fun xs => F (xs++ys))) /\
  gaussian_iterated_expectation (d+e) (fun zs => Rabs (F zs)) =
    gaussian_iterated_expectation d (fun xs => gaussian_iterated_expectation e (fun ys => Rabs (F (xs++ys)))) /\
  gaussian_iterated_expectation (d+e) (fun zs => Rabs (F zs)) =
    gaussian_iterated_expectation e (fun ys => gaussian_iterated_expectation d (fun xs => Rabs (F (xs++ys)))).
Proof.
  intros HC HB.
  destruct (gaussian_block_suffix_domains d e F C p HC HB) as [HS [HM [HMC HMB]]].
  destruct (gaussian_block_prefix_domains d e F C p HC HB) as [HT [HN [HNC HNB]]].
  pose proof (finite_joint_continuous_abs (d+e) F HC) as HCa.
  pose proof (finite_polynomial_bound_abs (d+e) C p F HB) as HBa.
  destruct (gaussian_block_suffix_domains d e (fun zs => Rabs (F zs)) C p HCa HBa) as [_ [HMa _]].
  destruct (gaussian_block_prefix_domains d e (fun zs => Rabs (F zs)) C p HCa HBa) as [_ [HNa _]].
  destruct (gaussian_block_exchange_signed d e F C p HC HB) as [HE1 HE2].
  destruct (gaussian_block_exchange_signed d e (fun zs => Rabs (F zs)) C p HCa HBa) as [HA1 HA2].
  split; [exact (gaussian_list_domain_polynomial (d+e) F C p HC HB)|].
  split; [exact HS|]; split; [exact HT|].
  split.
  - constructor; [exact HM|]; constructor; [exact HMa|constructor].
  - split.
    + constructor; [exact HN|]; constructor; [exact HNa|constructor].
    + split; [exact HMC|]; split; [exact HMB|].
      split; [exact HNC|]; split; [exact HNB|].
      repeat split; assumption.
Qed.

