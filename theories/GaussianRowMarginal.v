(* Port of theories/GaussianRowMarginal.v from Coquelicot to
   MathComp-Analysis.

   Every theorem and lemma keeps its name, its arguments in the same order,
   and its text. The only change to the file is that the Coquelicot import
   line is dropped: no statement or proof here names a Coquelicot notion.
   The proofs are the original ones, word for word.

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions) and
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) have the
   original text. gaussian_iterated_integrable,
   gaussian_iterated_absolutely_integrable and
   gaussian_iterated_has_expectation (GaussianProductDefinitions) now ask at
   each level for the Lebesgue integrability over the line of the outer
   function times the Gaussian kernel, and record Lebesgue integrals
   against gaussian_density, in place of improper Riemann integrals
   (difference 4 of analysis/README.md). row_prefixes_gaussian_expectation
   is an equality of iterated expectations that holds for every F, as in
   the original. row_prefixes_gaussian_domain assumes continuity and a
   polynomial bound, under which every integrand is absolutely integrable
   against the kernel, and concludes the Lebesgue counterparts of the
   original conclusions. No statement is weakened.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So ++, length, firstn, skipn, the %nat scope and the
   operations on R are Stdlib's, as in the original. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianProduct GaussianLastDefinitions GaussianLastIntegration
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianPermutationContinuity
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianCoordinateMarginals
  RowMarginalDefinitions RowPrefixes.
Import ListNotations.
Open Scope R_scope.

Theorem row_prefixes_gaussian_expectation N d D (F : list R->R) :
  gaussian_iterated_expectation (N*(d+D)) (fun xs=>F(row_prefixes N d D xs)) =
  gaussian_iterated_expectation (N*d) F.
Proof.
  revert F; induction N as [|N IH]; intro F; [reflexivity|].
  change (gaussian_iterated_expectation ((d+D)+N*(d+D))
    (fun xs=>F(row_prefixes (S N) d D xs)) = gaussian_iterated_expectation (d+N*d) F).
  rewrite (gaussian_iterated_suffix_expectation (d+D) (N*(d+D))).
  rewrite (gaussian_iterated_suffix_expectation d D).
  rewrite (gaussian_iterated_suffix_expectation d (N*d) F).
  apply gaussian_iterated_expectation_ext; intros front HF.
  unfold gaussian_suffix_marginal.
  transitivity (gaussian_iterated_expectation D
    (fun _=>gaussian_iterated_expectation (N*d) (fun ys=>F(front++ys)))).
  - apply gaussian_iterated_expectation_ext; intros ignored HI.
    transitivity (gaussian_iterated_expectation (N*(d+D))
      (fun tail=>F(front++row_prefixes N d D tail))).
    + apply gaussian_iterated_expectation_ext; intros tail HT.
      rewrite <- app_assoc, row_prefixes_first_block by assumption; reflexivity.
    + exact (IH (fun ys=>F(front++ys))).
  - exact (proj2 (gaussian_iterated_constant D _)).
Qed.

Theorem row_prefixes_continuous N d D F :
  finite_joint_continuous (N*d) F ->
  finite_joint_continuous (N*(d+D)) (fun xs=>F(row_prefixes N d D xs)).
Proof.
  apply finite_joint_continuous_list_map.
  - apply row_prefixes_length.
  - intros e xs ys Hx Hy H; apply row_prefixes_forall2; exact H.
Qed.

Lemma row_product_weight_skipn_le p n xs :
  gaussian_coordinate_product_weight p (skipn n xs) <= gaussian_coordinate_product_weight p xs.
Proof.
  pose proof (gaussian_coordinate_product_weight_at_least_one p (firstn n xs)) as HF.
  pose proof (gaussian_coordinate_product_weight_nonnegative p (skipn n xs)) as HT.
  pose proof (gaussian_coordinate_product_weight_append p (firstn n xs) (skipn n xs)) as HE.
  rewrite firstn_skipn in HE; nra.
Qed.

Theorem row_prefixes_product_weight_le N d D p xs :
  gaussian_coordinate_product_weight p (row_prefixes N d D xs) <=
  gaussian_coordinate_product_weight p xs.
Proof.
  revert xs; induction N as [|N IH]; intro xs; simpl row_prefixes.
  - apply gaussian_coordinate_product_weight_at_least_one.
  - rewrite gaussian_coordinate_product_weight_append.
    pose proof (gaussian_coordinate_product_weight_nonnegative p (firstn d xs)) as HF.
    eapply Rle_trans.
    + apply Rmult_le_compat_l; [exact HF|apply IH].
    + pose proof (row_product_weight_skipn_le p D (skipn d xs)) as Hskip.
      rewrite skipn_skipn in Hskip.
      replace (d+D)%nat with (D+d)%nat by lia.
      pose proof (Rmult_le_compat_l _ _ _ HF Hskip) as Hmul.
      pose proof (gaussian_coordinate_product_weight_append p (firstn d xs) (skipn d xs)) as HE.
      rewrite firstn_skipn in HE; nra.
Qed.

Theorem row_prefixes_polynomial N d D C p F :
  finite_polynomial_bound (N*d) C p F ->
  finite_polynomial_bound (N*(d+D)) C p (fun xs=>F(row_prefixes N d D xs)).
Proof.
  intros [HC HB]; split; [exact HC|].
  intros xs HL; eapply Rle_trans.
  - apply HB; apply row_prefixes_length; exact HL.
  - apply Rmult_le_compat_l; [exact HC|apply row_prefixes_product_weight_le].
Qed.

Theorem row_prefixes_gaussian_domain N d D F C p :
  finite_joint_continuous (N*d) F -> finite_polynomial_bound (N*d) C p F ->
  gaussian_iterated_integrable (N*(d+D)) (fun xs=>F(row_prefixes N d D xs)) /\
  gaussian_iterated_absolutely_integrable (N*(d+D)) (fun xs=>F(row_prefixes N d D xs)) /\
  gaussian_iterated_has_expectation (N*(d+D)) (fun xs=>F(row_prefixes N d D xs))
    (gaussian_iterated_expectation (N*d) F) /\
  gaussian_iterated_has_expectation (N*(d+D)) (fun xs=>Rabs(F(row_prefixes N d D xs)))
    (gaussian_iterated_expectation (N*d) (fun xs=>Rabs(F xs))) /\
  gaussian_iterated_expectation (N*(d+D)) (fun xs=>F(row_prefixes N d D xs)) =
    gaussian_iterated_expectation (N*d) F /\
  gaussian_iterated_expectation (N*(d+D)) (fun xs=>Rabs(F(row_prefixes N d D xs))) =
    gaussian_iterated_expectation (N*d) (fun xs=>Rabs(F xs)).
Proof.
  intros HC HB.
  destruct (gaussian_iterated_polynomial_admissible (N*(d+D))
    (fun xs=>F(row_prefixes N d D xs)) C p
    (row_prefixes_continuous N d D F HC) (row_prefixes_polynomial N d D C p F HB))
    as [HI [HA [HV [HAV _]]]].
  rewrite row_prefixes_gaussian_expectation in HV.
  change (gaussian_iterated_has_expectation (N*(d+D))
    (fun xs=>Rabs(F(row_prefixes N d D xs)))
    (gaussian_iterated_expectation (N*(d+D))
      (fun xs=>(fun ys=>Rabs(F ys))(row_prefixes N d D xs)))) in HAV.
  rewrite row_prefixes_gaussian_expectation in HAV.
  repeat split; try assumption.
  - exact (row_prefixes_gaussian_expectation N d D F).
  - exact (row_prefixes_gaussian_expectation N d D (fun xs=>Rabs(F xs))).
Qed.
