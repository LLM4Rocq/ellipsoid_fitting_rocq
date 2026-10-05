(* Port of theories/MaximumRadiusMoments.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The only change to the file is that the import line
   "From Coquelicot Require Import Coquelicot." is dropped: no statement or
   proof here names a Coquelicot notion. The proofs are the original ones,
   word for word.

   The meaning of the statements follows the ported definitions they use.
   gaussian_iterated_integrable and gaussian_iterated_expectation
   (GaussianProductDefinitions) now ask at each level for Lebesgue
   integrability over the line against the Gaussian kernel, and take
   Lebesgue integrals, in place of improper Riemann integrals (difference 4
   of analysis/README.md). gaussian_sum_squares, gaussian_maximum_radius and
   gaussian_radius_exponential_sum (GaussianProductDefinitions,
   MaximumRadiusDefinitions) have their original texts and involve no
   integral. maximum_radius_firstn_append, maximum_radius_skipn_append,
   gaussian_radius_exponential_sum_nonnegative and
   gaussian_maximum_radius_exponential_majorant involve no integral either,
   and say exactly what they said. The integrands of
   gaussian_radius_exponential_sum_moment are nonnegative, continuous and
   Gaussian integrable for t < 1/2, so they are absolutely integrable and
   the Lebesgue and improper Riemann values agree on them. No statement is
   weakened.

   The proofs use gaussian_iterated_constant, gaussian_iterated_add,
   gaussian_iterated_integrable_ext and gaussian_iterated_expectation_ext
   (ported GaussianProduct), gaussian_iterated_suffix_integrable and
   gaussian_iterated_suffix_expectation (ported GaussianLastIntegration),
   gaussian_centered_chisquare_exponential_moment (ported
   GaussianCenteredChiSquare) and maximum_radius_squares_nonnegative (ported
   MaximumRadiusRegularity), whose statements are the original texts.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So firstn, skipn, ++, length, the %nat scope and the
   operations on R are Stdlib's, as in the original. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions GaussianProduct
  GaussianLastDefinitions GaussianLastIntegration GaussianCenteredChiSquare
  MaximumRadiusDefinitions MaximumRadiusRegularity.
Import ListNotations.
Open Scope R_scope.

Lemma maximum_radius_firstn_append d (xs ys : list R) :
  length xs=d -> firstn d (xs++ys)=xs.
Proof.
  intro H; rewrite <- H, firstn_app, firstn_all, Nat.sub_diag; simpl; apply app_nil_r.
Qed.
Lemma maximum_radius_skipn_append d (xs ys : list R) :
  length xs=d -> skipn d (xs++ys)=ys.
Proof. intro H; rewrite <- H, skipn_app, skipn_all, Nat.sub_diag; reflexivity. Qed.

Lemma gaussian_iterated_prefix_lift d k F :
  gaussian_iterated_integrable d F ->
  gaussian_iterated_integrable (d+k) (fun xs => F (firstn d xs)) /\
  gaussian_iterated_expectation (d+k) (fun xs => F (firstn d xs)) =
    gaussian_iterated_expectation d F.
Proof.
  intro HI.
  assert (HE : forall xs, length xs=d ->
    gaussian_suffix_marginal k (fun zs => F (firstn d zs)) xs = F xs).
  { intros xs Hxs; unfold gaussian_suffix_marginal.
    transitivity (gaussian_iterated_expectation k (fun _ => F xs)).
    - apply gaussian_iterated_expectation_ext; intros ys Hys.
      rewrite maximum_radius_firstn_append by exact Hxs; reflexivity.
    - exact (proj2 (gaussian_iterated_constant k (F xs))). }
  split.
  - apply gaussian_iterated_suffix_integrable; split.
    + intros xs Hxs; apply gaussian_iterated_integrable_ext with (F := fun _ => F xs).
      * intros ys Hys; rewrite maximum_radius_firstn_append by exact Hxs; reflexivity.
      * exact (proj1 (gaussian_iterated_constant k (F xs))).
    + apply gaussian_iterated_integrable_ext with (F := F); [|exact HI].
      intros xs Hxs; symmetry; apply HE, Hxs.
  - rewrite gaussian_iterated_suffix_expectation.
    apply gaussian_iterated_expectation_ext; exact HE.
Qed.

Lemma gaussian_iterated_suffix_lift d k F :
  gaussian_iterated_integrable k F ->
  gaussian_iterated_integrable (d+k) (fun xs => F (skipn d xs)) /\
  gaussian_iterated_expectation (d+k) (fun xs => F (skipn d xs)) =
    gaussian_iterated_expectation k F.
Proof.
  intro HI.
  assert (HE : forall xs, length xs=d ->
    gaussian_suffix_marginal k (fun zs => F (skipn d zs)) xs =
      gaussian_iterated_expectation k F).
  { intros xs Hxs; unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros ys Hys.
    rewrite maximum_radius_skipn_append by exact Hxs; reflexivity. }
  split.
  - apply gaussian_iterated_suffix_integrable; split.
    + intros xs Hxs; apply gaussian_iterated_integrable_ext with (F := F); [|exact HI].
      intros ys Hys; rewrite maximum_radius_skipn_append by exact Hxs; reflexivity.
    + apply gaussian_iterated_integrable_ext with
        (F := fun _ => gaussian_iterated_expectation k F).
      * intros xs Hxs; symmetry; apply HE, Hxs.
      * exact (proj1 (gaussian_iterated_constant d (gaussian_iterated_expectation k F))).
  - rewrite gaussian_iterated_suffix_expectation.
    transitivity (gaussian_iterated_expectation d (fun _ => gaussian_iterated_expectation k F)).
    + apply gaussian_iterated_expectation_ext; exact HE.
    + exact (proj2 (gaussian_iterated_constant d (gaussian_iterated_expectation k F))).
Qed.

Theorem gaussian_radius_exponential_sum_moment N d t :
  t<1/2 ->
  gaussian_iterated_integrable (N*d) (gaussian_radius_exponential_sum N d t) /\
  gaussian_iterated_expectation (N*d) (gaussian_radius_exponential_sum N d t) =
    INR N * gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d))).
Proof.
  intro Ht; induction N as [|N [HI HE]].
  - split; [exact I|simpl; ring].
  - destruct (gaussian_centered_chisquare_exponential_moment d t Ht) as [HC _].
    destruct (gaussian_iterated_prefix_lift d (N*d)
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d))) HC) as [HP HPE].
    destruct (gaussian_iterated_suffix_lift d (N*d)
      (gaussian_radius_exponential_sum N d t) HI) as [HS HSE].
    destruct (gaussian_iterated_add (d+N*d) _ _ HP HS) as [HA HAE].
    split; [exact HA|].
    change (gaussian_iterated_expectation (d+N*d)
      (fun xs => exp (t*(gaussian_sum_squares (firstn d xs)-INR d)) +
        gaussian_radius_exponential_sum N d t (skipn d xs)) =
      INR (S N) * gaussian_iterated_expectation d
        (fun xs => exp (t*(gaussian_sum_squares xs-INR d)))).
    rewrite HAE, HPE, HSE, HE, S_INR; ring.
Qed.

Lemma gaussian_radius_exponential_sum_nonnegative N d t xs :
  0 <= gaussian_radius_exponential_sum N d t xs.
Proof.
  revert xs; induction N; intro xs; simpl; [lra|].
  pose proof (exp_pos (t*(gaussian_sum_squares (firstn d xs)-INR d))).
  pose proof (IHN (skipn d xs)); lra.
Qed.

Theorem gaussian_maximum_radius_exponential_majorant N d t xs :
  (0<N)%nat -> 0<=t ->
  exp (t*(gaussian_maximum_radius N d xs-INR d)) <=
    gaussian_radius_exponential_sum N d t xs.
Proof.
  revert xs; induction N as [|N IH]; intros xs HN Ht; [lia|].
  destruct N as [|N].
  - simpl. rewrite Rmax_left by apply maximum_radius_squares_nonnegative; lra.
  - change (exp (t*(Rmax (gaussian_sum_squares (firstn d xs))
      (gaussian_maximum_radius (S N) d (skipn d xs))-INR d)) <=
      exp (t*(gaussian_sum_squares (firstn d xs)-INR d)) +
      gaussian_radius_exponential_sum (S N) d t (skipn d xs)).
    specialize (IH (skipn d xs) ltac:(lia) Ht).
    pose proof (gaussian_radius_exponential_sum_nonnegative (S N) d t (skipn d xs)) as Hsum.
    pose proof (exp_pos (t*(gaussian_sum_squares (firstn d xs)-INR d))) as Hexp.
    unfold Rmax; destruct Rle_dec; lra.
Qed.
