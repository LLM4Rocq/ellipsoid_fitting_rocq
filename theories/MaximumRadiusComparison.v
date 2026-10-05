(* Port of theories/MaximumRadiusComparison.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and the text of its statement, except that the logarithm is written
   Rpower.ln. It is Stdlib's logarithm, the one that a bare ln denotes in the
   original. This module imports no MathComp library, and none of its
   imports re-exports one, so a bare ln would also mean Rpower.ln here. The
   qualified name keeps the statements unambiguous for importers that load
   MathComp's exp module, where a bare ln is MathComp's exp.ln, and it
   matches the ported GaussianJensen, GaussianCenteredChiSquare and
   RadiusAlgebra, which write Rpower.ln. The same qualification is made in
   the proofs. The Stdlib lemmas ln_mult, ln_1 and ln_increasing are about
   Rpower.ln. Otherwise the proofs are the original ones, word for word, and
   the import line "From Coquelicot Require Import Coquelicot." is dropped:
   no statement or proof here names a Coquelicot notion. (0<N)%nat and
   (0<d)%nat are Peano's lt, and the operations on R are Stdlib's.

   The meaning of the statements follows the ported definitions they use.
   gaussian_iterated_integrable and gaussian_iterated_expectation
   (GaussianProductDefinitions) now ask at each level for Lebesgue
   integrability over the line against the Gaussian kernel, and take
   Lebesgue integrals, in place of improper Riemann integrals (difference 4
   of analysis/README.md). gaussian_sum_squares and gaussian_maximum_radius
   (GaussianProductDefinitions, MaximumRadiusDefinitions) have their
   original texts and involve no integral. The functions integrated here,
   gaussian_sum_squares, gaussian_maximum_radius, x |-> x*x plus a
   constant, and the exponential sums of gaussian_radius_exponential_sum
   for 0 < t < 1/2, are continuous and bounded by a constant times a
   polynomial or Gaussian integrable exponential weight, so they are
   absolutely integrable against the kernel, where the Lebesgue and the
   improper Riemann values agree. The statements are therefore the same as
   before, about the same numbers. This agreement is a mathematical argument
   and is not proved in Rocq. No statement is weakened.

   The proofs use gaussian_maximum_radius_domain,
   maximum_radius_squares_continuous, maximum_radius_squares_nonnegative and
   maximum_radius_squares_polynomial (ported MaximumRadiusRegularity),
   gaussian_radius_exponential_sum_moment and
   gaussian_maximum_radius_exponential_majorant (ported
   MaximumRadiusMoments), gaussian_iterated_constant, gaussian_iterated_add
   and gaussian_iterated_expectation_ext (ported GaussianProduct),
   gaussian_iterated_log_majorant_bound (ported GaussianJensen),
   gaussian_centered_chisquare_exponential_moment and
   gaussian_centered_chisquare_log_bound (ported GaussianCenteredChiSquare),
   gaussian_iterated_polynomial_integrable (ported
   GaussianCoordinateMarginals), gaussian_expectation_add and
   gaussian_expectation_of_constant (ported GaussianExpectation),
   gaussian_standard_moments and gaussian_power_moments (ported
   GaussianIntegration), and gaussian_radius_parameter (ported
   RadiusAlgebra). Their statements are the original texts, up to the
   Rpower.ln qualification.

   Assumptions. Stdlib defines Rpower.ln through ln_exists, whose proof uses
   Stdlib.Logic.Classical_Prop.classic, so the theorems of this module carry
   that axiom besides the seven of analysis/README.md. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions GaussianProduct
  GaussianCoordinateWeightDefinitions GaussianCoordinateMarginals GaussianIntegration
  GaussianCenteredChiSquare GaussianJensen RadiusAlgebra
  MaximumRadiusDefinitions MaximumRadiusRegularity MaximumRadiusMoments.
Import ListNotations.
Open Scope R_scope.

Theorem gaussian_maximum_radius_parameter_bound N d t :
  (0<N)%nat -> 0<t<1/2 ->
  gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) <=
    INR d + Rpower.ln (INR N)/t + INR d*t/(1-2*t).
Proof.
  intros HN Ht.
  pose proof (proj1 (gaussian_maximum_radius_domain N d)) as HM.
  destruct (gaussian_iterated_constant (N*d) (-INR d)) as [HC HCE].
  destruct (gaussian_iterated_add (N*d) (gaussian_maximum_radius N d)
    (fun _ => -INR d) HM HC) as [HCI HCIE].
  destruct (gaussian_radius_exponential_sum_moment N d t ltac:(lra)) as [HG HGE].
  pose proof (gaussian_iterated_log_majorant_bound (N*d)
    (fun xs => gaussian_maximum_radius N d xs - INR d)
    (gaussian_radius_exponential_sum N d t) t ltac:(lra) HCI HG) as HB.
  assert (Hexp : forall xs, length xs=(N*d)%nat ->
    exp (t*(gaussian_maximum_radius N d xs-INR d)) <=
      gaussian_radius_exponential_sum N d t xs).
  { intros xs Hxs; apply gaussian_maximum_radius_exponential_majorant; [exact HN|lra]. }
  specialize (HB Hexp).
  change (gaussian_iterated_expectation (N*d)
    (fun xs => gaussian_maximum_radius N d xs + -INR d) <=
      Rpower.ln (gaussian_iterated_expectation (N*d) (gaussian_radius_exponential_sum N d t))/t) in HB.
  rewrite HCIE, HCE, HGE in HB.
  assert (HNpos : 0<INR N) by (apply lt_0_INR; exact HN).
  assert (HZpos : 0<gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d)))).
  { destruct (gaussian_centered_chisquare_exponential_moment d t ltac:(lra))
      as [_ [_ [_ HE]]]; rewrite HE.
    apply Rmult_lt_0_compat; [apply exp_pos|apply pow_lt].
    apply Rdiv_lt_0_compat; [lra|apply sqrt_lt_R0; lra]. }
  rewrite ln_mult in HB by assumption.
  pose proof (gaussian_centered_chisquare_log_bound d t ltac:(lra)) as HL.
  assert (Hfrac : Rpower.ln (gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d)))) / t <=
      INR d*t/(1-2*t)).
  { apply (Rmult_le_reg_r t); [lra|].
    replace (Rpower.ln (gaussian_iterated_expectation d
      (fun xs => exp (t*(gaussian_sum_squares xs-INR d))))/t*t) with
      (Rpower.ln (gaussian_iterated_expectation d
        (fun xs => exp (t*(gaussian_sum_squares xs-INR d))))) by (field; lra).
    replace (INR d*t/(1-2*t)*t) with (INR d*t*t/(1-2*t)) by (field; lra).
    exact HL. }
  unfold Rdiv in HB, Hfrac |- *; nra.
Qed.

Lemma maximum_radius_squares_integrable d :
  gaussian_iterated_integrable d gaussian_sum_squares.
Proof.
  apply (gaussian_iterated_polynomial_integrable d gaussian_sum_squares (INR d) 2).
  - apply maximum_radius_squares_continuous.
  - split; [apply pos_INR|].
    intros xs Hxs; rewrite Rabs_pos_eq by apply maximum_radius_squares_nonnegative.
    rewrite <- Hxs; apply maximum_radius_squares_polynomial.
Qed.

Theorem gaussian_sum_squares_expectation d :
  gaussian_iterated_expectation d gaussian_sum_squares = INR d.
Proof.
  induction d as [|d IH]; [reflexivity|].
  change (gaussian_expectation (fun x =>
    gaussian_iterated_expectation d (fun xs => x*x+gaussian_sum_squares xs)) = INR (S d)).
  assert (HE : forall x, gaussian_iterated_expectation d
    (fun xs => x*x+gaussian_sum_squares xs) = x*x+INR d).
  { intro x; destruct (gaussian_iterated_constant d (x*x)) as [HC HCE].
    rewrite (proj2 (gaussian_iterated_add d (fun _ => x*x) gaussian_sum_squares
      HC (maximum_radius_squares_integrable d))), HCE, IH; reflexivity. }
  assert (Hfun : (fun x => gaussian_iterated_expectation d
    (fun xs => x*x+gaussian_sum_squares xs)) = (fun x => x^2+INR d)).
  { apply functional_extensionality; intro x; rewrite HE; simpl; ring. }
  rewrite Hfun, gaussian_expectation_add.
  - rewrite gaussian_expectation_of_constant, (proj1 (proj2 (proj2 gaussian_standard_moments))), S_INR; ring.
  - exact (proj1 (proj2 (gaussian_power_moments 2))).
  - exact (proj2 (proj1 (gaussian_iterated_constant 1 (INR d)))).
Qed.

Theorem gaussian_maximum_radius_single d :
  gaussian_iterated_expectation (1*d) (gaussian_maximum_radius 1 d) = INR d.
Proof.
  replace (1*d)%nat with d by lia.
  transitivity (gaussian_iterated_expectation d gaussian_sum_squares).
  - apply gaussian_iterated_expectation_ext; intros xs Hxs.
    change (Rmax (gaussian_sum_squares (firstn d xs)) 0 = gaussian_sum_squares xs).
    rewrite <- Hxs, firstn_all, Rmax_left by apply maximum_radius_squares_nonnegative.
    reflexivity.
  - apply gaussian_sum_squares_expectation.
Qed.

Theorem gaussian_maximum_radius_expected_bound N d :
  (0<N)%nat -> (0<d)%nat ->
  gaussian_iterated_expectation (N*d) (gaussian_maximum_radius N d) <=
    INR d + 2*sqrt (INR d * Rpower.ln (INR N)) + 2*Rpower.ln (INR N).
Proof.
  intros HN Hd; destruct (Nat.eq_dec N 1) as [->|HN1].
  - rewrite gaussian_maximum_radius_single; simpl INR; rewrite ln_1, Rmult_0_r, sqrt_0; lra.
  - assert (HD : 0<INR d) by (apply lt_0_INR; exact Hd).
    assert (HL : 0<Rpower.ln (INR N)).
    { pose proof (lt_INR 1 N ltac:(lia)) as H.
      pose proof (ln_increasing 1 (INR N) ltac:(lra) H) as HH.
      rewrite ln_1 in HH; exact HH. }
    destruct (gaussian_radius_parameter (INR d) (Rpower.ln (INR N)) HD HL) as [Ht HE].
    pose proof (gaussian_maximum_radius_parameter_bound N d
      (sqrt (Rpower.ln (INR N))/(sqrt (INR d)+2*sqrt (Rpower.ln (INR N)))) HN Ht) as HB.
    lra.
Qed.
