(* The exponential moments of a chi-square variable with d degrees of
   freedom. gaussian_chisquare_exponential_moment: for t < 1/2, the iterated
   Gaussian expectation of exp (t * (x_1^2 + ... + x_d^2)) exists, each
   level being a Lebesgue integral over the line, and equals
   (1 / sqrt (1 - 2 t)) ^ d. The proof writes the integrand as a product of
   one-dimensional factors (gaussian_chisquare_exponential_product) and uses
   the one-dimensional moment of Gaussian.QuadraticMGF. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Kernel
  Gaussian.Mass Gaussian.Expectation Gaussian.QuadraticMGF
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_chisquare_exponential_product d t xs :
  length xs = d ->
  exp (t * gaussian_sum_squares xs) =
    gaussian_separable_product (repeat (fun x => exp (t * (x*x))) d) xs.
Proof.
  revert xs; induction d as [|d IH]; intros xs Hxs; destruct xs as [|x xs]; simpl in *; try discriminate.
  - rewrite Rmult_0_r, exp_0; reflexivity.
  - replace (t * (x*x + gaussian_sum_squares xs)) with
      (t * (x*x) + t * gaussian_sum_squares xs) by ring.
    rewrite exp_plus, (IH xs ltac:(lia)); reflexivity.
Qed.

Lemma gaussian_product_expectations_repeat f d :
  gaussian_product_expectations (repeat f d) = gaussian_expectation f ^ d.
Proof. induction d; simpl; [reflexivity | now rewrite IHd]. Qed.

Theorem gaussian_chisquare_exponential_moment d t :
  t < 1/2 ->
  gaussian_iterated_integrable d (fun xs => exp (t * gaussian_sum_squares xs)) /\
  gaussian_iterated_absolutely_integrable d (fun xs => exp (t * gaussian_sum_squares xs)) /\
  gaussian_iterated_has_expectation d (fun xs => exp (t * gaussian_sum_squares xs))
    ((1 / sqrt (1-2*t)) ^ d) /\
  gaussian_iterated_expectation d (fun xs => exp (t * gaussian_sum_squares xs)) =
    (1 / sqrt (1-2*t)) ^ d.
Proof.
  intro Ht.
  set (f := fun x => exp (t * (x*x))).
  assert (Hf : List.Forall gaussian_integral_exists (repeat f d)).
  { induction d as [|d IH]; simpl; [constructor |].
    constructor; [apply gaussian_quadratic_exponential_integrable; exact Ht |exact IH]. }
  assert (Habs : List.Forall gaussian_absolutely_integrable (repeat f d)).
  { clear Hf; induction d as [|d IH]; simpl; [constructor |].
    constructor; [apply gaussian_quadratic_exponential_absolute_integrable; exact Ht |exact IH]. }
  destruct (gaussian_separable_product_integral (repeat f d) Hf Habs) as [HI [HA [HV HE]]].
  rewrite repeat_length in HI, HA, HE.
  assert (Hext : forall xs, length xs = d ->
    gaussian_separable_product (repeat f d) xs = exp (t * gaussian_sum_squares xs)).
  { intros xs Hxs; symmetry; apply gaussian_chisquare_exponential_product; exact Hxs. }
  assert (HIF : gaussian_iterated_integrable d (fun xs => exp (t * gaussian_sum_squares xs))).
  { apply gaussian_iterated_integrable_ext with (F := gaussian_separable_product (repeat f d)); assumption. }
  assert (HEF : gaussian_iterated_expectation d (fun xs => exp (t * gaussian_sum_squares xs)) =
    (1 / sqrt (1-2*t)) ^ d).
  { rewrite <- (gaussian_iterated_expectation_ext d _ _ Hext), HE,
      gaussian_product_expectations_repeat.
    unfold f; rewrite gaussian_quadratic_exponential_expectation by exact Ht; reflexivity. }
  split; [exact HIF |].
  split.
  - unfold gaussian_iterated_absolutely_integrable in *.
    apply gaussian_iterated_integrable_ext with
      (F := fun xs => Rabs (gaussian_separable_product (repeat f d) xs)); [|exact HA].
    intros xs Hxs; rewrite Hext by exact Hxs; reflexivity.
  - split; [rewrite <- HEF; apply gaussian_iterated_has_expectation_correct; exact HIF |exact HEF].
Qed.
