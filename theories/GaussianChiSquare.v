(* Port of theories/GaussianChiSquare.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem of the original keeps its name, its arguments in
   the same order, and its text. The iterated operators come from the ported
   GaussianProductDefinitions and gaussian_expectation from the ported
   GaussianDefinitions, where they are stated with the Lebesgue integral over
   the line (difference 4 of analysis/README.md). So in
   gaussian_chisquare_exponential_moment, gaussian_iterated_integrable and
   gaussian_iterated_absolutely_integrable ask at each level for Lebesgue
   integrability over the line, and gaussian_iterated_has_expectation for
   Lebesgue integrals against gaussian_density. For t < 1/2 every function
   integrated at a level is a positive constant times
   x |-> exp (t * (x*x)) * gaussian_kernel x, which is continuous, positive
   and absolutely integrable, so the Lebesgue and the improper Riemann
   readings say the same thing and give the same values.

   The proofs are those of the original. They use
   gaussian_quadratic_exponential_integrable,
   gaussian_quadratic_exponential_absolute_integrable and
   gaussian_quadratic_exponential_expectation of the ported
   GaussianQuadraticMGF, and gaussian_separable_product_integral,
   gaussian_iterated_integrable_ext, gaussian_iterated_expectation_ext and
   gaussian_iterated_has_expectation_correct of the ported GaussianProduct,
   whose statements keep the text of the originals.

   This module imports no MathComp module, so repeat, length, List.Forall
   and the operations on R in the statements are Stdlib's, as in the
   original. The Coquelicot import is dropped; the original used nothing
   from it. The assumptions of the module are the seven axioms of
   analysis/README.md. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass GaussianExpectation
  GaussianQuadraticMGF GaussianProductDefinitions GaussianProduct.
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
