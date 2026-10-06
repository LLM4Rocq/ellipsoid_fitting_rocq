(* Fubini's theorem for Gaussian expectations in two variables. Let F be
   jointly continuous (continuity_2d_pt) and dominated by g x * h y, where
   g and h are continuous, nonnegative and integrable against the Gaussian
   kernel.
   - gaussian_rectangle_approximation bounds the distance between the
     iterated expectation of F and its cutoff to [-A, A] x [-B, B] by the
     cutoff errors gaussian_cutoff_error_majorant of g and h.
   - gaussian_rectangle_limit: the iterated cutoff expectation on
     [-A, A] x [-A, A] tends to the iterated expectation as A tends to +oo.
   - gaussian_fubini_separable: the iterated expectations in the two orders
     are equal. Both are limits of the same cutoff expectations, which
     agree in the two orders by gaussian_finite_rectangle_fubini.
   The integrals over the line are Lebesgue integrals, and the cutoff
   integrals are oriented_integral over [-A, A]. The bound variable of a
   continuity hypothesis is written x : R (or y : R), so that Rocq does not
   infer a MathComp carrier for it. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCutoffDefinitions GaussianKernel
  GaussianMass GaussianExpectation ImproperBounds ImproperDomination ImproperCutoff
  GaussianCutoff RectangleFubini GaussianSections GaussianRectangle.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* A combination e1 + c * e2 of two functions that tend to 0 at +oo tends
   to 0 at +oo. *)
Lemma gaussian_fubini_limit_combination (e1 e2 : R -> R) (c : R) :
  (e1 A @[A --> +oo%R] --> 0)%classic -> (e2 A @[A --> +oo%R] --> 0)%classic ->
  (e1 A + c * e2 A @[A --> +oo%R] --> 0)%classic.
Proof.
  move=> /cvg_Reals_pinfty H1 /cvg_Reals_pinfty H2.
  apply/cvg_Reals_pinfty => eps Heps.
  pose proof (Rabs_pos c) as Hc.
  assert (He1 : 0 < eps / 2) by lra.
  assert (He2 : 0 < eps / (2 * (Rabs c + 1))) by (apply Rdiv_lt_0_compat; lra).
  destruct (H1 _ He1) as [M1 HM1].
  destruct (H2 _ He2) as [M2 HM2].
  exists (Rmax M1 M2) => x Hx.
  assert (Hx1 : M1 < x) by (pose proof (Rmax_l M1 M2); lra).
  assert (Hx2 : M2 < x) by (pose proof (Rmax_r M1 M2); lra).
  specialize (HM1 x Hx1). specialize (HM2 x Hx2).
  rewrite Rminus_0_r in HM1. rewrite Rminus_0_r in HM2. rewrite Rminus_0_r.
  assert (Heq : eps / (2 * (Rabs c + 1)) * (Rabs c + 1) = eps / 2) by (field; lra).
  pose proof (Rabs_triang (e1 x) (c * e2 x)) as Ht.
  rewrite Rabs_mult in Ht.
  pose proof (Rmult_le_compat_l (Rabs c) _ _ Hc (Rlt_le _ _ HM2)) as Hm.
  pose proof (Rabs_pos (e2 x)).
  nra.
Qed.

(* A function of a real variable has at most one limit at +oo. *)
Lemma gaussian_fubini_limit_unique (D : R -> R) (l1 l2 : R) :
  (D A @[A --> +oo%R] --> l1)%classic -> (D A @[A --> +oo%R] --> l2)%classic ->
  l1 = l2.
Proof.
  move=> h1 h2.
  exact: (@cvg_unique _ (@Rhausdorff _) _ _ l1 l2 h1 h2).
Qed.

Theorem gaussian_rectangle_approximation (F : R -> R -> R) (g h : R -> R) A B :
  0 <= A -> 0 <= B ->
  (forall x y, continuity_2d_pt F x y) ->
  (forall x : R, {for x, continuous g}) -> (forall y : R, {for y, continuous h}) ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  gaussian_integral_exists g -> gaussian_integral_exists h ->
  (forall x y, Rabs (F x y) <= g x*h y) ->
  Rabs (gaussian_expectation (fun x => gaussian_expectation (F x)) -
    gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A) <=
  gaussian_cutoff_error_majorant g (gaussian_expectation h) A +
    gaussian_expectation g * gaussian_cutoff_error_majorant h 1 B.
Proof.
  intros HA HB HF Hg Hh Hgp Hhp HIg HIh Hbound.
  apply (gaussian_rectangle_approximation_given_section_continuity F g h A B);
    try assumption.
  - intro x; apply (gaussian_section_expectation_continuous F g h x); assumption.
  - intro x; rewrite Rmult_comm; apply (gaussian_section_expectation_bound F g h); assumption.
Qed.

Theorem gaussian_rectangle_limit (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) ->
  (forall x : R, {for x, continuous g}) -> (forall y : R, {for y, continuous h}) ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  gaussian_integral_exists g -> gaussian_integral_exists h ->
  (forall x y, Rabs (F x y) <= g x*h y) ->
  (gaussian_cutoff_expectation
    (fun x => gaussian_cutoff_expectation (F x) A) A @[A --> +oo%R] -->
    gaussian_expectation (fun x => gaussian_expectation (F x)))%classic.
Proof.
  intros HF Hg Hh Hgp Hhp HIg HIh Hbound.
  apply (gaussian_vanishing_error_limit _
    (fun A => gaussian_cutoff_error_majorant g (gaussian_expectation h) A +
      gaussian_expectation g * gaussian_cutoff_error_majorant h 1 A)).
  - intros A HA; apply (gaussian_rectangle_approximation F g h A A); assumption.
  - apply gaussian_fubini_limit_combination.
    + apply gaussian_cutoff_majorant_limit; exact HIg.
    + apply gaussian_cutoff_majorant_limit; exact HIh.
Qed.

Theorem gaussian_fubini_separable (F : R -> R -> R) (g h : R -> R) :
  (forall x y, continuity_2d_pt F x y) ->
  (forall x : R, {for x, continuous g}) -> (forall y : R, {for y, continuous h}) ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  gaussian_integral_exists g -> gaussian_integral_exists h ->
  (forall x y, Rabs (F x y) <= g x*h y) ->
  gaussian_expectation (fun x => gaussian_expectation (F x)) =
  gaussian_expectation (fun y => gaussian_expectation (fun x => F x y)).
Proof.
  intros HF Hg Hh Hgp Hhp HIg HIh Hbound.
  pose proof (gaussian_rectangle_limit F g h HF Hg Hh Hgp Hhp HIg HIh Hbound) as HL.
  assert (HT : forall y x, continuity_2d_pt (fun v u => F u v) y x)
    by (intros; apply rectangle_continuous_transpose, HF).
  assert (HTbound : forall y x, Rabs (F x y) <= h y*g x)
    by (intros; rewrite Rmult_comm; apply Hbound).
  pose proof (gaussian_rectangle_limit (fun y x => F x y) h g HT Hh Hg Hhp Hgp HIh HIg HTbound) as HR.
  assert (HR' : (gaussian_cutoff_expectation
    (fun x => gaussian_cutoff_expectation (F x) A) A @[A --> +oo%R] -->
    gaussian_expectation (fun y => gaussian_expectation (fun x => F x y)))%classic).
  { have Hext : (fun A => gaussian_cutoff_expectation
        (fun y => gaussian_cutoff_expectation (fun x => F x y) A) A) =
      (fun A => gaussian_cutoff_expectation
        (fun x => gaussian_cutoff_expectation (F x) A) A).
    { apply: funext => A; symmetry; apply gaussian_finite_rectangle_fubini, HF. }
    rewrite -Hext; exact HR. }
  exact (gaussian_fubini_limit_unique _ _ _ HL HR').
Qed.
