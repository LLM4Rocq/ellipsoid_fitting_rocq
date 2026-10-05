(* Port of theories/GaussianFubini.v from Coquelicot to MathComp-Analysis.

   Every theorem and lemma of the original keeps its name and its arguments,
   in the same order, and no statement gains or loses a hypothesis. The
   statements use the vocabulary of AnalysisIntegralDefinitions and of the
   bridge:
   - Coquelicot's pointwise continuous f x becomes MathComp's
     {for x, continuous f} (difference 5 of analysis/README.md). The bound
     variable in front of such a hypothesis is written x : R (or y : R), as
     in the ports of GaussianSections and GaussianRectangle and in the
     restated challenge ellipsoid_gaussian_fubini, so that Rocq does not
     infer a MathComp carrier for it;
   - continuity_2d_pt keeps its name. It is the definition of
     AnalysisIntegralDefinitions, joint continuity at (x, y) for the product
     topology of R * R, which says the same thing as Coquelicot's;
   - is_lim h p_infty l becomes (h A @[A --> +oo%R] --> l)%classic, the limit
     of MathComp at +oo, as in the ports of GaussianCutoff and
     GaussianRectangle. This is the only change of form, in the conclusion of
     gaussian_rectangle_limit.
   The arithmetic in every statement is Stdlib's, as in the original.

   Meaning. gaussian_integral_exists, gaussian_absolutely_integrable,
   gaussian_expectation, gaussian_cutoff_expectation and
   gaussian_cutoff_error_majorant follow the ported GaussianDefinitions and
   GaussianCutoffDefinitions: the integral over the line is the Lebesgue
   integral (difference 4 of analysis/README.md) and the cutoff integral is
   oriented_integral over [-A, A] (difference 3). Every statement here is
   about a jointly continuous F dominated by g x * h y, with g and h
   continuous, nonnegative and integrable against the kernel. Every function
   integrated over the line is then continuous and dominated by an
   integrable function, and every function integrated on a segment is
   continuous, so the Lebesgue and the Riemann readings agree on them. The
   statements of gaussian_rectangle_approximation and
   gaussian_fubini_integrable are the fourth and fifth clauses of the
   restated challenge ellipsoid_gaussian_fubini, with the same text.

   What changes in the proofs. The proofs follow the original.
   - The limit of the sum of the two error majorants in
     gaussian_rectangle_limit comes from the new lemma
     gaussian_fubini_limit_combination, proved in epsilon form with
     cvg_Reals_pinfty of the bridge, in place of Coquelicot's is_lim_plus'
     and is_lim_scal_l.
   - In gaussian_fubini_separable, Coquelicot's is_lim_ext becomes a rewrite
     of the function under the limit with boolp's funext, and is_lim_unique
     becomes the new lemma gaussian_fubini_limit_unique, the uniqueness of
     a limit at +oo, proved from MathComp's cvg_unique in the Hausdorff
     space R.
   - gaussian_fubini_absolute_continuity uses continuity_1d_2d_pt_comp of
     RectangleFubini with Stdlib's Rcontinuity_abs, in place of Coquelicot's
     continuous_abs and continuity_pt_filterlim.
   - gaussian_fubini_signed_integrable builds its conjunction clause by
     clause, where the original used repeat split. With the ported
     definitions split would also open gaussian_integral_exists, which is
     now MathComp's integrability, itself a conjunction. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCutoffDefinitions GaussianKernel
  GaussianMass GaussianExpectation ImproperBounds ImproperDomination ImproperCutoff
  GaussianCutoff RectangleFubini GaussianSections GaussianRectangle.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* A combination e1 + c * e2 of two functions that tend to 0 at +oo tends
   to 0 at +oo. New lemma, used in gaussian_rectangle_limit. *)
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

(* A function of a real variable has at most one limit at +oo. New lemma,
   used in gaussian_fubini_separable in place of Coquelicot's
   is_lim_unique. *)
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
