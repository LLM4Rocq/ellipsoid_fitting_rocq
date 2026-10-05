(* Port of theories/GaussianCoordinateMarginals.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its text. The only change to the file is that the Coquelicot import
   line is dropped: no statement or proof here names a Coquelicot notion.

   The statements use finite_joint_continuous and finite_polynomial_bound,
   whose texts are the original ones (in the ported
   GaussianCoordinateDefinitions and GaussianCoordinateWeightDefinitions),
   and the Gaussian integrability and expectation notions of the ported
   GaussianDefinitions and GaussianProductDefinitions. Their meaning follows
   those definitions. gaussian_integral_exists f now says that
   x |-> f x * gaussian_kernel x is Borel measurable and Lebesgue integrable
   over the line, in place of the convergence of an improper Riemann
   integral (difference 4 of analysis/README.md), and
   gaussian_iterated_integrable, gaussian_iterated_absolutely_integrable and
   gaussian_iterated_has_expectation ask for the same Lebesgue notion at
   each level. In the theorems whose hypotheses are finite_joint_continuous
   and finite_polynomial_bound, every function integrated is continuous in
   the integrated variable and bounded by a constant times a polynomial
   weight. It is then absolutely integrable against the kernel, where the
   two integrals agree, and the conclusions are the Lebesgue counterparts
   of the original ones under the same hypotheses. The one theorem with an
   integrability hypothesis, gaussian_iterated_polynomial_expectation_bound,
   takes gaussian_iterated_integrable d F in the ported meaning; its
   importers obtain it from gaussian_iterated_polynomial_integrable, as in
   theories/. No statement is weakened.

   The continuity arguments of the proofs are MathComp's pointwise
   {for x, continuous f} (difference 5 of analysis/README.md). The ported
   lemmas that produce them (finite_joint_continuous_last_section,
   gaussian_coordinate_weight_continuous) and those that consume them
   (gaussian_majorant_integrability, gaussian_expectation_majorant_bound,
   gaussian_uniform_cutoff_convergence) agree on that form, so the proof
   scripts are the original ones.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So ++, length, the %nat scope and the operations on R are
   Stdlib's, as in the original, and the proofs are the original ones, word
   for word. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianExpectation GaussianProductDefinitions GaussianProduct
  GaussianCutoffDefinitions GaussianCutoff GaussianSections
  GaussianCoordinateDefinitions GaussianCoordinateBasics GaussianCoordinateTopology
  GaussianCoordinateBoxes GaussianCoordinateFiniteMarginal
  GaussianCoordinateWeightDefinitions GaussianCoordinateWeights GaussianLastDefinitions GaussianLastIntegration.
Import ListNotations.
Open Scope R_scope.

Lemma finite_polynomial_bound_abs d C p F :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d C p (fun xs => Rabs (F xs)).
Proof.
  intros [HC Hb]; split; [exact HC|].
  intros xs Hxs; rewrite Rabs_Rabsolu; apply Hb; exact Hxs.
Qed.

Lemma gaussian_last_section_polynomial_bound d F C p xs :
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  forall t, Rabs (F (xs++[t])) <=
    (C*gaussian_coordinate_product_weight p xs)*gaussian_coordinate_weight p t.
Proof.
  intros [HC Hb] Hxs t.
  specialize (Hb (xs++[t]) ltac:(rewrite length_app,Hxs; simpl; lia)).
  rewrite gaussian_coordinate_product_weight_append in Hb.
  simpl gaussian_coordinate_product_weight in Hb; nra.
Qed.

Theorem gaussian_last_section_admissible d F C p xs :
  finite_joint_continuous (S d) F ->
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  gaussian_integral_exists (fun t => F (xs++[t])) /\
  gaussian_absolutely_integrable (fun t => F (xs++[t])).
Proof.
  intros HF Hb Hxs.
  apply (gaussian_majorant_integrability (fun t => F (xs++[t]))
    (gaussian_coordinate_weight p) (C*gaussian_coordinate_product_weight p xs)).
  - apply (finite_joint_continuous_last_section d F xs); assumption.
  - apply gaussian_coordinate_weight_continuous.
  - apply (gaussian_last_section_polynomial_bound d F C p xs); assumption.
  - exact (proj1 (gaussian_coordinate_weight_integrable p)).
Qed.

Theorem gaussian_last_marginal_polynomial_bound d F C p :
  finite_joint_continuous (S d) F ->
  finite_polynomial_bound (S d) C p F ->
  finite_polynomial_bound d (C*gaussian_coordinate_weight_moment p) p
    (gaussian_last_marginal F).
Proof.
  intros HF Hb; split.
  - pose proof (proj1 Hb); pose proof (gaussian_coordinate_weight_moment_at_least_one p); nra.
  - intros xs Hxs.
    pose proof (gaussian_expectation_majorant_bound (fun t => F (xs++[t]))
      (gaussian_coordinate_weight p) (C*gaussian_coordinate_product_weight p xs)
      (finite_joint_continuous_last_section d F xs HF Hxs)
      (gaussian_coordinate_weight_continuous p)
      (gaussian_last_section_polynomial_bound d F C p xs Hb Hxs)
      (proj1 (gaussian_coordinate_weight_integrable p))) as H.
    change (Rabs (gaussian_expectation (fun t : R => F (xs++[t]))) <=
      C * gaussian_expectation (gaussian_coordinate_weight p) *
      gaussian_coordinate_product_weight p xs).
    replace (C * gaussian_expectation (gaussian_coordinate_weight p) *
      gaussian_coordinate_product_weight p xs) with
      (C * gaussian_coordinate_product_weight p xs *
       gaussian_expectation (gaussian_coordinate_weight p)) by ring.
    exact H.
Qed.

Theorem gaussian_iterated_polynomial_expectation_bound d F C p :
  gaussian_iterated_integrable d F -> finite_polynomial_bound d C p F ->
  Rabs (gaussian_iterated_expectation d F) <= C*gaussian_coordinate_weight_moment p ^ d.
Proof.
  intros HF [HC Hb].
  destruct (gaussian_coordinate_product_weight_expectation p d) as [HI HE].
  destruct (gaussian_iterated_scale d (gaussian_coordinate_product_weight p) C HI) as [HCI HCE].
  pose proof (gaussian_iterated_majorant_bound d F
    (fun xs => C*gaussian_coordinate_product_weight p xs) HF HCI Hb) as H.
  rewrite HCE, HE in H; exact H.
Qed.

Theorem gaussian_last_section_uniform_bound d F C p R xs :
  finite_polynomial_bound (S d) C p F -> length xs = d ->
  0 <= R -> (forall x, In x xs -> Rabs x <= R) ->
  forall t, Rabs (F (xs++[t])) <=
    (C*(1+R)^(p*d))*gaussian_coordinate_weight p t.
Proof.
  intros Hb Hxs HR Hbox t.
  eapply Rle_trans; [apply (gaussian_last_section_polynomial_bound d F C p xs Hb Hxs)|].
  apply Rmult_le_compat_r; [apply gaussian_coordinate_weight_nonnegative|].
  apply Rmult_le_compat_l; [exact (proj1 Hb)|].
  pose proof (gaussian_coordinate_product_weight_box p xs R HR Hbox) as H.
  rewrite Hxs in H; exact H.
Qed.

Theorem gaussian_last_marginal_continuous d F C p :
  finite_joint_continuous (S d) F ->
  finite_polynomial_bound (S d) C p F ->
  finite_joint_continuous d (gaussian_last_marginal F).
Proof.
  intros HF Hb z eps.
  destruct (coordinates_box_neighborhood d z) as [R [HR [Hz Hnear]]].
  assert (He : 0 < eps/3) by (pose proof (cond_pos eps); lra).
  destruct (gaussian_uniform_cutoff_convergence (gaussian_coordinate_weight p)
    (C*(1+R)^(p*d)) (gaussian_coordinate_weight_continuous p)
    (proj1 (gaussian_coordinate_weight_integrable p)) (mkposreal _ He))
    as [B [HB Htail]].
  set (A := B+1).
  assert (HBA : B < A) by (unfold A; lra).
  assert (HA : 0 <= A) by (unfold A; lra).
  destruct (gaussian_last_cutoff_continuous d F A HA HF z (mkposreal _ He))
    as [delta Hd].
  assert (Hmin : 0 < Rmin 1 delta) by (apply Rmin_pos; [lra|apply cond_pos]).
  exists (mkposreal _ Hmin); intros w Hw.
  assert (Hw1 : close_n d 1 w z).
  { apply (coordinates_close_mono d (Rmin 1 delta) 1 w z); [apply Rmin_l|exact Hw]. }
  assert (Hwd : close_n d delta w z).
  { apply (coordinates_close_mono d (Rmin 1 delta) delta w z); [apply Rmin_r|exact Hw]. }
  assert (Htails : forall xs, length xs = d ->
    (forall x, In x xs -> Rabs x <= R) ->
    Rabs (gaussian_expectation (fun t => F (xs++[t])) -
      gaussian_cutoff_expectation (fun t => F (xs++[t])) A) < eps/3).
  { intros xs Hxs Hbox; apply (Htail A HBA (fun t => F (xs++[t]))).
    - apply (finite_joint_continuous_last_section d F xs HF Hxs).
    - apply (gaussian_last_section_uniform_bound d F C p R xs Hb Hxs HR Hbox). }
  pose proof (Htails (coordinates_to_list d w) (coordinates_to_list_length d w)
    (Hnear w Hw1)) as Htw.
  pose proof (Htails (coordinates_to_list d z) (coordinates_to_list_length d z) Hz) as Htz.
  specialize (Hd w Hwd).
  set (fw := fun t => F (coordinates_to_list d w++[t])) in *.
  set (fz := fun t => F (coordinates_to_list d z++[t])) in *.
  change (Rabs (gaussian_cutoff_expectation fw A - gaussian_cutoff_expectation fz A) < eps/3) in Hd.
  change (Rabs (gaussian_expectation fw - gaussian_expectation fz) < eps).
  replace (gaussian_expectation fw - gaussian_expectation fz) with
    ((gaussian_expectation fw-gaussian_cutoff_expectation fw A) +
     (gaussian_cutoff_expectation fw A-gaussian_cutoff_expectation fz A) +
     -(gaussian_expectation fz-gaussian_cutoff_expectation fz A)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp.
  pose proof (Rabs_triang
    (gaussian_expectation fw-gaussian_cutoff_expectation fw A)
    (gaussian_cutoff_expectation fw A-gaussian_cutoff_expectation fz A)); lra.
Qed.

Theorem gaussian_iterated_polynomial_integrable d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F.
Proof.
  revert F C; induction d as [|d IH]; intros F C HF Hb; [exact I|].
  apply (proj2 (gaussian_iterated_last_integrable d F)); split.
  - intros xs Hxs; exact (proj1 (gaussian_last_section_admissible d F C p xs HF Hb Hxs)).
  - apply (IH (gaussian_last_marginal F) (C*gaussian_coordinate_weight_moment p)).
    + exact (gaussian_last_marginal_continuous d F C p HF Hb).
    + exact (gaussian_last_marginal_polynomial_bound d F C p HF Hb).
Qed.

Theorem gaussian_iterated_polynomial_absolutely_integrable d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_absolutely_integrable d F.
Proof.
  intros HF Hb; unfold gaussian_iterated_absolutely_integrable.
  apply (gaussian_iterated_polynomial_integrable d (fun xs => Rabs (F xs)) C p).
  - exact (finite_joint_continuous_abs d F HF).
  - exact (finite_polynomial_bound_abs d C p F Hb).
Qed.

Theorem gaussian_iterated_polynomial_admissible d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  gaussian_iterated_integrable d F /\
  gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))) /\
  Rabs (gaussian_iterated_expectation d F) <= C*gaussian_coordinate_weight_moment p ^ d.
Proof.
  intros HF Hb.
  pose proof (gaussian_iterated_polynomial_integrable d F C p HF Hb) as HI.
  pose proof (gaussian_iterated_polynomial_absolutely_integrable d F C p HF Hb) as HA.
  split; [exact HI|]; split; [exact HA|]; split.
  - apply gaussian_iterated_has_expectation_correct; exact HI.
  - split.
    + apply gaussian_iterated_has_expectation_correct; exact HA.
    + exact (gaussian_iterated_polynomial_expectation_bound d F C p HI Hb).
Qed.
