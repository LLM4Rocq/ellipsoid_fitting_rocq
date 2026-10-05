(* Port of theories/GaussianMoments.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions and of the bridge:
   Coquelicot's is_derive f x l becomes @is_derive R R^o R^o x 1 f l,
   continuous f x becomes {for x, continuous f},
   is_RInt_gen h (Rbar_locally m_infty) (Rbar_locally p_infty) l becomes
   whole_line_has_integral h l, and
   ex_RInt_gen h (Rbar_locally m_infty) (Rbar_locally p_infty) becomes
   whole_line_integrable h. The arithmetic in every statement is Stdlib's,
   as in the original.

   Meaning. The integrals over the line are now Lebesgue integrals, which
   require absolute integrability (difference 4 of analysis/README.md).
   Every integrand here is a polynomial times the Gaussian kernel, which is
   absolutely integrable, so each statement is the Lebesgue counterpart of
   the original. The hypothesis whole_line_has_integral gaussian_kernel J
   holds exactly for J = gaussian_mass, as the Coquelicot hypothesis did
   (gaussian_kernel_mass_integral of GaussianMass).

   What changes in the proofs. The derivative of t ^ S n comes from the
   tactic auto_derive of the bridge, in place of Coquelicot's is_derive_pow,
   and the continuity of t ^ n from continuous_Rpow of the bridge. Equalities
   of integrands are rewritten with funext, in place of is_RInt_gen_ext. The
   scaled integral comes from fubini_integrable_scale and
   fubini_integral_scale_l of GaussianFubiniLebesgue, in place of
   Coquelicot's is_RInt_gen_scal. gaussian_raw_moments_exist is proved from
   gaussian_raw_moments with J := whole_line_integral gaussian_kernel.

   The original imported Classical_Prop and Lia but used neither. This port
   imports neither, so the assumptions of the module are the seven axioms of
   analysis/README.md. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianDecay GaussianStein
  GaussianSteinPolynomial.
From EllipsoidFitting Require Import GaussianFubiniLebesgue.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_power_derivative n x :
  @is_derive R R^o R^o x 1 (fun t : R => t ^ S n) (INR (S n) * x ^ n).
Proof. auto_derive. cbn [Nat.pred]; ring. Qed.

Lemma gaussian_power_continuous n (x : R) :
  {for x, continuous (fun t : R => t ^ n)}.
Proof. exact (continuous_Rpow n x). Qed.

Theorem gaussian_moment_recurrence n L :
  whole_line_has_integral (fun x => x ^ n * gaussian_kernel x) L ->
  whole_line_has_integral (fun x => x ^ S (S n) * gaussian_kernel x)
    (INR (S n) * L).
Proof.
  intro HL.
  change (whole_line_has_integral (fun x => x * x ^ S n * gaussian_kernel x)
    (INR (S n) * L)).
  apply (gaussian_stein_polynomial_split (fun x => x ^ S n)
    (fun x => INR (S n) * x ^ n) 1 (S n) (INR (S n) * L)).
  - exact (gaussian_power_derivative n).
  - intro x.
    apply (continuous_mult R).
    + apply (continuous_const R).
    + apply gaussian_power_continuous.
  - intro x; rewrite <- RPow_abs; lra.
  - have E : (fun t => INR (S n) * t ^ n * gaussian_kernel t) =
        (fun t => INR (S n) * (t ^ n * gaussian_kernel t)).
    { apply/funext => t; ring. }
    rewrite E.
    destruct HL as [Hi Hl]; split.
    + exact (fubini_integrable_scale setT (fun x => x ^ n * gaussian_kernel x)
        (INR (S n)) measurableT Hi).
    + rewrite (fubini_integral_scale_l (fun x => x ^ n * gaussian_kernel x)
        (INR (S n)) Hi) Hl; reflexivity.
Qed.

Theorem gaussian_raw_moments J :
  whole_line_has_integral gaussian_kernel J ->
  forall n, whole_line_has_integral (fun x => x ^ n * gaussian_kernel x)
    (moment_factor n * J).
Proof.
  intro HJ.
  assert (Hp : forall n,
    whole_line_has_integral (fun x => x ^ n * gaussian_kernel x)
      (moment_factor n * J) /\
    whole_line_has_integral (fun x => x ^ S n * gaussian_kernel x)
      (moment_factor (S n) * J)).
  { intro n; induction n as [|n [Hn HSn]].
    - split.
      + simpl; rewrite Rmult_1_l.
        have E : (fun x : R => 1 * gaussian_kernel x) = gaussian_kernel.
        { apply/funext => x; ring. }
        rewrite E; exact HJ.
      + simpl; rewrite Rmult_0_l.
        have E : (fun x : R => x * 1 * gaussian_kernel x) =
            (fun x => x * gaussian_kernel x).
        { apply/funext => x; ring. }
        rewrite E; exact gaussian_first_moment_zero.
    - split; [exact HSn |].
      change (whole_line_has_integral (fun x => x ^ S (S n) * gaussian_kernel x)
        ((INR (S n) * moment_factor n) * J)).
      rewrite Rmult_assoc.
      exact (gaussian_moment_recurrence n (moment_factor n * J) Hn). }
  intro n; exact (proj1 (Hp n)).
Qed.

Corollary gaussian_raw_moments_exist :
  whole_line_integrable gaussian_kernel ->
  forall n, whole_line_integrable (fun x => x ^ n * gaussian_kernel x).
Proof.
  intros HI n.
  exact (proj1 (gaussian_raw_moments (whole_line_integral gaussian_kernel)
    (conj HI erefl) n)).
Qed.

Corollary gaussian_first_raw_moment J :
  whole_line_has_integral gaussian_kernel J ->
  whole_line_has_integral (fun x => x * gaussian_kernel x) 0.
Proof.
  intros _; exact gaussian_first_moment_zero.
Qed.

Corollary gaussian_second_raw_moment J :
  whole_line_has_integral gaussian_kernel J ->
  whole_line_has_integral (fun x => x ^ 2 * gaussian_kernel x) J.
Proof.
  intro HJ.
  pose proof (gaussian_raw_moments J HJ 2) as H.
  change (whole_line_has_integral (fun x => x ^ 2 * gaussian_kernel x)
    ((1 * 1) * J)) in H.
  rewrite !Rmult_1_l in H; exact H.
Qed.

Corollary gaussian_fourth_raw_moment J :
  whole_line_has_integral gaussian_kernel J ->
  whole_line_has_integral (fun x => x ^ 4 * gaussian_kernel x) (3 * J).
Proof.
  intro HJ.
  pose proof (gaussian_raw_moments J HJ 4) as H.
  change (whole_line_has_integral (fun x => x ^ 4 * gaussian_kernel x)
    (((1 + 1 + 1) * (1 * 1)) * J)) in H.
  replace (((1 + 1 + 1) * (1 * 1)) * J) with (3 * J) in H by ring.
  exact H.
Qed.
