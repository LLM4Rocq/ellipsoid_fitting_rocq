(* Port of theories/GaussianRectangle.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order, and no statement gains or loses a hypothesis. The statements use
   the vocabulary of AnalysisIntegralDefinitions and of the bridge:
   - Coquelicot's continuous f x becomes {for x, continuous f} (difference 5
     of analysis/README.md);
   - RInt f a b becomes oriented_integral f a b (difference 3);
   - continuity_2d_pt F x y is the definition of the same name in
     AnalysisIntegralDefinitions, which says the same thing;
   - is_lim h p_infty l becomes (h A @[A --> +oo%R] --> l)%classic, the limit
     of MathComp at +oo, as in the port of GaussianCutoff.
   The bound variable in front of a continuity hypothesis is written x : R,
   as in the port of GaussianCutoff, so that Rocq does not infer a MathComp
   carrier for it. The arithmetic in every statement is Stdlib's, as in the
   original.

   Meaning. gaussian_integral, gaussian_integral_exists, gaussian_expectation
   and the cutoff definitions follow the ported GaussianDefinitions and
   GaussianCutoffDefinitions: the integral over the line is the Lebesgue
   integral (difference 4) and the cutoff integral is oriented_integral over
   [-A, A] (difference 3). Every integral on a segment in this module is the
   integral of a function continuous everywhere, where oriented_integral
   agrees with Coquelicot's RInt, and every integral over the line is the
   integral of a continuous function dominated by an integrable one or of a
   nonnegative integrable one, where the Lebesgue integral agrees with the
   improper Riemann integral. So each statement is the Lebesgue counterpart
   of the original, with the same meaning on the functions it is about.

   Statements that change form, besides the vocabulary.
   - gaussian_cutoff_density and gaussian_rectangle_density conclude an
     equality with oriented_integral in place of RInt.
   - gaussian_vanishing_error_limit takes and concludes limits at +oo in
     MathComp's notation. The bridge lemma cvg_Reals_pinfty turns them into
     the epsilon form that the original obtained with is_lim_spec.

   What changes in the proofs. Coquelicot's RInt_scal, RInt_minus and RInt_ext
   become rectangle_oriented_scal, rectangle_oriented_minus and
   rectangle_oriented_ext of RectangleFubini. The last one asks for the
   equality on the closed segment, and every use here proves it for every x.
   The integrability of continuous functions on segments comes from
   continuous_finite_integrable of ImproperBounds. The continuity lemmas on
   one variable are those of AnalysisBridge (continuous_mult,
   continuous_const, continuous_minus, continuous_ext), and those on two
   variables are those of RectangleFubini, which keep Coquelicot's names. *)

From Stdlib Require Import Reals Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianCutoffDefinitions GaussianKernel
  GaussianMass GaussianExpectation ImproperBounds ImproperDomination ImproperCutoff
  GaussianCutoff RectangleFubini.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_density_continuous (x : R) : {for x, continuous gaussian_density}.
Proof.
  apply (continuous_ext R (fun t => gaussian_kernel t * / gaussian_mass)).
  - intro t; unfold gaussian_density, Rdiv; reflexivity.
  - apply (continuous_mult R);
      [apply gaussian_kernel_continuous | apply (continuous_const R)].
Qed.

Lemma gaussian_cutoff_density (f : R -> R) (A : R) :
  (forall x : R, {for x, continuous f}) ->
  gaussian_cutoff_expectation f A =
    oriented_integral (fun x => gaussian_density x * f x) (-A) A.
Proof.
  intro HC. unfold gaussian_cutoff_expectation, gaussian_cutoff_integral.
  transitivity
    (oriented_integral (fun x => / gaussian_mass * (f x * gaussian_kernel x)) (-A) A).
  - pose proof (rectangle_oriented_scal (fun x => f x * gaussian_kernel x)
      (-A) A (/ gaussian_mass)
      (continuous_finite_integrable _ (gaussian_weighted_continuous f HC) (-A) A))
      as HS.
    rewrite HS.
    unfold Rdiv; ring.
  - apply rectangle_oriented_ext; intros x Hx; unfold gaussian_density, Rdiv.
    ring.
Qed.

Lemma gaussian_cutoff_section_continuous (F : R -> R -> R) A (x : R) :
  (forall u v, continuity_2d_pt F u v) ->
  {for x, continuous (fun u : R => gaussian_cutoff_expectation (F u) A)}.
Proof.
  intro HC.
  apply (continuous_ext R
    (fun u => oriented_integral (fun v => gaussian_density v * F u v) (-A) A)).
  - intro u; symmetry; apply gaussian_cutoff_density.
    intro v; apply rectangle_continuous_slice_right, HC.
  - apply (rectangle_parameter_integral_continuous
      (fun u v => gaussian_density v * F u v) (-A) A x).
    intros u v; apply continuity_2d_pt_mult; [|apply HC].
    apply (continuity_1d_2d_pt_comp gaussian_density (fun _ y => y)).
    + apply (proj2 (continuity_pt_filterlim _ _)), gaussian_density_continuous.
    + apply continuity_2d_pt_id2.
Qed.

Lemma gaussian_rectangle_weighted_continuous (F : R -> R -> R) x y :
  (forall u v, continuity_2d_pt F u v) ->
  continuity_2d_pt
    (fun u v => gaussian_density u * (gaussian_density v * F u v)) x y.
Proof.
  intro HC. apply continuity_2d_pt_mult.
  - apply (continuity_1d_2d_pt_comp gaussian_density (fun x _ => x)).
    + apply (proj2 (continuity_pt_filterlim _ _)), gaussian_density_continuous.
    + apply continuity_2d_pt_id1.
  - apply continuity_2d_pt_mult; [|apply HC].
    apply (continuity_1d_2d_pt_comp gaussian_density (fun _ y => y)).
    + apply (proj2 (continuity_pt_filterlim _ _)), gaussian_density_continuous.
    + apply continuity_2d_pt_id2.
Qed.

Lemma gaussian_rectangle_density (F : R -> R -> R) A B :
  (forall x y, continuity_2d_pt F x y) ->
  gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A =
  oriented_integral
    (fun x => oriented_integral
      (fun y => gaussian_density x * (gaussian_density y * F x y)) (-B) B) (-A) A.
Proof.
  intro HC.
  rewrite (gaussian_cutoff_density (fun x => gaussian_cutoff_expectation (F x) B) A
    (fun x => gaussian_cutoff_section_continuous F B x HC)).
  apply rectangle_oriented_ext; intros x Hx.
  rewrite (gaussian_cutoff_density (F x) B
    (fun y => rectangle_continuous_slice_right F x y (HC x y))).
  symmetry.
  apply (rectangle_oriented_scal (fun y => gaussian_density y * F x y)).
  apply continuous_finite_integrable; intro y.
  apply (continuous_mult R);
    [apply gaussian_density_continuous | apply rectangle_continuous_slice_right, HC].
Qed.

Theorem gaussian_finite_rectangle_fubini (F : R -> R -> R) A B :
  (forall x y, continuity_2d_pt F x y) ->
  gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A =
  gaussian_cutoff_expectation (fun y => gaussian_cutoff_expectation (fun x => F x y) A) B.
Proof.
  intro HC. rewrite (gaussian_rectangle_density F A B HC).
  assert (HT : forall y x, continuity_2d_pt (fun v u => F u v) y x).
  { intros y x; apply rectangle_continuous_transpose, HC. }
  rewrite (gaussian_rectangle_density (fun y x => F x y) B A HT).
  rewrite (continuous_rectangle_fubini _ (-A) A (-B) B
    (fun x y => gaussian_rectangle_weighted_continuous F x y HC)).
  apply rectangle_oriented_ext; intros y Hy; apply rectangle_oriented_ext; intros x Hx.
  ring.
Qed.

Lemma gaussian_cutoff_expectation_sub (f g : R -> R) A :
  (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  gaussian_cutoff_expectation (fun x => f x - g x) A =
  gaussian_cutoff_expectation f A - gaussian_cutoff_expectation g A.
Proof.
  intros HC HG. unfold gaussian_cutoff_expectation, gaussian_cutoff_integral.
  replace (oriented_integral (fun x => (f x - g x) * gaussian_kernel x) (-A) A) with
    (oriented_integral (fun x => f x * gaussian_kernel x - g x * gaussian_kernel x) (-A) A).
  2:{ apply rectangle_oriented_ext; intros x Hx; ring. }
  pose proof (rectangle_oriented_minus
    (fun x => f x * gaussian_kernel x) (fun x => g x * gaussian_kernel x) (-A) A
    (continuous_finite_integrable _ (gaussian_weighted_continuous f HC) (-A) A)
    (continuous_finite_integrable _ (gaussian_weighted_continuous g HG) (-A) A)) as HS.
  rewrite HS.
  unfold Rdiv; ring.
Qed.

Lemma gaussian_cutoff_expectation_abs_bound (f g : R -> R) C A :
  0 <= A -> (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous g}) ->
  (forall x, Rabs (f x) <= C * g x) ->
  Rabs (gaussian_cutoff_expectation f A) <= C * gaussian_cutoff_expectation g A.
Proof.
  intros HA HC HG Hb.
  assert (HCG : forall x : R,
    {for x, continuous (fun t => C * (g t * gaussian_kernel t))}).
  { intro x; apply (continuous_mult R);
      [apply (continuous_const R) | apply gaussian_weighted_continuous, HG]. }
  pose proof (continuous_finite_integral_abs_bound
    (fun x => f x * gaussian_kernel x) (fun x => C * (g x * gaussian_kernel x)) (-A) A
    (gaussian_weighted_continuous f HC) HCG
    (gaussian_weighted_abs_domination f g C Hb) ltac:(lra)) as H.
  pose proof (rectangle_oriented_scal (fun x => g x * gaussian_kernel x)
    (-A) A C (continuous_finite_integrable _ (gaussian_weighted_continuous g HG) (-A) A))
    as HS.
  rewrite HS in H.
  change (Rabs (gaussian_cutoff_integral f A) <= C * gaussian_cutoff_integral g A) in H.
  pose proof gaussian_mass_positive as HM.
  unfold gaussian_cutoff_expectation, Rdiv.
  rewrite Rabs_mult Rabs_inv (Rabs_pos_eq gaussian_mass (Rlt_le _ _ HM)).
  pose proof (Rinv_0_lt_compat gaussian_mass HM).
  nra.
Qed.

Lemma gaussian_cutoff_expectation_upper (g : R -> R) A :
  0 <= A -> (forall x : R, {for x, continuous g}) -> (forall x, 0 <= g x) ->
  gaussian_integral_exists g -> gaussian_cutoff_expectation g A <= gaussian_expectation g.
Proof.
  intros HA HG Hpos HI.
  pose proof (improper_nonnegative_interval_bound
    (fun x => g x * gaussian_kernel x) (gaussian_integral g)
    (gaussian_weighted_continuous g HG)
    (fun x => Rmult_le_pos _ _ (Hpos x) (Rlt_le _ _ (gaussian_kernel_positive x)))
    (gaussian_integral_correct g HI) (-A) A ltac:(lra)) as H.
  unfold gaussian_cutoff_expectation, gaussian_expectation, gaussian_cutoff_integral, Rdiv.
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat, gaussian_mass_positive | exact H].
Qed.

Lemma gaussian_cutoff_difference_bound (f k g : R -> R) C A :
  0 <= A -> (forall x : R, {for x, continuous f}) -> (forall x : R, {for x, continuous k}) ->
  (forall x : R, {for x, continuous g}) -> (forall x, Rabs (f x - k x) <= C * g x) ->
  Rabs (gaussian_cutoff_expectation f A - gaussian_cutoff_expectation k A) <=
    C * gaussian_cutoff_expectation g A.
Proof.
  intros HA Hf Hk Hg Hb.
  rewrite <- (gaussian_cutoff_expectation_sub f k A Hf Hk).
  apply (gaussian_cutoff_expectation_abs_bound (fun x => f x - k x) g C A HA).
  - intro x; exact (continuous_minus R f k x (Hf x) (Hk x)).
  - exact Hg.
  - exact Hb.
Qed.

Lemma gaussian_cutoff_majorant_scale (g : R -> R) C A :
  gaussian_cutoff_error_majorant g C A = C * gaussian_cutoff_error_majorant g 1 A.
Proof. unfold gaussian_cutoff_error_majorant, Rdiv; ring. Qed.

Lemma gaussian_rectangle_approximation_given_section_continuity
  (F : R -> R -> R) (g h : R -> R) A B :
  0 <= A -> 0 <= B ->
  (forall x y, continuity_2d_pt F x y) ->
  (forall x : R, {for x, continuous g}) -> (forall y : R, {for y, continuous h}) ->
  (forall x, 0 <= g x) -> (forall y, 0 <= h y) ->
  gaussian_integral_exists g -> gaussian_integral_exists h ->
  (forall x y, Rabs (F x y) <= g x * h y) ->
  (forall x : R, {for x, continuous (fun u : R => gaussian_expectation (F u))}) ->
  (forall x, Rabs (gaussian_expectation (F x)) <= gaussian_expectation h * g x) ->
  Rabs (gaussian_expectation (fun x => gaussian_expectation (F x)) -
    gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A) <=
  gaussian_cutoff_error_majorant g (gaussian_expectation h) A +
    gaussian_expectation g * gaussian_cutoff_error_majorant h 1 B.
Proof.
  intros HA HB HF Hg Hh Hgp Hhp HIg HIh Hbound Hsection Hsectionbound.
  pose proof (gaussian_normalized_cutoff_error_bound
    (fun x => gaussian_expectation (F x)) g (gaussian_expectation h) A
    HA Hsection Hg Hsectionbound HIg) as Houter.
  assert (Hinner : forall x,
    Rabs (gaussian_expectation (F x) - gaussian_cutoff_expectation (F x) B) <=
      gaussian_cutoff_error_majorant h 1 B * g x).
  { intro x. pose proof (gaussian_normalized_cutoff_error_bound
      (F x) h (g x) B HB
      (fun y => rectangle_continuous_slice_right F x y (HF x y)) Hh (Hbound x) HIh) as H.
    rewrite gaussian_cutoff_majorant_scale in H; nra. }
  pose proof (gaussian_cutoff_difference_bound
    (fun x => gaussian_expectation (F x))
    (fun x => gaussian_cutoff_expectation (F x) B) g
    (gaussian_cutoff_error_majorant h 1 B) A HA Hsection
    (fun x => gaussian_cutoff_section_continuous F B x HF) Hg Hinner) as Hdifference.
  pose proof (gaussian_cutoff_expectation_upper g A HA Hg Hgp HIg) as Hgupper.
  pose proof (gaussian_cutoff_majorant_nonnegative h 1 B ltac:(lra) HB Hh Hhp HIh)
    as Htailpos.
  pose proof (Rabs_triang
    (gaussian_expectation (fun x => gaussian_expectation (F x)) -
      gaussian_cutoff_expectation (fun x => gaussian_expectation (F x)) A)
    (gaussian_cutoff_expectation (fun x => gaussian_expectation (F x)) A -
      gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A))
    as Htriangle.
  replace (gaussian_expectation (fun x => gaussian_expectation (F x)) -
    gaussian_cutoff_expectation (fun x => gaussian_expectation (F x)) A +
    (gaussian_cutoff_expectation (fun x => gaussian_expectation (F x)) A -
      gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A))
    with (gaussian_expectation (fun x => gaussian_expectation (F x)) -
      gaussian_cutoff_expectation (fun x => gaussian_cutoff_expectation (F x) B) A)
    in Htriangle by ring.
  nra.
Qed.

Lemma gaussian_vanishing_error_limit (D e : R -> R) J :
  (forall A, 0 <= A -> Rabs (J - D A) <= e A) ->
  (e A @[A --> +oo%R] --> 0)%classic -> (D A @[A --> +oo%R] --> J)%classic.
Proof.
  intros HB HL. apply/cvg_Reals_pinfty => eps Heps.
  move/cvg_Reals_pinfty: HL => HL. destruct (HL eps Heps) as [a Ha].
  exists (Rmax 0 a); intros A HA.
  assert (HA0 : 0 <= A) by (pose proof (Rmax_l 0 a); lra).
  assert (HAa : a < A) by (pose proof (Rmax_r 0 a); lra).
  specialize (Ha A HAa); rewrite Rminus_0_r in Ha.
  specialize (HB A HA0). rewrite Rabs_minus_sym.
  pose proof (Rle_abs (e A)); lra.
Qed.
