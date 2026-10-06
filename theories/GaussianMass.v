(* The Gaussian kernel is integrable on the line, and its integral
   gaussian_mass is positive (gaussian_kernel_mass_integral,
   gaussian_mass_positive). Its value, the square root of 2 * pi, is
   computed in GaussianProbabilityDensity (gpb_mass).

   The proof studies gaussian_primitive, the oriented integral of the kernel
   from 0. It is nondecreasing, positive at 1 and bounded above, so it has a
   limit L > 0 at +oo (gaussian_primitive_positive_limit); it is odd, so its
   limit at -oo is -L (gaussian_primitive_negative_limit). The bound above
   comes from t * gaussian_kernel t >= gaussian_kernel t for t >= 1, where
   the left side has the primitive - gaussian_kernel t. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianKernel.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* The oriented integral from a to b of a function nonnegative on [a, b] is
   nonnegative when a <= b. *)
Lemma gaussian_mass_oriented_ge0 (f : R -> R) a b :
  a <= b -> (forall x, a <= x <= b -> 0 <= f x) ->
  0 <= oriented_integral f a b.
Proof.
  move=> Hab Hf; rewrite /oriented_integral.
  destruct (Rle_dec a b) as [H0|H]; last lra.
  apply/RleP; apply: Rintegral_ge0 => x.
  rewrite /= in_itv /= => /andP [/RleP H1 /RleP H2].
  apply/RleP; apply: Hf; lra.
Qed.

(* Monotonicity of the oriented integral in the integrand, a <= b. *)
Lemma gaussian_mass_oriented_le (f g : R -> R) a b :
  a <= b -> segment_integrable f a b -> segment_integrable g a b ->
  (forall x, a <= x <= b -> f x <= g x) ->
  oriented_integral f a b <= oriented_integral g a b.
Proof.
  move=> Hab; rewrite /segment_integrable (Rmin_left _ _ Hab) (Rmax_right _ _ Hab).
  move=> Hf Hg Hfg; rewrite /oriented_integral.
  destruct (Rle_dec a b) as [H0|H]; last lra.
  have mD : measurable (`[a, b]%classic : set (measurableTypeR R)).
  { exact: measurable_itv. }
  apply/RleP; apply: (le_Rintegral mD Hf Hg).
  move=> x; rewrite /= in_itv /= => /andP [/RleP H1 /RleP H2].
  apply/RleP; apply: Hfg; lra.
Qed.

Lemma gaussian_kernel_finite a b : segment_integrable gaussian_kernel a b.
Proof.
  apply: rectangle_continuous_segment_integrable.
  exact: gaussian_kernel_continuous.
Qed.

Lemma gaussian_primitive_derivative (x : R) :
  @is_derive R R^o R^o x 1 gaussian_primitive (gaussian_kernel x).
Proof.
  unfold gaussian_primitive.
  exact: (rectangle_oriented_primitive_derivative gaussian_kernel 0 x
    gaussian_kernel_continuous).
Qed.

Lemma gaussian_primitive_increasing a b :
  a <= b -> gaussian_primitive a <= gaussian_primitive b.
Proof.
  intro Hab; unfold gaussian_primitive.
  rewrite -(rectangle_oriented_chasles gaussian_kernel 0 a b
    (gaussian_kernel_finite 0 a) (gaussian_kernel_finite a b)).
  pose proof (gaussian_mass_oriented_ge0 gaussian_kernel a b Hab
    (fun x _ => Rlt_le _ _ (gaussian_kernel_positive x))).
  lra.
Qed.

Lemma gaussian_linear_kernel_finite a b :
  oriented_has_integral (fun t => t * gaussian_kernel t) a b
    (gaussian_kernel a - gaussian_kernel b).
Proof.
  have Hc : continuous (fun t => t * gaussian_kernel t).
  { move=> x; apply: continuous_mult.
    - exact: continuous_id.
    - exact: gaussian_kernel_continuous. }
  split; first exact: rectangle_continuous_segment_integrable.
  replace (gaussian_kernel a - gaussian_kernel b) with
    (- gaussian_kernel b - - gaussian_kernel a) by ring.
  apply: (rectangle_oriented_FTC (fun t => - gaussian_kernel t)); last exact Hc.
  move=> x /=.
  replace (x * gaussian_kernel x) with (- (- x * gaussian_kernel x)) by ring.
  apply: is_derive_opp; exact: gaussian_kernel_derivative.
Qed.

Lemma gaussian_primitive_upper x :
  gaussian_primitive x <= gaussian_primitive 1 + gaussian_kernel 1.
Proof.
  destruct (Rle_dec x 1) as [Hx|Hx].
  - pose proof (gaussian_primitive_increasing x 1 Hx).
    pose proof (gaussian_kernel_positive 1); lra.
  - assert (H1 : 1 <= x) by lra.
    have [Hi HI] := gaussian_linear_kernel_finite 1 x.
    assert (HB : oriented_integral gaussian_kernel 1 x <=
      gaussian_kernel 1 - gaussian_kernel x).
    { rewrite -HI; apply: gaussian_mass_oriented_le.
      - exact H1.
      - exact: gaussian_kernel_finite.
      - exact Hi.
      - move=> t Ht; pose proof (gaussian_kernel_positive t); nra. }
    unfold gaussian_primitive.
    rewrite -(rectangle_oriented_chasles gaussian_kernel 0 1 x
      (gaussian_kernel_finite 0 1) (gaussian_kernel_finite 1 x)).
    pose proof (gaussian_kernel_positive x); lra.
Qed.

Lemma gaussian_primitive_one_positive : 0 < gaussian_primitive 1.
Proof.
  have [c [Hc HE]] := MVT_Reals gaussian_primitive gaussian_kernel 0 1 Rlt_0_1
    (fun t _ => gaussian_primitive_derivative t)
    (fun t _ => is_derive_continuity_pt _ _ _ (gaussian_primitive_derivative t)).
  have H0 : gaussian_primitive 0 = 0 by exact: rectangle_oriented_point.
  rewrite H0 in HE.
  pose proof (gaussian_kernel_positive c); nra.
Qed.

(* A nondecreasing function bounded above has a limit L at +oo, and L
   bounds it above. *)
Lemma increasing_bounded_positive_limit (f : R -> R) M :
  (forall x y, x <= y -> f x <= f y) ->
  (forall x, f x <= M) ->
  exists L, (forall x, f x <= L) /\ (f x @[x --> +oo%R] --> L)%classic.
Proof.
  intros Hmono Hbound.
  destruct (completeness (fun r => exists x, r = f x)) as [L [HU HL]].
  - exists M; intros r [x ->]; apply Hbound.
  - exists (f 0); exists 0; reflexivity.
  - exists L; split.
    + intro x; apply HU; exists x; reflexivity.
    + apply (proj2 (cvg_Reals_pinfty f L)); intros eps Heps.
      assert (Hex : exists a, L - eps < f a).
      { case: (pselect (exists a, L - eps < f a)) => [//|Hnone].
        assert (Hupper : is_upper_bound (fun r => exists x, r = f x) (L - eps)).
        { intros r [x ->]. apply Rnot_lt_le; intro Hx; apply Hnone; exists x; exact Hx. }
        specialize (HL _ Hupper); lra. }
      destruct Hex as [a Ha]; exists a; intros x Hx.
      assert (Hfx : f x <= L) by (apply HU; exists x; reflexivity).
      pose proof (Hmono a x (Rlt_le _ _ Hx)); apply Rabs_def1; lra.
Qed.

Lemma gaussian_primitive_positive_limit :
  exists L, 0 < L /\ (gaussian_primitive x @[x --> +oo%R] --> L)%classic.
Proof.
  destruct (increasing_bounded_positive_limit gaussian_primitive
    (gaussian_primitive 1 + gaussian_kernel 1) gaussian_primitive_increasing
    gaussian_primitive_upper) as [L [HU HL]].
  exists L; split; [|exact HL].
  specialize (HU 1); pose proof gaussian_primitive_one_positive; lra.
Qed.

Lemma gaussian_kernel_even x : gaussian_kernel (-x) = gaussian_kernel x.
Proof.
  unfold gaussian_kernel; replace ((-x) * (-x)) with (x*x) by ring; reflexivity.
Qed.

(* The value is L - -L, where L is the limit of gaussian_primitive at +oo.
   The integral of the kernel over [0, +oo[ is L by MathComp's
   ge0_continuous_FTC2y, and the kernel is even, so its integral over the
   line is twice that (ge0_symfun_integralT). *)
Lemma gaussian_kernel_positive_integral :
  exists M, 0 < M /\ whole_line_has_integral gaussian_kernel M.
Proof.
  destruct gaussian_primitive_positive_limit as [L [HL Hp]].
  exists (L - -L); split; [lra|].
  have h0 : forall x, (0 <= gaussian_kernel x)%R.
  { move=> x; apply/RleP; exact: (Rlt_le _ _ (gaussian_kernel_positive x)). }
  have hc : continuous gaussian_kernel := gaussian_kernel_continuous.
  have he : gaussian_kernel =1 gaussian_kernel \o (@GRing.opp R).
  { move=> x; rewrite /comp -RoppE; symmetry; exact: gaussian_kernel_even. }
  have Hsym := ge0_symfun_integralT h0 hc he.
  have H0 : gaussian_primitive 0 = 0 by exact: rectangle_oriented_point.
  have Hhalf : (\int[lebesgue_measure]_(x in `[0%R, +oo[)
      (gaussian_kernel x)%:E = L%:E)%E.
  { have -> : (L%:E = L%:E - (gaussian_primitive 0)%:E)%E by rewrite H0 sube0.
    apply: (@ge0_continuous_FTC2y R gaussian_kernel gaussian_primitive 0%R L).
    - by move=> x _; exact: h0.
    - exact: continuous_subspaceT.
    - exact: Hp.
    - move=> x _; have [Hd _] := gaussian_primitive_derivative x; exact Hd.
    - apply: cvg_at_right_filter.
      exact: (is_derive_continuous _ _ _ (gaussian_primitive_derivative 0)).
    - move=> x _; rewrite derive1E.
      have [_ Hv] := gaussian_primitive_derivative x; exact Hv. }
  have Hset : [set x : R | (0 <= x)%R] = `[0%R, +oo[ by rewrite set_itvcy.
  rewrite Hset Hhalf in Hsym.
  split.
  - apply/integrableP; split.
    + apply/measurable_EFinP; exact: continuous_measurable_fun.
    + have -> : (\int[lebesgue_measure]_(x in setT)
          `|(EFin \o gaussian_kernel) x|)%E =
          (\int[lebesgue_measure]_x (gaussian_kernel x)%:E)%E.
      { apply: eq_integral => x _; rewrite /comp gee0_abs //.
        rewrite lee_fin; exact: h0. }
      rewrite Hsym; exact: ltry.
  - rewrite /whole_line_integral /Rintegral Hsym -EFinM /=.
    rewrite mulr_natl mulr2n -RplusE; lra.
Qed.

Theorem gaussian_kernel_integrable : whole_line_integrable gaussian_kernel.
Proof. destruct gaussian_kernel_positive_integral as [M [HM [HI _]]]; exact HI. Qed.

Theorem gaussian_mass_positive : 0 < gaussian_mass.
Proof.
  destruct gaussian_kernel_positive_integral as [M [HM [_ HI]]].
  unfold gaussian_mass; rewrite HI; exact HM.
Qed.

Theorem gaussian_kernel_mass_integral :
  whole_line_has_integral gaussian_kernel gaussian_mass.
Proof. split; [exact gaussian_kernel_integrable | reflexivity]. Qed.
