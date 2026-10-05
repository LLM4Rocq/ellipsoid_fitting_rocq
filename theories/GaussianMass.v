(* Port of theories/GaussianMass.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements use the vocabulary of AnalysisIntegralDefinitions
   and of the bridge:
   - ex_RInt f a b becomes segment_integrable f a b, and is_RInt f a b l
     becomes oriented_has_integral f a b l;
   - is_derive f x l becomes @is_derive R R^o R^o x 1 f l;
   - is_lim f p_infty l and is_lim f m_infty l become
     (f x @[x --> +oo%R] --> l)%classic and (f x @[x --> -oo%R] --> l)%classic;
   - ex_RInt_gen f (Rbar_locally m_infty) (Rbar_locally p_infty) becomes
     whole_line_integrable f, and is_RInt_gen over the same filters becomes
     whole_line_has_integral f l, the Lebesgue integral over the line;
   - continuous h x becomes {for x, continuous h}.
   The arithmetic in every statement is Stdlib's, as in the original.

   The kernel is continuous, positive and absolutely integrable, so for it
   the Lebesgue integrals over a segment and over the line have, as a
   mathematical fact, the values of Coquelicot's Riemann integrals
   (differences 3 and 4 of analysis/README.md). This module does not prove
   that agreement; it proves every statement directly with the Lebesgue
   integral.

   Statements that change form.

   1. continuous_nonnegative_primitive_limit. The original concluded
      is_RInt_gen h (at_point a) (Rbar_locally p_infty) L, which says that
      RInt h a x tends to L as x tends to +oo. There is no half-line
      vocabulary in AnalysisIntegralDefinitions, so the port states that
      limit for the oriented integral, and adds the Lebesgue form: h is
      integrable on [a, +oo[ and its integral there is L. The new statement
      implies the translation of the old one. The hypothesis
      (forall x, continuous h x) becomes (forall x, {for x, continuous h}).
      No module of theories/ uses this lemma of GaussianMass.

   2. gaussian_kernel_positive_integral, gaussian_kernel_integrable,
      gaussian_kernel_absolute_integrable and gaussian_kernel_mass_integral
      are about the Lebesgue integral over the line, which requires
      absolute integrability. For the kernel this changes nothing: it is
      nonnegative, and the proof obtains its integrability from the limits
      of gaussian_primitive, with MathComp's ge0_continuous_FTC2y on
      [0, +oo[ and the symmetry lemma ge0_symfun_integralT.

   New lemmas, used in the proofs and available to importers:
   - gaussian_mass_oriented_ge0: the oriented integral from a to b of a
     function that is nonnegative on [a, b] is nonnegative when a <= b;
   - gaussian_mass_oriented_le: the oriented integral is monotone in the
     integrand when a <= b and both integrands are integrable on [a, b].

   The original imported Classical_Prop for NNPP. The port uses MathComp's
   pselect instead, so the assumptions of the module are the seven axioms
   of analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianKernel.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* The oriented integral of a function nonnegative on [a, b], a <= b. *)
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

Lemma gaussian_primitive_odd x : gaussian_primitive (-x) = - gaussian_primitive x.
Proof.
  have HD : forall t, @is_derive R R^o R^o t 1
      (fun y => - gaussian_primitive (- y)) (gaussian_kernel t).
  { move=> t.
    have Hn : @is_derive R R^o R^o t 1 (fun y => - y) (- 1).
    { exact: (is_derive_opp (fun y => y) t 1 (is_derive_id_R t)). }
    have H := is_derive_comp gaussian_primitive (fun y => - y) t
      (gaussian_kernel (- t)) (- 1) (gaussian_primitive_derivative (- t)) Hn.
    have H2 := is_derive_opp _ _ _ H.
    rewrite gaussian_kernel_even in H2.
    replace (gaussian_kernel t) with (- (- 1 * gaussian_kernel t)) by ring.
    exact H2. }
  have E := rectangle_oriented_FTC _ _ 0 x HD gaussian_kernel_continuous.
  change (gaussian_primitive x =
    - gaussian_primitive (- x) - - gaussian_primitive (- 0)) in E.
  have H0 : gaussian_primitive 0 = 0 by exact: rectangle_oriented_point.
  rewrite Ropp_0 H0 in E; lra.
Qed.

Lemma gaussian_primitive_negative_limit (L : R) :
  (gaussian_primitive x @[x --> +oo%R] --> L)%classic ->
  (gaussian_primitive x @[x --> -oo%R] --> - L)%classic.
Proof.
  move=> /(cvg_Reals_pinfty gaussian_primitive L) HL.
  apply/(cvg_Reals_ninfty gaussian_primitive (- L)); intros eps Heps.
  destruct (HL eps Heps) as [a Ha]; exists (-a); intros x Hx.
  replace (gaussian_primitive x - -L) with
    (- (gaussian_primitive (-x) - L)) by (rewrite gaussian_primitive_odd; ring).
  rewrite Rabs_Ropp; apply Ha; lra.
Qed.

(* The value is L - -L, where L is the limit of gaussian_primitive at +oo.
   The integral of the kernel over [0, +oo[ is L by MathComp's
   ge0_continuous_FTC2y, and the kernel is even. *)
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

Theorem gaussian_kernel_absolute_integrable :
  whole_line_integrable (fun x => Rabs (gaussian_kernel x)).
Proof.
  have E : (fun x => Rabs (gaussian_kernel x)) = gaussian_kernel.
  { apply/funext => x; apply: Rabs_pos_eq; apply: Rlt_le.
    exact: gaussian_kernel_positive. }
  rewrite E; exact gaussian_kernel_integrable.
Qed.

Theorem gaussian_kernel_mass_integral :
  whole_line_has_integral gaussian_kernel gaussian_mass.
Proof. split; [exact gaussian_kernel_integrable | reflexivity]. Qed.

(* The original concluded is_RInt_gen h (at_point a) (Rbar_locally p_infty) L,
   the limit of RInt h a x as x tends to +oo. The port states that limit for
   the oriented integral and adds the Lebesgue integral over [a, +oo[
   (header, item 1). *)
Lemma continuous_nonnegative_primitive_limit (h : R -> R) a M :
  (forall x, {for x, continuous h}) ->
  (forall x, 0 <= h x) ->
  (forall x, a <= x -> oriented_integral h a x <= M) ->
  exists L, 0 <= L /\
    (oriented_integral h a x @[x --> +oo%R] --> L)%classic /\
    lebesgue_measure.-integrable `[a, +oo[ (EFin \o h) /\
    Rintegral lebesgue_measure `[a, +oo[ h = L.
Proof.
  intros HC Hnonneg Hbound.
  have Hc : continuous h := HC.
  have HI : forall u v, segment_integrable h u v.
  { move=> u v; exact: rectangle_continuous_segment_integrable. }
  have Hmono : forall x y, x <= y ->
      oriented_integral h a x <= oriented_integral h a y.
  { move=> x y Hxy.
    rewrite -(rectangle_oriented_chasles h a x y (HI a x) (HI x y)).
    pose proof (gaussian_mass_oriented_ge0 h x y Hxy (fun t _ => Hnonneg t)).
    lra. }
  have Hglobal : forall x, oriented_integral h a x <= M.
  { move=> x; destruct (Rle_dec a x) as [Hx|Hx]; [apply Hbound; exact Hx|].
    apply Rle_trans with (r2 := oriented_integral h a a).
    - apply Hmono; lra.
    - apply Hbound; lra. }
  destruct (increasing_bounded_positive_limit (oriented_integral h a) M
    Hmono Hglobal) as [L [HU HL]].
  have HL0 : 0 <= L.
  { specialize (HU a); rewrite rectangle_oriented_point in HU; exact HU. }
  have HD : forall x, @is_derive R R^o R^o x 1 (oriented_integral h a) (h x).
  { move=> x; exact: (rectangle_oriented_primitive_derivative h a x Hc). }
  have Hhalf : (\int[lebesgue_measure]_(x in `[a, +oo[) (h x)%:E = L%:E)%E.
  { have -> : (L%:E = L%:E - (oriented_integral h a a)%:E)%E.
    { by rewrite rectangle_oriented_point sube0. }
    apply: (@ge0_continuous_FTC2y R h (oriented_integral h a) a L).
    - move=> x _; apply/RleP; exact: Hnonneg.
    - exact: continuous_subspaceT.
    - exact: HL.
    - move=> x _; have [Hd _] := HD x; exact Hd.
    - apply: cvg_at_right_filter; exact: (is_derive_continuous _ _ _ (HD a)).
    - move=> x _; rewrite derive1E; have [_ Hv] := HD x; exact Hv. }
  exists L; split; first exact HL0.
  split; first exact HL.
  split.
  - apply/integrableP; split.
    + apply/measurable_EFinP; apply: measurable_funTS.
      exact: continuous_measurable_fun.
    + have -> : (\int[lebesgue_measure]_(x in `[a, +oo[)
          `|(EFin \o h) x|)%E =
          (\int[lebesgue_measure]_(x in `[a, +oo[) (h x)%:E)%E.
      { apply: eq_integral => x _; rewrite /comp gee0_abs // lee_fin.
        apply/RleP; exact: Hnonneg. }
      rewrite Hhalf; exact: ltry.
  - by rewrite /Rintegral Hhalf.
Qed.
