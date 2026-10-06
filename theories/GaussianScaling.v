(* The Gaussian kernel under a dilation. For a > 0, the function
   x |-> gaussian_kernel (a * x) is integrable on the line with integral
   gaussian_mass / a (gaussian_scaled_kernel_integral); the integral is the
   Lebesgue integral (whole_line_has_integral). The proof computes the
   integral over [0, +oo[ from the primitive
   t |-> / a * gaussian_primitive (a * t)
   (gaussian_scaled_primitive_derivative) with MathComp's
   ge0_continuous_FTC2y, and doubles it with ge0_symfun_integralT, since the
   integrand is even.

   On the way: a * x tends to +oo with x (positive_dilation_limit_positive),
   so f (a * x) has the limit of f at +oo
   (positive_dilation_comp_limit_positive); and gaussian_mass = L - - L
   when gaussian_primitive tends to L at +oo
   (gaussian_primitive_limit_mass, from gaussian_kernel_line_FTC of
   GaussianKernel). The arithmetic in every statement is Stdlib's. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import GaussianKernel GaussianMass.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma positive_dilation_limit_positive a :
  0 < a -> ((a * x) @[x --> +oo%R] --> +oo%R)%classic.
Proof.
  move=> Ha.
  have key : forall M x : R, M / a < x -> M <= a * x.
  { move=> M x Hx.
    assert (H : a * (M / a) < a * x) by nra.
    replace (a * (M / a)) with M in H by (field; lra).
    lra. }
  apply/cvgryPge => M.
  exists (M / a); split; first exact: num_real.
  move=> x /RltP Hx; apply/RleP; exact: key.
Qed.

(* L is any set system on R, read as a filter by the notation -->: nbhs l
   for a finite limit l, or +oo%R and -oo%R. Rocq infers L from the limit
   hypothesis. *)
Lemma positive_dilation_comp_limit_positive (f : R -> R) a
    (L : set_system R) :
  0 < a -> (f x @[x --> +oo%R] --> L)%classic ->
  (f (a * x) @[x --> +oo%R] --> L)%classic.
Proof.
  move=> Ha HL.
  exact: (cvg_comp _ _ (positive_dilation_limit_positive a Ha) HL).
Qed.

Lemma gaussian_scaled_primitive_derivative a x :
  0 < a ->
  @is_derive R R^o R^o x 1 (fun t => / a * gaussian_primitive (a * t))
    (gaussian_kernel (a * x)).
Proof.
  intro Ha.
  replace (gaussian_kernel (a * x)) with
    (/ a * (a * gaussian_kernel (a * x))) by (field; lra).
  apply: is_derive_scal.
  have Hl : @is_derive R R^o R^o x 1 (fun t => a * t) a.
  { have H := is_derive_scal a (fun t => t) x 1 (is_derive_id_R x).
    rewrite Rmult_1_r in H; exact H. }
  exact: (is_derive_comp gaussian_primitive (fun t => a * t) x
    (gaussian_kernel (a * x)) a (gaussian_primitive_derivative (a * x)) Hl).
Qed.

Lemma gaussian_scaled_kernel_continuous a x :
  {for x, continuous (fun t => gaussian_kernel (a * t))}.
Proof.
  have Hl : @is_derive R R^o R^o x 1 (fun t => a * t) a.
  { have H := is_derive_scal a (fun t => t) x 1 (is_derive_id_R x).
    rewrite Rmult_1_r in H; exact H. }
  exact: (is_derive_continuous _ _ _ (is_derive_comp gaussian_kernel
    (fun t => a * t) x _ a (gaussian_kernel_derivative (a * x)) Hl)).
Qed.

Lemma gaussian_primitive_limit_mass (L : R) :
  (gaussian_primitive x @[x --> +oo%R] --> L)%classic ->
  gaussian_mass = L - - L.
Proof.
  move=> HP.
  exact: (gaussian_kernel_line_FTC gaussian_kernel gaussian_primitive L (- L)
    gaussian_primitive_derivative gaussian_kernel_continuous
    gaussian_kernel_integrable HP (gaussian_primitive_negative_limit L HP)).
Qed.

Theorem gaussian_scaled_kernel_integral a :
  0 < a ->
  whole_line_has_integral (fun x => gaussian_kernel (a * x))
    (gaussian_mass / a).
Proof.
  move=> Ha.
  have [L [HL HP]] := gaussian_primitive_positive_limit.
  have Hmass := gaussian_primitive_limit_mass L HP.
  pose h := fun x => gaussian_kernel (a * x).
  pose F := fun t => / a * gaussian_primitive (a * t).
  have h0 : forall x, (0 <= h x)%R.
  { move=> x; apply/RleP; exact: (Rlt_le _ _ (gaussian_kernel_positive _)). }
  have hc : continuous h := gaussian_scaled_kernel_continuous a.
  have he : h =1 h \o (@GRing.opp R).
  { move=> x; rewrite /h /comp -RoppE.
    replace (a * - x) with (- (a * x)) by ring.
    by rewrite gaussian_kernel_even. }
  have Hsym := ge0_symfun_integralT h0 hc he.
  have HD : forall x, @is_derive R R^o R^o x 1 F (h x).
  { move=> x; exact: (gaussian_scaled_primitive_derivative a x Ha). }
  have HF : (F x @[x --> +oo%R] --> / a * L)%classic.
  { have H1 := positive_dilation_comp_limit_positive gaussian_primitive a
      _ Ha HP.
    exact: (@cvgMl_tmp _ _ _ _ _ (/ a) L H1). }
  have HF0 : F 0 = 0.
  { rewrite /F Rmult_0_r.
    have H0 := gaussian_primitive_odd 0.
    rewrite Ropp_0 in H0.
    have -> : gaussian_primitive 0 = 0 by lra.
    ring. }
  have Hhalf : (\int[lebesgue_measure]_(x in `[0%R, +oo[)
      (h x)%:E = (/ a * L)%:E)%E.
  { have -> : ((/ a * L)%:E = (/ a * L)%:E - (F 0)%:E)%E.
    { by rewrite HF0 sube0. }
    apply: (@ge0_continuous_FTC2y R h F 0%R (/ a * L)).
    - by move=> x _; exact: h0.
    - exact: continuous_subspaceT.
    - exact: HF.
    - move=> x _; have [Hd _] := HD x; exact Hd.
    - apply: cvg_at_right_filter.
      exact: (is_derive_continuous _ _ _ (HD 0)).
    - move=> x _; rewrite derive1E.
      have [_ Hv] := HD x; exact Hv. }
  have Hset : [set x : R | (0 <= x)%R] = `[0%R, +oo[ by rewrite set_itvcy.
  rewrite Hset Hhalf in Hsym.
  split.
  - apply/integrableP; split.
    + apply/measurable_EFinP; exact: continuous_measurable_fun.
    + have -> : (\int[lebesgue_measure]_(x in setT)
          `|(EFin \o h) x|)%E =
          (\int[lebesgue_measure]_x (h x)%:E)%E.
      { apply: eq_integral => x _; rewrite /comp gee0_abs //.
        rewrite lee_fin; exact: h0. }
      rewrite Hsym; exact: ltry.
  - rewrite /whole_line_integral /Rintegral.
    change (fine (\int[lebesgue_measure]_(x in setT) (h x)%:E)%E =
      gaussian_mass / a).
    rewrite Hsym -EFinM /=.
    rewrite mulr_natl mulr2n -RplusE -!RmultE Hmass.
    field; lra.
Qed.
