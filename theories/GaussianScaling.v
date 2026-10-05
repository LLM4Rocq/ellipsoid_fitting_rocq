(* Port of theories/GaussianScaling.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements use the vocabulary of AnalysisIntegralDefinitions
   and of the bridge, as in the ports of GaussianKernel and GaussianMass:
   Coquelicot's is_derive f x l becomes @is_derive R R^o R^o x 1 f l,
   continuous f x becomes {for x, continuous f}, is_lim f p_infty l and
   is_lim f m_infty l become (f x @[x --> +oo%R] --> l)%classic and
   (f x @[x --> -oo%R] --> l)%classic, and
   is_RInt_gen f (Rbar_locally m_infty) (Rbar_locally p_infty) l becomes
   whole_line_has_integral f l, the Lebesgue integral over the line. The
   arithmetic in every statement is Stdlib's, as in the original.

   Statements that change form.

   1. positive_dilation_limit_positive and positive_dilation_limit_negative
      say that a * x tends to +oo at +oo and to -oo at -oo. Coquelicot's
      neighbourhoods of p_infty and m_infty are the sets that contain a half
      line ]M, +oo[ or ]-oo, M[, and so are MathComp's +oo%R and -oo%R on R.
      They say the same as the originals.

   2. positive_dilation_comp_limit_positive and
      positive_dilation_comp_limit_negative. The limit L : Rbar of the
      original, a finite number or an infinity, becomes any set system L on
      R, read as a filter by the notation -->. The lemmas are thus
      generalizations: L := nbhs l gives the finite case, and L := +oo%R and
      L := -oo%R the two infinite ones. The call shape is unchanged, and
      Rocq infers L from the limit hypothesis.

   3. gaussian_scaled_kernel_integral concludes whole_line_has_integral,
      that is, Lebesgue integrability over the line with integral
      gaussian_mass / a, in place of the improper Riemann integral
      (difference 4 of analysis/README.md). The integrand is continuous and
      positive, so the two readings say the same thing. The proof no longer
      uses is_RInt_gen_Derive: as in the port of GaussianMass, it computes
      the integral over [0, +oo[ with MathComp's ge0_continuous_FTC2y and
      uses the symmetry lemma ge0_symfun_integralT, since the integrand is
      even.

   gaussian_scaled_primitive_derivative, gaussian_scaled_kernel_continuous
   and gaussian_primitive_limit_mass say the same thing as before, in the
   new vocabulary. The proof of gaussian_primitive_limit_mass applies
   gaussian_kernel_line_FTC of the port of GaussianKernel.

   The original imported Classical_Prop but did not use it. This port does
   not import it, so the assumptions of the module are the seven axioms of
   analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
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

Lemma positive_dilation_limit_negative a :
  0 < a -> ((a * x) @[x --> -oo%R] --> -oo%R)%classic.
Proof.
  move=> Ha.
  have key : forall M x : R, x < M / a -> a * x <= M.
  { move=> M x Hx.
    assert (H : a * x < a * (M / a)) by nra.
    replace (a * (M / a)) with M in H by (field; lra).
    lra. }
  apply/cvgrNyPle => M.
  exists (M / a); split; first exact: num_real.
  move=> x /RltP Hx; apply/RleP; exact: key.
Qed.

(* The limit L : Rbar of the original becomes any set system L on R
   (header, item 2). *)
Lemma positive_dilation_comp_limit_positive (f : R -> R) a
    (L : set_system R) :
  0 < a -> (f x @[x --> +oo%R] --> L)%classic ->
  (f (a * x) @[x --> +oo%R] --> L)%classic.
Proof.
  move=> Ha HL.
  exact: (cvg_comp _ _ (positive_dilation_limit_positive a Ha) HL).
Qed.

(* The limit L : Rbar of the original becomes any set system L on R
   (header, item 2). *)
Lemma positive_dilation_comp_limit_negative (f : R -> R) a
    (L : set_system R) :
  0 < a -> (f x @[x --> -oo%R] --> L)%classic ->
  (f (a * x) @[x --> -oo%R] --> L)%classic.
Proof.
  move=> Ha HL.
  exact: (cvg_comp _ _ (positive_dilation_limit_negative a Ha) HL).
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

(* The conclusion is the Lebesgue integral over the line (header, item 3). *)
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
