(* The Gaussian kernel gaussian_kernel x = exp (- (x * x) / 2), and Stein's
   identity, Gaussian integration by parts on the line.

   The kernel is positive, has derivative - x * gaussian_kernel x, and tends
   to 0 at -oo and +oo. Let f be bounded, with a continuous derivative df
   such that df t * gaussian_kernel t is integrable on the line. Then the
   derivative of f * gaussian_kernel, gaussian_stein_integrand f df, has
   integral 0 over the line (gaussian_stein_improper). So
   t * f t * gaussian_kernel t has the same integral as
   df t * gaussian_kernel t (gaussian_stein_split). The case f = 1 gives
   gaussian_first_moment_zero. gaussian_stein_improper_decay assumes
   instead that f * gaussian_kernel tends to 0 at -oo and +oo and that the
   Stein integrand is integrable.

   The integrals over the line are Lebesgue integrals, which require
   absolute integrability, and the integrability of df t * gaussian_kernel t
   does not follow from the other hypotheses. For example
   f x = sin (exp (x * x)) is bounded with a continuous derivative df, but
   df x * gaussian_kernel x is not absolutely integrable. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import RectangleFubini GaussianFubiniLebesgue.
From mathcomp Require Import measurable_realfun.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_kernel_positive x : 0 < gaussian_kernel x.
Proof. apply exp_pos. Qed.

Lemma gaussian_kernel_derivative x :
  @is_derive R R^o R^o x 1 gaussian_kernel (- x * gaussian_kernel x).
Proof.
  unfold gaussian_kernel.
  auto_derive.
  - lra.
  - field.
Qed.

Lemma gaussian_kernel_continuous x : {for x, continuous gaussian_kernel}.
Proof. exact (is_derive_continuous _ _ _ (gaussian_kernel_derivative x)). Qed.

Lemma gaussian_kernel_limit_positive :
  (gaussian_kernel x @[x --> +oo%R] --> 0)%classic.
Proof.
  unfold gaussian_kernel.
  have Hq : ((fun x => - (x * x) / 2) x @[x --> +oo%R] --> -oo%R)%classic.
  { apply/cvgrNyPle => M.
    exists (Rmax 1 (-2*M)); split; first exact: num_real.
    move=> x /RltP Hx; apply/RleP.
    pose proof (Rmax_l 1 (-2*M)).
    pose proof (Rmax_r 1 (-2*M)).
    assert (1 < x) by lra.
    assert (x <= x*x) by nra.
    lra. }
  exact: (cvg_comp _ _ Hq is_lim_exp_m).
Qed.

Lemma gaussian_kernel_limit_negative :
  (gaussian_kernel x @[x --> -oo%R] --> 0)%classic.
Proof.
  unfold gaussian_kernel.
  have Hq : ((fun x => - (x * x) / 2) x @[x --> -oo%R] --> -oo%R)%classic.
  { apply/cvgrNyPle => M.
    exists (Rmin (-1) (2*M)); split; first exact: num_real.
    move=> x /RltP Hx; apply/RleP.
    pose proof (Rmin_l (-1) (2*M)).
    pose proof (Rmin_r (-1) (2*M)).
    assert (x < -1) by lra.
    assert (-x <= x*x) by nra.
    lra. }
  exact: (cvg_comp _ _ Hq is_lim_exp_m).
Qed.

(* z is any filter on R: z := -oo%R and z := +oo%R give the limits at the
   two ends of the line. *)
Lemma gaussian_bounded_product_limit (f : R -> R) B (z : set_system R)
    {Fz : Filter z} :
  (forall x, Rabs (f x) <= B) ->
  (gaussian_kernel x @[x --> z] --> 0)%classic ->
  ((f x * gaussian_kernel x) @[x --> z] --> 0)%classic.
Proof.
  move=> Hb Hl.
  have Hlo : ((- B * gaussian_kernel x) @[x --> z] --> 0)%classic.
  { have H := @cvgMl_tmp _ _ _ Fz gaussian_kernel (- B) 0 Hl.
    rewrite mulr0 in H; exact H. }
  have Hhi : ((B * gaussian_kernel x) @[x --> z] --> 0)%classic.
  { have H := @cvgMl_tmp _ _ _ Fz gaussian_kernel B 0 Hl.
    rewrite mulr0 in H; exact H. }
  apply: (squeeze_cvgr _ Hlo Hhi).
  apply: nearW => x.
  specialize (Hb x).
  pose proof (Rle_abs (f x)).
  pose proof (Rle_abs (- f x)) as Hopp. rewrite Rabs_Ropp in Hopp.
  pose proof (gaussian_kernel_positive x).
  apply/andP; split; apply/RleP; nra.
Qed.

Lemma gaussian_product_derivative (f df : R -> R) x :
  @is_derive R R^o R^o x 1 f (df x) ->
  @is_derive R R^o R^o x 1 (fun t => f t * gaussian_kernel t)
    (gaussian_stein_integrand f df x).
Proof.
  intro Hf.
  unfold gaussian_stein_integrand.
  replace (df x * gaussian_kernel x - x * f x * gaussian_kernel x)
    with (df x * gaussian_kernel x + f x * (- x * gaussian_kernel x)) by ring.
  apply is_derive_mult.
  - exact Hf.
  - apply gaussian_kernel_derivative.
Qed.

Lemma gaussian_stein_continuous (f df : R -> R) x :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  {for x, continuous df} ->
  {for x, continuous (gaussian_stein_integrand f df)}.
Proof.
  intros Hd Hc.
  have Hf : {for x, continuous f} := is_derive_continuous _ _ _ (Hd x).
  unfold gaussian_stein_integrand.
  apply: continuous_minus.
  - apply: continuous_mult.
    + exact Hc.
    + apply gaussian_kernel_continuous.
  - apply: continuous_mult.
    + apply: continuous_mult.
      * apply continuous_id.
      * exact Hf.
    + apply gaussian_kernel_continuous.
Qed.

(* The fundamental theorem of calculus on the whole line, for a continuous
   integrable derivative. The proof takes the limit of the integrals over
   [-n, n] (fubini_cutoff_cvg of GaussianFubiniLebesgue). *)
Lemma gaussian_kernel_line_FTC (g F : R -> R) (L M : R) :
  (forall x, @is_derive R R^o R^o x 1 F (g x)) ->
  continuous g ->
  whole_line_integrable g ->
  (F x @[x --> +oo%R] --> L)%classic ->
  (F x @[x --> -oo%R] --> M)%classic ->
  whole_line_integral g = L - M.
Proof.
  move=> HF Hg Hi HL HM.
  have H1 := fubini_cutoff_cvg g Hi.
  have E : forall n : nat,
      Rintegral lebesgue_measure `[- INR n, INR n] g = F (INR n) - F (- INR n).
  { move=> n.
    rewrite -(rectangle_oriented_FTC F g (- INR n) (INR n) HF Hg).
    symmetry; apply: fubini_oriented_symmetric; exact: pos_INR. }
  have Hn : (INR n @[n --> \oo] --> +oo%R)%classic.
  { have -> : INR = (fun n : nat => n%:R%R) by apply/funext => n; exact: INRE.
    exact: cvgr_idn. }
  have HLn : (F (INR n) @[n --> \oo] --> L)%classic := cvg_comp _ _ Hn HL.
  have HM' := iffLR (cvgNy_compNP F (nbhs M)) HM.
  have HMn : (F (- INR n) @[n --> \oo] --> M)%classic := cvg_comp _ _ Hn HM'.
  have H2 : ((F (INR n) - F (- INR n)) @[n --> \oo] --> L - M)%classic.
  { exact: (@cvgB R R^o nat \oo _ _ _ L M HLn HMn). }
  apply: (fubini_seq_unique _ _ _ H1).
  rewrite (eq_cvg _ _ E).
  exact: H2.
Qed.

(* The first absolute moment of the kernel is finite: the integral of
   Rabs x * gaussian_kernel x over [0, +oo[ is 1, by MathComp's
   ge0_continuous_FTC2y, and the function is even. *)
Lemma gaussian_kernel_abs_moment_integrable :
  whole_line_integrable (fun x => Rabs x * gaussian_kernel x).
Proof.
  set h := fun x => Rabs x * gaussian_kernel x.
  have h0 : forall x, (0 <= h x)%R.
  { move=> x; apply/RleP; apply: Rmult_le_pos; first exact: Rabs_pos.
    exact: (Rlt_le _ _ (gaussian_kernel_positive x)). }
  have hc : continuous h.
  { move=> x; apply: continuous_mult; first exact: continuous_Rabs.
    exact: gaussian_kernel_continuous. }
  have he : h =1 h \o (@GRing.opp R).
  { move=> x; rewrite /h /comp /= -RoppE Rabs_Ropp.
    have -> : gaussian_kernel (- x) = gaussian_kernel x.
    { unfold gaussian_kernel; f_equal; field. }
    done. }
  have Hsym := ge0_symfun_integralT h0 hc he.
  have HF : forall x, @is_derive R R^o R^o x 1 (fun y => - gaussian_kernel y)
      (- (- x * gaussian_kernel x)).
  { move=> x; apply: is_derive_opp; exact: gaussian_kernel_derivative. }
  have Hhalf : (\int[lebesgue_measure]_(x in `[0%R, +oo[) (h x)%:E = 1%:E)%E.
  { have -> : (1%:E = 0%:E - (- gaussian_kernel 0)%:E)%E.
    { rewrite /gaussian_kernel.
      have -> : - (0 * 0) / 2 = 0 by field.
      rewrite exp_0 -EFinB; congr (_%:E); change (1 = 0 - - 1); lra. }
    apply: (@ge0_continuous_FTC2y R h (fun y => - gaussian_kernel y) 0%R 0%R).
    - by move=> x _; exact: h0.
    - exact: continuous_subspaceT.
    - have H : ((fun x => - gaussian_kernel x) @ +oo%R -->
          (- (0 : R))%R)%classic.
      { exact: (@cvgN R R^o R (+oo%R) _ gaussian_kernel 0
          gaussian_kernel_limit_positive). }
      rewrite oppr0 in H; exact H.
    - move=> x _; have [Hd _] := HF x; exact Hd.
    - apply: cvg_at_right_filter.
      exact: (is_derive_continuous _ _ _ (HF 0)).
    - move=> x; rewrite in_itv /= => /andP [/RltP x0 _].
      rewrite derive1E.
      have [_ Hv] := HF x.
      have -> : h x = - (- x * gaussian_kernel x).
      { rewrite /h (Rabs_pos_eq x (Rlt_le _ _ x0)); ring. }
      exact Hv. }
  have Hset : [set x : R | (0 <= x)%R] = `[0%R, +oo[ by rewrite set_itvcy.
  rewrite Hset Hhalf in Hsym.
  apply/integrableP; split.
  - apply/measurable_EFinP; exact: continuous_measurable_fun.
  - have -> : (\int[lebesgue_measure]_(x in setT) `|(EFin \o h) x|)%E =
        (\int[lebesgue_measure]_x (h x)%:E)%E.
    { apply: eq_integral => x _; rewrite /comp gee0_abs //.
      rewrite lee_fin; exact: h0. }
    rewrite Hsym; exact: ltry.
Qed.

(* For f continuous and bounded, x * f x * gaussian_kernel x is integrable. *)
Lemma gaussian_kernel_bounded_moment_integrable (f : R -> R) B :
  continuous f -> (forall x, Rabs (f x) <= B) ->
  whole_line_integrable (fun x => x * f x * gaussian_kernel x).
Proof.
  move=> Hc Hb.
  apply: (fubini_dominated_integrable setT _
    (fun x => Rabs x * gaussian_kernel x) B measurableT).
  - apply: fubini_continuous_measurable => x.
    apply: continuous_mult; last exact: gaussian_kernel_continuous.
    apply: continuous_mult; [exact: continuous_id | exact: Hc].
  - exact: gaussian_kernel_abs_moment_integrable.
  - move=> y _; cbv beta.
    rewrite !Rabs_mult
      (Rabs_pos_eq _ (Rlt_le _ _ (gaussian_kernel_positive y))).
    pose proof (Hb y); pose proof (Rabs_pos y).
    pose proof (gaussian_kernel_positive y); pose proof (Rabs_pos (f y)).
    have Hp : 0 <= Rabs y * gaussian_kernel y by nra.
    nra.
Qed.

(* The last hypothesis, the integrability of the Stein integrand on the
   line, does not follow from the others (see the example in the header). *)
Lemma gaussian_stein_improper_decay (f df : R -> R) :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (f x * gaussian_kernel x @[x --> -oo%R] --> 0)%classic ->
  (f x * gaussian_kernel x @[x --> +oo%R] --> 0)%classic ->
  whole_line_integrable (gaussian_stein_integrand f df) ->
  whole_line_has_integral (gaussian_stein_integrand f df) 0.
Proof.
  intros Hd Hc Hm Hp Hi.
  split; first exact Hi.
  have HP : forall x, @is_derive R R^o R^o x 1
      (fun t => f t * gaussian_kernel t) (gaussian_stein_integrand f df x).
  { intro x; apply gaussian_product_derivative; apply Hd. }
  have HC : continuous (gaussian_stein_integrand f df).
  { intro t; apply gaussian_stein_continuous; [exact Hd | apply Hc]. }
  rewrite (gaussian_kernel_line_FTC _ _ 0 0 HP HC Hi Hp Hm).
  ring.
Qed.

(* Since f is bounded, t * f t * gaussian_kernel t is integrable
   (gaussian_kernel_bounded_moment_integrable), so the last hypothesis gives
   the integrability of the Stein integrand. *)
Lemma gaussian_stein_improper (f df : R -> R) B :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (forall t, Rabs (f t) <= B) ->
  whole_line_integrable (fun t => df t * gaussian_kernel t) ->
  whole_line_has_integral (gaussian_stein_integrand f df) 0.
Proof.
  intros Hd Hc Hb Hi.
  have Hf : continuous f := fun t => is_derive_continuous _ _ _ (Hd t).
  have Hx := gaussian_kernel_bounded_moment_integrable f B Hf Hb.
  apply gaussian_stein_improper_decay; [exact Hd | exact Hc | | | ].
  - exact (gaussian_bounded_product_limit f B (-oo%R) Hb
      gaussian_kernel_limit_negative).
  - exact (gaussian_bounded_product_limit f B (+oo%R) Hb
      gaussian_kernel_limit_positive).
  - apply: (eq_integrable measurableT _ _ _ (integrableB measurableT Hi Hx)).
    move=> y _ /=.
    by rewrite -EFinB /gaussian_stein_integrand -RminusE.
Qed.

Lemma gaussian_stein_split (f df : R -> R) B l :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (forall t, Rabs (f t) <= B) ->
  whole_line_has_integral (fun t => df t * gaussian_kernel t) l ->
  whole_line_has_integral (fun t => t * f t * gaussian_kernel t) l.
Proof.
  intros Hd Hc Hb [Hi Hl].
  have Hf : continuous f := fun t => is_derive_continuous _ _ _ (Hd t).
  have Hx := gaussian_kernel_bounded_moment_integrable f B Hf Hb.
  have [Hs Hs0] := gaussian_stein_improper f df B Hd Hc Hb Hi.
  split; first exact Hx.
  have E : (fun t => t * f t * gaussian_kernel t) =
      (fun t => df t * gaussian_kernel t - gaussian_stein_integrand f df t).
  { apply/funext => t; unfold gaussian_stein_integrand; ring. }
  rewrite E /whole_line_integral (RintegralB measurableT Hi Hs).
  unfold whole_line_integral in Hl, Hs0.
  rewrite Hl Hs0 -RminusE; ring.
Qed.

Lemma gaussian_first_moment_zero :
  whole_line_has_integral (fun x => x * gaussian_kernel x) 0.
Proof.
  have H0 : whole_line_has_integral (fun t => 0 * gaussian_kernel t) 0.
  { have E : (fun t => 0 * gaussian_kernel t) = (fun _ => 0).
    { apply/funext => t; ring. }
    rewrite E; split.
    - exact: integrable0.
    - rewrite /whole_line_integral (Rintegral_cst _ measurableT).
      by rewrite mul0r. }
  have H := gaussian_stein_split (fun _ => 1) (fun _ => 0) 1 0
    (fun t => is_derive_const 1 t) (fun t => continuous_const _ 0 t)
    (fun t => Req_le _ _ Rabs_R1) H0.
  have E : (fun t => t * 1 * gaussian_kernel t) =
      (fun t => t * gaussian_kernel t).
  { apply/funext => t; ring. }
  rewrite E in H; exact H.
Qed.
