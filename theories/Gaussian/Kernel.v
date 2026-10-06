(* The Gaussian kernel gaussian_kernel x = exp (- (x * x) / 2) of
   GaussianDefinitions, and its relation to the standard normal law
   normal_prob 0 1 of MathComp-Analysis.

   The kernel is normal_fun 0 1, and the density of the law is
   normal_peak 1 * gaussian_kernel x (gaussian_kernelE,
   normal_pdf_gaussian_kernel). So a function is integrable against the
   kernel exactly when it is integrable under the law
   (gaussian_integral_exists_normal), and its integral against the kernel
   is (normal_peak 1)^-1 times its integral under the law
   (gaussian_integral_normal, whole_line_integral_normal). The other modules
   of the group read the mass, the moments and the integrability of
   functions of polynomial growth off the library
   (GaussianAnalysis.normal_integral and gauss_moments) through these
   lemmas.

   The kernel is positive, has derivative - x * gaussian_kernel x, and tends
   to 0 at -oo and +oo. Rabs x * gaussian_kernel x is integrable
   (gaussian_kernel_abs_moment_integrable) and x * gaussian_kernel x has
   integral 0 (gaussian_first_moment_zero, from normal_mean).
   gaussian_stein_improper_decay is the fundamental theorem of calculus on
   the line for f * gaussian_kernel: if that product tends to 0 at both
   ends and its derivative, gaussian_stein_integrand f df, is integrable,
   then the derivative has integral 0.

   The integrals over the line are Lebesgue integrals, which require
   absolute integrability, and the integrability of the Stein integrand
   does not follow from the other hypotheses: f x = sin (exp (x * x)) is
   bounded with a continuous derivative df, but df x * gaussian_kernel x
   is not absolutely integrable. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import Analysis.RectangleFubini
  Analysis.ParameterIntegrals.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From GaussianAnalysis Require Import normal_integral gauss_moments.
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

(* The kernel and the standard normal law normal_prob 0 1 of
   MathComp-Analysis, at Stdlib's R. *)
Section normal_law.
Local Open Scope ring_scope.
Local Notation N := (@normal_prob R 0 1).
Local Notation mu := (@lebesgue_measure R).

Lemma gaussian_kernel_gt0 x : 0 < gaussian_kernel x.
Proof. by apply/RltP; exact: gaussian_kernel_positive. Qed.

Lemma gaussian_kernelE x : gaussian_kernel x = normal_fun 0 1 x.
Proof.
rewrite /gaussian_kernel /normal_fun RexpE; congr expR.
rewrite subr0 expr1n expr2; reflexivity.
Qed.

Lemma normal_pdf_gaussian_kernel x :
  normal_pdf 0 1 x = normal_peak 1 * gaussian_kernel x.
Proof. by rewrite normal_pdfE ?oner_neq0 //= gaussian_kernelE. Qed.

Lemma normal_peak1_gt0 : 0 < normal_peak (1 : R).
Proof. exact: normal_peak_gt0 (oner_neq0 _). Qed.

Lemma gaussian_kernel_normal_pdf x :
  gaussian_kernel x = (normal_peak 1)^-1 * normal_pdf 0 1 x.
Proof.
by rewrite normal_pdf_gaussian_kernel mulrA mulVf ?mul1r // lt0r_neq0 // normal_peak1_gt0.
Qed.

Lemma gaussian_kernel_measurable :
  measurable_fun [set: measurableTypeR R]
    (gaussian_kernel : measurableTypeR R -> measurableTypeR R).
Proof.
apply: (eq_measurable_fun (normal_fun 0 1)); last exact: measurable_normal_fun.
by move=> x _; rewrite gaussian_kernelE.
Qed.

Lemma gaussian_kernel_inv_measurable :
  measurable_fun [set: measurableTypeR R]
    ((fun x => (gaussian_kernel x)^-1) : measurableTypeR R -> measurableTypeR R).
Proof.
apply: (eq_measurable_fun (fun x : measurableTypeR R => expR (x * x / 2))).
  move=> x _; rewrite /gaussian_kernel RexpE -expRN; congr expR.
  by rewrite RdivE RoppE RmultE mulNr opprK.
apply: measurableT_comp => //; apply: measurable_funM => //.
exact: measurable_funM.
Qed.

(* A function integrable against the kernel is measurable. *)
Lemma gaussian_integral_exists_measurable (f : R -> R) :
  gaussian_integral_exists f ->
  measurable_fun [set: measurableTypeR R] (f : measurableTypeR R -> measurableTypeR R).
Proof.
move=> /integrableP[/measurable_EFinP mfk _].
have -> : f = (fun x => (f x * gaussian_kernel x) * (gaussian_kernel x)^-1).
  by apply/funext => x; rewrite mulfK // lt0r_neq0 // gaussian_kernel_gt0.
exact: measurable_funM mfk gaussian_kernel_inv_measurable.
Qed.

(* f is integrable against the kernel iff it is integrable under the law. *)
Lemma gaussian_integral_exists_normal (f : R -> R) :
  gaussian_integral_exists f <->
  N.-integrable [set: measurableTypeR R] (EFin \o f).
Proof.
have p0 : normal_peak 1 != 0 :> R by rewrite lt0r_neq0 // normal_peak1_gt0.
have E : (fun x => (f x)%:E * (normal_pdf 0 1 x)%:E)%E =
    (fun x => (normal_peak 1)%:E * (f x * gaussian_kernel x)%:E)%E.
  by apply/funext => x; rewrite -!EFinM normal_pdf_gaussian_kernel mulrCA.
split=> Hf.
  have mf : measurable_fun [set: measurableTypeR R] (EFin \o f).
    by apply/measurable_EFinP; exact: gaussian_integral_exists_measurable.
  apply/(integrable_normal_prob _ _ mf); rewrite /= E.
  exact: (integrableZl measurableT (normal_peak 1) Hf).
have := (integrable_normal_prob _ _ (measurable_int _ Hf)).1 Hf.
rewrite /= E => /(integrableZl measurableT (normal_peak 1)^-1) H.
apply: (eq_integrable measurableT _ _ _ H) => x _ /=.
by rewrite muleA -!EFinM mulVf // mul1r.
Qed.

Lemma gaussian_integral_normal (f : R -> R) : gaussian_integral_exists f ->
  (\int[mu]_x (f x * gaussian_kernel x)%:E =
   ((normal_peak 1)^-1)%:E * \int[N]_x (f x)%:E)%E.
Proof.
move=> Hf; have Nf := (gaussian_integral_exists_normal f).1 Hf.
have p0 : normal_peak 1 != 0 :> R by rewrite lt0r_neq0 // normal_peak1_gt0.
rewrite (integral_normal_prob Nf).
under [in RHS]eq_integral do
  rewrite /= -EFinM normal_pdf_gaussian_kernel mulrCA EFinM.
by rewrite integralZl // muleA -EFinM mulVf // mul1e.
Qed.

Lemma whole_line_integral_normal (f : R -> R) : gaussian_integral_exists f ->
  whole_line_integral (fun x => f x * gaussian_kernel x) =
  (normal_peak 1)^-1 * fine (\int[N]_x (f x)%:E)%E.
Proof.
move=> Hf; rewrite /whole_line_integral /Rintegral gaussian_integral_normal //.
rewrite fineM //; apply: integrable_fin_num => //.
exact: ((gaussian_integral_exists_normal f).1 Hf).
Qed.

End normal_law.

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
apply/cvgNy_compNP.
have -> : gaussian_kernel \o (@GRing.opp _) = gaussian_kernel.
  apply/funext => x; rewrite /comp /gaussian_kernel; congr exp.
  by rewrite !(RoppE, RmultE, RdivE) mulrNN.
exact: gaussian_kernel_limit_positive.
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
   [-n, n] (fubini_cutoff_cvg of Analysis.ParameterIntegrals). *)
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

(* The first absolute moment of the kernel is finite: Rabs is integrable
   under the law (integrable_normal_exprn of the library). *)
Lemma gaussian_kernel_abs_moment_integrable :
  whole_line_integrable (fun x => Rabs x * gaussian_kernel x).
Proof.
apply/(gaussian_integral_exists_normal Rabs).
apply: (eq_integrable measurableT _ _ _ (integrable_normal_exprn 1)) => x _ /=.
by rewrite expr1 RabsE.
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

(* The first moment of the kernel is 0: the mean of the law is 0
   (normal_mean of the library). *)
Lemma gaussian_first_moment_zero :
  whole_line_has_integral (fun x => x * gaussian_kernel x) 0.
Proof.
have Nf : (@normal_prob R 0 1).-integrable [set: measurableTypeR R]
    (EFin \o (fun x : R => x)).
  apply: (integrable_normal_poly (C := 1) (k := 1)) => [|x].
    exact: measurable_id.
  by rewrite /= expr1 mul1r lerDr.
have Hf : gaussian_integral_exists (fun x : R => x).
  exact/gaussian_integral_exists_normal.
split; first exact: Hf.
by rewrite (whole_line_integral_normal _ Hf) normal_mean /= mulr0.
Qed.
