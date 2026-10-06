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

   The kernel is positive (gaussian_kernel_positive, gaussian_kernel_gt0)
   and its inverse is measurable (gaussian_kernel_inv_measurable), so a
   function with a Gaussian integral is measurable
   (gaussian_integral_exists_measurable). *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From GaussianAnalysis Require Import normal_integral gauss_moments.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_kernel_positive x : 0 < gaussian_kernel x.
Proof. apply exp_pos. Qed.

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
