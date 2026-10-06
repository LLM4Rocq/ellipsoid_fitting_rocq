(* The standard normal law gaussian_law, MathComp-Analysis's normal_prob 0 1,
   against the Gaussian kernel of GaussianDefinitions.
   - gpb_mass: gaussian_mass = sqrt (2 pi), from MathComp's
     integral_normal_pdf and the integrability of the kernel.
   - gpb_RN_ae and gpb_change_ge0: the Radon-Nikodym derivative of the law
     with respect to Lebesgue measure is normal_pdf 0 1 almost everywhere,
     so the integral of a nonnegative measurable function against the law
     is its Lebesgue integral against that density.
   - gpb_law_abs: the integral of |f| against the law is (sqrt (2 pi))^-1
     times the Lebesgue integral of |f * gaussian_kernel|.
   The kernel and its inverse are measurable (gpb_kernel_measurable,
   gpb_kernel_inv_measurable). *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import trigo probability normal_distribution charge.
From mathcomp Require Import sequences exp measurable_realfun.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions GaussianProbabilityDefinitions.
From EllipsoidFitting Require Gaussian.Mass.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Notation gpb_mu := (@lebesgue_measure R).

Lemma gpb_dom : gaussian_law `<< gpb_mu.
Proof. exact: normal_prob_dominates. Qed.

Lemma gpb_pdf_measurable : measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (normal_pdf 0 1 x)%:E).
Proof. by apply/measurable_EFinP; exact: measurable_normal_pdf. Qed.

Lemma gpb_RN_ae : ae_eq gpb_mu setT (Radon_Nikodym_SigmaFinite.f gaussian_law gpb_mu)
  (fun x => (normal_pdf 0 1 x)%:E).
Proof.
apply: integral_ae_eq => //.
- exact: Radon_Nikodym_SigmaFinite.f_integrable gpb_dom.
- exact: gpb_pdf_measurable.
- move=> E _ mE; rewrite -(Radon_Nikodym_SigmaFinite.f_integral gpb_dom mE).
  by [].
Qed.

Lemma gpb_change_ge0 (f : measurableTypeR R -> \bar R) : (forall x, 0 <= f x) -> measurable_fun setT f ->
  \int[gaussian_law]_x f x = \int[gpb_mu]_x (f x * (normal_pdf 0 1 x)%:E).
Proof.
move=> f0 mf.
rewrite -(Radon_Nikodym_SigmaFinite.change_of_variables gpb_dom f0 measurableT mf).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
  exact: measurable_int (Radon_Nikodym_SigmaFinite.f_integrable gpb_dom).
- by apply: emeasurable_funM => //; exact: gpb_pdf_measurable.
- exact: ae_eqe_mul2l gpb_RN_ae.
Qed.

Local Open Scope ring_scope.

Lemma gpb_kernelE (x : R) : gaussian_kernel x = normal_fun 0 1 x.
Proof.
rewrite /gaussian_kernel /normal_fun RexpE; congr expR.
rewrite subr0 expr1n expr2; reflexivity.
Qed.

Lemma gpb_law_densityE (x : R) :
  gaussian_law_density x = (Num.sqrt (pi *+ 2))^-1 * gaussian_kernel x.
Proof.
rewrite /gaussian_law_density normal_pdfE ?oner_neq0 // /normal_peak expr1n mul1r.
by rewrite gpb_kernelE.
Qed.

Lemma gpb_sqrt_pos : 0 < Num.sqrt (pi *+ 2) :> R.
Proof. by rewrite sqrtr_gt0 pmulrn_lgt0 // pi_gt0. Qed.

Lemma gpb_kernel_integral :
  (\int[gpb_mu]_x (gaussian_kernel x)%:E = gaussian_mass%:E)%E.
Proof.
have [HI HV] := Gaussian.Mass.gaussian_kernel_mass_integral.
rewrite -HV /whole_line_integral /Rintegral fineK //.
exact: integrable_fin_num HI.
Qed.

Lemma gpb_mass : gaussian_mass = Num.sqrt (pi *+ 2).
Proof.
have H : (\int[gpb_mu]_x (gaussian_law_density x)%:E = 1)%E by exact: integral_normal_pdf.
have E : (\int[gpb_mu]_x (gaussian_law_density x)%:E =
    ((Num.sqrt (pi *+ 2))^-1)%:E * \int[gpb_mu]_x (gaussian_kernel x)%:E)%E.
{ under eq_integral do rewrite gpb_law_densityE EFinM.
  apply: integralZl => //; exact: Gaussian.Mass.gaussian_kernel_integrable. }
rewrite E gpb_kernel_integral -EFinM in H.
have H' : (Num.sqrt (pi *+ 2))^-1 * gaussian_mass = 1 by case: H.
have hc := gpb_sqrt_pos.
by rewrite -[LHS]mul1r -[in LHS](divff (lt0r_neq0 hc)) -mulrA H' mulr1.
Qed.

Lemma gpb_kernel_pos (x : R) : 0 < gaussian_kernel x.
Proof. by rewrite /gaussian_kernel RexpE expR_gt0. Qed.

Lemma gpb_kernel_measurable :
  measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (gaussian_kernel x)%:E).
Proof.
apply/measurable_EFinP.
apply: (eq_measurable_fun (normal_fun 0 1)); last exact: measurable_normal_fun.
by move=> x _; rewrite gpb_kernelE.
Qed.

Lemma gpb_kernel_inv_measurable :
  measurable_fun [set: measurableTypeR R]
    (fun x : measurableTypeR R => ((gaussian_kernel x)^-1)%:E).
Proof.
apply/measurable_EFinP.
apply: (eq_measurable_fun (fun x : measurableTypeR R => expR ((x * x) / 2))); last first.
  apply: measurableT_comp => //; apply: measurable_funM => //.
  exact: measurable_funM.
move=> x _; rewrite /gaussian_kernel RexpE -expRN; congr expR.
by rewrite RdivE RoppE RmultE mulNr opprK.
Qed.

Lemma gpb_abs_pdf (f : R -> R) (x : R) :
  (`|f x|%:E * (normal_pdf 0 1 x)%:E =
   ((Num.sqrt (pi *+ 2))^-1)%:E * `|f x * gaussian_kernel x|%:E)%E.
Proof.
rewrite -!EFinM; congr EFin.
rewrite -/(gaussian_law_density x) gpb_law_densityE normrM (gtr0_norm (gpb_kernel_pos x)).
by rewrite mulrCA.
Qed.

Lemma gpb_law_abs (f : R -> R) :
  measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (f x)%:E) ->
  (\int[gaussian_law]_x `|(f x)%:E| =
   ((Num.sqrt (pi *+ 2))^-1)%:E * \int[gpb_mu]_x `|(f x * gaussian_kernel x)%:E|)%E.
Proof.
move=> mf.
have mabs : measurable_fun [set: measurableTypeR R]
    (fun x : measurableTypeR R => (`|(f x)%:E|)%E).
{ by apply: measurableT_comp => //. }
rewrite gpb_change_ge0 //.
under eq_integral do rewrite abse_EFin gpb_abs_pdf.
rewrite ge0_integralZl_EFin //.
apply: (eq_measurable_fun (fun x : measurableTypeR R => (`|(f x * gaussian_kernel x)%:E|)%E)).
  by move=> x _; rewrite abse_EFin.
apply: measurableT_comp => //.
apply/measurable_EFinP; apply: measurable_funM.
- exact/measurable_EFinP.
- by move/measurable_EFinP: gpb_kernel_measurable.
Qed.
