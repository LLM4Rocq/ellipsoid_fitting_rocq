(* Helper lemmas for the challenge gaussian_probability_bridge, second part:
   integrability and expectation under the standard normal law of
   MathComp-Analysis against the library's Gaussian integrals. Written by the
   solver on 30 September 2026. Proof module: no Definition, Axiom, Parameter
   or Admitted.
   - gpb_integrable_iff: integrability under the law is gaussian_integral_exists.
   - gpb_law_on, gpb_law_setT: the law on Borel sets, and its total mass.
   - gpb_RNc_ae, gpb_law_integral: the Radon-Nikodym derivative of the law's
     charge is normal_pdf 0 1 a.e., so an integrable f has expectation
     gaussian_expectation f under the law.
   - gpb_law_expectation, gpb_first_moment, gpb_second_moment. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import trigo probability normal_distribution charge.
From mathcomp Require Import sequences exp measurable_realfun boolp.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions GaussianProbabilityDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityDensity.
From EllipsoidFitting Require GaussianMass GaussianMoments.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma gpb_integrable_iff (f : R -> R) :
  gaussian_law_integrable f <-> gaussian_integral_exists f.
Proof.
rewrite /gaussian_law_integrable /gaussian_integral_exists /whole_line_integrable.
have hc := gpb_sqrt_pos.
have Hmu : forall mf : measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (f x)%:E),
  (\int[gpb_mu]_x `|(f x * gaussian_kernel x)%:E| =
   (Num.sqrt (pi *+ 2))%:E * \int[gaussian_law]_x `|(f x)%:E|)%E.
{ move=> mf; rewrite (gpb_law_abs f mf) muleA -EFinM divff ?mul1e //; exact: lt0r_neq0. }
split.
- move=> /integrableP [mf fin].
  have mf2 : measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (f x)%:E) := mf.
  apply/integrableP; split.
  + apply/measurable_EFinP; apply: measurable_funM.
    * exact/measurable_EFinP.
    * by move/measurable_EFinP: gpb_kernel_measurable.
  + rewrite (Hmu mf2); apply: lte_mul_pinfty => //; by rewrite lee_fin ltW.
- move=> /integrableP [mfk fin].
  have mfk2 : measurable_fun [set: measurableTypeR R]
      (fun x : measurableTypeR R => (f x * gaussian_kernel x)%:E) := mfk.
  have mf : measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (f x)%:E).
  { apply/measurable_EFinP.
    have -> : f = (fun x => (f x * gaussian_kernel x) * (gaussian_kernel x)^-1).
      by apply: funext => x; rewrite mulfK //; exact: lt0r_neq0 (gpb_kernel_pos x).
    apply: measurable_funM.
    - exact/measurable_EFinP.
    - by move/measurable_EFinP: gpb_kernel_inv_measurable. }
  apply/integrableP; split; first exact: mf.
  rewrite (gpb_law_abs f mf).
  apply: lte_mul_pinfty => //; by rewrite lee_fin invr_ge0 ltW.
Qed.

Lemma gpb_RNc_ae : ae_eq gpb_mu setT
  (Radon_Nikodym (charge_of_finite_measure gaussian_law) gpb_mu)
  (fun x => (normal_pdf 0 1 x)%:E).
Proof.
have hd : charge_of_finite_measure gaussian_law `<< gpb_mu by exact: gpb_dom.
apply: integral_ae_eq => //.
- exact: Radon_Nikodym_integrable hd.
- exact: gpb_pdf_measurable.
- move=> E _ mE; rewrite -(Radon_Nikodym_integral hd mE); by [].
Qed.

Lemma gpb_law_integral (f : R -> R) : gaussian_integral_exists f ->
  (\int[gaussian_law]_x (f x)%:E = (gaussian_expectation f)%:E)%E.
Proof.
move=> hf.
have hl : gaussian_law_integrable f by apply/gpb_integrable_iff.
have mf : measurable_fun [set: measurableTypeR R] (fun x : measurableTypeR R => (f x)%:E).
{ by case/integrableP: hl. }
have hd : charge_of_finite_measure gaussian_law `<< gpb_mu by exact: gpb_dom.
have E : (\int[gpb_mu]_x ((f x)%:E *
      Radon_Nikodym (charge_of_finite_measure gaussian_law) gpb_mu x) =
    \int[gpb_mu]_x ((f x)%:E * (normal_pdf 0 1 x)%:E))%E.
{ apply: ae_eq_integral => //.
  - by apply: emeasurable_funM => //;
      solve [exact: mf | exact: measurable_int (Radon_Nikodym_integrable hd)].
  - by apply: emeasurable_funM => //; solve [exact: mf | exact: gpb_pdf_measurable].
  - exact: ae_eqe_mul2l gpb_RNc_ae. }
rewrite -(Radon_Nikodym_change_of_variables gpb_dom measurableT hl) E.
under eq_integral do rewrite -EFinM -/(gaussian_law_density _) gpb_law_densityE mulrCA EFinM.
have hf2 : gpb_mu.-integrable [set: measurableTypeR R]
    (fun x : measurableTypeR R => (f x * gaussian_kernel x)%:E) := hf.
rewrite integralZl //.
have hI := integrable_fin_num measurableT hf2.
rewrite -(fineK hI) -EFinM /gaussian_expectation /gaussian_integral /whole_line_integral /Rintegral gpb_mass.
by rewrite RdivE mulrC.
Qed.
