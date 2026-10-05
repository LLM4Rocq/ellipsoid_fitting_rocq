(* Completing the square for a linear Gaussian tilt, using the library's
   shifted normal density with its proved total mass. *)
From Stdlib Require Import Reals Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions
  GaussianProbabilityDefinitions GaussianProbabilityDensity GaussianMass GaussianFubiniLebesgue.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma paper_main_gaussian_shifted_density t x :
  normal_pdf t 1 x = gaussian_density (x-t).
Proof.
rewrite -(gpb_density (x-t)) /gaussian_law_density !normal_pdfE ?oner_neq0 //.
rewrite (normal_fun_center t 1).
reflexivity.
Qed.

Lemma paper_main_gaussian_linear_tilt_density t x :
  exp (t*x) * gaussian_density x = exp (t^2/2) * normal_pdf t 1 x.
Proof.
rewrite paper_main_gaussian_shifted_density /gaussian_density /gaussian_kernel /Rdiv.
rewrite -!Rmult_assoc.
congr (_ * /gaussian_mass).
rewrite -!exp_plus.
f_equal; field.
Qed.

Lemma paper_main_gaussian_linear_density_integral t :
  whole_line_has_integral (fun x => exp (t*x)*gaussian_density x) (exp (t^2/2)).
Proof.
have E : (fun x => exp (t*x)*gaussian_density x) =
  (fun x => exp (t^2/2)*normal_pdf t 1 x).
{ apply: funext => x; exact: paper_main_gaussian_linear_tilt_density. }
rewrite E /whole_line_has_integral; split.
- rewrite /whole_line_integrable /=.
  change (lebesgue_measure.-integrable setT
    (fun x : measurableTypeR R => (exp (t^2/2)*normal_pdf t 1 x)%:E)).
  have -> : (fun x : measurableTypeR R => (exp (t^2/2)*normal_pdf t 1 x)%:E) =
    (fun x : measurableTypeR R => ((exp (t^2/2))%:E*(normal_pdf t 1 x)%:E)%E).
  { apply: funext => x; exact: EFinM. }
  apply: integrableZl => //; exact: integrable_normal_pdf.
- rewrite /whole_line_integral /Rintegral.
  under eq_integral do rewrite EFinM.
  rewrite integralZl ?integrable_normal_pdf // integral_normal_pdf mule1.
  reflexivity.
Qed.

Lemma paper_main_gaussian_from_density f l :
  whole_line_has_integral (fun x => f x*gaussian_density x) l ->
  gaussian_integral_exists f /\ gaussian_expectation f = l.
Proof.
move=> [HI HE].
have HM := gaussian_mass_positive.
have E : (fun x => f x*gaussian_kernel x) =
  (fun x => gaussian_mass*(f x*gaussian_density x)).
{ apply: funext => x; rewrite /gaussian_density; field; lra. }
split.
- rewrite /gaussian_integral_exists E.
  exact: (fubini_integrable_scale _ _ gaussian_mass measurableT HI).
- rewrite /gaussian_expectation /gaussian_integral E.
  rewrite fubini_integral_scale_l // HE.
  field; lra.
Qed.
