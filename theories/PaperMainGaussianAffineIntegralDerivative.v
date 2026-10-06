(* Local domination for differentiating bounded Gaussian convolutions.
   The density coordinate is (y-t)/eps and the neighborhood radius is eps. *)
From Stdlib Require Import Reals Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge AnalysisIntegralDefinitions
  GaussianDefinitions GaussianKernel GaussianFubiniLebesgue GaussianAdmissible
  GaussianExpectation PaperMainGaussianAffineIntegralStdlib.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_affine_density0 eps (h : R -> R) t y :=
  h y * gaussian_kernel ((y - t) / eps) / eps.
Definition paper_main_gaussian_affine_density1 eps (h : R -> R) t y :=
  h y * ((y - t) / eps) * gaussian_kernel ((y - t) / eps) / eps.
Definition paper_main_gaussian_affine_densityD0 eps (h : R -> R) t y :=
  h y * ((y - t) / eps) * gaussian_kernel ((y - t) / eps) / eps ^ 2.
Definition paper_main_gaussian_affine_densityD1 eps (h : R -> R) t y :=
  h y * (((y - t) / eps) ^ 2 - 1) * gaussian_kernel ((y - t) / eps) / eps ^ 2.
Definition paper_main_gaussian_affine_majorant eps K a y :=
  (3 * K / eps ^ 2 * exp 1) * (1 + ((y - a) / eps) ^ 2) *
    gaussian_kernel (((y - a) / eps) / 2).

Lemma paper_main_gaussian_kernel_shift_bound r z :
  Rabs (r - z) <= 1 -> gaussian_kernel z <= exp 1 * gaussian_kernel (r / 2).
Proof.
intros H; apply Rabs_le_between in H.
assert (Hb : (r - z) ^ 2 <= 1) by nra.
pose proof (pow2_ge_0 (r - 2 * z)).
unfold gaussian_kernel; rewrite <- exp_plus; apply Rlt_le, exp_increasing; nra.
Qed.

Lemma paper_main_gaussian_hermite_shift_bounds r z :
  Rabs (r - z) <= 1 ->
  Rabs z <= 3 * (1 + r ^ 2) /\ Rabs (z ^ 2 - 1) <= 3 * (1 + r ^ 2).
Proof.
intros H; apply Rabs_le_between in H.
assert (Hb : (r - z) ^ 2 <= 1) by nra.
pose proof (pow2_ge_0 (z - 2 * r)).
pose proof (pow2_ge_0 r).
assert (Hz : z ^ 2 <= 2 * r ^ 2 + 2) by nra.
pose proof (pow2_ge_0 (z - 1)); pose proof (pow2_ge_0 (z + 1)).
split; apply Rabs_le; split; nra.
Qed.

Lemma paper_main_gaussian_affine_density0_derivative eps h t y :
  0 < eps ->
  @is_derive R R^o R^o t 1 (fun u => paper_main_gaussian_affine_density0 eps h u y)
    (paper_main_gaussian_affine_densityD0 eps h t y).
Proof.
intros Heps; unfold paper_main_gaussian_affine_density0,
  paper_main_gaussian_affine_densityD0, gaussian_kernel.
auto_derive; try lra; field; lra.
Qed.

Lemma paper_main_gaussian_affine_density1_derivative eps h t y :
  0 < eps ->
  @is_derive R R^o R^o t 1 (fun u => paper_main_gaussian_affine_density1 eps h u y)
    (paper_main_gaussian_affine_densityD1 eps h t y).
Proof.
intros Heps; unfold paper_main_gaussian_affine_density1,
  paper_main_gaussian_affine_densityD1, gaussian_kernel.
auto_derive; try lra; field; lra.
Qed.

Lemma paper_main_gaussian_affine_coordinate_near eps a t y :
  0 < eps -> Rabs (t - a) <= eps ->
  Rabs ((y - a) / eps - (y - t) / eps) <= 1.
Proof.
intros Heps Ht.
replace ((y - a) / eps - (y - t) / eps) with ((t - a) / eps) by (field; lra).
rewrite (Rabs_div (t - a) eps ltac:(lra)).
rewrite (Rabs_pos_eq eps (Rlt_le _ _ Heps)).
apply (Rmult_le_reg_r eps); [exact Heps|].
replace (Rabs (t - a) / eps * eps) with (Rabs (t - a)) by (field; lra).
lra.
Qed.

Lemma paper_main_gaussian_affine_majorant_nonnegative eps K a y :
  0 < eps -> 0 <= K -> 0 <= paper_main_gaussian_affine_majorant eps K a y.
Proof.
intros Heps HK; unfold paper_main_gaussian_affine_majorant, Rdiv.
pose proof (pow2_ge_0 ((y - a) * / eps)).
repeat apply Rmult_le_pos; try lra.
- left; apply Rinv_0_lt_compat; apply pow_lt; exact Heps.
- left; apply exp_pos.
- left; apply gaussian_kernel_positive.
Qed.

Lemma paper_main_gaussian_affine_density_dominate eps K a t y h q :
  0 < eps -> 0 <= K -> Rabs (h y) <= K -> Rabs (t - a) <= eps ->
  Rabs q <= 3 * (1 + ((y - a) / eps) ^ 2) ->
  Rabs (h y * q * gaussian_kernel ((y - t) / eps) / eps ^ 2) <=
    paper_main_gaussian_affine_majorant eps K a y.
Proof.
intros Heps HK Hh Ht Hq.
pose proof (paper_main_gaussian_affine_coordinate_near eps a t y Heps Ht) as Hnear.
pose proof (paper_main_gaussian_kernel_shift_bound _ _ Hnear) as Hkernel.
assert (He2 : 0 < eps ^ 2) by (apply pow_lt; exact Heps).
rewrite (Rabs_div (h y * q * gaussian_kernel ((y - t) / eps)) (eps ^ 2) ltac:(lra)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ He2)).
rewrite !Rabs_mult.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ (gaussian_kernel_positive _))).
replace (paper_main_gaussian_affine_majorant eps K a y) with
  ((K * (3 * (1 + ((y - a) / eps) ^ 2)) *
    (exp 1 * gaussian_kernel (((y - a) / eps) / 2))) / eps ^ 2).
2: { unfold paper_main_gaussian_affine_majorant, Rdiv; ring. }
apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact He2|].
apply Rmult_le_compat.
- apply Rmult_le_pos; apply Rabs_pos.
- left; apply gaussian_kernel_positive.
- apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Hh|exact Hq].
- exact Hkernel.
Qed.

Lemma paper_main_gaussian_affine_densityD0_bound eps K a t y h :
  0 < eps -> 0 <= K -> Rabs (h y) <= K -> Rabs (t - a) <= eps ->
  Rabs (paper_main_gaussian_affine_densityD0 eps h t y) <=
    paper_main_gaussian_affine_majorant eps K a y.
Proof.
intros Heps HK Hh Ht; unfold paper_main_gaussian_affine_densityD0.
apply paper_main_gaussian_affine_density_dominate; try assumption.
apply (proj1 (paper_main_gaussian_hermite_shift_bounds _ _
  (paper_main_gaussian_affine_coordinate_near eps a t y Heps Ht))).
Qed.

Lemma paper_main_gaussian_affine_densityD1_bound eps K a t y h :
  0 < eps -> 0 <= K -> Rabs (h y) <= K -> Rabs (t - a) <= eps ->
  Rabs (paper_main_gaussian_affine_densityD1 eps h t y) <=
    paper_main_gaussian_affine_majorant eps K a y.
Proof.
intros Heps HK Hh Ht; unfold paper_main_gaussian_affine_densityD1.
apply paper_main_gaussian_affine_density_dominate; try assumption.
apply (proj2 (paper_main_gaussian_hermite_shift_bounds _ _
  (paper_main_gaussian_affine_coordinate_near eps a t y Heps Ht))).
Qed.

Lemma paper_main_gaussian_affine_majorant_integrable eps K a :
  0 < eps -> whole_line_integrable (paper_main_gaussian_affine_majorant eps K a).
Proof.
intros Heps.
set c := 3 * K / eps ^ 2 * exp 1.
set H := paper_main_gaussian_affine_majorant eps K a.
assert (HC : continuous H).
{ intros y; unfold H, paper_main_gaussian_affine_majorant.
  apply (continuous_mult R).
  - apply (continuous_mult R); [apply (continuous_const R)|].
    apply (continuous_plus R); [apply (continuous_const R)|].
    apply (@continuous_comp R^o R^o R^o (fun x : R => (x - a) / eps) (fun z : R => z ^ 2) y);
      [exact: paper_main_affine_inverse_continuous|exact: continuous_Rpow].
  - apply (@continuous_comp R^o R^o R^o (fun x : R => ((x - a) / eps) / 2) gaussian_kernel y);
      [|exact: gaussian_kernel_continuous].
    unfold Rdiv; apply (continuous_mult R); [|apply (continuous_const R)].
    exact: paper_main_affine_inverse_continuous. }
apply (proj2 (paper_main_whole_line_affine_integrable a (2 * eps) H ltac:(lra) HC)).
assert (HE : (fun z => H (a + (2 * eps) * z) * (2 * eps)) =
  (fun z => (c * (2 * eps) * (1 + 4 * z ^ 2)) * gaussian_kernel z)).
{ apply functional_extensionality; intros z; unfold H, paper_main_gaussian_affine_majorant.
  replace ((a + 2 * eps * z - a) / eps) with (2 * z) by (field; lra).
  replace (2 * z / 2) with z by field.
  unfold c; ring. }
rewrite HE.
apply (gaussian_polynomial_integrable _ (4 * Rabs (c * (2 * eps))) 2).
- intros z; apply (continuous_mult R); [apply (continuous_const R)|].
  apply (continuous_plus R); [apply (continuous_const R)|].
  apply (continuous_mult R); [apply (continuous_const R)|apply continuous_Rpow].
- intros z.
  assert (Hz : 0 <= 1 + 4 * z ^ 2) by (pose proof (pow2_ge_0 z); nra).
  rewrite Rabs_mult (Rabs_pos_eq _ Hz).
  pose proof (Rabs_pos (c * (2 * eps))) as Hc.
  pose proof (Rsqr_abs z) as Hsq; unfold Rsqr in Hsq.
  nra.
Qed.

Lemma paper_main_gaussian_affine_shift_continuous (eps : R) (h : R -> R) (t : R) :
  continuous h -> continuous (fun z : R => h (t + eps * z)).
Proof.
intros Hh z; apply (@continuous_comp R^o R^o R^o (fun z : R => t + eps * z) h z).
- apply (continuous_plus R); [apply (continuous_const R)|].
  apply (continuous_mult R); [apply (continuous_const R)|apply continuous_id].
- exact: Hh.
Qed.

Lemma paper_main_gaussian_affine_bounded_domains eps h K t :
  0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  gaussian_integral_exists (fun z => h (t + eps * z)) /\
  gaussian_integral_exists (fun z => h (t + eps * z) * z).
Proof.
intros HK Hh Hb; split.
- apply (gaussian_polynomial_integrable _ K 0).
  + exact (paper_main_gaussian_affine_shift_continuous eps h t Hh).
  + intros z; pose proof (Hb (t + eps * z)); simpl; lra.
- apply (gaussian_polynomial_integrable _ K 1).
  + intros z; apply (continuous_mult R); [exact: paper_main_gaussian_affine_shift_continuous|apply continuous_id].
  + intros z; rewrite Rabs_mult; pose proof (Hb (t + eps * z)).
    pose proof (Rabs_pos z); simpl; nra.
Qed.

Lemma paper_main_gaussian_affine_density0_integral eps h t :
  0 < eps -> continuous h ->
  gaussian_integral (fun z => h (t + eps * z)) =
    whole_line_integral (paper_main_gaussian_affine_density0 eps h t).
Proof.
intros Heps Hh.
pose proof (paper_main_gaussian_affine_density_integral t eps h (fun _ => 1)
  Heps Hh (continuous_const R 1)) as H.
assert (H1 : (fun z => h (t + eps * z) * 1) = (fun z => h (t + eps * z))).
{ apply functional_extensionality; intros z; ring. }
assert (H2 : (fun y => h y * 1 * gaussian_kernel ((y - t) / eps) / eps) =
  paper_main_gaussian_affine_density0 eps h t).
{ apply functional_extensionality; intros y; unfold paper_main_gaussian_affine_density0, Rdiv; ring. }
rewrite H1 H2 in H; exact H.
Qed.

Lemma paper_main_gaussian_affine_density1_integral eps h t :
  0 < eps -> continuous h ->
  gaussian_integral (fun z => h (t + eps * z) * z) =
    whole_line_integral (paper_main_gaussian_affine_density1 eps h t).
Proof.
intros Heps Hh.
exact (paper_main_gaussian_affine_density_integral t eps h (fun z => z)
  Heps Hh continuous_id).
Qed.

Lemma paper_main_gaussian_affine_density_domains eps h K t :
  0 < eps -> 0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  whole_line_integrable (paper_main_gaussian_affine_density0 eps h t) /\
  whole_line_integrable (paper_main_gaussian_affine_density1 eps h t).
Proof.
intros Heps HK Hh Hb.
destruct (paper_main_gaussian_affine_bounded_domains eps h K t HK Hh Hb) as [HI0 HI1].
split.
- pose proof (paper_main_gaussian_affine_density_integrable t eps h (fun _ => 1)
    Heps Hh (continuous_const R 1)) as H.
  assert (H1 : (fun z => h (t + eps * z) * 1) = (fun z => h (t + eps * z))).
  { apply functional_extensionality; intros z; ring. }
  assert (H2 : (fun y => h y * 1 * gaussian_kernel ((y - t) / eps) / eps) =
    paper_main_gaussian_affine_density0 eps h t).
  { apply functional_extensionality; intros y; unfold paper_main_gaussian_affine_density0, Rdiv; ring. }
  rewrite H1 H2 in H; apply (proj1 H); exact HI0.
- exact (proj1 (paper_main_gaussian_affine_density_integrable t eps h (fun z => z)
    Heps Hh continuous_id) HI1).
Qed.

Theorem paper_main_gaussian_affine_integral0_derivative eps (h : R -> R) K a :
  0 < eps -> 0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  whole_line_integrable (paper_main_gaussian_affine_densityD0 eps h a) /\
  @is_derive R R^o R^o a 1
    (fun t => whole_line_integral (paper_main_gaussian_affine_density0 eps h t))
    (whole_line_integral (paper_main_gaussian_affine_densityD0 eps h a)).
Proof.
intros Heps HK Hh Hb.
apply (whole_line_parameter_derivative
  (paper_main_gaussian_affine_density0 eps h)
  (paper_main_gaussian_affine_densityD0 eps h) a eps
  (paper_main_gaussian_affine_majorant eps K a)).
- exact Heps.
- intros t y _; apply paper_main_gaussian_affine_density0_derivative; exact Heps.
- intros t _; exact (proj1 (paper_main_gaussian_affine_density_domains eps h K t Heps HK Hh Hb)).
- intros t y Ht; apply paper_main_gaussian_affine_densityD0_bound; auto.
- apply paper_main_gaussian_affine_majorant_integrable; exact Heps.
- intros y; apply paper_main_gaussian_affine_majorant_nonnegative; assumption.
Qed.

Theorem paper_main_gaussian_affine_integral1_derivative eps (h : R -> R) K a :
  0 < eps -> 0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  whole_line_integrable (paper_main_gaussian_affine_densityD1 eps h a) /\
  @is_derive R R^o R^o a 1
    (fun t => whole_line_integral (paper_main_gaussian_affine_density1 eps h t))
    (whole_line_integral (paper_main_gaussian_affine_densityD1 eps h a)).
Proof.
intros Heps HK Hh Hb.
apply (whole_line_parameter_derivative
  (paper_main_gaussian_affine_density1 eps h)
  (paper_main_gaussian_affine_densityD1 eps h) a eps
  (paper_main_gaussian_affine_majorant eps K a)).
- exact Heps.
- intros t y _; apply paper_main_gaussian_affine_density1_derivative; exact Heps.
- intros t _; exact (proj2 (paper_main_gaussian_affine_density_domains eps h K t Heps HK Hh Hb)).
- intros t y Ht; apply paper_main_gaussian_affine_densityD1_bound; auto.
- apply paper_main_gaussian_affine_majorant_integrable; exact Heps.
- intros y; apply paper_main_gaussian_affine_majorant_nonnegative; assumption.
Qed.

Lemma paper_main_gaussian_affine_derivative_transport eps (h w : R -> R) a :
  0 < eps -> continuous h -> continuous w ->
  gaussian_integral_exists (fun z => h (a + eps * z) * w z) ->
  whole_line_integral (fun y =>
    h y * w ((y - a) / eps) * gaussian_kernel ((y - a) / eps) / eps ^ 2) =
    / eps * gaussian_integral (fun z => h (a + eps * z) * w z).
Proof.
intros Heps Hh Hw HI.
pose proof (proj1 (paper_main_gaussian_affine_density_integrable a eps h w Heps Hh Hw) HI) as HF.
pose proof (paper_main_gaussian_affine_density_integral a eps h w Heps Hh Hw) as HE.
rewrite HE.
rewrite <- (fubini_integral_scale_l _ (/ eps) HF).
apply: congr1; apply functional_extensionality; intros y; field; lra.
Qed.

Lemma paper_main_gaussian_affine_hermite_domain eps (h : R -> R) K a :
  0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  gaussian_integral_exists (fun z => h (a + eps * z) * (z ^ 2 - 1)).
Proof.
intros HK Hh Hb.
apply (gaussian_polynomial_integrable _ K 2).
- intros z; apply (continuous_mult R).
  + exact: paper_main_gaussian_affine_shift_continuous.
  + apply (continuous_minus R); [apply continuous_Rpow|apply (continuous_const R)].
- intros z; rewrite Rabs_mult.
  pose proof (Hb (a + eps * z)) as Hbound.
  pose proof (Rabs_pos (h (a + eps * z))) as Hh0.
  pose proof (Rabs_pos (z ^ 2 - 1)) as Hz0.
  assert (HZ : Rabs (z ^ 2 - 1) <= 1 + Rabs z ^ 2).
  { apply Rabs_le; pose proof (pow2_ge_0 z); pose proof (Rsqr_abs z) as Hsq;
    unfold Rsqr in Hsq; split; nra. }
  nra.
Qed.

Theorem paper_main_gaussian_shift_expectation_derivative eps (h : R -> R) K a :
  0 < eps -> 0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  @is_derive R R^o R^o a 1
    (fun t => gaussian_expectation (fun z => h (t + eps * z)))
    (/ eps * gaussian_expectation (fun z => h (a + eps * z) * z)).
Proof.
intros Heps HK Hh Hb.
destruct (paper_main_gaussian_affine_integral0_derivative eps h K a Heps HK Hh Hb)
  as [HI HD].
pose proof (proj2 (paper_main_gaussian_affine_bounded_domains eps h K a HK Hh Hb)) as HIz.
pose proof (paper_main_gaussian_affine_derivative_transport eps h (fun z => z) a
  Heps Hh continuous_id HIz) as HT.
change (whole_line_integral (paper_main_gaussian_affine_densityD0 eps h a) =
  / eps * gaussian_integral (fun z => h (a + eps * z) * z)) in HT.
pose proof (is_derive_scal_l (/ gaussian_mass)
  (fun t => whole_line_integral (paper_main_gaussian_affine_density0 eps h t))
  a _ HD) as HS.
rewrite HT in HS.
unfold gaussian_expectation, Rdiv.
replace (/ eps * (gaussian_integral (fun z => h (a + eps * z) * z) * / gaussian_mass))
  with ((/ eps * gaussian_integral (fun z => h (a + eps * z) * z)) * / gaussian_mass) by ring.
apply (is_derive_ext
  (fun t => whole_line_integral (paper_main_gaussian_affine_density0 eps h t) * / gaussian_mass)).
- intros t; rewrite <- (paper_main_gaussian_affine_density0_integral eps h t Heps Hh).
  reflexivity.
- exact HS.
Qed.

Theorem paper_main_gaussian_shift_weighted_expectation_derivative eps (h : R -> R) K a :
  0 < eps -> 0 <= K -> continuous h -> (forall y, Rabs (h y) <= K) ->
  @is_derive R R^o R^o a 1
    (fun t => gaussian_expectation (fun z => h (t + eps * z) * z))
    (/ eps * gaussian_expectation (fun z => h (a + eps * z) * (z ^ 2 - 1))).
Proof.
intros Heps HK Hh Hb.
destruct (paper_main_gaussian_affine_integral1_derivative eps h K a Heps HK Hh Hb)
  as [HI HD].
pose proof (paper_main_gaussian_affine_hermite_domain eps h K a HK Hh Hb) as HIz.
assert (HC : continuous (fun z : R => z ^ 2 - 1)).
{ intros z; apply (continuous_minus R); [apply continuous_Rpow|apply (continuous_const R)]. }
pose proof (paper_main_gaussian_affine_derivative_transport eps h (fun z => z ^ 2 - 1) a
  Heps Hh HC HIz) as HT.
change (whole_line_integral (paper_main_gaussian_affine_densityD1 eps h a) =
  / eps * gaussian_integral (fun z => h (a + eps * z) * (z ^ 2 - 1))) in HT.
pose proof (is_derive_scal_l (/ gaussian_mass)
  (fun t => whole_line_integral (paper_main_gaussian_affine_density1 eps h t))
  a _ HD) as HS.
rewrite HT in HS.
unfold gaussian_expectation, Rdiv.
replace (/ eps * (gaussian_integral (fun z => h (a + eps * z) * (z ^ 2 - 1)) * / gaussian_mass))
  with ((/ eps * gaussian_integral (fun z => h (a + eps * z) * (z ^ 2 - 1))) * / gaussian_mass) by ring.
apply (is_derive_ext
  (fun t => whole_line_integral (paper_main_gaussian_affine_density1 eps h t) * / gaussian_mass)).
- intros t; rewrite <- (paper_main_gaussian_affine_density1_integral eps h t Heps Hh).
  reflexivity.
- exact HS.
Qed.
