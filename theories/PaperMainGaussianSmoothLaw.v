(* Bounded smooth tests under the exact public Gaussian product law.
   A continuous test with a polynomial bound is a measurable and
   integrable random variable for gaussian_product_law d, and its public
   expectation is the iterated Gaussian expectation. For a bounded C2
   test with squared gradient norm at most L^2, the centered exponential
   moment of the checked iterated bound transfers to the public law. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateSteinDomains
  GaussianProbabilityProductDefinitions GaussianProbabilityProductIntegrals
  GaussianProbabilityProductContinuity PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGaussianSmoothExponential
  PaperMainGaussianMGFBound.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_smooth_random d (f : list R -> R)
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R := f (tval x).

Lemma paper_main_gaussian_smooth_random_measurable d f :
  finite_joint_continuous d f ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_smooth_random d f).
Proof. move=> Hf; exact: (gpp_joint_measurable d f Hf). Qed.

Lemma paper_main_gaussian_law_transport d F C p :
  finite_joint_continuous d F -> finite_polynomial_bound d C p F ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> Hc Hb.
have [HI [HA _]] := gaussian_coordinate_polynomial_domain d F C p Hc Hb.
apply: (gpp_all_sections d F _ HI HA).
exact: (proj2 (measurable_EFinP _ _) (gpp_joint_measurable d F Hc)).
Qed.

Theorem paper_main_gaussian_smooth_law_expectation d f Df D2f M r :
  paper_main_gaussian_smooth_test d f Df D2f M r ->
  (gaussian_product_law d).-integrable setT (fun x => (f (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (f (tval x))%:E =
    (gaussian_iterated_expectation d f)%:E)%E.
Proof.
move=> [Hc _ _ _ _ Hb _ _].
exact: (paper_main_gaussian_law_transport d f M r Hc Hb).
Qed.

Lemma paper_main_gaussian_shift_continuous d f c :
  finite_joint_continuous d f ->
  finite_joint_continuous d (fun xs => f xs - c).
Proof.
move=> Hf; unfold Rminus.
apply: finite_joint_continuous_add; first exact: Hf.
exact: finite_joint_continuous_constant.
Qed.

Definition paper_main_gaussian_centered_exp d t (f : list R -> R) xs :=
  exp (t * (f xs - gaussian_iterated_expectation d f)).

Lemma paper_main_gaussian_centered_exp_continuous d t f :
  finite_joint_continuous d f ->
  finite_joint_continuous d (paper_main_gaussian_centered_exp d t f).
Proof.
move=> Hf.
exact: (paper_main_gaussian_exp_continuous d t _
  (paper_main_gaussian_shift_continuous d f (gaussian_iterated_expectation d f) Hf)).
Qed.

Lemma paper_main_gaussian_centered_exp_bound d t f M :
  0 <= t -> finite_polynomial_bound d M 0 f ->
  finite_polynomial_bound d
    (exp (t * (M + Rabs (gaussian_iterated_expectation d f)))) 0
    (paper_main_gaussian_centered_exp d t f).
Proof.
move=> Ht Hb.
have [HM HB] := proj1 (paper_main_polynomial_zero_bound d M f) Hb.
apply (proj2 (paper_main_polynomial_zero_bound d _ _)); split.
- apply Rlt_le; apply exp_pos.
- move=> xs Hxs; unfold paper_main_gaussian_centered_exp.
  set m := gaussian_iterated_expectation d f.
  rewrite (Rabs_pos_eq _ (Rlt_le _ _ (exp_pos _))).
  have Hf := HB xs Hxs.
  have H1 := Rle_abs (f xs).
  have H2 := Rle_abs (- m); rewrite Rabs_Ropp in H2.
  have Hle : t * (f xs - m) <= t * (M + Rabs m) by nra.
  destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt|Heq].
  + apply Rlt_le; apply exp_increasing; exact Hlt.
  + rewrite Heq; apply Rle_refl.
Qed.

Theorem paper_main_gaussian_smooth_law_centered_mgf d f Df D2f M L t :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 <= t ->
  (gaussian_product_law d).-integrable setT
    (fun x => (paper_main_gaussian_centered_exp d t f (tval x))%:E) /\
  (\int[gaussian_product_law d]_x
      (paper_main_gaussian_centered_exp d t f (tval x))%:E <=
    (exp (t ^ 2 * L ^ 2 / 2))%:E)%E.
Proof.
move=> Hs Hg Ht.
have Hs' := Hs; case: Hs' => Hc _ _ _ _ Hb _ _.
have [HI HE] := paper_main_gaussian_law_transport d
  (paper_main_gaussian_centered_exp d t f) _ 0
  (paper_main_gaussian_centered_exp_continuous d t f Hc)
  (paper_main_gaussian_centered_exp_bound d t f M Ht Hb).
split; first exact: HI.
rewrite HE lee_fin; apply/RleP.
exact: (paper_main_gaussian_bounded_centered_mgf d f Df D2f M L t Hs Hg Ht).
Qed.
