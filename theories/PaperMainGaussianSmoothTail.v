(* Gaussian concentration for bounded smooth tests under the exact public
   product law. If the squared gradient norm of a bounded C2 test f is at
   most L^2 everywhere, then f exceeds its mean by u, or falls below it by
   u, with probability at most exp(-u^2/(2 L^2)) each, by Chernoff's
   inequality applied to the transported centered exponential moment. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateSteinDomains GaussianCovarianceSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainGaussianSmoothCalculus PaperMainGaussianSmoothCovariance
  PaperMainGaussianMGFBound PaperMainGaussianSmoothLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_smooth_centered d (f : list R -> R)
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R :=
  f (tval x) - gaussian_iterated_expectation d f.

Lemma paper_main_gaussian_smooth_centered_measurable d f :
  finite_joint_continuous d f ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_smooth_centered d f).
Proof.
move=> Hf.
exact: (gpp_joint_measurable d _
  (paper_main_gaussian_shift_continuous d f (gaussian_iterated_expectation d f) Hf)).
Qed.

Lemma paper_main_gaussian_smooth_ge_measurable d f c :
  finite_joint_continuous d f ->
  measurable [set x : d.-tuple (measurableTypeR R) | Rle c (f (tval x))].
Proof.
move=> Hf.
have HE : [set x : d.-tuple (measurableTypeR R) | Rle c (f (tval x))] =
  paper_main_gaussian_smooth_random d f @^-1` `[c, +oo[.
{ rewrite preimage_itvcy; apply/seteqP; split=> x /=.
  - by move=> H; apply/RleP.
  - by move/RleP. }
rewrite HE.
have H := paper_main_gaussian_smooth_random_measurable d f Hf measurableT
  `[c, +oo[ (measurable_itv _).
by rewrite setTI in H.
Qed.

Lemma paper_main_gaussian_chernoff_exponent L u :
  0 < L ->
  exp ((u / L ^ 2) ^ 2 * L ^ 2 / 2) * exp (- (u / L ^ 2 * u)) =
  exp (- u ^ 2 / (2 * L ^ 2)).
Proof.
intros HL; rewrite <- exp_plus; f_equal.
field; apply Rgt_not_eq; exact HL.
Qed.

Theorem paper_main_gaussian_smooth_upper_tail d f Df D2f M L u :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 < L -> 0 < u ->
  (gaussian_product_law d
     [set x | Rle (gaussian_iterated_expectation d f + u) (f (tval x))] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> Hs Hg HL Hu.
have Hs' := Hs; case: Hs' => Hc _ _ _ _ Hb _ _.
have HL2 : 0 < L ^ 2 by apply pow_lt.
have Hq : 0 < u / L ^ 2 by apply Rdiv_lt_0_compat.
have Hq' : (0 < (u / L ^ 2)%Rcoq)%R by apply/RltP.
pose X : {RV gaussian_product_law d >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (paper_main_gaussian_smooth_centered d f)
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (paper_main_gaussian_smooth_centered_measurable d f Hc))).
have H := chernoff X (r := u / L ^ 2) u Hq'.
have [_ HT] := paper_main_gaussian_law_transport d
  (paper_main_gaussian_centered_exp d (u / L ^ 2) f) _ 0
  (paper_main_gaussian_centered_exp_continuous d (u / L ^ 2) f Hc)
  (paper_main_gaussian_centered_exp_bound d (u / L ^ 2) f M (Rlt_le _ _ Hq) Hb).
have HM : (@mmt_gen_fun _ _ _ (gaussian_product_law d) X (u / L ^ 2) =
    (gaussian_iterated_expectation d
      (paper_main_gaussian_centered_exp d (u / L ^ 2) f))%:E)%E.
{ rewrite -HT /mmt_gen_fun unlock; apply: eq_integral => x _ /=.
  by rewrite /paper_main_gaussian_centered_exp RexpE
    /paper_main_gaussian_smooth_centered mulrC. }
have HB := paper_main_gaussian_bounded_centered_mgf d f Df D2f M L (u / L ^ 2)
  Hs Hg (Rlt_le _ _ Hq).
have Hreal : Rle
  (gaussian_iterated_expectation d (paper_main_gaussian_centered_exp d (u / L ^ 2) f) *
    exp (- (u / L ^ 2 * u)))
  (exp (- u ^ 2 / (2 * L ^ 2))).
{ rewrite <- (paper_main_gaussian_chernoff_exponent L u HL).
  apply Rmult_le_compat_r; [apply Rlt_le, exp_pos|exact HB]. }
have HS : [set x | (u <= X x)%R] =
  [set x : d.-tuple (measurableTypeR R) |
    Rle (gaussian_iterated_expectation d f + u) (f (tval x))].
{ apply/seteqP; split=> x /=.
  - move/RleP; rewrite /paper_main_gaussian_smooth_centered => Hx.
    change (Rle u (f (tval x) - gaussian_iterated_expectation d f)) in Hx.
    change (Rle (gaussian_iterated_expectation d f + u) (f (tval x))); lra.
  - move=> Hx; apply/RleP; rewrite /paper_main_gaussian_smooth_centered.
    change (Rle (gaussian_iterated_expectation d f + u) (f (tval x))) in Hx.
    change (Rle u (f (tval x) - gaussian_iterated_expectation d f)); lra. }
rewrite -HS; apply: (le_trans H).
rewrite HM -EFinM lee_fin -RexpE; apply/RleP; exact Hreal.
Qed.

Lemma paper_main_gaussian_smooth_test_neg d f Df D2f M :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  paper_main_gaussian_smooth_test d (fun xs => -1 * f xs)
    (fun a xs => -1 * Df a xs) (fun a b xs => -1 * D2f a b xs) M 0.
Proof.
intros [Hc HD HDc HD2 HD2c Hb HDb HD2b].
assert (Hneg : forall F, finite_polynomial_bound d M 0 F ->
  finite_polynomial_bound d M 0 (fun xs => -1 * F xs)).
{ intros F HF.
  destruct (proj1 (paper_main_polynomial_zero_bound d M F) HF) as [HM HB].
  apply (proj2 (paper_main_polynomial_zero_bound d M _)); split; [exact HM|].
  intros xs Hxs; replace (-1 * F xs) with (- F xs) by ring.
  rewrite Rabs_Ropp; exact (HB xs Hxs). }
constructor.
- apply finite_joint_continuous_scale; exact Hc.
- intros a Ha; apply paper_main_coordinate_derivative_scale; exact (HD a Ha).
- intros a Ha; apply finite_joint_continuous_scale; exact (HDc a Ha).
- intros a b Ha Hb'; apply paper_main_coordinate_derivative_scale; exact (HD2 a b Ha Hb').
- intros a b Ha Hb'; apply finite_joint_continuous_scale; exact (HD2c a b Ha Hb').
- apply Hneg; exact Hb.
- intros a Ha; apply Hneg; exact (HDb a Ha).
- intros a b Ha Hb'; apply Hneg; exact (HD2b a b Ha Hb').
Qed.

Lemma paper_main_gaussian_smooth_neg_gradient d (Df : nat -> list R -> R) L :
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  forall xs, List.length xs = d ->
    finite_sum (fun a => (-1 * Df a xs) ^ 2) (List.seq 0 d) <= L ^ 2.
Proof.
intros Hg xs Hxs.
replace (finite_sum (fun a => (-1 * Df a xs) ^ 2) (List.seq 0 d)) with
  (finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d)); [exact (Hg xs Hxs)|].
apply finite_sum_ext; intros a _; ring.
Qed.

Lemma paper_main_gaussian_smooth_neg_mean d f Df D2f M :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  gaussian_iterated_expectation d (fun xs => -1 * f xs) =
    -1 * gaussian_iterated_expectation d f.
Proof.
intros [Hc _ _ _ _ Hb _ _].
destruct (gaussian_coordinate_polynomial_domain d f M 0 Hc Hb) as [HI _].
exact (proj2 (gaussian_iterated_scale d f (-1) HI)).
Qed.

Theorem paper_main_gaussian_smooth_lower_tail d f Df D2f M L u :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 < L -> 0 < u ->
  (gaussian_product_law d
     [set x | Rle (f (tval x)) (gaussian_iterated_expectation d f - u)] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> Hs Hg HL Hu.
have H := paper_main_gaussian_smooth_upper_tail d (fun xs => -1 * f xs)
  (fun a xs => -1 * Df a xs) (fun a b xs => -1 * D2f a b xs) M L u
  (paper_main_gaussian_smooth_test_neg d f Df D2f M Hs)
  (paper_main_gaussian_smooth_neg_gradient d Df L Hg) HL Hu.
rewrite (paper_main_gaussian_smooth_neg_mean d f Df D2f M Hs) in H.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle (f (tval x)) (gaussian_iterated_expectation d f - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d f + u) (-1 * f (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS; exact H.
Qed.

Theorem paper_main_gaussian_smooth_two_sided_tail d f Df D2f M L u :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  (forall xs, List.length xs = d ->
    finite_sum (fun a => Df a xs ^ 2) (List.seq 0 d) <= L ^ 2) ->
  0 < L -> 0 < u ->
  (gaussian_product_law d
     [set x | Rle u (Rabs (f (tval x) - gaussian_iterated_expectation d f))] <=
   (2 * exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> Hs Hg HL Hu.
have Hs' := Hs; case: Hs' => Hc _ _ _ _ _ _ _.
have Hcn : finite_joint_continuous d (fun xs => -1 * f xs)
  by apply finite_joint_continuous_scale.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (f (tval x) - gaussian_iterated_expectation d f))] =
  [set x | Rle (gaussian_iterated_expectation d f + u) (f (tval x))] `|`
  [set x | Rle (-1 * gaussian_iterated_expectation d f + u) (-1 * f (tval x))].
{ apply/seteqP; split=> x /=.
  - unfold Rabs; destruct Rcase_abs => Hx; [right|left]; lra.
  - move=> [Hx|Hx]; unfold Rabs; destruct Rcase_abs; lra. }
rewrite HS.
have H1 := paper_main_gaussian_smooth_upper_tail d f Df D2f M L u Hs Hg HL Hu.
have H2 := paper_main_gaussian_smooth_lower_tail d f Df D2f M L u Hs Hg HL Hu.
have HS2 : [set x : d.-tuple (measurableTypeR R) |
    Rle (f (tval x)) (gaussian_iterated_expectation d f - u)] =
  [set x | Rle (-1 * gaussian_iterated_expectation d f + u) (-1 * f (tval x))].
{ apply/seteqP; split=> x /= Hx; lra. }
rewrite HS2 in H2.
eapply le_trans; first exact: (measureU2 _
  (paper_main_gaussian_smooth_ge_measurable d f _ Hc)
  (paper_main_gaussian_smooth_ge_measurable d (fun xs => -1 * f xs) _ Hcn)).
have H := leeD H1 H2.
move: H; rewrite -EFinD.
have HE (z : R) : (z + z)%R = Rmult 2 z.
{ change (z + z = 2 * z); lra. }
rewrite HE; trivial.
Qed.
