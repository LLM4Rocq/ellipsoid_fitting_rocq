(* Quantitative bounded-condition support estimates for the actual
   isotropic symmetric Gaussian. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix numfun.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral probability.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gaussian.Law.ProductBasics
  Analysis.CoordinateContinuityDefinitions Analysis.CoordinateTopology
  Gaussian.Coordinate.WeightDefinitions
  Gaussian.Coordinate.PolynomialContinuity Gaussian.Coordinate.Weights
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Geometry.HeadFrobenius
  Geometry.HeadWidth Geometry.HeadWidthCompact Geometry.HeadWidthLipschitz
  Cone.Projection Cone.ConditionOperator Gaussian.Symmetric.Coordinates
  Gaussian.Symmetric.PublicLaw Gaussian.Width.Psd
  Gaussian.Symmetric.DimensionReal Gordon.Lipschitz Gaussian.Lipschitz.Law
  Gaussian.Smooth.Law Gaussian.Lipschitz.ExceptionalEvent.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_condition_support n kappa xs :=
  paper_main_head_support (paper_main_public_symmetric_gaussian n xs)
    (paper_main_head_cone_sphere kappa).
Definition paper_main_gaussian_condition_width n kappa :=
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (paper_main_gaussian_condition_support n kappa).

Theorem paper_main_gaussian_condition_lipschitz n kappa :
  1 <= kappa ->
  forall xs ys, List.length xs = paper_main_symmetric_dimension n ->
    List.length ys = paper_main_symmetric_dimension n ->
    Rabs (paper_main_gaussian_condition_support n kappa xs -
      paper_main_gaussian_condition_support n kappa ys) <=
    1 * paper_main_gordon_distance (paper_main_symmetric_dimension n) xs ys.
Proof.
move=> Hk.
apply: (paper_main_public_symmetric_lipschitz_transfer n
  (fun A => paper_main_head_support A (paper_main_head_cone_sphere kappa)) 1).
move=> A B _ _.
have Hk' : (1 <= kappa)%R by apply/RleP.
have H := paper_main_head_cone_support_lipschitz (S n) kappa A B (ltn0Sn n) Hk'.
rewrite -RabsE in H; move/RleP: H => H.
change (Rabs (paper_main_head_support A (paper_main_head_cone_sphere kappa) -
  paper_main_head_support B (paper_main_head_cone_sphere kappa)) <=
  paper_main_frobenius (A-B)%R) in H; lra.
Qed.

Theorem paper_main_gaussian_condition_law n kappa :
  1 <= kappa ->
  (gaussian_product_law (paper_main_symmetric_dimension n)).-integrable setT
    (fun x => (paper_main_gaussian_condition_support n kappa (tval x))%:E) /\
  (\int[gaussian_product_law (paper_main_symmetric_dimension n)]_x
    (paper_main_gaussian_condition_support n kappa (tval x))%:E =
    (paper_main_gaussian_condition_width n kappa)%:E)%E.
Proof.
move=> Hk; exact: (paper_main_gaussian_lipschitz_law _ _ 1 Rle_0_1
  (paper_main_gaussian_condition_lipschitz n kappa Hk)).
Qed.

Lemma paper_main_gaussian_condition_abs n kappa xs :
  1 <= kappa ->
  Rabs (paper_main_gaussian_condition_support n kappa xs) <=
  paper_main_frobenius (paper_main_public_symmetric_gaussian n xs).
Proof.
move=> Hk.
have Hk' : (1 <= kappa)%R by apply/RleP.
have Hne : (@paper_main_head_cone_sphere (S n) kappa) !=set0.
  exists (((Num.sqrt (S n)%:R)^-1 *: (1%:M : 'M[R]_(S n)))%R).
  exact: paper_main_head_cone_sphere_nonempty.
have H := paper_main_head_support_bound (S n)
  (paper_main_public_symmetric_gaussian n xs) _ Hne (fun S H => proj2 H).
rewrite -RabsE in H; move/RleP: H; exact.
Qed.

Lemma paper_main_gaussian_projection_norm_le n xs :
  0 <= paper_main_gaussian_psd_projection_norm n xs <=
    paper_main_frobenius (paper_main_public_symmetric_gaussian n xs).
Proof.
pose Z := paper_main_public_symmetric_gaussian n xs.
have HZ := paper_main_public_symmetric_gaussian_symmetric n xs.
have H := paper_main_psd_moreau_frobenius (S n) Z HZ.
rewrite !expr2 in H.
have HP : 0 <= paper_main_gaussian_psd_projection_norm n xs.
  apply/RleP; exact: pmh_frobenius_ge0.
have HN : 0 <= paper_main_frobenius Z by apply/RleP; exact: pmh_frobenius_ge0.
change (paper_main_frobenius Z * paper_main_frobenius Z =
  paper_main_gaussian_psd_projection_norm n xs * paper_main_gaussian_psd_projection_norm n xs +
  paper_main_frobenius (paper_main_psd_negative_part (S n) Z) *
  paper_main_frobenius (paper_main_psd_negative_part (S n) Z)) in H.
change (0 <= paper_main_gaussian_psd_projection_norm n xs <= paper_main_frobenius Z).
split; [exact HP|nra].
Qed.

Lemma paper_main_condition_trace_young d x :
  0 < d -> Rabs x / sqrt d <= 1/2 + (x*x)/(2*d).
Proof.
move=> Hd.
have Hs := sqrt_lt_R0 d Hd.
have HS := pow2_sqrt d (Rlt_le _ _ Hd).
have HA := Rsqr_abs x; unfold Rsqr in HA.
have Hsquare := pow2_ge_0 (Rabs x-sqrt d).
apply (Rmult_le_reg_r (2*d)); first lra.
replace ((1/2+x*x/(2*d))*(2*d)) with (d+x*x) by (field; lra).
replace (Rabs x/sqrt d*(2*d)) with (2*Rabs x*sqrt d).
- nra.
- replace (2*d) with (2*(sqrt d*sqrt d)) by nra; field; lra.
Qed.

Lemma paper_main_condition_parameter C s :
  0 <= C -> 0 < s -> 1 <= (C+s)/s.
Proof.
move=> HC Hs; apply (Rmult_le_reg_r s); first exact Hs.
replace ((C+s)/s*s) with (C+s) by (field; lra); lra.
Qed.

Theorem paper_main_gaussian_condition_good n C s kappa xs :
  0 <= C -> 0 < s -> kappa = (C+s)/s ->
  paper_main_cone_opnorm_le (paper_main_public_symmetric_gaussian n xs)
    (C*sqrt (INR (S n))) ->
  paper_main_gaussian_psd_projection_norm n xs <=
    paper_main_gaussian_condition_support n kappa xs + s*INR (S n) + 1/2 +
    (paper_main_trace (paper_main_public_symmetric_gaussian n xs) *
      paper_main_trace (paper_main_public_symmetric_gaussian n xs))/(2*INR (S n)).
Proof.
move=> HC Hs Hk HO.
have HC' : (0 <= C)%R by apply/RleP.
have Hs' : (0 < s)%R by apply/RltP.
have Hb : C*sqrt (INR (S n)) = (C * Num.sqrt (S n)%:R)%R.
  by rewrite -INRE -RsqrtE -RmultE.
have Ht : s*sqrt (INR (S n)) = (s * Num.sqrt (S n)%:R)%R.
  by rewrite -INRE -RsqrtE -RmultE.
have Hk' : kappa = ((C+s)/s)%R by rewrite -RdivE -RplusE.
have [_ H] := paper_main_cone_shift_opnorm_scaled (S n)
  (paper_main_public_symmetric_gaussian n xs) C s _ _ kappa (ltn0Sn n)
  (paper_main_public_symmetric_gaussian_symmetric n xs) Hs' HC' Hb Ht Hk' HO.
rewrite -INRE -RsqrtE -RabsE -RdivE in H.
move/RleP: H => H.
change (paper_main_gaussian_psd_projection_norm n xs - s*INR (S n) -
  Rabs (paper_main_trace (paper_main_public_symmetric_gaussian n xs))/sqrt (INR (S n)) <=
  paper_main_gaussian_condition_support n kappa xs) in H.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
have HT := paper_main_condition_trace_young (INR (S n))
  (paper_main_trace (paper_main_public_symmetric_gaussian n xs)) Hd.
lra.
Qed.

Theorem paper_main_gaussian_condition_point_bound n C s kappa
    (A : set ((paper_main_symmetric_dimension n).-tuple (measurableTypeR R))) a :
  0 <= C -> 0 < s -> kappa = (C+s)/s -> 0 < a ->
  (forall x, ~ A x -> paper_main_cone_opnorm_le
    (paper_main_public_symmetric_gaussian n (tval x)) (C*sqrt (INR (S n)))) ->
  forall x,
    paper_main_gaussian_psd_projection_norm n (tval x) <=
    paper_main_gaussian_condition_support n kappa (tval x) + s*INR (S n) + 1/2 +
    (paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)) *
      paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)))/(2*INR (S n)) +
    (paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x))^2)/(2*a) +
    (2*a) * ((\1_A x)%R).
Proof.
move=> HC Hs Hk Ha HO x.
have Hkap : 1 <= kappa by rewrite Hk; exact: paper_main_condition_parameter.
have Hd : 0 < INR (S n) by apply lt_0_INR; lia.
pose Z := paper_main_public_symmetric_gaussian n (tval x).
pose F := paper_main_gaussian_condition_support n kappa (tval x).
pose P := paper_main_gaussian_psd_projection_norm n (tval x).
pose N := paper_main_frobenius Z.
pose T := paper_main_trace Z.
have HqN : 0 <= N^2/(2*a).
  unfold Rdiv; apply Rmult_le_pos; [apply pow2_ge_0|left; apply Rinv_0_lt_compat; lra].
have HqT : 0 <= T*T/(2*INR (S n)).
  unfold Rdiv; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra].
change (P <= F+s*INR (S n)+1/2+T*T/(2*INR (S n))+N^2/(2*a)+(2*a)*((\1_A x)%R)).
rewrite /numfun.indic.
case: (boolP (x \in A)) => Hx.
- have HP := paper_main_gaussian_projection_norm_le n (tval x).
  change (0 <= P <= N) in HP.
  have HF := paper_main_gaussian_condition_abs n kappa (tval x) Hkap.
  change (Rabs F <= N) in HF.
  have HF' := Rle_abs (-F); rewrite Rabs_Ropp in HF'.
  have HY := paper_main_exceptional_young N a Ha.
  have HE : N^2/(2*a) = 2*(/(4*a)*(N*N)) by (field; lra).
  change (P <= F+s*INR (S n)+1/2+T*T/(2*INR (S n))+N^2/(2*a)+(2*a)*1).
  rewrite HE; nra.
- have Hnot : ~ A x.
    move=> HA; have Hmem : x \in A by exact/asboolP.
    by rewrite Hmem in Hx.
  have HG := paper_main_gaussian_condition_good n C s kappa (tval x) HC Hs Hk (HO x Hnot).
  change (P <= F+s*INR (S n)+1/2+T*T/(2*INR (S n))) in HG.
  change (P <= F+s*INR (S n)+1/2+T*T/(2*INR (S n))+N^2/(2*a)+(2*a)*0).
  lra.
Qed.

Theorem paper_main_gaussian_condition_expectation n C s kappa
    (A : set ((paper_main_symmetric_dimension n).-tuple (measurableTypeR R))) a :
  0 <= C -> 0 < s -> kappa = (C+s)/s -> 0 < a -> measurable A ->
  (forall x, ~ A x -> paper_main_cone_opnorm_le
    (paper_main_public_symmetric_gaussian n (tval x)) (C*sqrt (INR (S n)))) ->
  ((gaussian_iterated_expectation (paper_main_symmetric_dimension n)
      (paper_main_gaussian_psd_projection_norm n))%:E <=
    ((paper_main_gaussian_condition_width n kappa+s*INR (S n)+1+
       INR (paper_main_symmetric_dimension n)/(2*a))%Rcoq)%:E +
    ((2*a)%Rcoq)%:E * gaussian_product_law (paper_main_symmetric_dimension n) A)%E.
Proof.
move=> HC Hs Hk Ha mA HO.
pose D := paper_main_symmetric_dimension n.
pose P := fun x : D.-tuple (measurableTypeR R) => paper_main_gaussian_psd_projection_norm n (tval x).
pose F := fun x : D.-tuple (measurableTypeR R) => paper_main_gaussian_condition_support n kappa (tval x).
pose T2 := fun x : D.-tuple (measurableTypeR R) =>
  paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)) *
  paper_main_trace (paper_main_public_symmetric_gaussian n (tval x)).
pose N2 := fun x : D.-tuple (measurableTypeR R) =>
  paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval x))^2.
pose c := s*INR (S n)+1/2.
pose q := / (2*INR (S n)).
pose r := / (2*a).
pose t := 2*a.
have Hkap : 1 <= kappa by rewrite Hk; exact: paper_main_condition_parameter.
have [IP EP] := paper_main_gaussian_lipschitz_law D _ 1 Rle_0_1
  (paper_main_gaussian_psd_projection_lipschitz n).
have [IF EF] := paper_main_gaussian_condition_law n kappa Hkap.
have [IN [EN [_ [_ [IT ET]]]]] := paper_main_public_symmetric_gaussian_law_moments n.
have [IC EC] := paper_main_gaussian_law_transport D (fun _ => c) _ 0
  (finite_joint_continuous_constant D c) (finite_polynomial_bound_constant D c).
rewrite (proj2 (gaussian_iterated_constant D c)) in EC.
have II := integrable_indic (gaussian_product_law D) mA.
have IQ : (gaussian_product_law D).-integrable setT (fun x => (q%:E*(T2 x)%:E)%E).
  exact: integrableZl IT.
have IR : (gaussian_product_law D).-integrable setT (fun x => (r%:E*(N2 x)%:E)%E).
  exact: integrableZl IN.
have IJ : (gaussian_product_law D).-integrable setT (fun x => (t%:E*((\1_A x)%R)%:E)%E).
  exact: integrableZl II.
have I1 := integrableD measurableT IF IC.
have I2 := integrableD measurableT I1 IQ.
have I3 := integrableD measurableT I2 IR.
have I4 := integrableD measurableT I3 IJ.
have HB : (\int[gaussian_product_law D]_x (P x)%:E <=
  \int[gaussian_product_law D]_x
    ((F x)%:E+c%:E+q%:E*(T2 x)%:E+r%:E*(N2 x)%:E+t%:E*((\1_A x)%R)%:E))%E.
  eapply (le_integral measurableT IP I4).
  move=> x _; rewrite -!EFinM -!EFinD lee_fin; apply/RleP.
  have H := paper_main_gaussian_condition_point_bound n C s kappa A a HC Hs Hk Ha HO x.
  change (P x <= F x+c+q*T2 x+r*N2 x+t*((\1_A x)%R)).
  change (P x <= F x+s*INR (S n)+1/2+T2 x/(2*INR (S n))+N2 x/(2*a)+t*((\1_A x)%R)) in H.
  unfold c,q,r,t,Rdiv; unfold t,Rdiv in H; nra.
rewrite (integralD measurableT I3 IJ) (integralD measurableT I2 IR)
  (integralD measurableT I1 IQ) (integralD measurableT IF IC)
  (integralZl measurableT IT) (integralZl measurableT IN) (integralZl measurableT II)
  EP EF EC EN ET (integral_indic (gaussian_product_law D) measurableT mA) setIT in HB.
have HE : ((paper_main_gaussian_condition_width n kappa)%:E+c%:E+
    q%:E*(INR (S n))%:E+r%:E*(INR D)%:E)%E =
  ((paper_main_gaussian_condition_width n kappa+s*INR (S n)+1+INR D/(2*a))%Rcoq)%:E.
  rewrite -!EFinM -!EFinD; congr (_%:E).
  change (paper_main_gaussian_condition_width n kappa+c+q*INR (S n)+r*INR D =
    paper_main_gaussian_condition_width n kappa+s*INR (S n)+1+INR D/(2*a)).
  unfold c,q,r; field; split; [lra|apply not_0_INR; lia].
rewrite HE in HB; exact HB.
Qed.
