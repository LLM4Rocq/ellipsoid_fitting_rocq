(* The uniform head small ball under the actual Gaussian law. Let r = n + 1,
   let x be an m-point sample of R^r (paper_main_probability m r: m
   independent standard Gaussian rows g_1, ..., g_m), and for a symmetric
   H of size r and real b let
     Y_i(H, b) = g_i^T H g_i - Tr H - b,   sigma2(H, b) = 2 |H|_F^2 + b^2.
   Theorem (paper_main_head_small_ball_uniform). There is a measurable bad
   event B with
     P(B) <= exp (L_r - c1 m) + exp (- c2 m),
     c1 = (1/76) (1/2 - ln 2 / 4),  c2 = (2 ln 2 - 1) / 1216,
   where L_r = C(eps_r) (D + 1) (D = r (r + 1) / 2, eps_r of order 1 / r,
   L_r <= 504 ln 2 (r + 1)^3), such that off B, simultaneously for every
   symmetric H, every real b and every J : {set 'I_m} with
   |J| >= (1 - 1/1216) m,
     sum_(i in J) Y_i(H, b)^2 >= (m / 4864) sigma2(H, b).
   Proof, replacing the VC bound of the manuscript.
   - One row: P(Y^2 >= sigma2 / 2) >= 1/76 (PaperMainHeadSmallBallPZ) and,
     with A(g) = g g^T - I, E |A(g)|_F^2 = r (r + 1)
     (PaperMainDataFeatureMoments), so by Markov
     P(|A(g)|_F^2 >= Psi) <= 1/1216 for Psi = 1216 r (r + 1).
   - Net: points (H_t, b_t), t < s, of the unit parameter sphere at sigma2
     distance eps^2 with eps^2 (Psi/2 + 1) = 1/25 and ln s <= L_r
     (PaperMainHeadSmallBallNet). If sigma2(H - H_t, b - b_t) <= eps^2 and
     |A(g)|_F^2 < Psi then |Y(H, b) - Y(H_t, b_t)| <= 1/5, so
     Y(H_t, b_t)^2 >= 1/2 gives Y(H, b)^2 >= 1/4.
   - Counts (PaperMainHeadSmallBallCount): for each t,
     P(#{i | Y_i(H_t, b_t)^2 >= 1/2} <= m/304) <= exp (- c1 m), and
     P(#{i | |A(g_i)|_F^2 >= Psi} >= m/608) <= exp (- c2 m). B is the union.
   - Off B, for (H, b) on the unit sphere, #{i | Y_i^2 >= 1/4} > m/608;
     deleting at most m/1216 rows leaves more than m/1216 of them, so the
     sum over J is at least m/4864. Homogeneity gives every (H, b).
   Corollaries (using 3/5 < ln 2 < 1): with c0 = (2 ln 2 - 1) / 2432,
   P(B) <= exp (- c0 m) when m >= 306432 (r + 1)^3
   (paper_main_head_small_ball_uniform_poly), and, for every gamma > 0 and
   all large d, when r <= sqrt d + 1 (in particular r <= ceil (sqrt d)) and
   m >= gamma d^2 (paper_main_head_small_ball_uniform_density). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability numfun.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainSampling PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainDataFeatureMoments
  PaperMainSymmetricDiagonalizationBridge PaperMainGaussianQuadraticTail
  PaperMainHeadSectionMeasurable PaperMainGaussianUnion PaperMainMatrixDuality
  PaperMainGaussianFeatureCoordinates PaperMainGaussianDimensionBounds PaperMainGordonEntropy
  PaperMainHeadSmallBallPZ PaperMainHeadSmallBallCount PaperMainHeadSmallBallNet.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* One row of the sample as a Gaussian vector. *)

Lemma paper_main_head_small_ball_val_tcast k l (e : k = l) (h : k.-tuple T) :
  tval (tcast e h) = tval h.
Proof. by case: l / e. Qed.

Lemma paper_main_head_small_ball_row_point d (h : paper_main_sample 1 d) :
  paper_main_point h 0 = paper_main_symmetric_column (tval (tcast (mul1n d) h)).
Proof.
rewrite paper_main_head_small_ball_val_tcast.
by apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma paper_main_head_small_ball_row_event_eq d (rho : 'cV[R]_d -> Prop) :
  paper_main_head_row_event d rho =
  tcast (mul1n d) @^-1` [set x : d.-tuple T | rho (paper_main_symmetric_column (tval x))].
Proof.
apply/seteqP; split => h;
  rewrite /paper_main_head_row_event /= paper_main_head_small_ball_row_point //.
Qed.

Lemma paper_main_head_small_ball_row_law d (rho : 'cV[R]_d -> Prop) :
  measurable [set x : d.-tuple T | rho (paper_main_symmetric_column (tval x))] ->
  measurable (paper_main_head_row_event d rho) /\
  paper_main_probability 1 d (paper_main_head_row_event d rho) =
  gaussian_product_law d [set x : d.-tuple T | rho (paper_main_symmetric_column (tval x))].
Proof.
move=> mE; rewrite paper_main_head_small_ball_row_event_eq; split.
  have := paper_main_tcast_measurable _ _ (mul1n d) measurableT _ mE.
  by rewrite setTI.
exact: paper_main_tcast_law.
Qed.

(* The small-ball probability of one row on the unit parameter sphere. *)

Theorem paper_main_head_small_ball_row_small d (H : 'M[R]_d) (b : R) :
  paper_main_symmetric H -> paper_main_head_small_ball_sigma2 H b = 1 ->
  measurable (paper_main_head_row_event d
    (fun g => Rle (1 / 2) (paper_main_head_small_ball_value H b g ^ 2))) /\
  (((1 / 76)%Rcoq)%:E <= paper_main_probability 1 d (paper_main_head_row_event d
    (fun g => Rle (1 / 2) (paper_main_head_small_ball_value H b g ^ 2))))%E.
Proof.
move=> HH Hs.
set rho := fun g => Rle (1 / 2) (paper_main_head_small_ball_value H b g ^ 2).
have mE : measurable [set x : d.-tuple T | rho (paper_main_symmetric_column (tval x))].
  exact: (paper_main_head_small_ball_joint_event d (fun x => x) (fun _ => H) (fun _ => b)
    (fun _ => 1 / 2) (@measurable_id _ _ setT) (fun i j => measurable_cst _)
    (measurable_cst _) (measurable_cst _)).
have [mA EA] := paper_main_head_small_ball_row_law d rho mE.
split => //; rewrite EA.
have := paper_main_head_small_ball_probability d H b HH.
rewrite /paper_main_head_small_ball_sigma2 in Hs.
by rewrite Hs.
Qed.

(* Markov's inequality for a nonnegative integrable function. *)

Lemma paper_main_head_small_ball_markov {dX : measure_display} {X : measurableType dX}
    (P : probability X R) (F : X -> R) (M Psi : R) :
  measurable_fun [set: X] (F : X -> T) ->
  P.-integrable [set: X] (fun x => (F x)%:E) -> (\int[P]_x (F x)%:E = M%:E)%E ->
  (forall x, 0 <= F x) -> 0 < Psi ->
  measurable [set x | Rle Psi (F x)] /\
  (P [set x | Rle Psi (F x)] <= ((M / Psi)%Rcoq)%:E)%E.
Proof.
move=> mF HI HE HF0 HPsi.
set A := [set x | Rle Psi (F x)].
have mA : measurable A.
  have H := paper_main_head_section_le_measurable (fun _ => Psi) F (measurable_cst _) mF.
  have -> : A = [set x | (Psi <= F x)%R].
    by apply/seteqP; split => x /=; [move/RleP | move/RleP].
  exact: H.
split => //.
have HIA := integrable_indic P mA.
have HL : P.-integrable setT (fun x => (Psi%:E * (\1_A x)%:E)%E) by exact: integrableZl HIA.
have Hle : (\int[P]_x (Psi%:E * (\1_A x)%:E) <= \int[P]_x (F x)%:E)%E.
  apply: (le_integral measurableT HL HI) => x _.
  rewrite /numfun.indic -EFinM lee_fin; apply/RleP.
  case: (boolP (x \in A)) => Hx.
    have Hx' : Rle Psi (F x) by move: Hx; rewrite inE.
    by rewrite mulr1.
  by rewrite mulr0; exact: HF0.
rewrite (integralZl measurableT HIA) (integral_indic P measurableT mA) setIT HE in Hle.
have HfA : P A \is a fin_num by apply: fin_num_measure.
rewrite -(fineK HfA) in Hle *.
have Hle' : (Psi%:E * P A <= M%:E)%E := Hle.
rewrite -(fineK HfA) -EFinM lee_fin in Hle'.
rewrite lee_fin; apply/RleP; move/RleP: Hle' => Hle'.
apply: (Rmult_le_reg_l Psi) => //.
have -> : Psi * (M / Psi) = M by field; lra.
exact: Hle'.
Qed.

(* The feature g g^T - I is sqrt r times the data feature of
   PaperMainDataFeatureMoments. *)

Lemma paper_main_head_small_ball_feature_data n (xs : list R) :
  paper_main_head_small_ball_feature (paper_main_symmetric_column xs : 'cV[R]_n.+1) =
  (Num.sqrt (n.+1)%:R *: paper_main_data_feature n (fun j => List.nth j xs 0))%R.
Proof.
apply/matrixP => a b.
rewrite [in RHS]mxE paper_main_data_feature_entry.
rewrite /paper_main_head_small_ball_feature /paper_main_symmetric_column !mxE.
have Hs : Num.sqrt ((n.+1)%:R : R) != 0 by rewrite sqrtr_eq0 -ltNge ltr0Sn.
by rewrite mulrA mulfV // mul1r.
Qed.

Lemma paper_main_head_small_ball_feature_frobenius n (xs : list R) :
  paper_main_frobenius (paper_main_head_small_ball_feature
    (paper_main_symmetric_column xs : 'cV[R]_n.+1)) ^ 2 =
  INR n.+1 * paper_main_frobenius (paper_main_data_feature n (fun j => List.nth j xs 0)) ^ 2.
Proof.
rewrite !RpowE !pmh_frobenius_sqr paper_main_head_small_ball_feature_data.
rewrite pmh_pairingZl paper_main_pairing_scale mulrA -expr2 sqr_sqrtr ?ler0n //.
by rewrite INRE.
Qed.

(* Few large rows: by Markov, P(|g g^T - I|_F^2 >= Psi) <= r (r + 1) / Psi. *)

Theorem paper_main_head_small_ball_row_large n (Psi : R) : 0 < Psi ->
  measurable (paper_main_head_row_event n.+1
    (fun g => Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2))) /\
  (paper_main_probability 1 n.+1 (paper_main_head_row_event n.+1
    (fun g => Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2))) <=
    ((INR n.+1 * (INR n.+1 + 1) / Psi)%Rcoq)%:E)%E.
Proof.
move=> HPsi.
set rho := fun g : 'cV[R]_n.+1 =>
  Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2).
have [HI HE] := paper_main_data_feature_frobenius n.
set F := fun x : n.+1.-tuple T =>
  (paper_main_frobenius (paper_main_data_row_feature n x) ^+ 2)%R.
have mF : measurable_fun [set: n.+1.-tuple T] (F : _ -> T).
  by apply/measurable_EFinP; exact: (measurable_int _ HI).
have HF0 : forall x, 0 <= F x.
  by move=> x; apply/RleP; rewrite /F exprn_ge0 // pmh_frobenius_ge0.
have HN : 0 < INR n.+1 by apply: lt_0_INR; lia.
have HPsi' : 0 < Psi / INR n.+1 by apply: Rdiv_lt_0_compat.
have [mA HA] := paper_main_head_small_ball_markov (gaussian_product_law n.+1) F
  (n.+1%:R + 1)%R (Psi / INR n.+1) mF HI HE HF0 HPsi'.
have Hset : [set x : n.+1.-tuple T | rho (paper_main_symmetric_column (tval x))] =
    [set x | Rle (Psi / INR n.+1) (F x)].
  apply/seteqP; split => x /=;
    rewrite /rho paper_main_head_small_ball_feature_frobenius /F -RpowE;
    rewrite /paper_main_data_row_feature => H.
    apply: (Rmult_le_reg_l (INR n.+1)) => //.
    have -> : INR n.+1 * (Psi / INR n.+1) = Psi by field; lra.
    exact: H.
  have := Rmult_le_compat_l (INR n.+1) _ _ (Rlt_le _ _ HN) H.
  have -> : INR n.+1 * (Psi / INR n.+1) = Psi by field; lra.
  by [].
have mE : measurable [set x : n.+1.-tuple T | rho (paper_main_symmetric_column (tval x))].
  by rewrite Hset.
have [mR ER] := paper_main_head_small_ball_row_law n.+1 rho mE.
split => //; rewrite ER Hset.
apply: le_trans HA _; rewrite lee_fin; apply/RleP.
rewrite -INRE -RplusE.
have E : (INR n.+1 + 1) / (Psi / INR n.+1) = INR n.+1 * (INR n.+1 + 1) / Psi.
  by field; lra.
apply: Req_le; exact: E.
Qed.

(* Counts and deletion sets. *)

Definition paper_main_head_small_ball_energy {m d : nat} (H : 'M[R]_d) (b : R)
    (J : {set 'I_m}) (x : paper_main_sample m d) : R :=
  (\sum_(i in J) paper_main_head_small_ball_value H b (paper_main_point x i) ^+ 2)%R.

Lemma paper_main_head_small_ball_count_cover m d (rho1 rho2 rho3 : 'cV[R]_d -> Prop)
    (x : paper_main_sample m d) :
  (forall g, rho1 g -> rho2 g \/ rho3 g) ->
  paper_main_head_row_count m d rho1 x <=
  paper_main_head_row_count m d rho2 x + paper_main_head_row_count m d rho3 x.
Proof.
move=> Hc; rewrite /paper_main_head_row_count -finite_sum_plus.
apply: finite_sum_le => i _.
case: (pselect (rho1 _)) => H1; case: (pselect (rho2 _)) => H2;
  case: (pselect (rho3 _)) => H3 /=; try lra.
by case: (Hc _ H1).
Qed.

Lemma paper_main_head_small_ball_sum_delete m (J : {set 'I_m}) (F : 'I_m -> R) :
  (forall i, 0 <= F i <= 1) ->
  (\sum_(i < m) F i <= \sum_(i in J) F i + (m%:R - #|J|%:R))%R.
Proof.
move=> HF.
rewrite (bigID (fun i => i \in J)) /=.
apply: lerD; first exact: lexx.
have -> : (\sum_(i < m | i \notin J) F i = \sum_(i in ~: J) F i)%R.
  by apply: eq_bigl => i; rewrite inE.
apply: le_trans (_ : (\sum_(i in ~: J) (1 : R) <= _)%R).
  by apply: ler_sum => i _; apply/RleP; exact: (proj2 (HF i)).
rewrite sumr_const.
have Hc : #|~: J| = (m - #|J|)%N by rewrite cardsCs finset.setCK card_ord.
have Hm : (#|J| <= m)%N by apply: (leq_trans (max_card _)); rewrite card_ord.
by rewrite Hc natrB.
Qed.

(* Deleting rows: count{Y^2 >= 1/4} - (m - |J|) <= 4 sum_(i in J) Y_i^2. *)

Lemma paper_main_head_small_ball_energy_count m d (H : 'M[R]_d) (b : R) (J : {set 'I_m})
    (x : paper_main_sample m d) :
  paper_main_head_row_count m d
    (fun g => Rle (1 / 4) (paper_main_head_small_ball_value H b g ^ 2)) x -
  (INR m - INR #|J|) <= 4 * paper_main_head_small_ball_energy H b J x.
Proof.
set Q := fun g => Rle (1 / 4) (paper_main_head_small_ball_value H b g ^ 2).
set ind := fun i : nat => if pselect (Q (paper_main_point x i)) then 1 else 0.
have Hc : paper_main_head_row_count m d Q x = (\sum_(i < m) ind i)%R.
  exact: paper_main_finite_sum_public.
have HF : forall i : 'I_m, 0 <= ind i <= 1.
  by move=> i; rewrite /ind; case: (pselect _) => _ /=; lra.
have Hd := paper_main_head_small_ball_sum_delete m J (fun i => ind i) HF.
have HJ : (\sum_(i in J) ind i <= 4 * paper_main_head_small_ball_energy H b J x)%R.
  rewrite /paper_main_head_small_ball_energy mulr_sumr.
  apply: ler_sum => i _; rewrite /ind; case: (pselect _) => HQ /=; apply/RleP.
    rewrite /Q in HQ; rewrite -RpowE -RmultE.
    have H4 : (4%R : R) = 4 by rewrite -[4%R]/(4%:R)%R -INRE /=; lra.
    rewrite H4; lra.
  apply/RleP; apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0].
rewrite Hc.
move: Hd HJ; set S := (\sum_(i < m) ind i)%R; set SJ := (\sum_(i in J) ind i)%R.
set E := paper_main_head_small_ball_energy H b J x.
move=> /RleP Hd /RleP HJ.
rewrite -!INRE -RminusE -RplusE in Hd.
rewrite -INRE -RmultE /= in HJ.
lra.
Qed.

(* The transfer from a net point: if sigma2 (H - H_t, b - b_t) <= eps^2,
   eps^2 (Psi/2 + 1) <= 1/25 and |A(g)|_F^2 < Psi, then
   |Y(H, b) - Y(H_t, b_t)| <= 1/5, so Y_t^2 >= 1/2 gives Y^2 >= 1/4. *)

Lemma paper_main_head_small_ball_sigma2_ge0 {d : nat} (H : 'M[R]_d) (b : R) :
  0 <= paper_main_head_small_ball_sigma2 H b.
Proof.
have Hp : 0 <= paper_main_pairing H H by apply/RleP; exact: paper_main_pairing_self_ge0.
rewrite /paper_main_head_small_ball_sigma2; have := pow2_ge_0 b; lra.
Qed.

Lemma paper_main_head_small_ball_transfer d (H Ht : 'M[R]_d) (b bt eps Psi : R)
    (g : 'cV[R]_d) :
  paper_main_head_small_ball_sigma2 (H - Ht)%R (b - bt) <= eps ^ 2 ->
  eps ^ 2 * (Psi / 2 + 1) <= 1 / 25 ->
  Rle (1 / 2) (paper_main_head_small_ball_value Ht bt g ^ 2) ->
  ~ Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2) ->
  Rle (1 / 4) (paper_main_head_small_ball_value H b g ^ 2).
Proof.
move=> Hs He HYt0 Hf.
have Hdiff := paper_main_head_small_ball_value_diff H Ht b bt g.
set s := paper_main_head_small_ball_sigma2 (H - Ht)%R (b - bt) in Hs Hdiff.
set f := paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2 in Hf Hdiff.
set Y := paper_main_head_small_ball_value H b g in Hdiff *.
set Yt := paper_main_head_small_ball_value Ht bt g in HYt0 Hdiff.
have Hs0 : 0 <= s by exact: paper_main_head_small_ball_sigma2_ge0.
have Hf0 : 0 <= f by rewrite /f; exact: pow2_ge_0.
have Hf1 : f < Psi by apply: Rnot_le_lt.
set u := sqrt s in Hdiff.
set w := sqrt (f / 2 + 1) in Hdiff.
have Hu0 : 0 <= u by exact: sqrt_pos.
have Hw0 : 0 <= w by exact: sqrt_pos.
have Hu2 : u * u = s by apply: sqrt_sqrt.
have Hw2 : w * w = f / 2 + 1 by apply: sqrt_sqrt; lra.
set D := Rabs (Y - Yt) in Hdiff.
have HD0 : 0 <= D by exact: Rabs_pos.
have HD2 : D * D <= 1 / 25.
  have H1 : D * D <= (u * w) * (u * w) by apply: Rmult_le_compat.
  have H2 : (u * w) * (u * w) = s * (f / 2 + 1) by rewrite -Hu2 -Hw2; ring.
  have H3 : s * (f / 2 + 1) <= eps ^ 2 * (Psi / 2 + 1).
    apply: Rmult_le_compat; lra.
  lra.
have HD : D <= 1 / 5 by nra.
have HA : Rabs Y * Rabs Y = Y * Y by rewrite -Rabs_mult Rabs_right //; nra.
have HAt : Rabs Yt * Rabs Yt = Yt * Yt by rewrite -Rabs_mult Rabs_right //; nra.
have Htri : Rabs Yt <= Rabs Y + D.
  have := Rabs_triang Y (Yt - Y).
  have -> : Y + (Yt - Y) = Yt by ring.
  by rewrite /D Rabs_minus_sym.
have HY0 := Rabs_pos Y.
have HYt1 := Rabs_pos Yt.
rewrite /= Rmult_1_r in HYt0 *.
apply: Rnot_lt_le => HY.
have HYa : Rabs Y < 1 / 2 by nra.
have HYt : Rabs Yt < 7 / 10 by lra.
nra.
Qed.

(* Homogeneity in (H, b). *)

Lemma paper_main_head_small_ball_value_scale {d : nat} (H : 'M[R]_d) (b c : R)
    (g : 'cV[R]_d) :
  paper_main_head_small_ball_value (c *: H)%R (c * b) g =
  c * paper_main_head_small_ball_value H b g.
Proof.
rewrite !paper_main_head_small_ball_value_pairing pmh_pairingZl.
set p := paper_main_pairing H _.
rewrite -RmultE; ring.
Qed.

Lemma paper_main_head_small_ball_sigma2_scale {d : nat} (H : 'M[R]_d) (b c : R) :
  paper_main_head_small_ball_sigma2 (c *: H)%R (c * b) =
  c ^ 2 * paper_main_head_small_ball_sigma2 H b.
Proof.
rewrite /paper_main_head_small_ball_sigma2 pmh_pairingZl paper_main_pairing_scale.
set p := paper_main_pairing H H.
rewrite -!RmultE; ring.
Qed.

Lemma paper_main_head_small_ball_energy_scale {m d : nat} (H : 'M[R]_d) (b c : R)
    (J : {set 'I_m}) (x : paper_main_sample m d) :
  paper_main_head_small_ball_energy (c *: H)%R (c * b) J x =
  c ^ 2 * paper_main_head_small_ball_energy H b J x.
Proof.
rewrite /paper_main_head_small_ball_energy RpowE.
transitivity (\sum_(i in J)
  (c ^+ 2 * paper_main_head_small_ball_value H b (paper_main_point x i) ^+ 2))%R.
  apply: eq_bigr => i _.
  by rewrite paper_main_head_small_ball_value_scale RmultE exprMn.
by rewrite -mulr_sumr.
Qed.

Lemma paper_main_head_small_ball_energy_ge0 {m d : nat} (H : 'M[R]_d) (b : R)
    (J : {set 'I_m}) (x : paper_main_sample m d) :
  0 <= paper_main_head_small_ball_energy H b J x.
Proof. by apply/RleP; apply: sumr_ge0 => i _; exact: sqr_ge0. Qed.

(* The deterministic step on the good event. *)

Theorem paper_main_head_small_ball_good m n (eps Psi : R) (s : nat)
    (Hn : nat -> 'M[R]_n.+1) (bn : nat -> R) (x : paper_main_sample m n.+1) :
  eps ^ 2 * (Psi / 2 + 1) <= 1 / 25 ->
  (forall (H : 'M[R]_n.+1) (b : R), paper_main_symmetric H ->
     paper_main_head_small_ball_sigma2 H b = 1 ->
     exists t, (t < s)%N /\
       paper_main_head_small_ball_sigma2 (H - Hn t)%R (b - bn t) <= eps ^ 2) ->
  (forall t, (t < s)%N -> INR m / 304 < paper_main_head_row_count m n.+1
     (fun g => Rle (1 / 2) (paper_main_head_small_ball_value (Hn t) (bn t) g ^ 2)) x) ->
  paper_main_head_row_count m n.+1
     (fun g => Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2)) x <
     INR m / 608 ->
  forall (H : 'M[R]_n.+1) (b : R) (J : {set 'I_m}), paper_main_symmetric H ->
    (1 - 1 / 1216) * INR m <= INR #|J| ->
    INR m / 4864 * paper_main_head_small_ball_sigma2 H b <=
      paper_main_head_small_ball_energy H b J x.
Proof.
move=> He Hcov Hgood Hlarge H b J HH HJ.
have Hs0 := paper_main_head_small_ball_sigma2_ge0 H b.
case: (Rle_lt_or_eq_dec 0 _ Hs0) => Hs; last first.
  rewrite -Hs Rmult_0_r; exact: paper_main_head_small_ball_energy_ge0.
set sg := paper_main_head_small_ball_sigma2 H b in Hs *.
have Hsq : 0 < sqrt sg by apply: sqrt_lt_R0.
set c := 1 / sqrt sg.
have Hc2 : c ^ 2 * sg = 1.
  have Hss := sqrt_sqrt sg (Rlt_le _ _ Hs).
  rewrite /c -{2}Hss; field; lra.
have HH' : paper_main_symmetric (c *: H)%R by move=> i j; rewrite !mxE HH.
have Hs' : paper_main_head_small_ball_sigma2 (c *: H)%R (c * b) = 1.
  by rewrite paper_main_head_small_ball_sigma2_scale.
have [t [Ht Hd]] := Hcov _ _ HH' Hs'.
have Hcnt := paper_main_head_small_ball_count_cover m n.+1
  (fun g => Rle (1 / 2) (paper_main_head_small_ball_value (Hn t) (bn t) g ^ 2))
  (fun g => Rle (1 / 4) (paper_main_head_small_ball_value (c *: H)%R (c * b) g ^ 2))
  (fun g => Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2)) x.
have Hcover : forall g : 'cV[R]_n.+1,
    Rle (1 / 2) (paper_main_head_small_ball_value (Hn t) (bn t) g ^ 2) ->
    Rle (1 / 4) (paper_main_head_small_ball_value (c *: H)%R (c * b) g ^ 2) \/
    Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2).
  move=> g Hg.
  case: (pselect (Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2)))
    => HL; [by right | left].
  exact: (paper_main_head_small_ball_transfer n.+1 (c *: H)%R (Hn t) (c * b) (bn t) eps Psi g
    Hd He Hg HL).
have Hc := Hcnt Hcover.
have Hen := paper_main_head_small_ball_energy_count m n.+1 (c *: H)%R (c * b) J x.
rewrite paper_main_head_small_ball_energy_scale in Hen.
have Hg := Hgood t Ht.
set E := paper_main_head_small_ball_energy H b J x in Hen *.
have HcE : c ^ 2 * E * sg = E by rewrite (Rmult_comm (c ^ 2)) Rmult_assoc Hc2 Rmult_1_r.
nra.
Qed.

(* The constants. Psi = 1216 r (r + 1) makes the large-row probability at
   most 1/1216; eps^2 (Psi/2 + 1) = 1/25. *)

Definition paper_main_head_small_ball_psi (n : nat) : R :=
  1216 * (INR n.+1 * (INR n.+1 + 1)).

Definition paper_main_head_small_ball_eps (n : nat) : R :=
  1 / (5 * sqrt (paper_main_head_small_ball_psi n / 2 + 1)).

Definition paper_main_head_small_ball_entropy (n : nat) : R :=
  paper_main_gordon_entropy_constant (paper_main_head_small_ball_eps n) *
  INR (paper_main_symmetric_dimension n).+1.

Lemma paper_main_head_small_ball_psi_pos n : 0 < paper_main_head_small_ball_psi n.
Proof.
have := pos_INR n.+1; rewrite /paper_main_head_small_ball_psi S_INR => H.
have := pos_INR n; nra.
Qed.

Lemma paper_main_head_small_ball_eps_pos n : 0 < paper_main_head_small_ball_eps n.
Proof.
have HP := paper_main_head_small_ball_psi_pos n.
have Hs : 0 < sqrt (paper_main_head_small_ball_psi n / 2 + 1) by apply: sqrt_lt_R0; lra.
rewrite /paper_main_head_small_ball_eps; apply: Rdiv_lt_0_compat; lra.
Qed.

Lemma paper_main_head_small_ball_eps_psi n :
  paper_main_head_small_ball_eps n ^ 2 * (paper_main_head_small_ball_psi n / 2 + 1) = 1 / 25.
Proof.
have HP := paper_main_head_small_ball_psi_pos n.
have Hq : 0 < paper_main_head_small_ball_psi n / 2 + 1 by lra.
have Hs := sqrt_lt_R0 _ Hq.
have Hss := sqrt_sqrt _ (Rlt_le _ _ Hq).
rewrite /paper_main_head_small_ball_eps -{2}Hss; field; lra.
Qed.

Lemma paper_main_head_small_ball_union_notin {X : Type} (S : list nat) (E : nat -> set X) x :
  ~ paper_main_finite_event_union S E x -> forall i, List.In i S -> ~ E i x.
Proof.
elim: S => [|j S IH] /= Hx i Hi //.
case: Hi => [<-|Hi] HE; apply: Hx; [by left | right].
by apply: contrapT => Hn; exact: (IH Hn i Hi HE).
Qed.

(* The uniform head small ball with explicit failure probability. *)

Theorem paper_main_head_small_ball_uniform n m :
  exists B : set (paper_main_sample m n.+1),
    measurable B /\
    (paper_main_probability m n.+1 B <=
      ((exp (paper_main_head_small_ball_entropy n - 1 / 76 * (1 / 2 - ln 2 / 4) * INR m) +
        exp (- ((2 * ln 2 - 1) / 1216) * INR m))%Rcoq)%:E)%E /\
    forall x, ~ B x ->
      forall (H : 'M[R]_n.+1) (b : R) (J : {set 'I_m}), paper_main_symmetric H ->
        (1 - 1 / 1216) * INR m <= INR #|J| ->
        INR m / 4864 * paper_main_head_small_ball_sigma2 H b <=
          paper_main_head_small_ball_energy H b J x.
Proof.
set Psi := paper_main_head_small_ball_psi n.
set eps := paper_main_head_small_ball_eps n.
have HPsi : 0 < Psi by exact: paper_main_head_small_ball_psi_pos.
have Heps : 0 < eps by exact: paper_main_head_small_ball_eps_pos.
have He : eps ^ 2 * (Psi / 2 + 1) <= 1 / 25.
  by rewrite paper_main_head_small_ball_eps_psi; lra.
have [Hs [Hn [bn [Hmem [Hcov Hln]]]]] := paper_main_head_small_ball_param_net n eps Heps.
set s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n).+1 eps)
  in Hs Hmem Hcov Hln.
set rho := fun t (g : 'cV[R]_n.+1) =>
  Rle (1 / 2) (paper_main_head_small_ball_value (Hn t) (bn t) g ^ 2).
set rhoL := fun g : 'cV[R]_n.+1 =>
  Rle Psi (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2).
set Bad := fun t => [set x : paper_main_sample m n.+1 |
  Rle (paper_main_head_row_count m n.+1 (rho t) x) (1 / 76 * INR m / 4)].
set BadL := [set x : paper_main_sample m n.+1 |
  Rle (INR m / 608) (paper_main_head_row_count m n.+1 rhoL x)].
exists (paper_main_finite_event_union (List.seq 0 s) Bad `|` BadL).
have Hrow : forall t, (t < s)%N ->
    measurable (paper_main_head_row_event n.+1 (rho t)) /\
    (((1 / 76)%Rcoq)%:E <=
      paper_main_probability 1 n.+1 (paper_main_head_row_event n.+1 (rho t)))%E.
  move=> t Ht; have [HHt Hst] := Hmem t Ht.
  exact: (paper_main_head_small_ball_row_small n.+1 (Hn t) (bn t) HHt Hst).
have [mL HL] := paper_main_head_small_ball_row_large n Psi HPsi.
have HLq : (paper_main_probability 1 n.+1 (paper_main_head_row_event n.+1 rhoL) <=
    ((1 / 1216)%Rcoq)%:E)%E.
  apply: le_trans HL _; rewrite lee_fin; apply/RleP.
  have HN : 0 < INR n.+1 by apply: lt_0_INR; lia.
  have E : INR n.+1 * (INR n.+1 + 1) / Psi = 1 / 1216.
    rewrite /Psi /paper_main_head_small_ball_psi; field; nra.
  by rewrite E; lra.
have Hseq : forall t, List.In t (List.seq 0 s) -> (t < s)%N.
  by move=> t; rewrite List.in_seq => -[_ Ht]; apply/ssrnat.ltP; lia.
have Hp0 : 0 <= 1 / 76 by lra.
have Hq0 : 0 <= 1 / 1216 by lra.
have mBad : forall t, List.In t (List.seq 0 s) -> measurable (Bad t).
  move=> t Ht; have [mA HA] := Hrow t (Hseq t Ht).
  exact: (proj1 (paper_main_head_row_count_lower n.+1 (rho t) (1 / 76) mA Hp0 HA m
    (1 / 76 * INR m / 4))).
have PBad : forall t, List.In t (List.seq 0 s) ->
    (gaussian_product_law (m * n.+1) (Bad t) <=
      ((exp (- (1 / 76 * INR m) * (1 / 2 - ln 2 / 4)))%Rcoq)%:E)%E.
  move=> t Ht; have [mA HA] := Hrow t (Hseq t Ht).
  exact: (paper_main_head_row_count_lower_exp n.+1 (rho t) (1 / 76) m mA Hp0 HA).
have mBL : measurable BadL.
  exact: (proj1 (paper_main_head_row_count_upper n.+1 rhoL (1 / 1216) mL Hq0 HLq m
    (INR m / 608))).
have PBL : (gaussian_product_law (m * n.+1) BadL <=
    ((exp (1 / 1216 * INR m - INR m / 608 * ln 2))%Rcoq)%:E)%E.
  exact: (paper_main_head_row_count_upper_exp n.+1 rhoL (1 / 1216) (INR m / 608) m
    mL Hq0 HLq).
have mU := paper_main_gaussian_union_measurable (m * n.+1) (List.seq 0 s) Bad mBad.
have PU := paper_main_gaussian_union_bound (m * n.+1) (List.seq 0 s) Bad _ mBad PBad.
split; first exact: measurableU mU mBL.
split.
  apply: le_trans (measureU2 _ mU mBL) _.
  apply: le_trans (leeD PU PBL) _.
  rewrite -EFinD lee_fin; apply/RleP.
  rewrite List.length_seq.
  have HsR : 0 < INR s by apply: lt_0_INR; apply/ssrnat.ltP.
  have E1 : INR s * exp (- (1 / 76 * INR m) * (1 / 2 - ln 2 / 4)) =
      exp (ln (INR s) - 1 / 76 * (1 / 2 - ln 2 / 4) * INR m).
    rewrite exp_plus exp_ln //; congr (_ * exp _); ring.
  have E2 : exp (1 / 1216 * INR m - INR m / 608 * ln 2) =
      exp (- ((2 * ln 2 - 1) / 1216) * INR m).
    by congr exp; field.
  have H1 : exp (ln (INR s) - 1 / 76 * (1 / 2 - ln 2 / 4) * INR m) <=
      exp (paper_main_head_small_ball_entropy n - 1 / 76 * (1 / 2 - ln 2 / 4) * INR m).
    have Hln' : ln (INR s) <= paper_main_head_small_ball_entropy n := Hln.
    case: (Rle_lt_or_eq_dec _ _ Hln') => Hlt; last by rewrite Hlt; lra.
    by apply: Rlt_le; apply: exp_increasing; lra.
  have Hfin : INR s * exp (- (1 / 76 * INR m) * (1 / 2 - ln 2 / 4)) +
      exp (1 / 1216 * INR m - INR m / 608 * ln 2) <=
    exp (paper_main_head_small_ball_entropy n - 1 / 76 * (1 / 2 - ln 2 / 4) * INR m) +
      exp (- ((2 * ln 2 - 1) / 1216) * INR m) by rewrite E1 E2; lra.
  exact: Hfin.
move=> x Hx.
have HxU : ~ paper_main_finite_event_union (List.seq 0 s) Bad x by move=> HU; apply: Hx; left.
have HxL : ~ BadL x by move=> HB; apply: Hx; right.
apply: (paper_main_head_small_ball_good m n eps Psi s Hn bn x He Hcov).
  move=> t Ht.
  have Hin : List.In t (List.seq 0 s).
    by rewrite List.in_seq; split; [lia | apply/ssrnat.ltP].
  have HB := paper_main_head_small_ball_union_notin _ _ x HxU t Hin.
  apply: Rnot_le_lt => HB'; apply: HB; rewrite /Bad /=; move: HB'; rewrite /rho; lra.
by apply: Rnot_le_lt => HL'; apply: HxL.
Qed.

(* Numerical facts: 3/5 < ln 2 < 1. *)

Lemma paper_main_head_small_ball_ln2_lt1 : ln 2 < 1.
Proof.
have H := exp_ineq1 1 R1_neq_R0.
rewrite -[X in _ < X](ln_exp 1).
apply: ln_increasing; lra.
Qed.

Lemma paper_main_head_small_ball_ln2_gt : 3 / 5 < ln 2.
Proof.
have He1 := exp_le_3.
have He0 : 0 < exp 1 := exp_pos 1.
have H5 : exp (3 / 5) ^ 5 = exp 1 * exp 1 * exp 1.
  rewrite -paper_main_head_row_exp_mul -!exp_plus; congr exp; rewrite /=; field.
have Hlt : exp (3 / 5) < 2.
  apply: Rnot_le_lt => H2.
  have Hx : 0 <= exp (3 / 5) by exact: Rlt_le (exp_pos _).
  have H32 : 2 ^ 5 <= exp (3 / 5) ^ 5 by apply: pow_incr; lra.
  have H27 : exp 1 * exp 1 * exp 1 <= 27.
    have : exp 1 * exp 1 <= 9 by nra.
    nra.
  rewrite H5 /= in H32; lra.
rewrite -[X in X < _](ln_exp (3 / 5)).
apply: ln_increasing => //; exact: exp_pos.
Qed.

(* The entropy term is O(r^3): L_r <= 504 ln 2 (r + 1)^3 with r = n + 1. *)

Lemma paper_main_head_small_ball_entropy_le n :
  paper_main_head_small_ball_entropy n <= 504 * ln 2 * (INR n + 2) ^ 3.
Proof.
rewrite /paper_main_head_small_ball_entropy /paper_main_gordon_entropy_constant.
have Hn0 := pos_INR n.
have Hl : 0 < ln 2 by rewrite -ln_1; apply: ln_increasing; lra.
have HP := paper_main_head_small_ball_psi_pos n.
have Hq : 0 < paper_main_head_small_ball_psi n / 2 + 1 by lra.
set w := sqrt (paper_main_head_small_ball_psi n / 2 + 1).
have Hw0 : 0 < w by exact: sqrt_lt_R0.
have Hw2 : w * w = paper_main_head_small_ball_psi n / 2 + 1.
  exact: sqrt_sqrt (Rlt_le _ _ Hq).
have Hw : w <= 25 * (INR n + 2).
  rewrite /paper_main_head_small_ball_psi S_INR in Hw2.
  nra.
have Hinv : 4 / paper_main_head_small_ball_eps n = 20 * w.
  rewrite /paper_main_head_small_ball_eps -/w; field; lra.
have HD : INR (paper_main_symmetric_dimension n).+1 <= (INR n + 2) ^ 2.
  have := le_INR _ _ (paper_main_symmetric_dimension_upper n).
  rewrite mult_INR !S_INR => H.
  nra.
rewrite Hinv.
have HD0 := pos_INR (paper_main_symmetric_dimension n).+1.
have Hc : (4 + 20 * w) * ln 2 <= 504 * (INR n + 2) * ln 2.
  apply: Rmult_le_compat_r; lra.
have Hc0 : 0 <= (4 + 20 * w) * ln 2 by nra.
apply: Rle_trans (_ : 504 * (INR n + 2) * ln 2 * (INR n + 2) ^ 2 <= _).
  apply: Rmult_le_compat => //; lra.
right; ring.
Qed.

(* Exponential failure probability once m >= 306432 (r + 1)^3, r = n + 1:
   P(B) <= exp (- c0 m) with c0 = (2 ln 2 - 1) / 2432 > 1/12160. *)

Corollary paper_main_head_small_ball_uniform_poly n m :
  306432 * (INR n + 2) ^ 3 <= INR m ->
  exists B : set (paper_main_sample m n.+1),
    measurable B /\
    (paper_main_probability m n.+1 B <=
      ((exp (- ((2 * ln 2 - 1) / 2432) * INR m))%Rcoq)%:E)%E /\
    forall x, ~ B x ->
      forall (H : 'M[R]_n.+1) (b : R) (J : {set 'I_m}), paper_main_symmetric H ->
        (1 - 1 / 1216) * INR m <= INR #|J| ->
        INR m / 4864 * paper_main_head_small_ball_sigma2 H b <=
          paper_main_head_small_ball_energy H b J x.
Proof.
move=> Hm.
have [B [mB [PB HB]]] := paper_main_head_small_ball_uniform n m.
exists B; split => //; split => //.
apply: le_trans PB _; rewrite lee_fin; apply/RleP.
have Hl1 := paper_main_head_small_ball_ln2_lt1.
have Hl2 := paper_main_head_small_ball_ln2_gt.
have HL := paper_main_head_small_ball_entropy_le n.
have Hn0 := pos_INR n.
have H8 : 8 <= (INR n + 2) ^ 3.
  have H2 : 2 <= INR n + 2 by lra.
  have := pow_incr 2 (INR n + 2) 3 (conj (Rlt_le _ _ Rlt_0_2) H2); simpl; lra.
set M := INR m in Hm *.
have HM : 306432 * 8 <= M by lra.
have Hexp : forall u v, u <= v -> exp u <= exp v.
  move=> u v Huv; case: (Rle_lt_or_eq_dec _ _ Huv) => H; last by rewrite H; lra.
  by apply: Rlt_le; apply: exp_increasing.
have Hi : paper_main_head_small_ball_entropy n - 1 / 76 * (1 / 2 - ln 2 / 4) * M + ln 2 <=
    - ((2 * ln 2 - 1) / 2432) * M.
  have H1 : 504 * ln 2 * (INR n + 2) ^ 3 <= ln 2 * M / 608.
    have Hl0 : 0 < ln 2 by lra.
    have : 504 * (INR n + 2) ^ 3 <= M / 608 by lra.
    nra.
  nra.
have Hii : - ((2 * ln 2 - 1) / 1216) * M + ln 2 <= - ((2 * ln 2 - 1) / 2432) * M.
  by nra.
have E2 : forall u, exp (u + ln 2) = 2 * exp u.
  by move=> u; rewrite exp_plus exp_ln; [lra | ring].
have Ha := Hexp _ _ Hi.
have Hb := Hexp _ _ Hii.
rewrite E2 in Ha; rewrite E2 in Hb.
lra.
Qed.

(* The regime of the manuscript: r <= ceil (sqrt d) (implied by
   r <= sqrt d + 1) and m >= gamma d^2. For every gamma > 0 and all large d
   the failure probability is at most exp (- c0 m). *)

Corollary paper_main_head_small_ball_uniform_density (gamma : R) : 0 < gamma ->
  exists d0 : nat, forall d n m, (d0 <= d)%N ->
    INR n.+1 <= sqrt (INR d) + 1 -> gamma * INR d ^ 2 <= INR m ->
    exists B : set (paper_main_sample m n.+1),
      measurable B /\
      (paper_main_probability m n.+1 B <=
        ((exp (- ((2 * ln 2 - 1) / 2432) * INR m))%Rcoq)%:E)%E /\
      forall x, ~ B x ->
        forall (H : 'M[R]_n.+1) (b : R) (J : {set 'I_m}), paper_main_symmetric H ->
          (1 - 1 / 1216) * INR m <= INR #|J| ->
          INR m / 4864 * paper_main_head_small_ball_sigma2 H b <=
            paper_main_head_small_ball_energy H b J x.
Proof.
move=> Hg.
set K0 := 2451456 / gamma.
have HK0 : 0 < K0 by apply: Rdiv_lt_0_compat; lra.
have [d1 Hd1] := INR_unbounded (K0 ^ 2).
exists (maxn 4 d1) => d n m Hd Hn Hm.
apply: paper_main_head_small_ball_uniform_poly.
have Hd4 : 4 <= INR d.
  have : (4 <= d)%N by apply: leq_trans Hd; exact: leq_maxl.
  move/ssrnat.leP/le_INR; rewrite /=; lra.
have HdK : K0 ^ 2 < INR d.
  have : (d1 <= d)%N by apply: leq_trans Hd; exact: leq_maxr.
  move/ssrnat.leP/le_INR => H; lra.
set q := sqrt (INR d).
have Hq0 : 0 <= q by exact: sqrt_pos.
have Hq2 : q * q = INR d by apply: sqrt_sqrt; lra.
have Hq2' : 2 <= q by nra.
have HqK : K0 < q by nra.
have Hn0 := pos_INR n.
rewrite S_INR -/q in Hn.
have Hn2 : INR n + 2 <= 2 * q by lra.
have H3 : (INR n + 2) ^ 3 <= (2 * q) ^ 3 by apply: pow_incr; lra.
have Hgq : 2451456 <= gamma * q.
  have : gamma * K0 = 2451456 by rewrite /K0; field; lra.
  nra.
have H4 : 306432 * (2 * q) ^ 3 <= gamma * INR d ^ 2.
  have Hq3 : 0 <= q ^ 3 by apply: pow_le.
  have H5 : 2451456 * q ^ 3 <= gamma * q * q ^ 3 by apply: Rmult_le_compat_r.
  have E1 : (2 * q) ^ 3 = 8 * q ^ 3 by ring.
  have E2 : INR d ^ 2 = q * q ^ 3 by rewrite -Hq2; ring.
  rewrite E1 E2; lra.
lra.
Qed.
