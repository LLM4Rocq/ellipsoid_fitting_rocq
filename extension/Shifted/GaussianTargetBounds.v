(* Finite probability bounds for Gaussian shift interpolation targets. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun realfun measurable_realfun probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss normal_integral gauss_moments.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.
From GaussianAnalysis.probability Require Import symmetrization small_ball_method.
From GaussianAnalysis.comparison Require Import normal_mgf.
From GaussianAnalysis.random_matrix Require Import goe_entries.
From EllipsoidUniversality.Shifted Require Import GaussianTargets.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Condition Require Import Unsat.
From GaussianAnalysis.matrix Require Import condition_perturbation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

(* Finite probability bounds for the two terms in the interpolation norm.
   They do not use independence from the interpolation event. *)
Lemma measurable_gaussian_target_square_sum n p (s a : R) :
  measurable_fun [set: 'rV[RR]_n] (fun xi =>
    (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2 : RR)).
Proof.
apply: measurable_sum => i; apply: measurable_funX.
exact: measurable_gaussian_shift_target.
Qed.

Lemma gaussian_shift_target_square_sum_tail n p (s a B : R) : 0 < B ->
  (gauss n [set xi : 'rV[RR]_n |
      (B < \sum_(i < n) gaussian_shift_target p s a xi i ^+ 2)%R] <=
    (n%:R * s ^+ 2 * (2 + 4%:R * a ^+ 2) / p%:R / B)%:E)%E.
Proof.
move=> B0.
have Y0 xi : 0 <= \sum_(i < n) gaussian_shift_target p s a xi i ^+ 2.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have h := @markov_ge0 _ _ RR (gauss n)
  (fun xi => \sum_(i < n) gaussian_shift_target p s a xi i ^+ 2) B
  (measurable_gaussian_target_square_sum p s a)
  Y0 B0.
rewrite gaussian_shift_target_sum_moment -EFinM in h.
by rewrite mulrC in h.
Qed.

Lemma gaussian_coordinate_max_tail n (r : R) : 0 <= r ->
  (gauss n [set xi : 'rV[RR]_n | (r < max_norm (fun i => xi 0 i))%R] <=
    (2 * n%:R * expR (- r ^+ 2 / 2))%:E)%E.
Proof.
move=> r0.
pose F (i : 'I_n) := [set xi : 'rV[RR]_n | (r <= `|xi 0 i|)%R].
have mF i : measurable (F i).
  rewrite /F -[X in measurable X]setTI.
  apply: measurable_fun_ler => //.
  exact: measurableT_comp (measurable_mxentry _ _).
have hsub : [set xi : 'rV[RR]_n | (r < max_norm (fun i => xi 0 i))%R]
    `<=` \bigcup_i F i.
  move=> xi hx; apply: contrapT => hn.
  have lemax : max_norm (fun i => xi 0 i) <= r.
    apply: bigmax_le => // i _.
    have ni : ~ F i xi by move=> hi; apply: hn; exists i => //.
    have hr : `|xi 0 i| < r.
      by rewrite ltNge; apply/negP; exact: ni.
    exact: ltW hr.
  by move: hx; rewrite /= (ltNge r) lemax.
have hbound i : (gauss n (F i) <=
    (2 * expR (- r ^+ 2 / 2))%:E)%E.
  have mA : measurable [set z : RR | r <= `|z|].
    by rewrite -[X in measurable X]setTI; apply: measurable_fun_ler.
  rewrite /F (gauss_coord i mA).
  have h := @normal_prob_abs_tail RR 0 1 r (oner_neq0 _) r0.
  have he : [set z : RR | r <= `|z - 0|] = [set z : RR | r <= `|z|].
    by apply/seteqP; split => z /=; rewrite subr0.
  rewrite he in h.
  by move: h; rewrite expr1n mulr1.
have mmax : measurable [set xi : 'rV[RR]_n | r < max_norm (fun i => xi 0 i)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  apply: measurable_max_norm => i; exact: measurable_mxentry.
apply: le_trans (le_measure _ _ _ hsub) _; rewrite ?inE //.
  apply: fin_bigcup_measurable => [|i _]; first exact: cardinality.finite_finset.
  exact: mF.
apply: le_trans (measure_bigcup_fin_le _ mF) _.
have hs : (\sum_(i < n) gauss n (F i) <=
    \sum_(i < n) (2 * expR (- r ^+ 2 / 2))%:E)%E.
  by apply: lee_sum => i _; exact: hbound.
apply: le_trans hs _.
rewrite sumEFin sumr_const card_ord -mulr_natl.
by rewrite lee_fin; nra.
Qed.

Lemma gaussian_shift_target_l2_split n p (s a : R) (xi : 'rV[RR]_n) :
  Num.sqrt (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2) <=
  `|s| / Num.sqrt p%:R *
    (Num.sqrt (\sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2) +
      2 * `|a| * frobenius xi).
Proof.
have row_norm (v : 'I_n -> R) :
    frobenius (\row_i v i) = Num.sqrt (\sum_(i < n) v i ^+ 2).
  rewrite /frobenius /mxdot big_ord1; congr Num.sqrt.
  by apply: eq_bigr => i _; rewrite !mxE expr2.
have he : (\row_i gaussian_shift_target p s a xi i) =
    (- s / Num.sqrt p%:R) *:
      ((\row_i (xi 0 i ^+ 2 - 1)) + (2 * a) *: xi).
  apply/matrixP => i j; rewrite (ord1 i) !mxE.
  rewrite /gaussian_shift_target gaussian_centered_shift_squareE.
  by ring.
rewrite -row_norm he frobeniusZ normrM normrN normfV
  (ger0_norm (sqrtr_ge0 (p%:R : R))).
apply: ler_wpM2l; first by rewrite mulr_ge0 ?normr_ge0 ?invr_ge0 ?sqrtr_ge0.
apply: le_trans (frobeniusD _ _) _.
by rewrite row_norm frobeniusZ normrM normr_nat.
Qed.

Lemma gaussian_centered_shift_square_abs_le (a t r : R) :
  0 <= r -> `|t| <= r ->
  `|gaussian_centered_shift_square a t| <= r ^+ 2 + 1 + 2 * `|a| * r.
Proof.
move=> r0 tr.
have t2r : t ^+ 2 <= r ^+ 2.
  by rewrite -real_normK ?num_real // ler_sqr ?nnegrE ?normr_ge0.
have h1 : `|t ^+ 2 - 1| <= t ^+ 2 + 1.
  apply: le_trans (ler_normB _ _) _.
  by rewrite (ger0_norm (sqr_ge0 t)) normr1.
have h2 : 2 * `|a| * `|t| <= 2 * `|a| * r.
  by apply: ler_wpM2l => //; rewrite mulr_ge0 ?normr_ge0.
rewrite gaussian_centered_shift_squareE.
apply: le_trans (ler_normD _ _) _.
rewrite !normrM normr_nat.
by apply: le_trans (lerD h1 h2) _; rewrite lerD2r lerD2r.
Qed.

Lemma gaussian_shift_target_max_le n p (s a r : R) (xi : 'rV[RR]_n) :
  0 <= r -> max_norm (fun i => xi 0 i) <= r ->
  max_norm (gaussian_shift_target p s a xi) <=
    `|s| / Num.sqrt p%:R * (r ^+ 2 + 1 + 2 * `|a| * r).
Proof.
move=> r0 xr.
have c0 : 0 <= `|s| / Num.sqrt p%:R.
  by rewrite mulr_ge0 ?normr_ge0 ?invr_ge0 ?sqrtr_ge0.
apply: bigmax_le => [|i _].
  by rewrite mulr_ge0 // addr_ge0 ?addr_ge0 ?sqr_ge0 // mulr_ge0 ?mulr_ge0 ?normr_ge0.
rewrite /gaussian_shift_target !normrM normrN normfV
  (ger0_norm (sqrtr_ge0 (p%:R : R))) mulrAC.
apply: ler_wpM2l => //.
exact: gaussian_centered_shift_square_abs_le r0 (le_trans (ler_max_norm _ i) xr).
Qed.

Lemma gaussian_shift_target_size_le n p (L s a B r : R) (xi : 'rV[RR]_n) :
  0 <= L -> 0 <= r ->
  \sum_(i < n) gaussian_shift_target p s a xi i ^+ 2 <= B ->
  max_norm (fun i => xi 0 i) <= r ->
  shifted_interpolation_size p L (gaussian_shift_target p s a xi) <=
    L * (Num.sqrt B / p%:R + ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
      (`|s| / Num.sqrt p%:R * (r ^+ 2 + 1 + 2 * `|a| * r))).
Proof.
move=> L0 r0 sumB maxr; rewrite /shifted_interpolation_size.
apply: ler_wpM2l => //; apply: lerD.
- apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  exact: ler_wsqrtr sumB.
- apply: ler_wpM2l.
  + by rewrite divr_ge0 ?sqrtr_ge0 // exprn_even_ge0.
  + exact: gaussian_shift_target_max_le.
Qed.

Lemma gaussian_shift_target_size_tail n p (L s a B r : R) :
  0 <= L -> 0 < B -> 0 <= r ->
  (gauss n [set xi : 'rV[RR]_n |
      (L * (Num.sqrt B / p%:R + ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
        (`|s| / Num.sqrt p%:R * (r ^+ 2 + 1 + 2 * `|a| * r))) <
       shifted_interpolation_size p L (gaussian_shift_target p s a xi))%R] <=
    (n%:R * s ^+ 2 * (2 + 4%:R * a ^+ 2) / p%:R / B +
      2 * n%:R * expR (- r ^+ 2 / 2))%:E)%E.
Proof.
move=> L0 B0 r0.
pose ES := [set xi : 'rV[RR]_n |
  (B < \sum_(i < n) gaussian_shift_target p s a xi i ^+ 2)%R].
pose EM := [set xi : 'rV[RR]_n | (r < max_norm (fun i => xi 0 i))%R].
have mES : measurable ES.
  rewrite /ES -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_square_sum.
have mEM : measurable EM.
  rewrite /EM -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  apply: measurable_max_norm => i; exact: measurable_mxentry.
have mE : measurable [set xi : 'rV[RR]_n |
    L * (Num.sqrt B / p%:R + ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
      (`|s| / Num.sqrt p%:R * (r ^+ 2 + 1 + 2 * `|a| * r))) <
    shifted_interpolation_size p L (gaussian_shift_target p s a xi)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
have sub : [set xi : 'rV[RR]_n |
    L * (Num.sqrt B / p%:R + ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
      (`|s| / Num.sqrt p%:R * (r ^+ 2 + 1 + 2 * `|a| * r))) <
    shifted_interpolation_size p L (gaussian_shift_target p s a xi)] `<=` ES `|` EM.
  move=> xi /= hx; have [hs|hs] := ltP B
      (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2).
    by left.
  have [hm|hm] := ltP r (max_norm (fun i => xi 0 i)); first by right.
  have hb := gaussian_shift_target_size_le L0 r0 hs hm.
  by move: hx; rewrite ltNge hb.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  exact: measurableU.
apply: le_trans (measureU2 (gauss n) mES mEM) _.
rewrite EFinD.
exact: leeD (gaussian_shift_target_square_sum_tail n p s a B0)
  (gaussian_coordinate_max_tail n r0).
Qed.

Lemma gaussian_centered_square_sum_tail n (B : R) : 0 < B ->
  (gauss n [set xi : 'rV[RR]_n |
      (B < \sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2)%R] <=
    (2 * n%:R / B)%:E)%E.
Proof.
move=> B0.
have he xi i : gaussian_shift_target 1 1 0 xi i ^+ 2 =
    (xi 0 i ^+ 2 - 1) ^+ 2.
  rewrite /gaussian_shift_target gaussian_centered_shift_squareE sqrtr1 divr1.
  change ((- (1 : RR) * (xi 0 i ^+ 2 - 1 + 2 * (0 : RR) * xi 0 i)) ^+ 2 =
    (xi 0 i ^+ 2 - 1) ^+ 2).
  by ring.
have h := gaussian_shift_target_square_sum_tail n 1 1 0 B0.
have hset : [set xi : 'rV[RR]_n |
      (B < \sum_(i < n) gaussian_shift_target 1 1 0 xi i ^+ 2)%R] =
    [set xi : 'rV[RR]_n | (B < \sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2)%R].
  apply/seteqP; split => xi /=.
  - have -> : \sum_(i < n) gaussian_shift_target 1 1 0 xi i ^+ 2 =
        \sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2.
      by apply: eq_bigr => i _; exact: he.
    by [].
  - have -> : \sum_(i < n) gaussian_shift_target 1 1 0 xi i ^+ 2 =
        \sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2.
      by apply: eq_bigr => i _; exact: he.
    by [].
rewrite hset expr0n expr1n mulr0 addr0 mulr1 divr1 in h.
apply: le_trans h _.
rewrite lee_fin; by nra.
Qed.

(* At fixed e, the central-square contribution vanishes, while the linear
   term has limiting size 2 e sqrt(alpha). Applying Markov directly to the
   full target norm would leave an O(e^2) probability error. *)
Lemma gaussian_shift_target_l2_weighted n p (s a e B F : R)
    (xi : 'rV[RR]_n) :
  (0 < p)%N -> `|s| <= 1 -> 0 <= e -> `|s * a| <= e * Num.sqrt p%:R ->
  \sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2 <= B -> frobenius xi <= F ->
  Num.sqrt (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2) / p%:R <=
    Num.sqrt B / (p%:R * Num.sqrt p%:R) + 2 * e * F / p%:R.
Proof.
move=> p0 s1 e0 saB sumB xF.
have pR : 0 < p%:R :> R by rewrite ltr0n.
have q0 : 0 < Num.sqrt p%:R :> R by rewrite sqrtr_gt0.
have qn : Num.sqrt p%:R != 0 :> R by rewrite gt_eqF.
have pn : p%:R != 0 :> R by rewrite gt_eqF.
have B0 : 0 <= B.
  apply: le_trans _ sumB; by apply: sumr_ge0 => i _; exact: sqr_ge0.
have hcent : `|s| * Num.sqrt (\sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2) <= Num.sqrt B.
  apply: le_trans (ler_wpM2r (sqrtr_ge0 _) s1) _.
  by rewrite mul1r; exact: ler_wsqrtr sumB.
have hlin : 2 * `|s| * `|a| * frobenius xi <=
    2 * e * Num.sqrt p%:R * F.
  have -> : 2 * `|s| * `|a| * frobenius xi =
      2 * `|s * a| * frobenius xi by rewrite normrM; ring.
  apply: le_trans (ler_wpM2r (frobenius_ge0 _) (ler_wpM2l (ler0n RR 2) saB)) _.
  rewrite mulrA; apply: ler_wpM2l => //.
  by rewrite mulr_ge0 ?mulr_ge0 ?sqrtr_ge0.
have hs := gaussian_shift_target_l2_split p s a xi.
rewrite ler_pdivrMr //.
apply: le_trans hs _.
rewrite mulrDr.
have htot := lerD hcent hlin.
have heq : (Num.sqrt B / (p%:R * Num.sqrt p%:R) + 2 * e * F / p%:R) * p%:R =
    (Num.sqrt B + 2 * e * Num.sqrt p%:R * F) / Num.sqrt p%:R.
  by field.
rewrite heq.
have heq' : `|s| / Num.sqrt p%:R *
      Num.sqrt (\sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2) +
    `|s| / Num.sqrt p%:R * (2 * `|a| * frobenius xi) =
    (`|s| * Num.sqrt (\sum_(i < n) (xi 0 i ^+ 2 - 1) ^+ 2) +
      2 * `|s| * `|a| * frobenius xi) / Num.sqrt p%:R by ring.
rewrite heq'; apply: ler_wpM2r => //; by rewrite invr_ge0 ltW.
Qed.

Lemma gaussian_fourth_root_inv_small (A z : R) :
  0 <= A -> 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    A / Num.sqrt (Num.sqrt p%:R) < z.
Proof.
move=> A0 z0; pose u := A / z.
have u0 : 0 <= u by rewrite /u divr_ge0 // ltW.
exists (archimedean.Num.truncn (u ^+ 4)).+1 => p hp.
have p0 : (0 < p)%N := leq_trans (ltn0Sn _) hp.
have pR : 0 < p%:R :> R by rewrite ltr0n.
have q0 : 0 < Num.sqrt p%:R :> R by rewrite sqrtr_gt0.
have qq0 : 0 < Num.sqrt (Num.sqrt p%:R) :> R by rewrite sqrtr_gt0.
have up : u ^+ 4 < p%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have eu : Num.sqrt (Num.sqrt (u ^+ 4)) = u.
  have e4 : u ^+ 4 = (u ^+ 2) ^+ 2 by rewrite -exprM.
  rewrite e4.
  by rewrite sqrtr_sqr (ger0_norm (sqr_ge0 u)) sqrtr_sqr ger0_norm.
have hroot : u < Num.sqrt (Num.sqrt p%:R).
  by rewrite -{1}eu !ltr_sqrt.
rewrite /u ltr_pdivrMr // mulrC in hroot.
by rewrite ltr_pdivrMr.
Qed.

Lemma gaussian_norm_over_dimension_cvg (N : nat -> nat) (alpha : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) ->
  cvg_prob (fun p => gauss (N p)) (fun p xi => frobenius xi / p%:R)
    (Num.sqrt alpha).
Proof.
move=> hN.
have h := cvg_prob_sqrt (gauss_sqnorm_cvg N alpha hN).
apply: cvg_prob_eq h; exists 1%N => p p1 xi /=.
by rewrite -expr_div_n sqrtr_sqr ger0_norm // divr_ge0 ?frobenius_ge0 ?ler0n.
Qed.

Lemma gaussian_centered_square_scaled_cvg (N : nat -> nat) (alpha : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) ->
  cvg_prob (fun p => gauss (N p))
    (fun p xi => (\sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2) / p%:R ^+ 3) 0.
Proof.
move=> hN eta eta0 z z0.
have [D0 h0] := hN 1 ltr01.
pose A := `|alpha| + 1.
have A0 : 0 < A by rewrite /A ltr_wpDl ?normr_ge0.
have ez0 : 0 < eta * z by rewrite mulr_gt0.
exists (maxn D0 (archimedean.Num.truncn (4%:R * A / (eta * z))).+1) => p.
rewrite geq_max => /andP[pD pT].
have p0 : (0 < p)%N := leq_trans (ltn0Sn _) pT.
have pR : 0 < p%:R :> R by rewrite ltr0n.
have p20 : 0 < p%:R ^+ 2 :> R by rewrite exprn_gt0.
have p30 : 0 < p%:R ^+ 3 :> R by rewrite exprn_gt0.
have NR : (N p)%:R <= A * p%:R ^+ 2.
  rewrite -ler_pdivrMr //.
  have h := h0 p pD; move: h; rewrite ltr_norml => /andP[_ h].
  apply: le_trans (_ : alpha + 1 <= A); last by rewrite /A lerD2r ler_norm.
  by move: h; rewrite ltrBlDr addrC => /ltW.
have hp : 4%:R * A < p%:R * (eta * z).
  rewrite -ltr_pdivrMr //.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
pose B := eta / 2 * p%:R ^+ 3.
have B0 : 0 < B by rewrite /B mulr_gt0 ?divr_gt0.
exists [set xi : 'rV[RR]_(N p) |
  B < \sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2]; split.
- rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  apply: measurable_sum => i; apply: measurable_funX.
  apply: measurable_funB => //; apply: measurable_funX; exact: measurable_mxentry.
- apply: le_trans (gaussian_centered_square_sum_tail (N p) B0) _.
  rewrite lee_fin ler_pdivrMr // /B.
  rewrite !exprS expr0 !mulr1 in NR p20 p30 *.
  nra.
- move=> xi /= hx.
  have S0 : 0 <= \sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2.
    by apply: sumr_ge0 => i _; exact: sqr_ge0.
  have V0 : 0 <= (\sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2) / p%:R ^+ 3.
    by rewrite divr_ge0 // ltW.
  rewrite subr0 (ger0_norm V0) ler_pdivlMr // in hx.
  rewrite /B; nra.
Qed.

Lemma gaussian_centered_square_norm_cvg (N : nat -> nat) (alpha : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) ->
  cvg_prob (fun p => gauss (N p))
    (fun p xi => Num.sqrt (\sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2) /
      (p%:R * Num.sqrt p%:R)) 0.
Proof.
move=> hN.
have h := cvg_prob_sqrt (@gaussian_centered_square_scaled_cvg N alpha hN).
rewrite sqrtr0 in h.
apply: cvg_prob_eq h; exists 0%N => p _ xi /=.
have S0 : 0 <= \sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have p30 : 0 <= p%:R ^+ 3 :> R by rewrite exprn_ge0 ?ler0n.
rewrite sqrtrM // sqrtrV //.
have ep : (p%:R : R) ^+ 3 = p%:R ^+ 2 * p%:R by ring.
by rewrite ep sqrtrM ?sqr_ge0 // sqrtr_sqr ger0_norm ?ler0n.
Qed.

Lemma gaussian_log_eventually_large (b : R) :
  exists D : nat, forall p, (D <= p)%N -> b <= ln (p%:R : R).
Proof.
exists (archimedean.Num.truncn (expR b)).+1 => p hp.
have p0 : (0 < p)%N := leq_trans (ltn0Sn _) hp.
have pR : 0 < p%:R :> R by rewrite ltr0n.
have h : expR b < p%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
by rewrite -ler_expR lnK ?posrE // ltW.
Qed.

Lemma gaussian_coordinate_log_tail n p : (0 < p)%N ->
  8%:R <= ln (p%:R : R) ->
  (gauss n [set xi : 'rV[RR]_n |
      (ln (p%:R : R) < max_norm (fun i => xi 0 i))%R] <=
    (2 * n%:R / p%:R ^+ 4)%:E)%E.
Proof.
move=> p0 lp8.
have lp0 : 0 <= ln (p%:R : R) := le_trans (ler0n RR 8) lp8.
have pR : 0 < p%:R :> R by rewrite ltr0n.
apply: le_trans (gaussian_coordinate_max_tail n lp0) _.
rewrite lee_fin; apply: ler_wpM2l; first by rewrite mulr_ge0 ?ler0n.
have hpow : expR (- (4%:R * ln (p%:R : R))) = (p%:R ^+ 4)^-1.
  by rewrite expRN expRM_natl lnK ?posrE.
rewrite -hpow ler_expR.
nra.
Qed.

Definition gaussian_log_rate p : R :=
  Num.sqrt (2 ^+ 10 * 10`!%:R) / Num.sqrt (Num.sqrt p%:R).

Lemma gaussian_log_rate_ge0 p : 0 <= gaussian_log_rate p.
Proof. by rewrite /gaussian_log_rate divr_ge0 ?sqrtr_ge0. Qed.

Lemma gaussian_log_rate_cvg :
  forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|gaussian_log_rate p - 0| < z.
Proof.
move=> z z0.
have [D hD] := gaussian_fourth_root_inv_small
  (sqrtr_ge0 (2 ^+ 10 * 10`!%:R : R)) z0.
exists D => p pD.
by rewrite subr0 (ger0_norm (gaussian_log_rate_ge0 p)); exact: hD.
Qed.

Lemma gaussian_shift_target_log_term_le n p (s a e : R) (xi : 'rV[RR]_n) :
  (0 < p)%N -> 1 <= ln (p%:R : R) -> `|s| <= 1 -> 0 <= e ->
  `|s * a| <= e * Num.sqrt p%:R ->
  max_norm (fun i => xi 0 i) <= ln (p%:R : R) ->
  ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
    max_norm (gaussian_shift_target p s a xi) <=
  2 * gaussian_log_rate p ^+ 2 + 2 * e * gaussian_log_rate p.
Proof.
move=> p0 l1 s1 e0 sa xm.
pose l := ln (p%:R : R); pose q := Num.sqrt (p%:R : R).
pose H := gaussian_log_rate p.
have l0 : 0 <= l := le_trans ler01 l1.
have q0 : 0 < q by rewrite /q sqrtr_gt0 ltr0n.
have qi0 : 0 <= q^-1 by rewrite invr_ge0 ltW.
have H0 : 0 <= H := gaussian_log_rate_ge0 p.
have h5 : l ^+ 5 / q <= H := ln_pow5_le p p0.
have h5num : l ^+ 5 <= H * q by move: h5; rewrite ler_pdivrMr.
have l25 : l ^+ 2 <= l ^+ 5 by apply: ler_weXn2l.
have l45 : l ^+ 4 <= l ^+ 5 by apply: ler_weXn2l.
have l05 : 1 <= l ^+ 5 by apply: exprn_ege1.
have xH : l ^+ 4 / q <= H.
  by rewrite ler_pdivrMr //; exact: le_trans l45 h5num.
have yH : (l ^+ 2 + 1) / q <= 2 * H.
  rewrite ler_pdivrMr //; nra.
have saH : `|s * a| / q <= e by rewrite ler_pdivrMr.
have xb0 : 0 <= l ^+ 4 / q := mulr_ge0 (exprn_ge0 4 l0) qi0.
have yb0 : 0 <= (l ^+ 2 + 1) / q.
  exact: mulr_ge0 (addr_ge0 (sqr_ge0 l) ler01) qi0.
have sb0 : 0 <= `|s * a| / q := mulr_ge0 (normr_ge0 _) qi0.
have l5b0 : 0 <= l ^+ 5 / q := mulr_ge0 (exprn_ge0 5 l0) qi0.
have hm := gaussian_shift_target_max_le p s a l0 xm.
apply: le_trans (ler_wpM2l xb0 hm) _.
change (l ^+ 4 / q * (`|s| / q * (l ^+ 2 + 1 + 2 * `|a| * l)) <=
  2 * H ^+ 2 + 2 * e * H).
have he : l ^+ 4 / q * (`|s| / q * (l ^+ 2 + 1 + 2 * `|a| * l)) =
  (l ^+ 4 / q) * `|s| * ((l ^+ 2 + 1) / q) +
    2 * (`|s * a| / q) * (l ^+ 5 / q).
  by rewrite normrM; ring.
rewrite he.
have hfirst : (l ^+ 4 / q) * `|s| * ((l ^+ 2 + 1) / q) <= 2 * H ^+ 2.
  apply: le_trans (ler_wpM2r yb0 (ler_wpM2l xb0 s1)) _.
  rewrite mulr1; have hp := ler_pM xb0 yb0 xH yH.
  nra.
have hsecond := ler_pM sb0 l5b0 saH h5.
nra.
Qed.

Lemma gaussian_coordinate_log_negligible (N : nat -> nat) (alpha : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) ->
  negligible (fun p => gauss (N p))
    (fun p => [set xi : 'rV[RR]_(N p) |
      ln (p%:R : R) < max_norm (fun i => xi 0 i)]).
Proof.
move=> hN z z0.
have [D0 h0] := hN 1 ltr01.
have [D1 h1] := gaussian_log_eventually_large 8%:R.
pose A := `|alpha| + 1.
have A0 : 0 < A by rewrite /A ltr_wpDl ?normr_ge0.
exists (maxn (maxn D0 D1) (archimedean.Num.truncn (2 * A / z)).+1) => p.
rewrite !geq_max => /andP[/andP[pD0 pD1] pT].
have p0 : (0 < p)%N := leq_trans (ltn0Sn _) pT.
have pR : 0 < p%:R :> R by rewrite ltr0n.
have p1 : 1 <= p%:R :> R by rewrite ler1n.
have p20 : 0 < p%:R ^+ 2 :> R by rewrite exprn_gt0.
have p40 : 0 < p%:R ^+ 4 :> R by rewrite exprn_gt0.
have NR : (N p)%:R <= A * p%:R ^+ 2.
  rewrite -ler_pdivrMr //.
  have h := h0 p pD0; move: h; rewrite ltr_norml => /andP[_ h].
  apply: le_trans (_ : alpha + 1 <= A); last by rewrite /A lerD2r ler_norm.
  by move: h; rewrite ltrBlDr addrC => /ltW.
have hp : 2 * A < p%:R * z.
  rewrite -ltr_pdivrMr //.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
exists [set xi : 'rV[RR]_(N p) |
  ln (p%:R : R) < max_norm (fun i => xi 0 i)]; split => //.
- rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  apply: measurable_max_norm => i; exact: measurable_mxentry.
- apply: le_trans (gaussian_coordinate_log_tail (N p) p0 (h1 p pD1)) _.
  rewrite lee_fin ler_pdivrMr //.
  have hp2 : p%:R <= p%:R ^+ 2 :> R by rewrite expr2 ler_peMl.
  have hn2 := ler_wpM2r (ltW p20) (ltW hp).
  have hp3 := ler_wpM2l (mulr_ge0 (ltW z0) (ltW p20)) hp2.
  nra.
Qed.

Lemma gaussian_shift_target_log_term_cvg (N : nat -> nat) (alpha : R)
    (s a : nat -> R) (e : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) -> 0 <= e ->
  (exists D0 : nat, forall p, (D0 <= p)%N ->
    `|s p| <= 1 /\ `|s p * a p| <= e * Num.sqrt p%:R) ->
  cvg_prob (fun p => gauss (N p))
    (fun p xi => ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
      max_norm (gaussian_shift_target p (s p) (a p) xi)) 0.
Proof.
move=> hN e0 [D0 h0] eta eta0.
have ec0 : 0 < 4%:R * (e + 1) by rewrite mulr_gt0 // ltr_wpDl.
have cut0 : 0 < Num.min 1 (eta / (4%:R * (e + 1))).
  by rewrite lt_min ltr01 divr_gt0.
have [D1 h1] := gaussian_log_rate_cvg cut0.
have [D2 h2] := gaussian_log_eventually_large 1.
apply: negligibleW; first exact: (@gaussian_coordinate_log_negligible N alpha hN).
exists (maxn 1 (maxn D0 (maxn D1 D2))) => p.
rewrite !geq_max => /andP[p1 /andP[pD0 /andP[pD1 pD2]]] xi /= hx.
have [sp sap] := h0 p pD0.
have lp1 := h2 p pD2.
have H0 := gaussian_log_rate_ge0 p.
have hH := h1 p pD1.
rewrite subr0 (ger0_norm H0) lt_min in hH.
move/andP: hH => [H1 He].
rewrite ltr_pdivlMr // in He.
have HH : gaussian_log_rate p ^+ 2 <= gaussian_log_rate p.
  have hmul := ler_wpM2l H0 (ltW H1).
  by rewrite mulr1 -expr2 in hmul.
have small : 2 * gaussian_log_rate p ^+ 2 + 2 * e * gaussian_log_rate p < eta.
  nra.
have V0 : 0 <= ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
    max_norm (gaussian_shift_target p (s p) (a p) xi).
  apply: mulr_ge0; last exact: max_norm_ge0.
  by rewrite divr_ge0 ?sqrtr_ge0 // exprn_even_ge0.
rewrite subr0 (ger0_norm V0) in hx.
apply: contrapT => hm.
have xm : max_norm (fun i => xi 0 i) <= ln (p%:R : R).
  by rewrite leNgt; apply/negP; exact: hm.
have hb := gaussian_shift_target_log_term_le p1 lp1 sp e0 sap xm.
have := le_lt_trans (le_trans hx hb) small.
by rewrite ltxx.
Qed.

Lemma gaussian_shift_target_size_upper (N : nat -> nat) (alpha : R)
    (s a : nat -> R) (L e : R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) -> 0 <= L -> 0 <= e ->
  (exists D0 : nat, forall p, (D0 <= p)%N ->
    `|s p| <= 1 /\ `|s p * a p| <= e * Num.sqrt p%:R) ->
  forall eta z : R, 0 < eta -> 0 < z -> exists D : nat,
  forall p, (D <= p)%N ->
    (gauss (N p) [set xi : 'rV[RR]_(N p) |
      (2 * L * e * Num.sqrt alpha + eta <
        shifted_interpolation_size p L (gaussian_shift_target p (s p) (a p) xi))%R]
      <= z%:E)%E.
Proof.
move=> hN L0 e0 hb eta z eta0 z0.
pose P p := @gauss RR (N p).
pose U p (xi : 'rV[RR]_(N p)) := L *
  (Num.sqrt (\sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2) /
    (p%:R * Num.sqrt p%:R) + (2 * e) * (frobenius xi / p%:R) +
   ln (p%:R : R) ^+ 4 / Num.sqrt p%:R *
    max_norm (gaussian_shift_target p (s p) (a p) xi)).
have hc := @gaussian_centered_square_norm_cvg N alpha hN.
have hn := @gaussian_norm_over_dimension_cvg N alpha hN.
have hm := @gaussian_shift_target_log_term_cvg N alpha s a e hN e0 hb.
have hU : cvg_prob P U (2 * L * e * Num.sqrt alpha).
  have h := cvg_probM (cvg_prob_cst P L)
    (cvg_probD (cvg_probD hc (cvg_probM (cvg_prob_cst P (2 * e)) hn)) hm).
  have he : L * (0 + 2 * e * Num.sqrt alpha + 0) =
      2 * L * e * Num.sqrt alpha by ring.
  by rewrite he in h.
have [D1 h1] := hU eta eta0 z z0.
move: hb => [D0 h0].
exists (maxn 1 (maxn D0 D1)) => p.
rewrite !geq_max => /andP[p1 /andP[pD0 pD1]].
have [A [mA PA subA]] := h1 p pD1.
have [sp sap] := h0 p pD0.
have mE : measurable [set xi : 'rV[RR]_(N p) |
    2 * L * e * Num.sqrt alpha + eta <
      shifted_interpolation_size p L (gaussian_shift_target p (s p) (a p) xi)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
have sub : [set xi : 'rV[RR]_(N p) |
    2 * L * e * Num.sqrt alpha + eta <
      shifted_interpolation_size p L (gaussian_shift_target p (s p) (a p) xi)] `<=` A.
  move=> xi /= hx; apply: subA.
  have hl2 := gaussian_shift_target_l2_weighted p1 sp e0 sap
    (lexx (\sum_(i < N p) (xi 0 i ^+ 2 - 1) ^+ 2)) (lexx (frobenius xi)).
  have hs : shifted_interpolation_size p L (gaussian_shift_target p (s p) (a p) xi) <= U p xi.
    rewrite /shifted_interpolation_size /U.
    apply: ler_wpM2l => //; apply: lerD => //.
    apply: le_trans hl2 _.
    by rewrite mulrA.
  have habs := ler_norm (U p xi - 2 * L * e * Num.sqrt alpha).
  change (eta <= `|U p xi - 2 * L * e * Num.sqrt alpha|).
  nra.
apply: le_trans (le_measure _ _ _ sub) PA; by rewrite ?inE.
Qed.

Lemma gaussian_small_shift_target_size (N : nat -> nat) (alpha L : R)
    (a : nat -> R) :
  (forall z : R, 0 < z -> exists D : nat, forall p, (D <= p)%N ->
    `|(N p)%:R / p%:R ^+ 2 - alpha| < z) -> 0 <= L ->
  (forall e : R, 0 < e -> exists D : nat, forall p, (D <= p)%N ->
    `|a p| <= e * Num.sqrt p%:R) ->
  forall delta z : R, 0 < delta -> 0 < z -> exists D : nat,
  forall p, (D <= p)%N ->
    (gauss (N p) [set xi : 'rV[RR]_(N p) |
      (delta < shifted_interpolation_size p L (gaussian_shift_target p 1 (a p) xi))%R]
      <= z%:E)%E.
Proof.
move=> hN L0 ha delta z delta0 z0.
pose c := 4%:R * (L * Num.sqrt alpha + 1).
have c0 : 0 < c.
  by rewrite /c mulr_gt0 // ltr_wpDl // mulr_ge0 ?sqrtr_ge0.
have cn : c != 0 by rewrite gt_eqF.
pose e := delta / c.
have e0 : 0 < e by rewrite /e divr_gt0.
have he : e * c = delta by rewrite /e divfK.
have small : 2 * L * e * Num.sqrt alpha + delta / 2 < delta.
  move: he; rewrite /c => he; nra.
have [D0 h0] := ha e e0.
have hb : exists D0 : nat, forall p, (D0 <= p)%N ->
    `|(1 : RR)| <= 1 /\ `|(1 : RR) * a p| <= e * Num.sqrt p%:R.
  exists D0 => p pD; split; first by rewrite normr1.
  by rewrite mul1r; exact: h0.
have d20 : 0 < delta / 2 by rewrite divr_gt0.
have [D1 h1] := @gaussian_shift_target_size_upper N alpha (fun=> (1 : RR)) a
  L e hN L0 (ltW e0) hb (delta / 2) z d20 z0.
exists D1 => p pD.
have mE : measurable [set xi : 'rV[RR]_(N p) |
    delta < shifted_interpolation_size p L (gaussian_shift_target p 1 (a p) xi)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
have mF : measurable [set xi : 'rV[RR]_(N p) |
    2 * L * e * Num.sqrt alpha + delta / 2 <
      shifted_interpolation_size p L (gaussian_shift_target p 1 (a p) xi)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
apply: le_trans _ (h1 p pD).
apply: le_measure; rewrite ?inE //.
by move=> xi /= hx; exact: lt_trans small hx.
Qed.
