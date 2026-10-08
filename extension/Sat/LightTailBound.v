(* Proposition 3.4 of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 2436-2450, proof lines
   3610-3805 of arxiv_v1.tex): the light-tail quotient-norm lower bound, at
   Stdlib's R. Item S9 of stage 3 of phase 5 (lane B), with Sat/LightTail,
   which proves the union bound over the nets and its count over any
   realType.

   Statement (light_tail_quotient). Let the coordinates of the points
   x_1, ..., x_n of R^d be independent with laws
   universality_coordinate_law kappa K, with 1 < kappa, and let n / d^2
   tend to alpha in (0, 1/2). There are K1 > 0 and gam > 0, depending only
   on kappa, K and alpha, such that for every C0 > 0 and every eps > 0, for
   every large d, outside a measurable event of probability at most eps:
   for every set I of at most C0 d ln d rows, every h supported on I and
   every t supported off I with K1 d t_i^2 <= |t|^2 for every i and
   |h|_1 <= d |t|,

     gam d |t| <= nuclear (L_X^* (h + t)),

   where L_X^* z = sum_i z_i (x_i x_i^T - I) / sqrt d is sample_adj of
   Sat/Apriori. This is the form in which Theorem 1.9 (Sat/Interpolation)
   takes the proposition. It contains the paper's statement, whose heads
   have |h|_1 <= d^(2/3) |t|; t is not normalized.

   Proof. The blocks of light_union (Sat/LightTail): eps = (1/2 - alpha) / 2
   and L > 2 / (1/2 - alpha) blocks of columns, so that
   a = (1 - eps) (L - 1) / (2 L) exceeds alpha; stage l controls all but
   floor (eps p_l) eigenvalues of its matrix Sigma_t. Two events:
   - the a priori event of Proposition 3.1 (adjoint_bound_limit of
     Sat/Apriori, from the Hanson-Wright inequality of lane A):
     |x_i|^2 < 2 d for every i and |L_X^* z|_F <= C1 sqrt d |z|, hence
     nuclear (L_X^* z) <= C1 d |z| and the same for every block; on it,
     Corollary 3.13 (block_effective_rank_light of Sat/EffectiveRank)
     gives the good events of all stages for every light unit tail, once
     K1 >= 16 L C1^2 / eps, and |t_i| |u_i| <= rho once K1 >= 2 / rho^2;
   - the bad event of light_union, of probability at most expR (- d) by
     light_count, for gam as in light_gamma.
   Outside their union the conclusion holds for unit tails, and for all t
   by homogeneity (light_scale).

   Also proved here: coordinate_law_truncated, the truncated second
   moment E[x^2 1_(|x| <= sqrt (2 kappa))] >= 1/2 of the coordinates;
   blk_k, the number of eigenvalues controlled at each stage, and
   blk_sum_ge, the exponent sum_l k_l q_l >= a (d - L)^2 of the count. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval archimedean.
From mathcomp Require Import boolp classical_sets cardinality reals Rstruct.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability.
From mathcomp Require Import measurable_realfun measurable_fun_approximation.
From GaussianAnalysis Require Import measurable_matrix.
From GaussianAnalysis Require Import euclidean opnorm nets real_spectral.
From GaussianAnalysis Require Import von_neumann nuclear restricted_isometry.
From GaussianAnalysis Require Import lindeberg tuple_rows conditioning.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Sat Require Import OneStage Apriori EffectiveRank.
From EllipsoidUniversality.Sat Require Import Interpolation LightTail.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

Section blk_count.
Context {RT : realType}.

(* The number of eigenvalues that the good event of stage s controls:
   all but floor (eps p_s). *)
Definition blk_k (L d : nat) (eps : RT) (s : nat) : nat :=
  (blk_p L d s - truncn (eps * (blk_p L d s)%:R))%N.

Lemma blk_k_ge (L d s : nat) (eps : RT) : 0 <= eps -> eps <= 1 ->
  (1 - eps) * (blk_p L d s)%:R <= (blk_k L d eps s)%:R.
Proof.
move=> e0 e1; rewrite /blk_k.
set p := blk_p L d s.
have ep0 : 0 <= eps * p%:R by rewrite mulr_ge0.
have tle : (truncn (eps * p%:R))%:R <= eps * p%:R by rewrite truncn_le.
have tp : (truncn (eps * p%:R) <= p)%N.
  rewrite -(ler_nat RT); apply: le_trans tle _.
  by rewrite ler_piMl.
by rewrite natrB // mulrBl mul1r lerD2l lerN2.
Qed.

Lemma blk_k_le (L d s : nat) (eps : RT) : (blk_k L d eps s <= blk_p L d s)%N.
Proof. exact: leq_subr. Qed.

Lemma sum_natr_succ (k : nat) :
  \sum_(l < k) (l%:R + 1) = k%:R * (k%:R + 1) / 2 :> RT.
Proof.
elim: k => [|k IH]; first by rewrite big_ord0 mul0r mul0r.
rewrite big_ord_recr /= IH -[k.+1%:R]natr1.
by field.
Qed.

(* The exponent of the probability of the bad pairs: sum_l k_l q_l is at
   least (1 - eps) (L - 1) / (2 L) (d - L)^2. *)
Lemma blk_sum_ge (L d : nat) (eps : RT) : (1 < L)%N -> (L <= d)%N ->
  0 <= eps -> eps <= 1 ->
  (1 - eps) * (L.-1)%:R / (2 * L%:R) * (d%:R - L%:R) ^+ 2 <=
  (\sum_(l < L.-1) blk_k L d eps l * blk_q L d l)%N%:R.
Proof.
move=> L1 Ld e0 e1.
have L0 : (0 < L)%N by apply: ltn_trans L1.
have L0R : 0 < L%:R :> RT by rewrite ltr0n.
have dL : 0 <= d%:R / L%:R - 1 :> RT.
  by rewrite subr_ge0 ler_pdivlMr // mul1r ler_nat.
set u : RT := d%:R / L%:R - 1.
rewrite natr_sum.
apply: le_trans (_ : \sum_(l < L.-1) ((1 - eps) * u ^+ 2 * (l%:R + 1)) <= _).
  rewrite -mulr_sumr sum_natr_succ.
  have LE : (L.-1)%:R + 1 = L%:R :> RT by rewrite natr1 prednK.
  rewrite LE /u le_eqVlt; apply/orP; left; apply/eqP.
  have Ln : L%:R != 0 :> RT by rewrite gt_eqF.
  by field.
apply: ler_sum => l _.
have lL : (l.+1 < L)%N by rewrite -ltn_predRL.
have hp := blk_p_ge d L0 (ltnW lL).
have hq := blk_q_ge d L0 lL.
have hk := blk_k_ge L d l eps e0 e1.
rewrite natrM.
have e10 : 0 <= 1 - eps by rewrite subr_ge0.
have p0 : 0 <= l.+1%:R * u by rewrite mulr_ge0.
apply: le_trans (_ : (1 - eps) * (blk_p L d l)%:R * (blk_q L d l)%:R <= _).
  have hp' : (l%:R + 1) * u <= (blk_p L d l)%:R by rewrite natr1.
  have -> : (1 - eps) * u ^+ 2 * (l%:R + 1) = (1 - eps) * ((l%:R + 1) * u) * u.
    by ring.
  apply: ler_pM => //; first by rewrite mulr_ge0 // mulr_ge0 // addr_ge0.
    exact: (ler_wpM2l e10 hp').
  exact: hq.
exact: (ler_wpM2r (ler0n _ _) hk).
Qed.

(* For d >= 2 L, the stages before the last reveal and add at least
   d / (2 L) columns. *)
Lemma blk_half (L d l : nat) : (0 < L)%N -> (2 * L <= d)%N -> (l < L.-1)%N ->
  d%:R / (2 * L%:R) <= (blk_p L d l)%:R :> RT /\
  d%:R / (2 * L%:R) <= (blk_q L d l)%:R :> RT.
Proof.
move=> L0 dL lL.
have lL' : (l.+2 <= L)%N by rewrite -ltn_predRL.
have L0R : 0 < L%:R :> RT by rewrite ltr0n.
have L2 : 0 < 2 * L%:R :> RT by apply: mulr_gt0; [exact: ltr0Sn | exact: L0R].
have hdL : 1 <= d%:R / (2 * L%:R) :> RT.
  by rewrite ler_pdivlMr // mul1r -natrM ler_nat.
have h1 : d%:R / (2 * L%:R) <= d%:R / L%:R - 1 :> RT.
  have -> : d%:R / L%:R = d%:R / (2 * L%:R) + d%:R / (2 * L%:R) :> RT.
    have Ln : L%:R != 0 :> RT by rewrite gt_eqF.
    by field.
  by rewrite -addrA lerDl subr_ge0.
have u0 : 0 <= d%:R / L%:R - 1 :> RT.
  by apply: le_trans h1; apply: le_trans hdL; exact: ler01.
split; last exact: le_trans h1 (blk_q_ge d L0 lL').
apply: le_trans h1 _; apply: le_trans _ (blk_p_ge d L0 (ltnW lL')).
by rewrite ler_peMl // ler1n.
Qed.

(* The hypotheses of light_union on the stages, with c0 = (1 - eps) / (2 L). *)
Lemma blk_k_hyp (L d l : nat) (eps : RT) : (1 < L)%N -> (2 * L <= d)%N ->
  0 <= eps -> eps <= 1 -> (l < L.-1)%N ->
  ((1 - eps) / (2 * L%:R) * d%:R <= (blk_k L d eps l)%:R) /\
  ((1 - eps) / (2 * L%:R) * d%:R <= (blk_q L d l)%:R) /\
  (blk_k L d eps l <= blk_p L d l)%N /\ (blk_k L d eps l <= d)%N.
Proof.
move=> L1 dL e0 e1 lL.
have L0 : (0 < L)%N by apply: ltn_trans L1.
have [hp hq] := blk_half L d l L0 dL lL.
have e10 : 0 <= 1 - eps by rewrite subr_ge0.
have ce : (1 - eps) / (2 * L%:R) * d%:R = (1 - eps) * (d%:R / (2 * L%:R)).
  by rewrite mulrAC -mulrA.
have dh0 : 0 <= d%:R / (2 * L%:R) :> RT.
  by rewrite divr_ge0 ?mulr_ge0 ?ler0n.
split.
  rewrite ce; exact: le_trans (ler_wpM2l e10 hp) (blk_k_ge L d l eps e0 e1).
split.
  rewrite ce; apply: le_trans _ hq.
  by rewrite ler_piMl // lerBlDr lerDl.
split; first exact: blk_k_le.
exact: leq_trans (blk_k_le L d l eps) (blk_bnd_le L d l.+1).
Qed.

(* The parameter k' = floor (eps p_l) + 1 of Corollary 3.13 at stage l:
   k' <= p_l, k' >= eps d / (2 L), and j + k' <= p_l for j < k_l. *)
Lemma blk_eff (L d l : nat) (eps : RT) : (1 < L)%N -> (2 * L <= d)%N ->
  0 < eps -> eps < 1 -> (l < L.-1)%N ->
  [/\ ((truncn (eps * (blk_p L d l)%:R)).+1 <= blk_p L d l)%N,
    eps * (d%:R / (2 * L%:R)) <= ((truncn (eps * (blk_p L d l)%:R)).+1)%:R &
    forall j, (j < blk_k L d eps l)%N ->
      (j + (truncn (eps * (blk_p L d l)%:R)).+1 <= blk_p L d l)%N].
Proof.
move=> L1 dL e0 e1 lL.
have L0 : (0 < L)%N by apply: ltn_trans L1.
have [hp _] := blk_half L d l L0 dL lL.
have L0R : 0 < L%:R :> RT by rewrite ltr0n.
have L2 : 0 < 2 * L%:R :> RT by apply: mulr_gt0; [exact: ltr0Sn | exact: L0R].
have hdL : 1 <= d%:R / (2 * L%:R) :> RT.
  by rewrite ler_pdivlMr // mul1r -natrM ler_nat.
have p0 : 0 < (blk_p L d l)%:R :> RT.
  by apply: lt_le_trans hp; apply: lt_le_trans hdL; exact: ltr01.
have ep0 : 0 <= eps * (blk_p L d l)%:R by rewrite mulr_ge0 // ltW.
have tle : (truncn (eps * (blk_p L d l)%:R))%:R <= eps * (blk_p L d l)%:R.
  by rewrite truncn_le.
split.
- rewrite -(ltr_nat RT); apply: le_lt_trans tle _.
  by rewrite -[X in _ < X]mul1r ltr_pM2r.
- apply: le_trans _ (ltW (truncnS_gt _)).
  by rewrite ler_pM2l.
- move=> j; rewrite /blk_k ltn_subRL => hj.
  by rewrite addnS addnC.
Qed.

End blk_count.

Section coordinate_truncated.
Local Open Scope ereal_scope.

(* The truncated second moment of the coordinates, from the fourth moment:
   E[x^2 1_(|x| <= sqrt (2 kappa))] >= 1/2, since x^2 1_(|x| > M) <=
   x^4 / M^2. *)
Lemma coordinate_law_truncated (kappa K : R)
    (mu : probability (measurableTypeR R) R) :
  (1 < kappa)%R -> universality_coordinate_law kappa K mu ->
  (2^-1)%:E <= \int[mu]_x
    (((x : RR) ^+ 2 *
      \1_[set y : RR | (`|y| <= Num.sqrt (2 * kappa))%R] x)%R)%:E.
Proof.
move=> k1 hmu.
set M := Num.sqrt (2 * kappa).
have k0 : (0 < kappa)%R by apply: lt_trans k1; exact: ltr01.
have k2 : (0 < 2 * kappa)%R by rewrite mulr_gt0.
have M0 : (0 <= M)%R by exact: sqrtr_ge0.
have M2 : (M ^+ 2 = 2 * kappa)%R by rewrite sqr_sqrtr // ltW.
pose c := ((2 * kappa)^-1)%R.
have c0 : (0 <= c)%R by rewrite invr_ge0 ltW.
have i2 := coordinate_law_integrable _ _ _ hmu 2.
have i4 := coordinate_law_integrable _ _ _ hmu 4.
pose f (x : RR) := (x ^+ 2 - c * x ^+ 4)%R.
pose g (x : RR) := (x ^+ 2 * \1_[set y : RR | (`|y| <= M)%R] x)%R.
have mA : measurable [set y : RR | (`|y| <= M)%R].
  rewrite (_ : [set y | _] = `[(- M)%R, M]%classic); last exact: measurable_itv.
  by apply/seteqP; split => y /=; rewrite in_itv /= ler_norml.
have i4c : mu.-integrable setT
    (fun x : measurableTypeR R => (c * (x : RR) ^+ 4)%:E).
  have := integrableZl measurableT c i4.
  by apply: eq_integrable => // x _; rewrite EFinM.
have fi : mu.-integrable setT (EFin \o f).
  have := integrableB measurableT i2 i4c.
  by apply: eq_integrable => // x _; rewrite /f /= EFinB.
have mg : measurable_fun setT g.
  apply: measurable_funM; first exact: measurable_funX.
  exact: measurable_indic.
have gi : mu.-integrable setT (EFin \o g).
  apply: le_integrable i2 => //; first exact/measurable_EFinP.
  move=> x _; rewrite /comp /g !abse_EFin lee_fin (ger0_norm (sqr_ge0 x)) indicE.
  case: (x \in _); rewrite ?mulr1 ?mulr0 ?normr0 ?(ger0_norm (sqr_ge0 x)) //.
  exact: sqr_ge0.
have fg x : (f x <= g x)%R.
  rewrite /f /g indicE; case: (boolP (x \in _)) => [hx|hx].
    rewrite mulr1 lerBlDr lerDl; apply: mulr_ge0 => //.
    by rewrite (_ : 4%N = (2 * 2)%N) // exprM sqr_ge0.
  rewrite mulr0 subr_le0.
  have hM : (M ^+ 2 <= x ^+ 2)%R.
    have hx' : (M <= `|x|)%R.
      apply: ltW; rewrite ltNge; apply/negP => h; apply: (negP hx).
      by rewrite in_setE.
    have h1 : (M * M <= `|x| * `|x|)%R by apply: ler_pM.
    have h2 : (`|x| * `|x| = x ^+ 2)%R.
      by rewrite -normrM -expr2 (ger0_norm (sqr_ge0 x)).
    by rewrite [(M ^+ 2)%R]expr2 -h2.
  have Mp : (0 < M ^+ 2)%R by rewrite M2.
  have x4 : (x ^+ 4 = x ^+ 2 * x ^+ 2)%R by rewrite -exprD.
  rewrite /c -M2 mulrC ler_pdivlMr // x4.
  exact: (ler_wpM2l (sqr_ge0 x) hM).
apply: le_trans (_ : \int[mu]_x (f x)%:E <= _); last first.
  by apply: le_integral => // x _; rewrite lee_fin; exact: fg.
rewrite (integralB_EFin measurableT i2 i4c).
have e4 : \int[mu]_x ((c * (x : RR) ^+ 4)%R)%:E =
    c%:E * \int[mu]_x (((x : RR) ^+ 4)%R)%:E.
  transitivity (\int[mu]_x (c%:E * (((x : RR) ^+ 4)%R)%:E)).
    by apply: eq_integral => x _; rewrite EFinM.
  by rewrite integralZl.
rewrite e4.
rewrite (coordinate_law_second _ _ _ hmu) (coordinate_law_fourth _ _ _ hmu).
rewrite -EFinM -EFinB lee_fin /c.
have kn : kappa != 0%R by rewrite gt_eqF.
have -> : ((2 * kappa)^-1 * kappa = 2^-1)%R by field.
by lra.
Qed.

End coordinate_truncated.

Section sample_link.

Lemma paper_point_sample n d (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point x i = (sample_point x i)^T.
Proof.
rewrite paper_main_point_row; apply/matrixP => j k.
by rewrite ord1 !mxE !tnth_mktuple.
Qed.

Lemma sample_W_feature n d (x : paper_main_sample n d) (i : 'I_n) :
  sample_W x i = sample_feature x i.
Proof. by rewrite /sample_W /sample_feature paper_point_sample trmxK. Qed.

(* L_X^* of Sat/Apriori is coef_adj of the features of Sat/LightTail. *)
Lemma sample_adj_feature n d (x : paper_main_sample n d) (z : 'rV[R]_n) :
  sample_adj x z = coef_adj (sample_feature x) z.
Proof.
rewrite /sample_adj; congr coef_adj; apply/funext => i.
exact: sample_W_feature.
Qed.

(* The block rows of Sat/EffectiveRank are the stage rows of
   Sat/OneStage. *)
Lemma block_row_stage n d p (x : paper_main_sample n d) (c : 'I_p -> 'I_d)
    (i : 'I_n) :
  block_row n d p x c i = stage_row c x i.
Proof.
apply/rowP => a; rewrite /block_row /stage_row paper_point_sample.
by rewrite !mxE.
Qed.

Lemma coef_adj_featureZ n d (x : paper_main_sample n d) (a : R)
    (z : 'rV[R]_n) :
  coef_adj (sample_feature x) (a *: z) = a *: coef_adj (sample_feature x) z.
Proof.
rewrite /coef_adj scaler_sumr; apply: eq_bigr => i _.
by rewrite mxE -scalerA.
Qed.

Lemma l1normZ n (a : R) (h : 'rV[R]_n) : l1norm (a *: h) = `|a| * l1norm h.
Proof.
rewrite /l1norm mulr_sumr; apply: eq_bigr => i _.
by rewrite mxE normrM.
Qed.

End sample_link.

Section light_arith.
Context {RT : realType}.

Lemma density_upper (nd d2 al t : RT) : 0 < d2 ->
  `|nd / d2 - al| < t -> nd <= (al + t) * d2.
Proof.
move=> d20; rewrite ltr_distl => /andP[_ h].
by move: h; rewrite ltr_pdivrMr // => /ltW.
Qed.

(* The exponent a = (1 - eps) (L - 1) / (2 L) of the count exceeds alpha
   for eps = (1/2 - alpha) / 2 and L > 2 / (1/2 - alpha). *)
Lemma block_a_gt (al Lr : RT) : 0 < al -> al < 2^-1 ->
  2 / (2^-1 - al) < Lr ->
  al < (1 - (2^-1 - al) / 2) * (Lr - 1) / (2 * Lr).
Proof.
move=> a0 ah hL.
have dl0 : 0 < 2^-1 - al by rewrite subr_gt0.
have L0 : 0 < Lr by apply: lt_trans hL; rewrite divr_gt0.
have hL' : 2 < Lr * (2^-1 - al) by rewrite -ltr_pdivrMr.
rewrite ltr_pdivlMr ?mulr_gt0 //.
by nra.
Qed.

Lemma block_a_le (eps Lr : RT) : 0 <= eps -> 1 <= Lr ->
  (1 - eps) * (Lr - 1) / (2 * Lr) <= 1 / 2.
Proof.
move=> e0 L1; have L0 : 0 < Lr by apply: lt_le_trans L1; exact: ltr01.
rewrite ler_pdivrMr ?mulr_gt0 //.
have h : (1 - eps) * (Lr - 1) <= Lr - 1.
  by rewrite ler_piMl // ?subr_ge0 //; lra.
by apply: le_trans h _; lra.
Qed.

Lemma light_exp_small (K e : RT) : 0 < K -> 0 < e ->
  exists D : nat, forall d : nat, (D <= d)%N -> expR (- (K * d%:R)) <= e.
Proof.
move=> K0 e0; exists (truncn (e^-1 / K)).+1 => d hd.
have hdK : e^-1 / K < d%:R.
  apply: lt_le_trans (truncnS_gt _) _; rewrite ler_nat; exact: hd.
have x0 : 0 < K * d%:R.
  rewrite mulr_gt0 //; apply: le_lt_trans hdK.
  by rewrite divr_ge0 // ?invr_ge0 ltW.
rewrite expRN -[e]invrK lef_pV2 ?posrE ?invr_gt0 ?expR_gt0 //.
apply: le_trans (_ : 1 + K * d%:R <= _); last exact: expR_ge1Dx.
have : e^-1 < K * d%:R by rewrite mulrC -ltr_pdivrMr.
by lra.
Qed.

(* |t_i| |u_i| <= rho when |t_i| <= (K d)^(-1/2), |u_i|^2 <= 2 d and
   K >= 2 / rho^2. *)
Lemma tail_rho (K d rho b u : RT) : 0 < K -> 0 < d -> 0 < rho ->
  2 / rho ^+ 2 <= K -> 0 <= u -> u ^+ 2 <= 2 * d -> 0 <= b ->
  b <= (Num.sqrt (K * d))^-1 -> b * u <= rho.
Proof.
move=> K0 d0 r0 hK u0 hu b0 hb.
have Kd0 : 0 < K * d by rewrite mulr_gt0.
have bu0 : 0 <= b * u by rewrite mulr_ge0.
have r0' : 0 <= rho by exact: ltW.
rewrite -(@ler_pXn2r _ 2) ?nnegrE // exprMn.
have hb2 : b ^+ 2 <= (K * d)^-1.
  have m1 : b \in Num.nneg by rewrite nnegrE.
  have m2 : (Num.sqrt (K * d))^-1 \in Num.nneg.
    by rewrite nnegrE invr_ge0 sqrtr_ge0.
  apply: le_trans (lerXn2r 2 m1 m2 hb) _.
  by rewrite exprVn sqr_sqrtr // ltW.
apply: le_trans (_ : (K * d)^-1 * (2 * d) <= _).
  apply: ler_pM => //; [exact: sqr_ge0 | exact: sqr_ge0].
have -> : (K * d)^-1 * (2 * d) = 2 / K.
  have Kn : K != 0 by rewrite gt_eqF.
  have dn : d != 0 by rewrite gt_eqF.
  by field.
rewrite ler_pdivrMr // mulrC -ler_pdivrMr ?exprn_gt0 //.
Qed.

(* The condition 8 C1^2 d <= K1 k' of Corollary 3.13, for
   K1 >= 16 L C1^2 / eps and k' >= eps d / (2 L). *)
Lemma eff_K (K1 C1 eps Lr dr kr : RT) : 0 < eps -> 0 < Lr -> 0 <= dr ->
  16 * Lr * C1 ^+ 2 / eps <= K1 -> eps * (dr / (2 * Lr)) <= kr ->
  8 * C1 ^+ 2 * dr <= K1 * kr.
Proof.
move=> e0 L0 d0 hK hk.
have a0 : 0 <= 16 * Lr * C1 ^+ 2 / eps.
  apply: divr_ge0; last exact: ltW.
  apply: mulr_ge0; last exact: sqr_ge0.
  by apply: mulr_ge0; [exact: ler0n | exact: ltW].
have b0 : 0 <= eps * (dr / (2 * Lr)).
  apply: mulr_ge0; first exact: ltW.
  apply: divr_ge0 => //.
  by apply: mulr_ge0; [exact: ler0n | exact: ltW].
apply: le_trans _ (ler_pM a0 b0 hK hk).
have en : eps != 0 by rewrite gt_eqF.
have Ln : Lr != 0 by rewrite gt_eqF.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* A light unit tail: |b| <= (K d)^(-1/2) gives K d b^2 <= 1. *)
Lemma light_sq (Kd b : RT) : 0 < Kd -> `|b| <= (Num.sqrt Kd)^-1 ->
  Kd * b ^+ 2 <= 1.
Proof.
move=> K0 hb.
have h2 : b ^+ 2 <= ((Num.sqrt Kd)^-1) ^+ 2.
  rewrite -[b ^+ 2](ger0_norm (sqr_ge0 b)) normrX.
  by rewrite ler_sqr ?nnegrE ?normr_ge0 ?invr_ge0 ?sqrtr_ge0.
have Kn : Kd != 0 by rewrite gt_eqF.
have e : Kd * ((Num.sqrt Kd)^-1) ^+ 2 = 1.
  by rewrite exprVn sqr_sqrtr ?ltW // mulfV.
by rewrite -e ler_pM2l.
Qed.

(* Conversely, K d b^2 <= s^2 gives |b / s| <= (K d)^(-1/2). *)
Lemma light_unit (Kd b s : RT) : 0 < Kd -> 0 < s -> Kd * b ^+ 2 <= s ^+ 2 ->
  `|s^-1 * b| <= (Num.sqrt Kd)^-1.
Proof.
move=> K0 s0 h.
have sK : 0 < Num.sqrt Kd by rewrite sqrtr_gt0.
have h1 : Num.sqrt Kd * `|b| <= s.
  have e : Num.sqrt Kd * `|b| = Num.sqrt (Kd * b ^+ 2).
    by rewrite sqrtrM ?ltW // sqrtr_sqr.
  have s0' : 0 <= s by exact: ltW.
  rewrite e -[X in _ <= X](ger0_norm s0') -sqrtr_sqr.
  exact: ler_wsqrtr h.
have si : 0 <= s^-1 by rewrite invr_ge0; exact: ltW.
rewrite normrM (ger0_norm si).
have sn : Num.sqrt Kd != 0 by rewrite gt_eqF.
have sn' : s != 0 by rewrite gt_eqF.
have -> : s^-1 * `|b| = Num.sqrt Kd * `|b| / (Num.sqrt Kd * s) by field.
rewrite ler_pdivrMr ?mulr_gt0 //.
have -> : (Num.sqrt Kd)^-1 * (Num.sqrt Kd * s) = s by field.
exact: h1.
Qed.

Lemma norm_good_sq (u d : RT) : `|u - d| < 1 * d -> u <= 2 * d.
Proof. by rewrite mul1r ltr_distl => /andP[_ h]; apply: ltW; lra. Qed.

Lemma sq_le (u v w : RT) : 0 <= u -> u <= v -> v ^+ 2 <= w -> u ^+ 2 <= w.
Proof.
move=> u0 uv vw; apply: le_trans vw.
by rewrite ler_sqr ?nnegrE // (le_trans u0 uv).
Qed.

End light_arith.

Section prob_union.
Context {RT : realType} {dT : measure_display} {T : measurableType dT}.
Variable P : probability T RT.

Lemma prob_union_le (A B : set T) (a b : RT) : measurable A -> measurable B ->
  (P A <= a%:E)%E -> (P B <= b%:E)%E -> (P (A `|` B) <= (a + b)%:E)%E.
Proof.
move=> mA mB hA hB; apply: le_trans (measureU2 P mA mB) _.
by rewrite EFinD; exact: leeD.
Qed.

End prob_union.

Lemma adj_const_gt0 (K Chw C0 : R) : 0 < Chw -> 0 <= C0 ->
  0 < adj_const K Chw C0.
Proof.
move=> Chw0 C00; rewrite /adj_const.
set T0 := (2100 * Chw * K ^+ 2 * (2 + C0))%R.
have T00 : (0 <= T0)%R.
  apply: mulr_ge0; last exact: addr_ge0 (ler0n _ 2) C00.
  apply: mulr_ge0; last exact: sqr_ge0.
  by apply: mulr_ge0; [exact: ler0n | exact: ltW].
apply: mulr_gt0; rewrite sqrtr_gt0; last exact: ltr_wpDl C00 (ltr0Sn _ 1).
have h1 : (0 <= 256 * T0 ^+ 2)%R.
  by apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0].
have h2 : (0 <= 32 * Num.sqrt 5 * T0)%R.
  apply: mulr_ge0; last exact: T00.
  by apply: mulr_ge0; [exact: ler0n | exact: sqrtr_ge0].
apply: lt_le_trans (_ : (0 < 25%:R)%R) _; first exact: ltr0Sn.
by rewrite lerDr; exact: addr_ge0.
Qed.

Section scaling.

(* Outside the bad event of light_union, the conclusion for every head and
   every light tail, by scaling t to a unit vector. *)
Lemma light_scale n d L m (K gam : R) (x : paper_main_sample n d) :
  0 < K -> (0 < d)%N -> ~ light_bad L m K d%:R gam x ->
  forall (I : {set 'I_n}) (h t : 'rV[R]_n), (#|I| <= m)%N ->
    supported I h -> supported (~: I) t ->
    (forall i, K * d%:R * t 0 i ^+ 2 <= mxdot t t) ->
    l1_norm h <= d%:R * frobenius t ->
    gam * d%:R * frobenius t <= nuclear (sample_adj x (h + t)).
Proof.
move=> K0 d0 nb I h t hI hh ht hlight hl1.
rewrite /supported in hh ht.
have [->|tn0] := eqVneq t 0.
  by rewrite frobenius0 mulr0; exact: nuclear_ge0.
have s0 : 0 < frobenius t by rewrite frobenius_gt0.
have si0 : 0 <= (frobenius t)^-1 by rewrite invr_ge0 ltW.
have sn : frobenius t != 0 by rewrite gt_eqF.
have Kd0 : 0 < K * d%:R by rewrite mulr_gt0 // ltr0n.
rewrite leNgt; apply/negP => hlt; apply: nb.
exists I, ((frobenius t)^-1 *: h), ((frobenius t)^-1 *: t); split => //.
- split; first by move=> i hi; rewrite mxE hh // mulr0.
  by rewrite l1normZ ger0_norm // mulrC ler_pdivrMr.
- split.
  + move=> i hi; rewrite mxE (ht i) ?mulr0 //.
    by rewrite finset.in_setC hi.
  + by rewrite frobeniusZ ger0_norm // mulVf.
  + move=> i; rewrite mxE; apply: light_unit => //.
    by rewrite frobenius_sqr; exact: hlight.
- move=> l _.
  apply: le_lt_trans (nuclear_stage_map_le x _ (@blk_cU_inj L d l)
    (@blk_cJ_inj L d l) (@blk_cUJ L d l)) _.
  rewrite -scalerDr coef_adj_featureZ nuclearZ ger0_norm //.
  by rewrite -sample_adj_feature mulrC ltr_pdivrMr.
Qed.

End scaling.

Section light_tail_theorem.

(* Proposition 3.4, in the form that Theorem 1.9 takes. *)
Theorem light_tail_quotient (kappa K alpha : R) :
  1 < kappa -> 0 < alpha -> alpha < 2^-1 ->
  exists K1 gam : R, [/\ 0 < K1, 0 < gam &
  forall C0 : R, 0 < C0 ->
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_sample_law (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (I : {set 'I_(n d)}) (h t : 'rV[R]_(n d)),
      #|I|%:R <= C0 * d%:R * ln (d%:R : R) ->
      supported I h -> supported (~: I) t ->
      (forall i, K1 * d%:R * t 0 i ^+ 2 <= mxdot t t) ->
      l1_norm h <= d%:R * frobenius t ->
      gam * d%:R * frobenius t <= nuclear (sample_adj x (h + t))]].
Proof.
move=> k1 a0 ah.
(* the blocks: eps = (1/2 - alpha) / 2 and L > 2 / (1/2 - alpha) *)
set dlt : R := (2^-1 - alpha)%R.
have dlt0 : 0 < dlt by rewrite /dlt subr_gt0.
have dlt1 : dlt <= 2^-1 by rewrite /dlt gerBl ltW.
set ep : R := (dlt / 2)%R.
have ep0 : 0 < ep by rewrite /ep divr_gt0.
have ep1 : ep < 1.
  by apply: le_lt_trans (_ : ep <= 2^-1) _; rewrite /ep; lra.
have ep0' : 0 <= ep by exact: ltW.
have ep1' : ep <= 1 by exact: ltW.
set L : nat := (truncn (2 / dlt)).+1.
have LdR : 2 / dlt < L%:R by exact: truncnS_gt.
have L1 : (1 < L)%N.
  rewrite -(ltr_nat R); apply: le_lt_trans LdR.
  by rewrite ler_pdivlMr // mul1r; apply: le_trans dlt1 _; lra.
have L0 : (0 < L)%N by apply: ltn_trans L1.
have LR0 : 0 < L%:R :> R by rewrite ltr0n.
have LR1 : 1 <= L%:R :> R by rewrite ler1n.
set a : R := ((1 - ep) * (L.-1)%:R / (2 * L%:R))%R.
have LE : (L.-1)%:R = (L%:R - 1)%R :> R.
  by rewrite -subn1 natrB.
have aE : a = ((1 - ep) * (L%:R - 1) / (2 * L%:R))%R by rewrite /a LE.
have aa : alpha < a by rewrite aE /ep /dlt; exact: block_a_gt.
have a12 : a <= 1 / 2 by rewrite aE; apply: block_a_le => //; exact: ltW.
(* the constants of the union bound *)
set M : R := Num.sqrt (2 * kappa).
have M0 : 0 < M by rewrite sqrtr_gt0 mulr_gt0 //; lra.
set mu : R := 8^-1.
have mu0 : 0 < mu by rewrite invr_gt0 ltr0n.
set c0 : R := ((1 - ep) / (2 * L%:R))%R.
have c00 : 0 < c0 by rewrite /c0 divr_gt0 ?subr_gt0 // mulr_gt0 // ltr0n.
have [C C0' hC] := light_union M0 mu0 c00.
(* the constant of Proposition 3.1 *)
set C1 : R := adj_const K (252)%R (alpha + 1).
have C10 : 0 < C1.
  apply: adj_const_gt0; first by rewrite ltr0n.
  have a0' : 0 <= alpha by exact: ltW.
  exact: addr_ge0 a0' ler01.
have C10' : 0 <= C1 by exact: ltW.
have [gam [gam0 gam1 gamC1 gamC gexp]] := light_gamma a0 aa C0' C10.
set rho : R := (2 * gam / C)%R.
have rho0 : 0 < rho by rewrite /rho divr_gt0 // mulr_gt0.
have hCrho : C * rho <= 2 * gam.
  by rewrite /rho mulrC divfK ?gt_eqF.
(* K1: light tails for the union bound and for Corollary 3.13 *)
set K1 : R := Num.max (2 / rho ^+ 2) (16 * L%:R * C1 ^+ 2 / ep).
have K1rho : 2 / rho ^+ 2 <= K1 by rewrite le_max lexx.
have K1eff : 16 * L%:R * C1 ^+ 2 / ep <= K1 by rewrite le_max lexx orbT.
have K10 : 0 < K1.
  by apply: lt_le_trans K1rho; rewrite divr_gt0 // exprn_gt0.
exists K1, gam; split => //.
move=> C0 C00 nu hnu n hn eta eta0.
have e20 : 0 < eta / 2 by rewrite divr_gt0.
have [Dc hcount] := light_count L a0 aa a12 C0' C10 gam0 gamC gexp C00.
have [Dap hap] :=
  adjoint_bound_limit kappa K alpha nu n hnu a0 hn (eta / 2) e20.
set tol : R := ((a - alpha) / 2)%R.
have tol0 : 0 < tol by rewrite /tol divr_gt0 // subr_gt0.
have [Dn hdn] := hn tol tol0.
have [De hexp] := light_exp_small 1 (eta / 2) ltr01 e20.
exists (maxn (maxn Dc Dap) (maxn (maxn Dn De) (2 * L))) => d.
rewrite !geq_max => /andP[/andP[dc dap] /andP[/andP[dn de] d2L]].
have d0 : (0 < d)%N by apply: leq_trans d2L; rewrite muln_gt0 L0.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have d2R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0.
have dL : (L <= d)%N by apply: leq_trans d2L; rewrite leq_pmull.
have hna : (n d)%:R <= (alpha + a) / 2 * d%:R ^+ 2.
  have e : alpha + tol = (alpha + a) / 2 by rewrite /tol; field.
  rewrite -e; exact: (density_upper (n d)%:R (d%:R ^+ 2) alpha tol d2R
    (hdn d dn)).
have hnu' j : (j < d)%N -> universality_coordinate_law kappa K (nu d j).
  exact: hnu.
(* the a priori event (Proposition 3.1) *)
have [E0 [mE0 PE0 hE0]] := hap d dap.
(* the union bound *)
set m : nat := truncn (C0 * d%:R * ln (d%:R : R)).
set k := blk_k L d ep.
have lnd : 0 <= C0 * d%:R * ln (d%:R : R).
  have C00' : 0 <= C0 by exact: ltW.
  apply: mulr_ge0; first exact: mulr_ge0 C00' (ler0n _ d).
  by apply: ln_ge0; rewrite ler1n.
have hm : m%:R <= C0 * d%:R * ln (d%:R : R) by rewrite /m truncn_le.
have hm0 j : (j < d)%N -> (\int[nu d j]_x (x : R)%:E = 0)%E.
  by move=> hj; exact: coordinate_law_mean _ _ _ (hnu' j hj).
have hm1 j : (j < d)%N -> (\int[nu d j]_x ((x : R) ^+ 2)%:E = 1)%E.
  by move=> hj; exact: coordinate_law_second _ _ _ (hnu' j hj).
have hm2 j : (j < d)%N -> ((2^-1)%:E <=
    \int[nu d j]_x (((x : R) ^+ 2 * \1_[set y : RR | `|y| <= M] x)%R)%:E)%E.
  by move=> hj; exact: coordinate_law_truncated _ _ _ k1 (hnu' j hj).
have hk l : (l < L.-1)%N -> (c0 * d%:R <= (k l)%:R) /\
    (c0 * d%:R <= (blk_q L d l)%:R) /\ (k l <= blk_p L d l)%N /\
    (k l <= d)%N.
  by move=> hl; exact: blk_k_hyp L d l ep L1 d2L ep0' ep1' hl.
have [U [mU PU hU]] := hC (n d) d L m k (nu d) K1 d%:R C1 rho gam
  hm0 hm1 hm2 hk rho0 hCrho gam0 C10 (ler0n _ d) d0.
have hsum := blk_sum_ge L d ep L1 dL ep0' ep1'.
have PU' : (universality_sample_law (nu d) (n d) d U <= (eta / 2)%:E)%E.
  apply: le_trans PU _; rewrite lee_fin.
  apply: le_trans
    (hcount d (n d) m d%:R k dc hna hm (ler0n _ d) (lexx _) hsum) _.
  by have := hexp d de; rewrite mul1r.
exists (E0 `|` U); split; first exact: measurableU mE0 mU.
  have e : eta / 2 + eta / 2 = eta by field.
  by rewrite -e; exact: prob_union_le.
move=> x hx I h t hI hh ht hlight hl1.
have xE0 : ~ E0 x by move=> h0; apply: hx; left.
have xU : ~ U x by move=> h0; apply: hx; right.
have [hng hadj] := hE0 x xE0.
have hIm : (#|I| <= m)%N by rewrite /m truncn_ge_nat.
apply: (light_scale (n d) d L m K1 gam x K10 d0 _ I h t hIm hh ht hlight hl1).
have hnorm i : frobenius (sample_point x i) ^+ 2 <= 2 * d%:R.
  have := hng i; rewrite paper_point_sample mxdot_trmx -frobenius_sqr.
  exact: norm_good_sq.
move=> hb; apply: xU; apply: (hU x _ hnorm _ hb).
- (* the blocks of L_X^* lam *)
  move=> l lam _.
  apply: le_trans (nuclear_stage_map_le x lam (@blk_cU_inj L d l)
    (@blk_cJ_inj L d l) (@blk_cUJ L d l)) _.
  rewrite -sample_adj_feature.
  exact: nuclear_sample_adj_le (n d) d x C1 hadj lam.
- (* the good events, by Corollary 3.13 *)
  move=> I' t' _ [_ t'1 t'l] l hl; split.
  + move=> j hj.
    have [k'p k'd k'j] := blk_eff L d l ep L1 d2L ep0 ep1 hl.
    have hK := eff_K K1 C1 ep L%:R d%:R _ ep0 LR0 (ler0n _ d) K1eff k'd.
    have t'1' : mxdot t' t' = 1 by rewrite -frobenius_sqr t'1 expr1n.
    have Kd0 : 0 < K1 * d%:R by rewrite mulr_gt0.
    have t'l' i : K1 * d%:R * t' 0 i ^+ 2 <= 1.
      exact: light_sq (K1 * d%:R) (t' 0 i) Kd0 (t'l i).
    have h8 := block_effective_rank_light (n d) d (blk_p L d l) x
      (blk_cU L d l) C1 K1 t' _ d0 C10' (@blk_cU_inj L d l) hadj
      (ltn0Sn _) k'p t'1' t'l' hK j (k'j j hj).
    have e : stage_cov (blk_cU L d l) x t' =
        \sum_i t' 0 i ^+ 2 *: ((block_row (n d) d (blk_p L d l) x
          (blk_cU L d l) i)^T *m block_row (n d) d (blk_p L d l) x
          (blk_cU L d l) i).
      by rewrite /stage_cov; apply: eq_bigr => i _; rewrite block_row_stage.
    by rewrite e.
  + move=> i.
    apply: (tail_rho K1 d%:R rho `|t' 0 i| _ K10 dR rho0 K1rho
      (frobenius_ge0 _) _ (normr_ge0 _) (t'l i)).
    exact: (sq_le _ _ _ (frobenius_ge0 _) (frobenius_stage_row x i
      (@blk_cU_inj L d l)) (hnorm i)).
Qed.

End light_tail_theorem.
