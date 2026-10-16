(* A lower bound on the condition number of every translated fit.
   The same lower eigenvalue is retained in the quadratic upper bound and
   the linear lower bound, and canceled only after the two are compared.
   The resulting event is uniform in the translation and the fit. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.comparison Require Import gauss_matrix_law.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear real_spectral.
From GaussianAnalysis.matrix Require Import psd_splitting centered_correction.
From GaussianAnalysis.matrix Require Import centered_translation centered_quadratic_correction.
From GaussianAnalysis.matrix Require Import quadratic_series_variance.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.random_matrix Require Import restricted_isometry isotropic_rows.
From GaussianAnalysis.random_matrix Require Import gaussian_rows_bounds.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidFitting.Measurability Require Import Fit Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit.
From EllipsoidUniversality.Condition Require Import Unsat.
From EllipsoidUniversality.Shifted Require Import GaussianRows Translations.
From EllipsoidUniversality.Shifted Require Import ConditionTranslation GaussianExports MixtureAdjoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section lower_scalars.
Context {F : realType}.

Lemma condition_lower_combine (k t C : F) :
  0 <= t -> 1 <= C -> k*t <= C ->
  (Num.min 1 k / 2) * (1+t) <= C.
Proof.
move=> t0 C1 kt.
have b1 : Num.min 1 k <= 1 by rewrite ge_min lexx.
have bk : Num.min 1 k <= k by rewrite ge_min lexx orbT.
have bt : Num.min 1 k * t <= C := le_trans (ler_wpM2r t0 bk) kt.
have hn : Num.min 1 k + Num.min 1 k * t <= 2*C by nra.
have he : (Num.min 1 k / 2) * (1+t) =
    (Num.min 1 k + Num.min 1 k * t) / 2 by field.
rewrite he ler_pdivrMr //.
by rewrite [C*2]mulrC.
Qed.

Lemma condition_lower_ratio_from_squared (a L u v t C : F) :
  0 < a -> 0 < L -> 0 < v -> 0 <= t -> 0 <= C ->
  a*v^+2 <= u -> 2*u*t^+2 <= (L*v)^+2*v*C^+2 ->
  (Num.sqrt (2*a)/L) * (t/Num.sqrt v) <= C.
Proof.
move=> a0 L0 v0 t0 C0 density h.
have vd0 : 0 < v^+2 by rewrite exprn_gt0.
have hd := ler_wpM2r (sqr_ge0 t) density.
have hsmall : 2*a*t^+2 <= L^+2*v*C^+2.
  rewrite -(ler_pM2r vd0).
  move: h hd; rewrite !exprMn; nra.
have sa0 : 0 <= Num.sqrt (2*a) := sqrtr_ge0 _.
have sv0 : 0 < Num.sqrt v by rewrite sqrtr_gt0.
have sa2 : (Num.sqrt (2*a))^+2 = 2*a by rewrite sqr_sqrtr // mulr_ge0 ?ltW.
have sv2 : (Num.sqrt v)^+2 = v by rewrite sqr_sqrtr // ltW.
have hroot : Num.sqrt (2*a)*t <= L*Num.sqrt v*C.
  have hsq : (Num.sqrt (2*a)*t)^+2 <= (L*Num.sqrt v*C)^+2.
    by rewrite !exprMn sa2 sv2; nra.
  have l0 : 0 <= Num.sqrt (2*a)*t := mulr_ge0 sa0 t0.
  have r0 : 0 <= L*Num.sqrt v*C :=
    mulr_ge0 (mulr_ge0 (ltW L0) (ltW sv0)) C0.
  by move: hsq; rewrite ler_sqr ?nnegrE.
have he : (Num.sqrt (2*a)/L)*(t/Num.sqrt v) =
    (Num.sqrt (2*a)*t)/(L*Num.sqrt v) by rewrite mulrACA invfM.
rewrite he ler_pdivrMr ?mulr_gt0 //.
by rewrite [C*_]mulrC.
Qed.

End lower_scalars.

Definition condition_lower_constant (a L : R) : RR :=
  Num.min 1 (Num.sqrt (2*a)/L) / 2.

Lemma condition_lower_constant_pos (a L : R) :
  0 < a -> 0 < L -> 0 < condition_lower_constant a L.
Proof.
move=> a0 L0; rewrite /condition_lower_constant divr_gt0 // lt_min ltr01 /=.
by rewrite divr_gt0 // sqrtr_gt0 mulr_gt0.
Qed.

Lemma condition_lower_loewner_ge1 d (Q : 'M[RR]_d) (lm C : R) :
  (0 < d)%N -> 0 < lm ->
  paper_main_loewner_le (lm *: 1%:M) Q ->
  paper_main_loewner_le Q ((C*lm) *: 1%:M) -> 1 <= C.
Proof.
move=> d0 lm0 hlo hhi.
have [_ lo] := (uni_loewner_geP d lm Q).1 hlo.
have [_ hi] := (uni_loewner_leP d (C*lm) Q).1 hhi.
pose e : 'cV[RR]_d := const_mx 1.
have e0 : e != 0 := uni_ones_neq0 d d0.
have h := le_trans (lo e) (hi e).
have pos : 0 < lm * pm_sqnorm d e := mulr_gt0 lm0 (pm_sqnorm_gt0 d e e0).
by move: h; rewrite -mulrA -[X in X <= _]mul1r (ler_pM2r pos).
Qed.

Lemma condition_lower_data_infimum n d (x : paper_main_sample n d) (b : R) :
  (forall C, universality_conditioned_fit_event n d C x -> b <= C) ->
  (b%:E <= data_condition_number n d x)%E.
Proof.
move=> lower; rewrite /data_condition_number; apply: le_ereal_inf_tmp.
move=> _ [C hC <-]; rewrite lee_fin.
exact: lower C hC.
Qed.

Section condition_lower.
Context {R : realType}.

Lemma condition_lower_covariance_energy n d (H : 'M[R]_(n,d)) (v : 'cV[R]_d) :
  (0 < n)%N ->
  frobenius (centering_mx n *m (H *m v)) ^+ 2 =
    mxdot v (centered_covariance H *m v).
Proof.
move=> n0.
rewrite frobenius_sqr mxdot_mulmxl
  (symmetricmxP _ (@centering_symmetric R n)).
rewrite (mulmxA (centering_mx n) (centering_mx n) (H *m v))
  centering_idempotent //.
by rewrite mxdot_mulmxl /centered_covariance !mulmxA.
Qed.

Lemma condition_lower_covariance_lower n d (H : 'M[R]_(n,d)) (v : 'cV[R]_d) :
  (0 < n)%N ->
  opnorm (n%:R^-1 *: centered_covariance H - 1%:M) <= 2^-1 ->
  n%:R * frobenius v ^+ 2 <=
    2 * frobenius (centering_mx n *m (H *m v)) ^+ 2.
Proof.
move=> n0 near.
have nr0 : (0 : R) < n%:R by rewrite ltr0n.
have nrn : (n%:R : R) != 0 := lt0r_neq0 nr0.
pose E := n%:R^-1 *: centered_covariance H - 1%:M.
pose a := frobenius (centering_mx n *m (H *m v)) ^+ 2.
pose b := frobenius v ^+ 2.
have e : mxdot v (E *m v) = n%:R^-1 * a - b.
  rewrite /E mulmxBl -scalemxAl mul1mx mxdotBr mxdotZr.
  by rewrite -condition_lower_covariance_energy // -frobenius_sqr.
have hb : `|n%:R^-1 * a - b| <= 2^-1 * b.
  rewrite -e; apply: le_trans (mxdot_opnorm E v v) _.
  rewrite -mulrA -expr2 /b; apply: ler_wpM2r; first exact: sqr_ge0.
  exact: near.
have hn := ler_norm (- (n%:R^-1 * a - b)).
rewrite normrN in hn.
have hhalf : 2^-1 * b <= n%:R^-1 * a by nra.
have hmul := ler_wpM2l (ltW nr0) hhalf.
rewrite (mulrA n%:R n%:R^-1 a) mulfV // mul1r in hmul.
by rewrite /a /b in hmul; nra.
Qed.

Lemma condition_lower_mulmx_lower d (Q : 'M[R]_d) (lm : R) :
  0 <= lm ->
  (forall v : 'cV[R]_d, lm * mxdot v v <= mxdot v (Q *m v)) ->
  forall v : 'cV[R]_d, lm * frobenius v <= frobenius (Q *m v).
Proof.
move=> lm0 lo v.
have h := le_trans (lo v) (ler_mxdot v (Q *m v)).
rewrite -frobenius_sqr in h.
have [->|vn] := eqVneq (frobenius v) 0.
  by rewrite mulr0 frobenius_ge0.
have vp : 0 < frobenius v by rewrite lt_def vn frobenius_ge0.
by move: h; rewrite expr2 mulrCA ler_pM2l.
Qed.

Lemma condition_lower_frobenius_upper d (Q : 'M[R]_d) (lm C : R) :
  0 <= lm -> 0 <= C -> Q \is symmetricmx ->
  (forall v : 'cV[R]_d,
    lm * mxdot v v <= mxdot v (Q *m v) <= C * lm * mxdot v v) ->
  frobenius Q <= Num.sqrt d%:R * (C * lm).
Proof.
move=> lm0 C0 Qs bounds.
have CL0 : 0 <= C * lm := mulr_ge0 C0 lm0.
have Qbound : opnorm Q <= C * lm.
  apply/(opnorm_symP Qs CL0) => v.
  have /andP[lo hi] := bounds v.
  have pos : 0 <= mxdot v (Q *m v).
    exact: le_trans (mulr_ge0 lm0 (mxdot_ge0 v)) lo.
  by rewrite ger0_norm.
apply: le_trans (frobenius_le_opnorm Q) _.
by rewrite ler_wpM2l ?sqrtr_ge0.
Qed.

Lemma condition_lower_outer_pairing d (Q : 'M[R]_d) (v : 'cV[R]_d) :
  mxdot (v *m v^T) Q = mxdot v (Q *m v).
Proof. by rewrite [LHS]mxdotC mxdot_outer mxdot_colE mulmxA. Qed.

Lemma condition_lower_quadratic_coef n d (H : 'M[R]_(n,d)) (Q : 'M[R]_d) :
  (0 < n)%N ->
  centered_quadratic_values H Q =
    centering_mx n *m (coef_map (reserve_feature H) Q)^T.
Proof.
move=> n0.
have e : quadratic_values H Q = (coef_map (reserve_feature H) Q)^T +
    mxdot (1%:M : 'M[R]_d) Q *: centering_ones n.
  apply/matrixP => i j; rewrite !ord1 /quadratic_values /coef_map !mxE
    /reserve_feature mxdotBl mulr1.
  have hpair := condition_lower_outer_pairing Q (row i H)^T.
  rewrite trmxK in hpair.
  by rewrite hpair subrK.
by rewrite /centered_quadratic_values e mulmxDr -scalemxAr
  centering_ones_zero // scaler0 addr0.
Qed.

Lemma condition_lower_quadratic_bound n d (H : 'M[R]_(n,d)) (Q : 'M[R]_d) L :
  (0 < n)%N -> 0 <= L ->
  (forall z, frobenius (coef_adj (reserve_feature H) z) <= L * frobenius z) ->
  frobenius (centered_quadratic_values H Q) <= L * frobenius Q.
Proof.
move=> n0 L0 adj; rewrite condition_lower_quadratic_coef //.
apply: le_trans (centering_contract _ n0) _.
rewrite frobenius_trmx.
exact: coef_map_bound L0 adj Q.
Qed.

Theorem condition_lower_matrix_squared n d (H : 'M[R]_(n,d))
    (Q : 'M[R]_d) (m : 'cV[R]_d) (L C lm q : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= L -> 0 <= C -> 0 < lm ->
  Q \is symmetricmx ->
  (forall v : 'cV[R]_d,
    lm * mxdot v v <= mxdot v (Q *m v) <= C * lm * mxdot v v) ->
  opnorm (n%:R^-1 *: centered_covariance H - 1%:M) <= 2^-1 ->
  (forall z, frobenius (coef_adj (reserve_feature H) z) <= L * frobenius z) ->
  (forall i : 'I_n,
    mxdot (row i (matrix_translate H m))^T
      (Q *m (row i (matrix_translate H m))^T) = q) ->
  2 * n%:R * frobenius m ^+ 2 <= L ^+ 2 * d%:R * C ^+ 2.
Proof.
move=> n0 d0 L0 C0 lm0 Qs bounds near adj fit.
have lmge : 0 <= lm := ltW lm0.
have nR0 : (0 : R) <= n%:R by rewrite ler0n.
have qfit : quadratic_values (matrix_translate H m) Q = q *: centering_ones n.
  by apply/matrixP => i j; rewrite !ord1 /quadratic_values mxE fit
    /centering_ones !mxE mulr1.
have cfit : centered_quadratic_values (matrix_translate H m) Q = 0.
  by rewrite /centered_quadratic_values qfit -scalemxAr centering_ones_zero // scaler0.
have ce := centered_quadratic_translate H m n0 Qs.
rewrite cfit sub0r in ce.
have en := congr1 (@frobenius R n 1) ce.
rewrite frobeniusN frobeniusZ normr_nat -[H *m Q *m m]mulmxA in en.
have cov := condition_lower_covariance_lower (Q *m m) n0 near.
have low : lm * frobenius m <= frobenius (Q *m m).
  apply: (@condition_lower_mulmx_lower d Q lm lmge) => v.
  by case/andP: (bounds v).
have low2 : (lm * frobenius m) ^+ 2 <= frobenius (Q *m m) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0.
have lowN := ler_wpM2l nR0 low2.
have upper := condition_lower_quadratic_bound Q n0 L0 adj.
have Qupper := condition_lower_frobenius_upper lmge C0 Qs bounds.
have upper' : frobenius (centered_quadratic_values H Q) <=
    L * (Num.sqrt d%:R * (C * lm)).
  exact: le_trans upper (ler_wpM2l L0 Qupper).
have upper0 : 0 <= L * (Num.sqrt d%:R * (C * lm)).
  by rewrite !mulr_ge0 ?sqrtr_ge0.
have upper2 : frobenius (centered_quadratic_values H Q) ^+ 2 <=
    (L * (Num.sqrt d%:R * (C * lm))) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0.
rewrite !exprMn (sqr_sqrtr (ler0n R d)) in upper2.
have ensq := congr1 (fun a : R => a ^+ 2) en.
rewrite exprMn in ensq.
have lm2p : 0 < lm ^+ 2 by rewrite exprn_gt0.
have scaled : lm ^+ 2 * (2 * n%:R * frobenius m ^+ 2) <=
    lm ^+ 2 * (L ^+ 2 * d%:R * C ^+ 2).
  nra.
by move: scaled; rewrite ler_pM2l.
Qed.
End condition_lower.

Theorem condition_lower_raw_sample_squared n d (x : paper_main_sample n d)
    (Q : 'M[RR]_d) (m : 'cV[RR]_d) (A C lm q : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= A -> 0 < lm ->
  paper_main_loewner_le (lm *: 1%:M) Q ->
  paper_main_loewner_le Q ((C*lm) *: 1%:M) ->
  opnorm (n%:R^-1 *: centered_covariance (sample_point_matrix x) - 1%:M) <= 2^-1 ->
  (forall z, frobenius (raw_sample_adj x z) <= A*frobenius z) ->
  (forall i : 'I_n, paper_main_quadratic_form Q
    (paper_main_point (sample_translate m x) i) = q) ->
  2*n%:R*frobenius m^+2 <= A^+2*d%:R*C^+2.
Proof.
move=> n0 d0 A0 lm0 hlo hhi near adj fit.
have C1 := condition_lower_loewner_ge1 d0 lm0 hlo hhi.
have C0 : 0 <= C := le_trans ler01 C1.
have [Qs lo] := (uni_loewner_geP d lm Q).1 hlo.
have [_ hi] := (uni_loewner_leP d (C*lm) Q).1 hhi.
have symQ : Q \is symmetricmx.
  by apply/symmetricmxP/matrixP => i j; rewrite mxE Qs.
apply: (@condition_lower_matrix_squared RR n d (sample_point_matrix x)
  Q m A C lm q n0 d0 A0 C0 lm0 symQ) => //.
- move=> v; apply/andP; split.
  - by move: (lo v); rewrite pm_qf_col pm_sqnorm_col.
  - by move: (hi v); rewrite pm_qf_col pm_sqnorm_col.
- move=> i; rewrite matrix_translate_row /sample_point_matrix
    sample_row_matrix_row trmxK -sample_translate_point -pm_qf_col.
  exact: fit.
Qed.

Theorem condition_lower_sample_squared n d (x : paper_main_sample n d)
    (Q : 'M[RR]_d) (m : 'cV[RR]_d) (L C lm q : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= L -> 0 < lm ->
  paper_main_loewner_le (lm *: 1%:M) Q ->
  paper_main_loewner_le Q ((C*lm) *: 1%:M) ->
  opnorm (n%:R^-1 *: centered_covariance (sample_point_matrix x) - 1%:M) <= 2^-1 ->
  (forall z, frobenius (sample_adj x z) <= L*Num.sqrt d%:R*frobenius z) ->
  (forall i : 'I_n, paper_main_quadratic_form Q
    (paper_main_point (sample_translate m x) i) = q) ->
  2*n%:R*frobenius m^+2 <= (L*d%:R)^+2*d%:R*C^+2.
Proof.
move=> n0 d0 L0 lm0 hlo hhi near adj fit.
apply: (condition_lower_raw_sample_squared n0 d0 _ lm0 hlo hhi near _ fit).
- by apply: mulr_ge0; rewrite // ler0n.
- exact: raw_sample_adjoint_le d0 adj.
Qed.

Theorem condition_lower_fit_bound n d (x : paper_main_sample n d)
    (m : 'cV[RR]_d) (a L C : R) :
  (0 < n)%N -> (0 < d)%N -> 0 < a -> 0 < L -> a*d%:R^+2 <= n%:R ->
  opnorm (n%:R^-1 *: centered_covariance (sample_point_matrix x) - 1%:M) <= 2^-1 ->
  (forall z, frobenius (raw_sample_adj x z) <= L*d%:R*frobenius z) ->
  universality_conditioned_fit_event n d C (sample_translate m x) ->
  condition_lower_constant a L * (1+frobenius m/Num.sqrt d%:R) <= C.
Proof.
move=> n0 d0 a0 L0 density near adj [Q [lm [lm0 [hlo [hhi fit]]]]].
have C1 := condition_lower_loewner_ge1 d0 lm0 hlo hhi.
have C0 : 0 <= C := le_trans ler01 C1.
have dR0 : (0 : RR) < d%:R by rewrite ltr0n.
have A0 : 0 <= L*d%:R := mulr_ge0 (ltW L0) (ltW dR0).
have h := condition_lower_raw_sample_squared n0 d0 A0 lm0 hlo hhi near adj fit.
apply: condition_lower_combine _ C1 _.
- by rewrite divr_ge0 ?frobenius_ge0 ?sqrtr_ge0.
- exact: condition_lower_ratio_from_squared a0 L0 dR0
    (frobenius_ge0 m) C0 density h.
Qed.

Theorem condition_lower_data_bound n d (x : paper_main_sample n d)
    (a L : R) :
  (0 < n)%N -> (0 < d)%N -> 0 < a -> 0 < L -> a*d%:R^+2 <= n%:R ->
  opnorm (n%:R^-1 *: centered_covariance (sample_point_matrix x) - 1%:M) <= 2^-1 ->
  (forall z, frobenius (raw_sample_adj x z) <= L*d%:R*frobenius z) ->
  forall m : 'cV[RR]_d,
    ((condition_lower_constant a L * (1+frobenius m/Num.sqrt d%:R))%:E <=
      data_condition_number n d (sample_translate m x))%E.
Proof.
move=> n0 d0 a0 L0 density near adj m.
apply: condition_lower_data_infimum => C fit.
exact: condition_lower_fit_bound n0 d0 a0 L0 density near adj fit.
Qed.

Lemma gaussian_covariance_scalar_bound (a q u v : RR) :
  0 < a -> 0 < q -> 0 < u -> 1 <= v -> a*v^+2 <= u ->
  1 <= a*q*v -> 2 <= a*q^+2*v ->
  2*(1152*(Num.sqrt (u*(v+1))+(v+1))+v)/u <= 6914*q.
Proof.
move=> a0 q0 u0 v1 au h1 h2.
have v0 : 0 <= v by lra.
have hqu := ler_wpM2l (ltW q0) au.
have hq2u := ler_wpM2l (sqr_ge0 q) au.
have hv1 := ler_wpM2r v0 h1.
have hv2 := ler_wpM2r v0 h2.
have vq : v <= q*u by clear - hqu hv1; nra.
have vpq : v+1 <= q^+2*u by clear - hq2u hv2 v1; nra.
have hs0 := sqrtr_ge0 (u*(v+1)).
have hs2 : (Num.sqrt (u*(v+1)))^+2 = u*(v+1).
  by rewrite sqr_sqrtr // mulr_ge0 //; lra.
have hsq := ler_wpM2l (ltW u0) vpq.
have qu0 : 0 < q*u by rewrite mulr_gt0.
have hs : Num.sqrt (u*(v+1)) <= q*u.
  clear - hs2 hsq hs0 qu0; nra.
rewrite ler_pdivrMr //.
clear - hs vq v1; nra.
Qed.

Lemma gaussian_covariance_rate_tends (alpha : RR) (n : nat -> nat) :
  0 < alpha -> universality_density_tends_to n alpha ->
  forall eps : RR, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (0 < n d)%N /\
    2*(@isotropic_covariance_bound RR (n d) d 2+d%:R)/(n d)%:R <= eps.
Proof.
move=> alpha0 hn eps eps0.
pose a := alpha/2.
pose q := eps/6914.
have a0 : 0 < a by rewrite /a divr_gt0.
have q0 : 0 < q.
  apply: divr_gt0 eps0 _; by rewrite ltr0n.
have aq0 : 0 < a*q by rewrite mulr_gt0.
have aq20 : 0 < a*q^+2 by rewrite mulr_gt0 ?exprn_gt0.
have [Dn hDn] := af_ev_density n alpha alpha0 hn.
have [D1 hD1] := af_ev_ge (1/(a*q)).
have [D2 hD2] := af_ev_ge (2/(a*q^+2)).
exists (maxn Dn (maxn D1 D2)) => d.
rewrite !geq_max => /andP[dn /andP[d1 d2]].
have [d0 [nlo _]] := hDn d dn.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < (n d)%:R :> RR.
  apply: lt_le_trans _ nlo.
  exact: mulr_gt0 a0 (exprn_gt0 2 dR).
have n0 : (0 < n d)%N by move: nR; rewrite ltr0n.
split => //.
have h1 : 1 <= a*q*d%:R.
  have h := hD1 d d1.
  by rewrite ler_pdivrMr // mulrC in h.
have h2 : 2 <= a*q^+2*d%:R.
  have h := hD2 d d2.
  by rewrite ler_pdivrMr // mulrC in h.
have hd1 : 1 <= d%:R :> RR by rewrite ler1n.
have hs := gaussian_covariance_scalar_bound a0 q0 nR hd1 nlo h1 h2.
have hdS : d.+1%:R = d%:R+1 :> RR by rewrite -addn1 natrD.
rewrite /isotropic_covariance_bound hdS.
have -> : (288 : RR)*2^+2 = 1152 by ring.
apply: le_trans hs _.
have B0 : 0 < (6914 : RR) by rewrite ltr0n.
have h : (6914 : RR) != 0 := lt0r_neq0 B0.
have he : 6914*q = eps by rewrite /q; field.
by rewrite he.
Qed.

Lemma gaussian_condition_covariance_finite n d : (0 < n)%N ->
  exists G : set (paper_main_sample n d),
    [/\ measurable G,
      (gaussian_product_law (n*d) (~` G) <=
        (2*(@isotropic_covariance_bound RR n d 2+d%:R)/n%:R)%:E)%E &
      forall x, G x ->
        opnorm (n%:R^-1 *: centered_covariance (sample_point_matrix x)-1%:M)
          <= 2^-1].
Proof.
move=> n0.
have sub i (y : 'rV[RR]_d) : (i < n)%N -> frobenius y <= 1 ->
    subgaussian (gauss d) (fun x => mxdot x y) 2.
  by move=> _; exact: gauss_direction_subgaussian.
have iso i (y : 'rV[RR]_d) : (i < n)%N -> frobenius y <= 1 ->
    \int[gauss d]_x mxdot x y^+2 = frobenius y^+2.
  by move=> _ _; exact: gauss_direction_second.
have cen i (y : 'rV[RR]_d) : (i < n)%N -> frobenius y <= 1 ->
    \int[gauss d]_x mxdot x y = 0.
  by move=> _ _; exact: gauss_direction_mean.
have K0 : 0 < (2 : RR) by [].
have [G [mG pG bG]] := isotropic_centered_covariance_event K0 sub iso cen n0.
exists (sample_row_tuple @^-1` G); split.
- rewrite -[X in measurable X]setTI.
  exact: measurable_sample_row_tuple _ mG.
- have mGC : measurable (~` G) := measurableC mG.
  by rewrite preimage_setC (gaussian_sample_row_tuple_law mGC).
- move=> x gx.
  have h := bG (sample_row_tuple x) gx.
  have he : sample_point_matrix x = restricted_isometry.tuple_mx (sample_row_tuple x).
    by apply/matrixP => i j; rewrite /sample_point_matrix
      /gauss_matrix_law.tuple_mx /restricted_isometry.tuple_mx !mxE.
  by rewrite he.
Qed.

Theorem gaussian_condition_covariance_event (alpha : RR) (n : nat -> nat) :
  0 < alpha -> universality_density_tends_to n alpha ->
  forall eps : RR, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists G : set (paper_main_sample (n d) d),
    [/\ measurable G,
      (gaussian_product_law (n d*d) (~` G) <= eps%:E)%E &
      forall x, G x ->
        opnorm ((n d)%:R^-1 *: centered_covariance (sample_point_matrix x)-1%:M)
          <= 2^-1].
Proof.
move=> alpha0 hn eps eps0.
have [D hD] := gaussian_covariance_rate_tends alpha0 hn eps0.
exists D => d dD.
have [n0 rate] := hD d dD.
have [G [mG pG bG]] := @gaussian_condition_covariance_finite (n d) d n0.
exists G; split => //.
apply: le_trans pG _; by rewrite lee_fin.
Qed.

Theorem gaussian_translated_condition_lower (alpha : R) : 0 < alpha ->
  exists c : R, 0 < c /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (gaussian_product_law (n d*d) E <= eps%:E)%E &
      forall x, ~ E x -> forall m : 'cV[RR]_d,
        ((c*(1+frobenius m/Num.sqrt d%:R))%:E <=
          data_condition_number (n d) d (sample_translate m x))%E].
Proof.
move=> alpha0.
pose L : RR := Num.max 1 (adj_const 2%:R 252%:R (alpha+1)).
have L1 : 1 <= L by rewrite /L le_max lexx.
have L0 : 0 < L := lt_le_trans ltr01 L1.
have Ladj : adj_const 2%:R 252%:R (alpha+1) <= L.
  by rewrite /L le_max lexx orbT.
have a0 : 0 < alpha/2 by rewrite divr_gt0.
exists (condition_lower_constant (alpha/2) L); split.
  exact: condition_lower_constant_pos a0 L0.
move=> n hn eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [Da hDa] := gaussian_raw_adjoint_bound alpha0 hn e20.
have [Dc hDc] := gaussian_condition_covariance_event alpha0 hn e20.
have [Dn hDn] := af_ev_density n alpha alpha0 hn.
exists (maxn Da (maxn Dc Dn)) => d.
rewrite !geq_max => /andP[da /andP[dc dn]].
have [d0 [nlo _]] := hDn d dn.
have dR0 : (0 : RR) < d%:R by rewrite ltr0n.
have nR0 : (0 : RR) < (n d)%:R :=
  lt_le_trans (mulr_gt0 a0 (exprn_gt0 2 dR0)) nlo.
have n0 : (0 < n d)%N by move: nR0; rewrite ltr0n.
have [Ea [mEa pEa hEa]] := hDa d da.
have [G [mG pG hG]] := hDc d dc.
exists (Ea `|` ~` G); split.
- exact: measurableU mEa (measurableC mG).
- apply: le_trans (measureU2 _ mEa (measurableC mG)) _.
  apply: le_trans (leeD pEa pG) _.
  rewrite -EFinD lee_fin; have -> : eps/2+eps/2 = eps by field.
  exact: lexx.
- move=> x nx m.
  have nEa : ~ Ea x by move=> hx; apply: nx; left.
  have gx : G x.
    by apply: contrapT => ng; apply: nx; right.
  apply: (condition_lower_data_bound n0 d0 a0 L0 nlo (hG x gx)) => z.
  apply: le_trans (hEa x nEa z) _.
  apply: ler_wpM2r; first exact: frobenius_ge0.
  by apply: ler_wpM2r; [exact: ltW dR0 | exact: Ladj].
Qed.
