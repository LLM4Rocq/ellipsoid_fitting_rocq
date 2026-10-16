From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.gaussian Require Import normal_integral gauss_moments.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.comparison Require Import gauss_law gauss_concentration.
From GaussianAnalysis.random_matrix Require Import matrix_series goe_entries.
From GaussianAnalysis.probability Require Import symmetrization.

(**md**************************************************************************)
(* # Expected operator norm of a Rademacher matrix series                     *)
(*                                                                            *)
(* For symmetric A_j of size n >= 1, the expectation over independent signs   *)
(* of ||sum eps_j A_j|| is at most                                            *)
(*       40 sqrt(log(2 n)) sqrt(||sum A_j^2||).                              *)
(* The proof uses the Gaussian trace moments from matrix_series.v, Jensen's  *)
(* inequality for the operator norm, and Gaussian sign invariance. The       *)
(* elementary lower bound E|g| >= 1/8 suffices for the comparison constant.  *)
(* This is the classical Gaussian comparison argument requested in B1 of    *)
(* the shifted-Gaussian formalization plan; no differentiability of the norm *)
(* or bounded Lindeberg comparison is used.                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section variance_log_bound.
Context {R : realType}.

Lemma ln_double_ge_half (d : R) : 1 <= d -> 2^-1 <= ln (2 * d).
Proof.
move=> d1; have x0 : 0 < 2 * d by lra.
have := expR_ge1Dx (- ln (2 * d)); rewrite expRN lnK ?posrE //.
have : (2 * d)^-1 <= 2^-1 by rewrite lef_pV2 ?posrE //; lra.
lra.
Qed.

Lemma series_variance_log_bound (d s : R) : 1 <= d -> 0 <= s ->
  (\prod_(i < (truncn (ln (2 * d))).+1) i.*2.+1%:R) *
    s ^+ truncn (ln (2 * d)) * (2 * d * s) <=
  (5 * Num.sqrt (ln (2 * d)) * Num.sqrt s) ^+
    (truncn (ln (2 * d))).+1.*2.
Proof.
move=> d1 s0.
have d0 : 0 < d := lt_le_trans ltr01 d1.
set L := ln (2 * d); set k := truncn L; set q := k.+1.
have L12 : 2^-1 <= L := ln_double_ge_half d1.
have L0 : 0 <= L by lra.
have qL : L < q%:R := truncnS_gt L.
have Lq : q%:R <= L + 1 by rewrite /q -natr1 lerD2r truncn_le.
have P_le : \prod_(i < q) i.*2.+1%:R <= q.*2%:R ^+ q :> R.
  have -> : q.*2%:R ^+ q = \prod_(i < q) (q.*2%:R : R).
    by rewrite prodr_const card_ord.
  by apply: ler_prod => i _; rewrite ler0n ler_nat /= ltn_double.
have d4 : 2 * d <= 4 ^+ q.
  have h2 : 2 * d = expR L by rewrite lnK // posrE mulr_gt0.
  have h3 : expR L <= expR 1 ^+ q by rewrite -expRM_natl mulr1 ler_expR ltW.
  have h4 : expR 1 ^+ q <= 4 ^+ q :> R.
    by rewrite lerXn2r ?nnegrE ?expR_ge0 ?expR1_le4.
  rewrite h2; exact: le_trans h3 h4.
have q8 : q.*2%:R * 4 <= 25 * L.
  have -> : q.*2%:R = 2 * q%:R :> R by rewrite -muln2 natrM mulrC.
  by move: Lq L12; clear; lra.
have -> : (5 * Num.sqrt L * Num.sqrt s) ^+ q.*2 = (25 * L * s) ^+ q.
  rewrite -mul2n exprM; congr (_ ^+ _).
  by rewrite !exprMn !sqr_sqrtr // expr2 -natrM.
have -> : (\prod_(i < q) i.*2.+1%:R) * s ^+ k * (2 * d * s) =
    (\prod_(i < q) i.*2.+1%:R) * s ^+ q * (2 * d).
  rewrite /q exprSr.
  by move: (\prod_(i < k.+1) i.*2.+1%:R) (s ^+ k) => a b; ring.
apply: le_trans (_ : q.*2%:R ^+ q * s ^+ q * 4 ^+ q <= _).
  apply: ler_pM.
  - by rewrite mulr_ge0 ?prodr_ge0 ?exprn_ge0.
  - by rewrite mulr_ge0 //; exact: le_trans ler01 d1.
  - by rewrite ler_wpM2r ?exprn_ge0.
  - exact: d4.
rewrite -!exprMn lerXn2r ?nnegrE ?mulr_ge0 ?ler0n //.
by rewrite mulrAC ler_wpM2r.
Qed.

End variance_log_bound.

Section gaussian_variance.
Context {R : realType} {n r : nat}.
Variable A : 'I_r -> 'M[R]_n.
Hypothesis Asym : forall j, A j \is symmetricmx.

Let S := \sum_j A j ^+ 2.

Lemma series_variance_trace_ge0 : 0 <= \tr S.
Proof.
rewrite /S raddf_sum /=; apply: sumr_ge0 => j _.
have /symmetricmxP AT := Asym j.
by rewrite expr2 -mulmxE -{1}AT mxtrace_mulC -mxdot_trace mxdot_ge0.
Qed.

Lemma mxtrace_le_dim_opnorm (B : 'M[R]_n) : \tr B <= n%:R * opnorm B.
Proof.
have -> : n%:R * opnorm B = \sum_(i < n) opnorm B.
  by rewrite sumr_const card_ord mulr_natl.
rewrite /mxtrace.
apply: ler_sum => i _.
apply: le_trans (ler_norm (B i i)) _.
exact: le_trans (mx_norm_entry_le B i i) (mx_norm_le_opnorm B).
Qed.

Lemma gauss_mx_series_variance : (0 < n)%N ->
  (\int[gauss r]_g (opnorm (\sum_j g 0 j *: A j))%:E <=
    (5 * Num.sqrt (ln (2 * n%:R)) * Num.sqrt (opnorm S))%:E)%E.
Proof.
move=> n0.
have n1 : 1 <= n%:R :> R by rewrite ler1n.
have SE : \sum_j A j *m (A j)^T = S.
  apply: eq_bigr => j _; have /symmetricmxP -> := Asym j.
  by rewrite expr2 mulmxE.
have SE' : \sum_j (A j)^T *m A j = S.
  apply: eq_bigr => j _; have /symmetricmxP -> := Asym j.
  by rewrite expr2 mulmxE.
have s0 : 0 <= opnorm S := opnorm_ge0 S.
have t0 : 0 <= \tr S := series_variance_trace_ge0.
have ts : \tr S <= n%:R * opnorm S := mxtrace_le_dim_opnorm S.
have [s00|sN] := eqVneq (opnorm S) 0.
  have t00 : \tr S = 0 by apply/eqP; rewrite eq_le t0 andbT; move: ts; rewrite s00 mulr0.
  have h := gauss_mx_series_opnorm A (isT : (0 < 1)%N).
  by move: h; rewrite SE SE' maxxx t00 mulr0 mulr0 powR0 //
    s00 sqrtr0 mulr0.
pose q := (truncn (ln (2 * n%:R) : R)).+1.
have h := gauss_mx_series_opnorm_moment A (isT : (0 < q)%N).
rewrite SE SE' maxxx in h.
have Lp : 0 < ln (2 * n%:R) :> R.
  have := ln_double_ge_half n1; lra.
have sp : 0 < opnorm S by rewrite lt_def sN s0.
apply: (moment_root_le (k := q.*2.-1)) => //.
- exact: measurable_series_opnorm.
- by move=> g; exact: opnorm_ge0.
- by rewrite !mulr_gt0 ?sqrtr_gt0.
apply: le_trans h _; rewrite lee_fin /=.
apply: le_trans (_ : (\prod_(i < q) i.*2.+1%:R) *
    opnorm S ^+ q.-1 * (2 * n%:R * opnorm S) <= _).
  apply: ler_wpM2l; first by rewrite mulr_ge0 ?prodr_ge0 ?exprn_ge0.
  by rewrite -mulrA ler_wpM2l.
exact: series_variance_log_bound.
Qed.

End gaussian_variance.

Section normal_absolute_mean.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma integrable_normal_abs :
  N.-integrable setT (EFin \o (fun t : R => `|t|)).
Proof.
have := @integrable_normal_exprn R 1.
by apply: eq_integrable => // t _; rewrite /= expr1.
Qed.

Lemma normal_abs_mean_ge_eighth : 8^-1 <= \int[N]_t `|t|.
Proof.
have i2 : N.-integrable setT (EFin \o (fun t : R => t ^+ 2)).
  apply: (integrable_normal_poly (C := 1) (k := 2)) => [|t].
    exact: measurable_funX.
  by rewrite normrX mul1r lerDr.
have i4 : N.-integrable setT (EFin \o (fun t : R => t ^+ 4)).
  apply: (integrable_normal_poly (C := 1) (k := 4)) => [|t].
    exact: measurable_funX.
  by rewrite normrX mul1r lerDr.
have iF : N.-integrable setT
    (EFin \o (fun t : R => 2 * `|t| + t ^+ 4 / 4)).
  have := integrableD measurableT
    (integrableZl measurableT (2 : R) integrable_normal_abs)
    (integrableZr measurableT (4 : R)^-1 i4).
  by apply: eq_integrable => // t _; rewrite /= EFinD !EFinM.
have m2 : \int[N]_t t ^+ 2 = 1.
  by rewrite /Rintegral (normal_moment_even 1) big_ord1.
have m4 : \int[N]_t t ^+ 4 = 3.
  by rewrite /Rintegral (normal_moment_even 2) !big_ord_recr big_ord0 /= !mul1r.
have pt (t : R) : t ^+ 2 <= 2 * `|t| + t ^+ 4 / 4.
  have t0 := normr_ge0 t.
  have t2 : t ^+ 2 = `|t| ^+ 2 by rewrite -normrX ger0_norm // sqr_ge0.
  have t4 : t ^+ 4 = (`|t| ^+ 2) ^+ 2 by rewrite -exprM -normrX ger0_norm // exprn_even_ge0.
  rewrite t2 t4.
  have [h|h] := leP `|t| 2; first by have := sqr_ge0 (`|t| ^+ 2); nra.
  by have := sqr_ge0 (`|t| - 2); nra.
have h := le_Rintegral measurableT i2 iF (fun t _ => pt t).
have ia : N.-integrable setT (EFin \o (fun t : R => 2 * `|t|)).
  rewrite /comp; under eq_fun do rewrite EFinM.
  exact: (integrableZl measurableT 2 integrable_normal_abs).
have ib : N.-integrable setT (EFin \o (fun t : R => t ^+ 4 / 4)).
  rewrite /comp; under eq_fun do rewrite EFinM.
  exact: (integrableZr measurableT 4^-1 i4).
rewrite (RintegralD measurableT ia ib) in h.
rewrite (RintegralZl 2 measurableT integrable_normal_abs)
  (RintegralZr 4^-1 measurableT i4) m2 m4 in h.
by lra.
Qed.

End normal_absolute_mean.

Section norm_jensen.
Context {R : realType} {e} {T : measurableType e}.
Variable P : probability T R.
Context {m n r : nat}.
Variables (A : 'I_r -> 'M[R]_(m, n)) (f : 'I_r -> T -> R).
Hypothesis fi : forall j, P.-integrable setT (EFin \o f j).
Hypothesis normi : P.-integrable setT
  (EFin \o (fun t => opnorm (\sum_j f j t *: A j))).

Lemma opnorm_Rintegral_series :
  opnorm (\sum_j (\int[P]_t f j t) *: A j) <=
    \int[P]_t opnorm (\sum_j f j t *: A j).
Proof.
have b0 : 0 <= \int[P]_t opnorm (\sum_j f j t *: A j).
  by apply: Rintegral_ge0 => t _; exact: opnorm_ge0.
apply/(opnorm_bilinearP _ b0) => y x.
pose h (t : T) := mxdot y ((\sum_j f j t *: A j) *m x).
have hE t : h t = \sum_j f j t * mxdot y (A j *m x).
  rewrite /h mulmx_suml mxdot_sumr; apply: eq_bigr => j _.
  by rewrite -scalemxAl mxdotZr.
have ihj j : P.-integrable setT
    (EFin \o (fun t => f j t * mxdot y (A j *m x))).
  rewrite /comp; under eq_fun do rewrite EFinM.
  exact: (integrableZr measurableT _ (fi j)).
have ih : P.-integrable setT (EFin \o h).
  rewrite /comp; under eq_fun do rewrite hE -sumEFin.
  by apply: integrable_sum => // j _; exact: ihj.
have Eh : \int[P]_t h t =
    mxdot y ((\sum_j (\int[P]_t f j t) *: A j) *m x).
  under eq_Rintegral do rewrite hE.
  rewrite Rintegral_sum // mulmx_suml mxdot_sumr.
  by apply: eq_bigr => j _;
    rewrite (RintegralZr _ measurableT (fi j)) -scalemxAl mxdotZr.
rewrite -Eh; apply: le_trans (le_normr_Rintegral measurableT ih) _.
have ib : P.-integrable setT
    (EFin \o (fun t => opnorm (\sum_j f j t *: A j) *
      frobenius y * frobenius x)).
  rewrite /comp; under eq_fun do rewrite !EFinM.
  by apply: integrableZr => //; exact: integrableZr.
have hb := le_Rintegral measurableT (integrable_norm ih) ib
  (fun t _ => mxdot_opnorm (\sum_j f j t *: A j) y x).
apply: le_trans hb _.
rewrite !RintegralZr //; last first.
  rewrite /comp; under eq_fun do rewrite EFinM.
  exact: integrableZr.
Qed.

End norm_jensen.

Section gaussian_sign_comparison.
Context {R : realType} {m n r : nat}.
Local Notation N := (@normal_prob R 0 1).
Variable A : 'I_r -> 'M[R]_(m, n).

Let abs_row (g : 'rV[R]_r) : 'rV[R]_r := \row_j `|g 0 j|.

Let measurable_abs_row : measurable_fun setT abs_row.
Proof.
apply/measurable_fun_mxP => i j.
under eq_fun do rewrite /abs_row mxE.
by apply: measurableT_comp => //; exact: measurable_mxentry.
Qed.

Lemma integrable_gauss_series_opnorm :
  (gauss r).-integrable setT
    (EFin \o (fun g => opnorm (\sum_j g 0 j *: A j))).
Proof. exact: integrable_gauss_lipschitz (series_opnorm_lipschitz A). Qed.

Let abs_coord_int j : (gauss r).-integrable setT
    (EFin \o (fun g : 'rV[R]_r => `|g 0 j|)).
Proof.
apply/(integrable_gauss_coord j (f := fun t : R => (`|t|)%:E)).
  by apply/measurable_EFinP; exact: normr_measurable.
exact: integrable_normal_abs.
Qed.

Let measurable_abs_series : measurable_fun setT
    (fun g : 'rV[R]_r => opnorm (\sum_j `|g 0 j| *: A j)).
Proof.
have := measurableT_comp (measurable_series_opnorm A) measurable_abs_row.
by apply: eq_measurable_fun => // g _; congr opnorm; apply: eq_bigr => j _;
  rewrite /abs_row mxE.
Qed.

Lemma integrable_gauss_abs_series_opnorm :
  (gauss r).-integrable setT
    (EFin \o (fun g => opnorm (\sum_j `|g 0 j| *: A j))).
Proof.
have hi : (gauss r).-integrable setT
    (fun g : 'rV[R]_r => (\sum_j `|g 0 j| * opnorm (A j))%:E).
  under eq_fun do rewrite -sumEFin.
  apply: integrable_sum => // j _.
  under eq_fun do rewrite EFinM.
  exact: (integrableZr measurableT _ (abs_coord_int j)).
apply: le_integrable hi => //.
  exact/measurable_EFinP.
move=> g _.
have h0 : 0 <= \sum_j `|g 0 j| * opnorm (A j).
  by apply: sumr_ge0 => j _; rewrite mulr_ge0 ?normr_ge0 ?opnorm_ge0.
rewrite /comp !abse_EFin lee_fin (ger0_norm (opnorm_ge0 _)) (ger0_norm h0).
elim/big_rec2: _ => [|j M s _ h]; first by rewrite opnorm0.
apply: le_trans (opnormD _ _) _; rewrite opnormZ normr_id.
by apply: lerD.
Qed.

Lemma opnorm_abs_gauss_jensen :
  (\int[N]_t `|t|) * opnorm (\sum_j A j) <=
    \int[gauss r]_g opnorm (\sum_j `|g 0 j| *: A j).
Proof.
have h := opnorm_Rintegral_series (P := gauss r) (A := A) abs_coord_int
  integrable_gauss_abs_series_opnorm.
have e j : \int[gauss r]_g `|g 0 j| = \int[N]_t `|t|.
  rewrite /Rintegral; congr fine.
  exact: (integral_gauss_coord j integrable_normal_abs).
have Em : \sum_j (\int[gauss r]_g `|g 0 j|) *: A j =
    (\int[N]_t `|t|) *: \sum_j A j.
  rewrite scaler_sumr; apply: eq_bigr => j _; by rewrite e.
have u0 : 0 <= \int[N]_t `|t|.
  by apply: Rintegral_ge0 => t _; exact: normr_ge0.
by rewrite Em opnormZ (ger0_norm u0) in h.
Qed.

Let sign_diag (s : r.-tuple bool) : 'M[R]_r :=
  diag_mx (\row_j rademacher (tnth s j)).

Let sign_diag_orthogonal s : (sign_diag s)^T *m sign_diag s = 1%:M.
Proof.
rewrite /sign_diag tr_diag_mx mulmx_diag.
apply/matrixP => i j; rewrite !mxE.
by case: (i == j); rewrite //= -expr2 rademacher_sqr.
Qed.

Lemma integral_gauss_series_sign (s : r.-tuple bool) :
  \int[gauss r]_g opnorm
    (\sum_j (rademacher (tnth s j) * g 0 j) *: A j) =
  \int[gauss r]_g opnorm (\sum_j g 0 j *: A j).
Proof.
rewrite /Rintegral; apply: (congr1 (fun z : \bar R => fine z)).
have h := integral_gauss_orthogonal (sign_diag_orthogonal s)
  integrable_gauss_series_opnorm.
rewrite -h; apply: eq_integral => g _; congr (opnorm _)%:E.
apply: eq_bigr => j _.
by rewrite /sign_diag mul_mx_diag !mxE mulrC.
Qed.

Let sign_twist (g : 'rV[R]_r) (s : r.-tuple bool) : r.-tuple bool :=
  [tuple if 0 <= g 0 j then tnth s j else ~~ tnth s j | j < r].

Let sign_twistK g : involutive (sign_twist g).
Proof.
move=> s; apply: eq_from_tnth => j; rewrite /sign_twist !tnth_mktuple.
by case: (0 <= g 0 j); rewrite // negbK.
Qed.

Lemma rademacher_abs_series (g : 'rV[R]_r) :
  rademacher_mean (fun s : r.-tuple bool =>
    opnorm (\sum_j (rademacher (tnth s j) * `|g 0 j|) *: A j)) =
  rademacher_mean (fun s : r.-tuple bool =>
    opnorm (\sum_j (rademacher (tnth s j) * g 0 j) *: A j)).
Proof.
rewrite /rademacher_mean; congr (_ * _).
rewrite [RHS](reindex_inj (can_inj (sign_twistK g))).
apply: eq_bigr => s _; congr opnorm; apply: eq_bigr => j _.
rewrite /sign_twist tnth_mktuple.
have [h|h] := leP 0 (g 0 j); first by rewrite ger0_norm.
by rewrite rademacherN ltr0_norm // mulNr mulrN.
Qed.

End gaussian_sign_comparison.

Section real_sign_average.
Context {R : realType} {e} {T : measurableType e}.
Variable P : probability T R.

Lemma Rintegral_rademacher_mean r (F : r.-tuple bool -> T -> R) :
  (forall s, P.-integrable setT (EFin \o F s)) ->
  \int[P]_t rademacher_mean (fun s => F s t) =
    rademacher_mean (fun s => \int[P]_t F s t).
Proof.
move=> iF.
have iS : P.-integrable setT
    (EFin \o (fun t => \sum_(s : r.-tuple bool) F s t)).
  rewrite /comp; under eq_fun do rewrite -sumEFin.
  by apply: integrable_sum => // s _; exact: iF.
by rewrite /rademacher_mean (RintegralZl _ measurableT iS) Rintegral_sum.
Qed.

End real_sign_average.

Section comparison_conclusion.
Context {R : realType} {m n r : nat}.
Variable A : 'I_r -> 'M[R]_(m, n).

Lemma rademacher_mx_series_gauss :
  rademacher_mean (fun s : r.-tuple bool =>
    opnorm (\sum_j rademacher (tnth s j) *: A j)) <=
  8 * \int[gauss r]_g opnorm (\sum_j g 0 j *: A j).
Proof.
pose B (s : r.-tuple bool) j := rademacher (tnth s j) *: A j.
pose F s (g : 'rV[R]_r) := opnorm (\sum_j `|g 0 j| *: B s j).
pose G s (g : 'rV[R]_r) := opnorm (\sum_j g 0 j *: B s j).
have iF s : (gauss r).-integrable setT (EFin \o F s) :=
  integrable_gauss_abs_series_opnorm (B s).
have iG s : (gauss r).-integrable setT (EFin \o G s) :=
  integrable_gauss_series_opnorm (B s).
have FG g : rademacher_mean (fun s => F s g) =
    rademacher_mean (fun s => G s g).
  have F1 s : F s g = opnorm
      (\sum_j (rademacher (tnth s j) * `|g 0 j|) *: A j).
    congr opnorm; apply: eq_bigr => j _; rewrite /B scalerA mulrC.
    by [].
  have G1 s : G s g = opnorm
      (\sum_j (rademacher (tnth s j) * g 0 j) *: A j).
    congr opnorm; apply: eq_bigr => j _; rewrite /B scalerA mulrC.
    by [].
  have eF : (fun s => F s g) = (fun s => opnorm
      (\sum_j (rademacher (tnth s j) * `|g 0 j|) *: A j)).
    by apply/funext => s; exact: F1.
  have eG : (fun s => G s g) = (fun s => opnorm
      (\sum_j (rademacher (tnth s j) * g 0 j) *: A j)).
    by apply/funext => s; exact: G1.
  rewrite eF eG.
  exact: rademacher_abs_series.
have EG s : \int[gauss r]_g G s g =
    \int[gauss r]_g opnorm (\sum_j g 0 j *: A j).
  transitivity (\int[gauss r]_g opnorm
    (\sum_j (rademacher (tnth s j) * g 0 j) *: A j)).
    apply: eq_Rintegral => g _; congr opnorm; apply: eq_bigr => j _.
    by rewrite /B scalerA mulrC.
  exact: integral_gauss_series_sign.
have h : (\int[normal_prob 0 1]_t `|t|) *
    rademacher_mean (fun s => opnorm (\sum_j B s j)) <=
    \int[gauss r]_g opnorm (\sum_j g 0 j *: A j).
  rewrite -rademacher_meanZ.
  apply: le_trans (_ : rademacher_mean (fun s => \int[gauss r]_g F s g) <= _).
    apply: ler_rademacher_mean => s; exact: opnorm_abs_gauss_jensen.
  rewrite -(Rintegral_rademacher_mean iF).
  under eq_Rintegral do rewrite FG.
  rewrite Rintegral_rademacher_mean //.
  have -> : (fun s => \int[gauss r]_g G s g) =
      (fun _ : r.-tuple bool =>
        \int[gauss r]_g opnorm (\sum_j g 0 j *: A j)).
    by apply/funext => s; exact: EG.
  by rewrite rademacher_mean_cst.
have a0 : 0 <= rademacher_mean (fun s => opnorm (\sum_j B s j)).
  by apply: rademacher_mean_ge0 => s; exact: opnorm_ge0.
have u0 := @normal_abs_mean_ge_eighth R.
have hu := ler_wpM2r a0 u0.
by rewrite /B in h a0 hu; nra.
Qed.

End comparison_conclusion.

Section rademacher_variance.
Context {R : realType} {n r : nat}.
Variable A : 'I_r -> 'M[R]_n.

Theorem rademacher_mx_series_variance : (0 < n)%N ->
  (forall j, A j \is symmetricmx) ->
  rademacher_mean (fun s : r.-tuple bool =>
    opnorm (\sum_j rademacher (tnth s j) *: A j)) <=
  40 * Num.sqrt (ln (2 * n%:R)) *
    Num.sqrt (opnorm (\sum_j A j ^+ 2)).
Proof.
move=> n0 Asym.
have hg := gauss_mx_series_variance Asym n0.
have hi := integrable_gauss_series_opnorm A.
have he : (\int[gauss r]_g (opnorm (\sum_j g 0 j *: A j))%:E)%E =
    (\int[gauss r]_g opnorm (\sum_j g 0 j *: A j))%:E.
  by rewrite /Rintegral fineK //; exact: integrable_fin_num.
rewrite he lee_fin in hg.
apply: le_trans (rademacher_mx_series_gauss A) _.
have eight0 : 0 <= 8 :> R by [].
have h := ler_wpM2l eight0 hg.
have -> : 40 * Num.sqrt (ln (2 * n%:R)) *
    Num.sqrt (opnorm (\sum_j A j ^+ 2)) =
    8 * (5 * Num.sqrt (ln (2 * n%:R)) *
      Num.sqrt (opnorm (\sum_j A j ^+ 2))) by ring.
exact: h.
Qed.

End rademacher_variance.

Section diagonal_example.
Context {R : realType} {n r : nat}.

(* A family of signed diagonal matrices; sigma bounds every diagonal
   coordinate's Euclidean coefficient norm. *)
Example rademacher_diagonal_series (v : 'I_r -> 'rV[R]_n) (sigma : R) :
  (0 < n)%N -> 0 <= sigma ->
  (forall i, \sum_j v j 0 i ^+ 2 <= sigma ^+ 2) ->
  rademacher_mean (fun s : r.-tuple bool =>
    opnorm (\sum_j rademacher (tnth s j) *: diag_mx (v j))) <=
  40 * Num.sqrt (ln (2 * n%:R)) * sigma.
Proof.
move=> n0 sig0 hv.
have hs j : diag_mx (v j) \is symmetricmx.
  by apply/symmetricmxP; rewrite tr_diag_mx.
apply: le_trans (rademacher_mx_series_variance n0 hs) _.
apply: ler_wpM2l; first by rewrite mulr_ge0 // sqrtr_ge0.
rewrite -[leRHS](ger0_norm sig0) -sqrtr_sqr; apply: ler_wsqrtr.
have SE : \sum_j diag_mx (v j) ^+ 2 =
    diag_mx (\row_i \sum_j v j 0 i ^+ 2).
  under eq_bigr do rewrite expr2 -mulmxE mulmx_diag.
  rewrite -linear_sum /=; congr diag_mx; apply/matrixP => i j.
  by rewrite mxE summxE; apply: eq_bigr => k _; rewrite mxE expr2.
rewrite SE; apply: opnorm_diag_mx_le; first exact: sqr_ge0.
move=> i; rewrite mxE ger0_norm //.
by apply: sumr_ge0 => j _; exact: sqr_ge0.
Qed.

End diagonal_example.
