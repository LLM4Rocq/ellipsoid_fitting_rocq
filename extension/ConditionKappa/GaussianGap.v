(* The Gaussian gap above the threshold alpha(C, kappa), at Stdlib's R:
   item G1 of phase 11, second half (notes/phase11-plan.md, sections 3.4, 5
   and 6; lane B). The model is Condition/GaussianGap.v, which treats
   kappa = 3.

   Setting, constants and interface I1 as in GaussianWitness. I1 is a
   hypothesis of the lemmas here and of condition_kappa_unsat of Unsat.v,
   which applies the gap; condition_kappa_statement_of_I3 of Theorem.v
   discharges it with kcond_support_cvg of GaussianLimit.v (item M5).

   Output, interface I4 (the gap), for item D2 (Unsat): for 1 < Cp and
   alpha(Cp, kappa) < alpha, some g > 0 such that, for every n with
   n/d^2 -> alpha, every eps > 0 and every large d, outside a measurable
   set E of n d Gaussian features with
   tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps, every S
   of cond_slice Cp and every real b have
     g n <= sum_i (b - <Z_i, mxvec S>)^2:
   the gap is uniform in the intercept b, and the proof keeps the
   centering of Condition/GaussianGap.v, with n - 1 centered rows. This is
   the hypothesis of condition_unsat_gap of Condition/Unsat.v with
   gaussian_feature_law kappa d in place of gaussian_feature_law 3 d.

   Proved.
   1. Centering. kcenter_features_mul: for the k + 1 Gaussian features Z of
      the rows of A = vec_mx a and S symmetric,
      Q^T Z (mxvec S)^T = sqrt (2 / d) Q^T A (mxvec (T S))^T, with
      Q = centering_mx k (center_mx of Condition/GaussianGap);
      kescape_center_ge: the infimum of |Q^T Z x| over the original slice is
      at least sqrt (2 / d) times the infimum of |Q^T A x| over the base of
      T K_C, and Q^T A is a k x d^2 Gaussian matrix.
   2. The mean of the auxiliary value. With
      l = sqrt alpha - sqrt alpha(C, kappa) > 0 (kgap_l, kgap_l_gt0),
      (|g| - sigma_{C,kappa}(vec_mx h)) / d -> l in probability for z = (g, h)
      of law gauss ((n d - 1) + d * d) (kgap_ratio_cvg), so
      E (|g| - sigma_K(h))_+ >= l d / 4 for every large d (kgap_mean).
   3. The gap. kgaussian_gap_n: cone_escape_lower_tail on T K_C and its base
      with r = sqrt (a0 d) (kcond_B_ge), rho = sqrt (max(1, 1 + c) C d)
      (kcond_B_le) and u = l d r / 16 gives inf_(x in base) |Q^T A x| >=
      l d r / 8 outside an event of probability at most
      2 exp (- a0 l^2 d^2 / (512 max(1, 1 + c) C)), once
      d >= 256 max(1, 1 + c) C / (a0 l^2). So
      sum_i (b - <Z_i, mxvec S>)^2 >= (2 / d) (l d r / 8)^2 = a0 l^2 d^2 / 32
      >= g n for every S of the original slice and every b, with
      g = a0 l^2 / (64 alpha) and n <= 2 alpha d^2. gaussian_kappa_gap states
      this as the theorem whose hypothesis is interface I1 and whose
      conclusion is the output above. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From GaussianAnalysis Require Import euclidean measurable_matrix gauss.
From GaussianAnalysis Require Import gauss_law gauss_smoothing escape cgmt.
From GaussianAnalysis Require Import gauss_concentration.
From GaussianAnalysis Require Import cone_escape moreau condition_cone.
From GaussianAnalysis Require Import gauss_matrix_law lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Gaussian Require Import Cones Representation.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidUniversality.Gaussian Require Import Subcritical.
From EllipsoidUniversality.Condition Require Import GaussianWitness GaussianGap.
From EllipsoidUniversality.ConditionKappa Require Import Cone GaussianWitness.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. Centering. *)

(* Q^T Z (mxvec S)^T = sqrt (2 / d) Q^T A (mxvec (T S))^T for the Gaussian
   features Z of the rows of A = vec_mx a and S symmetric. *)
Lemma kcenter_features_mul (kappa : R) (k d : nat)
    (a : 'rV[RR]_(k.+1 * (d * d))) (S : 'M[RR]_d) : S \is symmetricmx ->
  center_mx (gaussian_features kappa k.+1 d a) *m (mxvec S)^T =
  Num.sqrt (2%:R / d%:R) *:
    ((vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d)) *m
     (mxvec (cone_map kappa S))^T).
Proof.
move=> Ss; rewrite /center_mx -mulmxA (kfeatures_mul kappa k.+1 d a S Ss).
by rewrite -scalemxAr centering_linE mxvecK mulmxA.
Qed.

(* The infimum over the original slice of the centered features is at least
   sqrt (2 / d) times the infimum over the base of T K_C of the centered
   Gaussian matrix. *)
Lemma kescape_center_ge (kappa C : R) (k d : nat)
    (a : 'rV[RR]_(k.+1 * (d * d))) : 1 < C -> (0 < d)%N ->
  Num.sqrt (2%:R / d%:R) * escape_inf (tr_set (kcond_slice_vec kappa C d))
    (vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d)) <=
  escape_inf (tr_set (@cond_slice_vec RR d C))
    (center_mx (gaussian_features kappa k.+1 d a)).
Proof.
move=> C1 d0; have B0 := cond_B_neq0 C d C1 d0.
apply: escape_inf_ge => // _ [v Bv <-].
have Ss : vec_mx v \is symmetricmx by case: Bv => [[]].
have Bx : tr_set (kcond_slice_vec kappa C d)
    (mxvec (cone_map kappa (vec_mx v)))^T.
  by exists (mxvec (cone_map kappa (vec_mx v))) => //; exists (vec_mx v).
rewrite -[v]vec_mxK kcenter_features_mul //.
rewrite frobeniusZ ger0_norm ?sqrtr_ge0 //.
by apply: ler_wpM2l; [exact: sqrtr_ge0 | exact: escape_inf_le].
Qed.

(* 2. The mean of the auxiliary value. *)

(* l = sqrt alpha - sqrt alpha(C, kappa). *)
Definition kgap_l (C kappa alpha : R) : R :=
  Num.sqrt alpha - Num.sqrt (condition_kappa_alpha C kappa).

Lemma kgap_half (x l : RR) : - (l / 2%:R) < x - l -> l / 2%:R < x.
Proof. by move=> h; lra. Qed.

Section kgap_mean.
Variables (kappa C alpha : R) (n : nat -> nat).
Hypotheses (a0 : 0 < alpha) (aC : condition_kappa_alpha C kappa < alpha).
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_kappa_alpha C kappa)).

Local Notation P := (fun d => @gauss RR ((n d).-1 + d * d)).

Lemma kgap_l_gt0 : 0 < kgap_l C kappa alpha.
Proof.
rewrite /kgap_l subr_gt0.
have [h|h] := leP (condition_kappa_alpha C kappa) 0.
  by rewrite ler0_sqrtr // sqrtr_gt0.
by rewrite ltr_sqrt.
Qed.

(* (|g| - sigma_{C,kappa}(vec_mx h)) / d -> l in probability. *)
Lemma kgap_ratio_cvg : cvg_prob P
  (fun d z => (frobenius (lsubmx z) -
     kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d)) / d%:R)
  (kgap_l C kappa alpha).
Proof.
have h1 := gnorm_cvg alpha n hn.
have h2 := @cvg_prob_gauss_rsubmx (fun d => d * d) (fun d => (n d).-1) _ _
  hQ2.
apply: cvg_prob_eq (cvg_probB h1 h2); exists 0%N => d _ z /=.
by rewrite mulrBl.
Qed.

Lemma kgap_mean : exists D : nat, forall d, (D <= d)%N ->
  kgap_l C kappa alpha * d%:R / 4%:R <=
  \int[P d]_z Num.max 0 (frobenius (lsubmx z) -
    cone_sup (tr_set (kcond_cone_vec kappa C d)) (rsubmx z)).
Proof.
have l0 : 0 < kgap_l C kappa alpha := kgap_l_gt0.
have l2 : 0 < kgap_l C kappa alpha / 2%:R by rewrite divr_gt0.
have e2 : (0 : RR) < 2^-1 by rewrite invr_gt0 ltr0n.
have [D hD] := kgap_ratio_cvg (kgap_l C kappa alpha / 2%:R) l2 _ e2.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have [A [mA PA EA]] := hD d dD.
have K0 : tr_set (kcond_cone_vec kappa C d) 0 := kcond_K0 kappa C d.
(* the positive part of |g| - sigma_K(h) is 2-Lipschitz, hence integrable *)
have fL (z z' : 'rV[RR]_((n d).-1 + d * d)) :
    `|Num.max 0 (frobenius (lsubmx z) -
        cone_sup (tr_set (kcond_cone_vec kappa C d)) (rsubmx z)) -
      Num.max 0 (frobenius (lsubmx z') -
        cone_sup (tr_set (kcond_cone_vec kappa C d)) (rsubmx z'))| <=
    2%:R * frobenius (z - z').
  apply: le_trans (max0_lipschitz _ _) _.
  have h1 := cone_sup_lipschitz K0 (rsubmx z) (rsubmx z').
  have h2 := ler_frobeniusB (lsubmx z) (lsubmx z').
  have h3 := frobenius_rsubmx_le (z - z').
  have h4 := frobenius_lsubmx_le (z - z').
  rewrite !linearB /= in h3 h4.
  set c1 := cone_sup _ (rsubmx z); set c2 := cone_sup _ (rsubmx z').
  have -> : frobenius (lsubmx z) - c1 - (frobenius (lsubmx z') - c2) =
      (frobenius (lsubmx z) - frobenius (lsubmx z')) - (c1 - c2) by ring.
  apply: le_trans (ler_normB _ _) _.
  apply: le_trans (lerD (le_trans h2 h4) (le_trans h1 h3)) _.
  by rewrite mulr_natl mulr2n.
have fi := integrable_gauss_lipschitz fL.
have dR : (0 : RR) < d%:R by rewrite ltr0n.
have c0 : (0 : RR) <= kgap_l C kappa alpha * d%:R / 2%:R.
  by rewrite divr_ge0 // mulr_ge0 // ltW.
have f0 (z : 'rV[RR]_((n d).-1 + d * d)) : 0 <= Num.max 0
    (frobenius (lsubmx z) -
     cone_sup (tr_set (kcond_cone_vec kappa C d)) (rsubmx z)).
  by rewrite le_max lexx.
(* outside A, (|g| - sigma_K(h)) / d > l / 2 *)
have fA (z : 'rV[RR]_((n d).-1 + d * d)) : (~` A) z ->
    kgap_l C kappa alpha * d%:R / 2%:R <= Num.max 0 (frobenius (lsubmx z) -
      cone_sup (tr_set (kcond_cone_vec kappa C d)) (rsubmx z)).
  move=> nz.
  have hlt : `|(frobenius (lsubmx z) -
      kcond_support kappa C (vec_mx (rsubmx z) : 'M[RR]_d)) / d%:R -
      kgap_l C kappa alpha| < kgap_l C kappa alpha / 2%:R.
    by rewrite ltNge; apply/negP => h; apply: nz; exact: EA.
  rewrite kcond_cone_supE le_max; apply/orP; right.
  move: hlt; rewrite ltr_norml => /andP[h _].
  have hX := kgap_half _ _ h.
  have e : kgap_l C kappa alpha * d%:R / 2%:R =
      kgap_l C kappa alpha / 2%:R * d%:R by rewrite mulrAC.
  by rewrite e -ler_pdivlMr // ltW.
have hf := Rintegral_ge_indic _ _ (gauss ((n d).-1 + d * d)) _ (~` A) _
  (measurableC mA) c0 f0 fA fi.
apply: le_trans hf.
have fA' : gauss ((n d).-1 + d * d) A \is a fin_num := fin_num_measure _ A mA.
have pa : fine (gauss ((n d).-1 + d * d) A) <= 2^-1.
  by rewrite -lee_fin fineK.
rewrite probability_setC // -(fineK fA') -EFinB /=.
have e4 : kgap_l C kappa alpha * d%:R / 4%:R =
    kgap_l C kappa alpha * d%:R / 2%:R * 2^-1 by field.
rewrite e4; apply: ler_wpM2l => //.
rewrite lerBrDl -lerBrDr; apply: le_trans pa _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

End kgap_mean.

(* 3. The gap. *)

Lemma kgap_tail_exp (L D r rho Q a : RR) : r ^+ 2 = a * D ->
  rho ^+ 2 = Q * D -> Q != 0 -> D != 0 -> L != 0 -> a != 0 ->
  (L * D * r) ^+ 2 / (2 * rho ^+ 2) = D / (2 * Q / (a * L ^+ 2)) * D.
Proof. by move=> r2 rho2 Qn Dn Ln an; rewrite !exprMn r2 rho2; field. Qed.

Lemma kgap_sq (s A r D a : RR) : s ^+ 2 = 2%:R / D -> r ^+ 2 = a * D ->
  D != 0 -> (s * (2%:R * A * r)) ^+ 2 = 8%:R * a * A ^+ 2.
Proof. by move=> s2 r2 Dn; rewrite !exprMn s2 r2; field. Qed.

Lemma kgap_const (L a al D : RR) : al != 0 ->
  a * L ^+ 2 / (64%:R * al) * (2 * al * D ^+ 2) =
  8%:R * a * (L / 16%:R * D) ^+ 2.
Proof. by move=> an; field. Qed.

(* Q D <= (L D)^2 (a D) once Q / (L^2 a) <= D and 1 <= D. *)
Lemma kgap_rho_le (Q a L D : RR) : 0 < a -> 0 < L -> 1 <= D -> 0 <= Q ->
  Q / (L ^+ 2 * a) <= D -> Q * D <= (L * D) ^+ 2 * (a * D).
Proof.
move=> a0 L0 D1 Q0 h.
have La : 0 < L ^+ 2 * a by rewrite mulr_gt0 // exprn_gt0.
rewrite ler_pdivrMr // in h.
have D0 : 0 <= D := le_trans ler01 D1.
have -> : (L * D) ^+ 2 * (a * D) = D * (L ^+ 2 * a) * D * D by ring.
have h1 : Q * D <= D * (L ^+ 2 * a) * D by rewrite ler_wpM2r.
apply: le_trans h1 _; rewrite -[X in X <= _]mulr1.
by apply: ler_wpM2l => //; rewrite !mulr_ge0 // ltW.
Qed.

Section kgap.
Variables (kappa C alpha : R) (n : nat -> nat).
Hypotheses (k1 : 1 < kappa) (C1 : 1 < C) (a0 : 0 < alpha).
Hypothesis aC : condition_kappa_alpha C kappa < alpha.
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_kappa_alpha C kappa)).

(* For one sequence n: outside an event of Gaussian probability at most
   eps, sum_i (b - <Z_i, mxvec S>)^2 >= g n for every S of the original
   slice and every b, with g = a0 l^2 / (64 alpha). *)
Lemma kgaussian_gap_n (eps : R) : 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      Num.min 1 (1 + cone_shift kappa) * kgap_l C kappa alpha ^+ 2 /
        (64%:R * alpha) * (n d)%:R <=
      \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2].
Proof.
move=> e0.
pose l : RR := kgap_l C kappa alpha.
have l0 : 0 < l := kgap_l_gt0 kappa C alpha a0 aC.
pose l' : RR := (l / 16%:R)%R.
have l'0 : 0 < l' by rewrite divr_gt0 // ltr0n.
have C0 : 0 < C := lt_trans ltr01 C1.
pose a' : RR := Num.min 1 (1 + cone_shift kappa).
have a'0 : 0 < a'.
  rewrite /a' lt_min ltr01 /= -ltrBlDl sub0r.
  exact: cone_shift_gtN1.
pose M : RR := Num.max 1 (1 + cone_shift kappa).
have M1 : 1 <= M by rewrite /M le_max lexx.
pose Q : RR := (M * C)%R.
have Q0 : 0 < Q by rewrite /Q mulr_gt0 // (lt_le_trans ltr01 M1).
pose c : RR := (2 * Q / (a' * l' ^+ 2))%R.
have c0 : 0 < c.
  apply: divr_gt0; first by rewrite mulr_gt0.
  by rewrite mulr_gt0 // exprn_gt0.
have [D1 hD1] := kgap_mean kappa C alpha n a0 aC hn hQ2.
have [D2 hD2] := sample_density_cvg alpha n hn alpha a0.
have [D3 hD3] := hn alpha a0.
have [D4 hD4] := expR_lin_small c eps c0 e0.
pose D5 := (archimedean.Num.truncn (Q / (l' ^+ 2 * a'))).+1.
exists (maxn (maxn (maxn D1 D2) (maxn D3 D4)) (maxn D5 1)) => d.
rewrite !geq_max => /andP[/andP[/andP[dD1 dD2] /andP[dD3 dD4]] /andP[dD5 d1]].
have dR : (0 : RR) < d%:R by rewrite ltr0n.
have dn : (d%:R : RR) != 0 := lt0r_neq0 dR.
have d2R : (0 : RR) < d%:R ^+ 2 := exprn_gt0 2 dR.
have d2n : (d%:R ^+ 2 : RR) != 0 := lt0r_neq0 d2R.
have hm := hD1 d dD1.
(* k + 1 = n d points, k > 0 and k + 1 < 2 alpha d^2 *)
have hk : (0 < (n d).-1)%N.
  have := mulr_gt0 (gap_near_gt0 _ _ (hD2 d dD2)) d2R.
  by rewrite (divfK d2n) ltr0n.
set k := (n d).-1 in hm hk.
have N0 : (0 < n d)%N := leq_trans hk (leq_pred (n d)).
have e : n d = k.+1 by rewrite /k prednK.
have hkn : k.+1%:R < 2 * alpha * d%:R ^+ 2.
  have := gap_near_lt2 _ _ (hD3 d dD3).
  by rewrite /paper_main_density RdivE e (ltr_pdivrMr _ _ d2R).
have hkn' : k.+1%:R <= 2 * alpha * d%:R ^+ 2 := ltW hkn.
(* the CGMT on T K_C and its base *)
pose K := tr_set (kcond_cone_vec kappa C d).
pose B := tr_set (kcond_slice_vec kappa C d).
pose B' := tr_set (@cond_slice_vec RR d C).
pose rho : RR := Num.sqrt (Num.max 1 (1 + cone_shift kappa) * C * d%:R).
pose r : RR := Num.sqrt (Num.min 1 (1 + cone_shift kappa) * d%:R).
pose A : RR := (l' * d%:R)%R.
pose u : RR := (A * r)%R.
have r0 : 0 < r by rewrite /r sqrtr_gt0 mulr_gt0.
have r0' : 0 <= r := ltW r0.
have A0 : 0 < A by rewrite /A mulr_gt0.
have u0 : 0 <= u by rewrite /u mulr_ge0 // ltW.
have K0 : K 0 := kcond_K0 kappa C d.
have B0 : B !=set0 := kcond_B_neq0 kappa C d C1.
have Bb : forall x, B x -> frobenius x <= rho := kcond_B_le kappa C d k1 C1.
have Kcone := kcond_K_cone kappa C d.
have BK : forall x, B x -> K x := kcond_B_sub kappa C d.
have Br : forall x, B x -> r <= frobenius x := kcond_B_ge kappa C d k1 C1.
have tail := cone_escape_lower_tail K0 B0 Bb hk Kcone BK Br u0.
pose mean : RR := \int[gauss (k + d * d)]_z
  Num.max 0 (frobenius (lsubmx z) - cone_sup K (rsubmx z)).
pose thr : RR := (r * mean - rho - u)%R.
have r2 : r ^+ 2 = a' * d%:R by rewrite /r sqr_sqrtr // mulr_ge0 ?ler0n ?ltW.
have rho2 : rho ^+ 2 = Q * d%:R.
  by rewrite /rho sqr_sqrtr // mulr_ge0 ?ler0n ?ltW.
(* thr >= 2 A r, for Q / (l'^2 a0) <= d *)
have hthr : 2%:R * A * r <= thr.
  have e4 : 4%:R * A = kgap_l C kappa alpha * d%:R / 4%:R.
    by rewrite /A /l' /l; field.
  have hm' : r * (4%:R * A) <= r * mean.
    by rewrite e4; apply: (ler_wpM2l r0'); exact: hm.
  have hrho : rho <= A * r.
    have hD5 : Q / (l' ^+ 2 * a') <= d%:R.
      apply: ltW; apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
      by rewrite ler_nat.
    have d1R : 1 <= d%:R :> RR by rewrite ler1n.
    have hsq := kgap_rho_le Q a' l' d%:R a'0 l'0 d1R (ltW Q0) hD5.
    have Ar0 : 0 <= A * r by rewrite mulr_ge0 // ltW.
    rewrite -(@ler_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 // rho2 exprMn r2.
    exact: hsq.
  exact: (gap_thr_ge _ _ _ _ hm' hrho).
pose s2 : RR := Num.sqrt (2%:R / d%:R).
have s20 : 0 < s2 by rewrite /s2 sqrtr_gt0 divr_gt0 // ltr0n.
have s20' : 0 <= s2 := ltW s20.
rewrite e.
pose E := [set Z : k.+1.-tuple 'rV[RR]_(d * d) |
  escape_inf B' (center_mx Z) <= s2 * thr].
have mE : measurable E :=
  measurable_le_set _ (s2 * thr) (measurable_escape_center C k d C1 d1).
exists E; split => //.
  (* the probability of the event *)
  rewrite gaussian_features_law //.
  pose T := [set b : 'rV[RR]_(k * (d * d)) |
    escape_inf B (vec_mx b : 'M[RR]_(k, d * d)) <= thr].
  have mT : measurable T :=
    measurable_le_set _ thr (measurable_escape_inf (N := k) B0 Bb).
  have mlin : measurable_fun setT
      (fun a : 'rV[RR]_(k.+1 * (d * d)) => a *m centering_lin k (d * d)).
    by apply: measurable_mulmx => //; exact: measurable_cst.
  have mTA : measurable
      [set a : 'rV[RR]_(k.+1 * (d * d)) | T (a *m centering_lin k (d * d))].
    by have := mlin measurableT _ mT; rewrite setTI.
  apply: (@le_trans _ _ (gauss (k.+1 * (d * d))
    [set a | T (a *m centering_lin k (d * d))])).
    apply: le_measure; rewrite ?inE.
    - have := measurable_gaussian_features kappa k.+1 d measurableT _ mE.
      by rewrite setTI.
    - exact: mTA.
    - move=> a ha.
      have ha' : escape_inf B' (center_mx (gaussian_features kappa k.+1 d a))
        <= s2 * thr := ha.
      have h := kescape_center_ge kappa C k d a C1 d1.
      have := le_trans h ha'.
      by rewrite (ler_pM2l s20) => h'; exact: h'.
  rewrite (gauss_orthogonal_law (centering_lin_orth k (d * d)) mT).
  apply: (le_trans tail).
  rewrite lee_fin; apply: (le_trans _ (hD4 d dD4)).
  have two0 : (0 : RR) < 2 by rewrite ltr0n.
  have Qn : Q != 0 := lt0r_neq0 Q0.
  have ln : l' != 0 := lt0r_neq0 l'0.
  have an : a' != 0 := lt0r_neq0 a'0.
  have eu : u ^+ 2 / (2 * rho ^+ 2) = d%:R / c * d%:R :=
    kgap_tail_exp _ _ _ _ _ _ r2 rho2 Qn dn ln an.
  have dc0 : 0 < d%:R / c by rewrite divr_gt0.
  rewrite (ler_pM2l two0) ler_expR mulNr lerN2 eu (ler_pMr _ dc0) ler1n.
  exact: d1.
(* outside the event, the gap *)
move=> Z nE S hS b.
have hlt : s2 * thr < escape_inf B' (center_mx Z) by rewrite ltNge; apply/negP.
have Bx : B' (mxvec S)^T.
  by exists (mxvec S) => //; rewrite /cond_slice_vec /= mxvecK.
have hle : escape_inf B' (center_mx Z) <=
    frobenius (center_mx Z *m (mxvec S)^T).
  by apply: escape_inf_le; exact: Bx.
have hsum := sum_sq_ge_center k (d * d) Z (mxvec S) b.
apply: (le_trans _ hsum).
have hA : 0 <= s2 * (2%:R * A * r) by rewrite !mulr_ge0 ?ler0n // ltW.
have h1 : s2 * (2%:R * A * r) <= frobenius (center_mx Z *m (mxvec S)^T).
  apply: (le_trans _ hle); apply: ltW; apply: (le_lt_trans _ hlt).
  exact: (ler_wpM2l s20').
have h2 : (s2 * (2%:R * A * r)) ^+ 2 <=
    frobenius (center_mx Z *m (mxvec S)^T) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0.
apply: (le_trans _ h2).
have s22 : s2 ^+ 2 = 2%:R / d%:R by rewrite /s2 sqr_sqrtr // divr_ge0 ?ler0n.
have eA : (s2 * (2%:R * A * r)) ^+ 2 = 8%:R * a' * A ^+ 2 :=
  kgap_sq _ _ _ _ _ s22 r2 dn.
rewrite eA.
have an : alpha != 0 := lt0r_neq0 a0.
have g0 : 0 <= a' * kgap_l C kappa alpha ^+ 2 / (64%:R * alpha).
  by rewrite divr_ge0 ?mulr_ge0 ?sqr_ge0 ?ler0n ?ltW.
apply: (le_trans (ler_wpM2l g0 hkn')).
by rewrite (kgap_const _ _ _ _ an).
Qed.

End kgap.

(* Item G1, the gap, in the form that the unsatisfiable half (item D2,
   Unsat) takes as its hypothesis: above alpha(C, kappa), with
   g = a0 l^2 / (64 alpha), a0 = min(1, 1 + c) and
   l = sqrt alpha - sqrt alpha(C, kappa). The hypothesis on kcond_support
   is interface I1, kcond_support_cvg of GaussianLimit.v, which
   condition_kappa_statement_of_I3 of Theorem.v supplies. *)
Theorem gaussian_kappa_gap (kappa C alpha : R) :
  1 < kappa -> 1 < C -> 0 < alpha -> condition_kappa_alpha C kappa < alpha ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => kcond_support kappa C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (condition_kappa_alpha C kappa)) ->
  exists g : R, 0 < g /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      g * (n d)%:R <= \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2].
Proof.
move=> k1 C1 a0 aC hQ2.
exists (Num.min 1 (1 + cone_shift kappa) * kgap_l C kappa alpha ^+ 2 /
  (64%:R * alpha)); split.
  have a'0 : 0 < Num.min 1 (1 + cone_shift kappa).
    rewrite lt_min ltr01 /= -ltrBlDl sub0r.
    exact: cone_shift_gtN1.
  have l0 := kgap_l_gt0 kappa C alpha a0 aC.
  by rewrite divr_gt0 ?mulr_gt0 ?exprn_gt0 ?ltr0n.
move=> n hn eps e0.
exact: (kgaussian_gap_n kappa C alpha n k1 C1 a0 aC hn hQ2 eps e0).
Qed.
