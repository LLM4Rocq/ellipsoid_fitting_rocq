(* The unsatisfiable direction for small deterministic Gaussian shifts.
   The condition residual gap is uniform in the candidate matrix. A
   finite Gaussian matrix bound controls the translation obstruction. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.random_matrix Require Import isotropic_rows gaussian_rows_bounds.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From GaussianAnalysis.comparison Require Import gauss_matrix_law.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions ConditionDefinitions.
From EllipsoidUniversality.Sat Require Import ApproximateFit.
From EllipsoidUniversality.Shifted Require Import GaussianRows Translations.
From EllipsoidUniversality.Shifted Require Import ConditionGap ConditionTranslation GaussianMatrixBounds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma gaussian_sample_point_matrixE n d (x : paper_main_sample n d) :
  sample_point_matrix x = restricted_isometry.tuple_mx (sample_row_tuple x).
Proof. by apply/matrixP => i j; rewrite /sample_point_matrix /gauss_matrix_law.tuple_mx
  /restricted_isometry.tuple_mx !mxE. Qed.

Lemma gaussian_translation_norm_tail n d (m : 'cV[RR]_d) (C eta : R) :
  (0 < n)%N -> (0 < d)%N -> 0 < eta ->
  (gaussian_product_law (n*d) (@translation_norm_obstruction n d m C eta) <=
    (4*C^+2*frobenius m^+2 * @gaussian_rows_bound RR n d /
      (eta*n%:R*d%:R))%:E)%E.
Proof.
move=> n0 d0 eta0.
have a0 : 0 <= 4*C^+2*frobenius m^+2.
  apply: mulr_ge0; last exact: sqr_ge0.
  by apply: mulr_ge0; [rewrite ler0n | exact: sqr_ge0].
have t0 : 0 < eta*n%:R*d%:R by rewrite !mulr_gt0 ?ltr0n.
have he : @translation_norm_obstruction n d m C eta =
    [set x : paper_main_sample n d | eta*n%:R*d%:R <=
      (4*C^+2*frobenius m^+2) *
        opnorm (restricted_isometry.tuple_mx (sample_row_tuple x))^+2].
  apply/funext => x; rewrite /translation_norm_obstruction /= gaussian_sample_point_matrixE.
  congr (_ <= _); ring.
rewrite he.
exact: gaussian_sample_matrix_scaled_tail a0 t0.
Qed.

Lemma sqrt_product_le_sum (a b : RR) : 0 <= a -> 0 <= b ->
  Num.sqrt (a*b) <= a+b.
Proof.
move=> a0 b0.
have s0 := sqrtr_ge0 (a*b).
have ss : (Num.sqrt (a*b))^+2 = a*b by rewrite sqr_sqrtr ?mulr_ge0.
have hsq : (a+b)^+2 - a*b = a^+2 + a*b + b^+2 by ring.
have hn : 0 <= (a+b)^+2 - a*b.
  rewrite hsq; apply: addr_ge0; last exact: sqr_ge0.
  by apply: addr_ge0; [exact: sqr_ge0 | exact: mulr_ge0].
have hle : (Num.sqrt (a*b))^+2 <= (a+b)^+2 by rewrite ss; nra.
have ab0 : 0 <= a+b := addr_ge0 a0 b0.
nra.
Qed.

Definition gaussian_matrix_density_constant (a : R) := 1153 + 4608/a.

Lemma gaussian_matrix_density_constant_pos (a : R) :
  0 < a -> 0 < gaussian_matrix_density_constant a.
Proof.
move=> a0; rewrite /gaussian_matrix_density_constant.
apply: addr_gt0; first by rewrite ltr0n.
by rewrite divr_gt0 ?ltr0n.
Qed.

Lemma gaussian_scalar_density_bound (a u v : R) :
  0 < a -> 0 <= u -> 1 <= v -> a*v^+2 <= u ->
  u + 1152 * (Num.sqrt (u*(v+1)) + (v+1)) <=
    gaussian_matrix_density_constant a * u.
Proof.
move=> a0 u0 v1 huv.
have v0 : 0 <= v by lra.
have vp0 : 0 <= v+1 by lra.
have hs := sqrt_product_le_sum u0 vp0.
have hv2 : v <= v^+2 by nra.
have hav : a*v <= u := le_trans (ler_wpM2l (ltW a0) hv2) huv.
have hv : v <= u/a by rewrite ler_pdivlMr // mulrC.
rewrite /gaussian_matrix_density_constant.
nra.
Qed.

Lemma gaussian_rows_bound_density n d (a : R) :
  0 < a -> (0 < d)%N -> a*d%:R^+2 <= n%:R ->
  @gaussian_rows_bound RR n d <= gaussian_matrix_density_constant a * n%:R.
Proof.
move=> a0 d0 hnd.
have hdS : (d.+1%:R : RR) = d%:R + 1 by rewrite -addn1 natrD.
rewrite /gaussian_rows_bound /isotropic_covariance_bound hdS.
have -> : (288 : RR) * 2^+2 = 1152 by ring.
apply: gaussian_scalar_density_bound => //; by rewrite ?ler0n ?ler1n.
Qed.

Lemma gaussian_translation_bound_scale (C v B K eta u d : R) :
  0 <= v -> B <= K*u -> 0 < eta -> 0 < u -> 0 < d ->
  4*C^+2*v*B/(eta*u*d) <= (4*C^+2*K/eta)*v/d.
Proof.
move=> v0 BK eta0 u0 d0.
have den0 : 0 < eta*u*d by rewrite !mulr_gt0.
have mul0 : 0 <= 4*C^+2*v.
  apply: mulr_ge0 => //.
  by apply: mulr_ge0; [rewrite ler0n | exact: sqr_ge0].
have h := ler_wpM2l mul0 BK.
have etaN := lt0r_neq0 eta0.
have uN := lt0r_neq0 u0.
have dN := lt0r_neq0 d0.
have he : (4*C^+2*K/eta)*v/d * (eta*u*d) = 4*C^+2*v*(K*u).
  by field.
by rewrite ler_pdivrMr // he.
Qed.

Theorem gaussian_small_shift_condition_bound (C alpha : R) :
  1 < C -> 0 < alpha -> condition_alpha C < alpha ->
  exists K : R, 0 < K /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  forall m : 'cV[RR]_d,
  (gaussian_product_law (n d*d)
      ((sample_translate m) @^-1` universality_conditioned_fit_event (n d) d C)
    <= eps%:E + (K*frobenius m^+2/d%:R)%:E)%E.
Proof.
move=> C1 alpha0 aC.
have C0 : 0 < C := lt_trans ltr01 C1.
have a20 : 0 < alpha/2 by rewrite divr_gt0.
have [eta [eta0 gap]] := @gaussian_condition_residual_gap C alpha C1 alpha0 aC.
pose K := 4*C^+2*gaussian_matrix_density_constant (alpha/2)/eta.
have K0 : 0 < K.
  rewrite /K divr_gt0 // !mulr_gt0 ?ltr0n ?exprn_gt0 //.
  exact: gaussian_matrix_density_constant_pos.
exists K; split => // n hn eps eps0.
have [Dg hDg] := gap n hn eps eps0.
have [Dn hDn] := af_ev_density n alpha alpha0 hn.
exists (maxn Dg Dn) => d; rewrite geq_max => /andP[dg dn] m.
have [d0 [nlo _]] := hDn d dn.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < (n d)%:R :> RR.
  apply: lt_le_trans _ nlo.
  by rewrite mulr_gt0 ?exprn_gt0.
have n0 : (0 < n d)%N by move: nR; rewrite ltr0n.
have [E [mE PE hE]] := hDg d dg.
have hp := @translated_condition_gap_probability (n d) d
  (gaussian_product_law (n d*d)) m C eta E d0 C0 mE hE.
apply: le_trans hp _; apply: leeD PE _.
apply: le_trans (@gaussian_translation_norm_tail (n d) d m C eta n0 d0 eta0) _.
rewrite lee_fin /K.
exact: gaussian_translation_bound_scale (sqr_ge0 (frobenius m))
  (gaussian_rows_bound_density a20 d0 nlo) eta0 nR dR.
Qed.

Corollary gaussian_small_shift_condition_unsat_squared (C alpha : R)
    (n : nat -> nat) (m : forall d, 'cV[RR]_d) :
  1 < C -> 0 < alpha -> condition_alpha C < alpha ->
  universality_density_tends_to n alpha ->
  (forall z : R, 0 < z -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d)^+2/d%:R <= z) ->
  paper_main_tends_to (fun d => gaussian_product_law (n d*d)
    ((sample_translate (m d)) @^-1` universality_conditioned_fit_event (n d) d C)) 0.
Proof.
move=> C1 alpha0 aC hn hm eps eps0.
have [K [K0 bound]] := @gaussian_small_shift_condition_bound C alpha C1 alpha0 aC.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have q0 : 0 < eps/(4*K) by rewrite divr_gt0 // mulr_gt0.
have [D1 h1] := bound n hn (eps/2) e20.
have [D2 h2] := hm (eps/(4*K)) q0.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
rewrite sube0 gee0_abs ?measure_ge0 //.
apply: le_lt_trans (h1 d d1 (m d)) _.
rewrite -EFinD lte_fin.
have hs := ler_wpM2l (ltW K0) (h2 d d2).
have Kn : K != 0 := lt0r_neq0 K0.
have he : K*(eps/(4*K)) = eps/4 by field.
rewrite he mulrA in hs.
have small : eps/2 + eps/4 < eps by lra.
apply: le_lt_trans _ small.
by rewrite lerD2l.
Qed.

Lemma shift_norm_square_ratio (v z t : R) :
  0 <= v -> 0 < z -> 0 < t -> v <= Num.sqrt z * Num.sqrt t ->
  v^+2/t <= z.
Proof.
move=> v0 z0 t0 hv.
have s0 : 0 <= Num.sqrt z * Num.sqrt t by rewrite mulr_ge0 ?sqrtr_ge0.
have ss : (Num.sqrt z * Num.sqrt t)^+2 = z*t.
  by rewrite exprMn !sqr_sqrtr ?ltW.
have v2 : v^+2 <= (Num.sqrt z * Num.sqrt t)^+2 by nra.
by rewrite ler_pdivrMr //; move: v2; rewrite ss.
Qed.

Corollary gaussian_small_shift_condition_unsat (C alpha : R)
    (n : nat -> nat) (m : forall d, 'cV[RR]_d) :
  1 < C -> 0 < alpha -> condition_alpha C < alpha ->
  universality_density_tends_to n alpha ->
  (forall e : R, 0 < e -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= e*Num.sqrt d%:R) ->
  paper_main_tends_to (fun d => gaussian_product_law (n d*d)
    ((sample_translate (m d)) @^-1` universality_conditioned_fit_event (n d) d C)) 0.
Proof.
move=> C1 alpha0 aC hn hm.
apply: (@gaussian_small_shift_condition_unsat_squared C alpha n m C1 alpha0 aC hn).
move=> z z0.
have ez0 : 0 < Num.sqrt z by rewrite sqrtr_gt0.
have [D hD] := hm (Num.sqrt z) ez0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have dR : 0 < d%:R :> RR by rewrite ltr0n.
exact: shift_norm_square_ratio (frobenius_ge0 (m d)) z0 dR (hD d dD).
Qed.
