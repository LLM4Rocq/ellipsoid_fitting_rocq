(* Convergence of guarded reserve corrections under an arbitrary full-sample
   law. The only probabilistic input is the vanishing reserve_model_bad
   event. No independence, density, symmetry, or moment hypothesis is added.
   Strict failure tails imply the closed tails of cvg_prob by using half
   the requested tolerance. Singularity remains a separate negligible event. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear.
From GaussianAnalysis.matrix Require Import centered_correction quadric_certificate.
From GaussianAnalysis.convex Require Import image_projection.
From GaussianAnalysis.probability Require Import subgaussian_matrix independent_matrix_blocks.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.
From EllipsoidUniversality.Gaussian Require Import InProbability.
From EllipsoidUniversality.Shifted Require Import GaussianRows MainMoment.
From EllipsoidUniversality.Shifted Require Import ReserveModel ReserveCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition reserve_matrix_correction n k d (H : 'M[RR]_(n+k,d)) : 'cV[RR]_k :=
  guarded_reserve_correction (dsubmx H) (matrix_residual_moment_map n d (usubmx H)).

Definition reserve_matrix_quadratic n k d (H : 'M[RR]_(n+k,d)) : 'M[RR]_d :=
  guarded_reserve_quadratic (dsubmx H) (matrix_residual_moment_map n d (usubmx H)).

Definition reserve_matrix_singular n k d : set 'M[RR]_(n+k,d) :=
  [set H | ~~ (centered_covariance (dsubmx H) \in unitmx)].

Lemma measurable_reserve_matrix_correction n k d :
  measurable_fun [set: 'M[RR]_(n+k,d)] (@reserve_matrix_correction n k d).
Proof.
apply: guarded_reserve_correction_measurable; first exact: measurable_dsubmx.
apply: measurableT_comp (measurable_funPT (matrix_residual_moment_map n d)) _.
exact: measurable_usubmx.
Qed.

Lemma measurable_reserve_matrix_quadratic n k d :
  measurable_fun [set: 'M[RR]_(n+k,d)] (@reserve_matrix_quadratic n k d).
Proof.
apply: guarded_reserve_quadratic_measurable; first exact: measurable_dsubmx.
apply: measurableT_comp (measurable_funPT (matrix_residual_moment_map n d)) _.
exact: measurable_usubmx.
Qed.

Lemma measurable_reserve_matrix_singular n k d :
  measurable (@reserve_matrix_singular n k d).
Proof.
have mu : measurable_fun [set: 'M[RR]_(n+k,d)]
    (fun H => centered_covariance (dsubmx H) \in unitmx).
  apply: reserve_unitmx_measurable; apply: reserve_covariance_measurable.
  exact: measurable_dsubmx.
have mn := measurable_neg mu.
have mt : measurable ([set true] : set bool) by [].
have m := mn measurableT _ mt.
by rewrite setTI preimage_true in m.
Qed.

Lemma measurable_reserve_correction_norm n k d :
  measurable_fun [set: 'M[RR]_(n+k,d)]
    (fun H => frobenius (@reserve_matrix_correction n k d H)).
Proof.
apply: measurable_frobenius_fun; exact: measurable_reserve_matrix_correction.
Qed.

Lemma measurable_reserve_quadratic_scaled n k d :
  measurable_fun [set: 'M[RR]_(n+k,d)]
    (fun H => opnorm (@reserve_matrix_quadratic n k d H) / Num.sqrt d%:R).
Proof.
apply: measurable_funM; last exact: measurable_cst.
apply: measurable_opnorm; apply/measurable_fun_mxP.
exact: measurable_reserve_matrix_quadratic.
Qed.

Lemma reserve_model_badE n k d (delta : R) (H : 'M[RR]_(n+k,d)) :
  @reserve_model_bad n k d delta H <->
  [|| ~~ (centered_covariance (dsubmx H) \in unitmx),
    delta < frobenius (reserve_matrix_correction H) |
    delta * Num.sqrt d%:R < opnorm (reserve_matrix_quadratic H)].
Proof. by []. Qed.

Lemma reserve_matrix_correctionE n k d (H : 'M[RR]_(n+k,d)) :
  centered_covariance (dsubmx H) \in unitmx ->
  reserve_matrix_correction H =
    reserve_correction (matrix_sample (usubmx H)) (dsubmx H).
Proof.
by move=> Hu; rewrite /reserve_matrix_correction /guarded_reserve_correction Hu.
Qed.

Lemma reserve_matrix_quadraticE n k d (H : 'M[RR]_(n+k,d)) :
  centered_covariance (dsubmx H) \in unitmx ->
  reserve_matrix_quadratic H =
    reserve_outer_error (matrix_sample (usubmx H)) (dsubmx H).
Proof.
move=> Hu; rewrite /reserve_matrix_quadratic guarded_reserve_quadraticE.
change (coef_adj (fun i => (row i (dsubmx H))^T *m row i (dsubmx H))
  (reserve_matrix_correction H)^T =
    reserve_outer_error (matrix_sample (usubmx H)) (dsubmx H)).
rewrite (reserve_matrix_correctionE Hu) /reserve_outer_error /weighted_outer /coef_adj.
apply: eq_bigr => i _; by rewrite mxE trmxK.
Qed.

Section correction_limits.
Variables N k : nat -> nat.
Variable P : forall d, probability 'M[RR]_(N d+k d,d) RR.
Hypothesis bad_probability : forall eps delta : R,
  0 < eps -> 0 < delta -> exists D : nat, forall d, (D <= d)%N ->
    (P d (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.

Lemma reserve_model_bad_negligible (delta : R) : 0 < delta ->
  negligible P (fun d => @reserve_model_bad (N d) (k d) d delta).
Proof.
move=> delta0; apply: negligible_measurable.
- by move=> d; exact: measurable_reserve_model_bad.
- move=> eps eps0; exact: (@bad_probability eps delta eps0 delta0).
Qed.

Theorem reserve_matrix_singular_negligible :
  negligible P (fun d => @reserve_matrix_singular (N d) (k d) d).
Proof.
have one0 : (0 : RR) < 1 := ltr01.
apply: negligibleW; first exact: (@reserve_model_bad_negligible 1 one0).
exists 0%N => d _ H /= Hu; rewrite reserve_model_badE.
by apply/or3P; constructor 1.
Qed.

Theorem reserve_correction_norm_cvg :
  cvg_prob P (fun d H => frobenius (@reserve_matrix_correction (N d) (k d) d H)) 0.
Proof.
move=> eta eta0.
have half0 : 0 < eta / 2 by rewrite divr_gt0.
apply: negligibleW; first exact: (@reserve_model_bad_negligible (eta / 2) half0).
exists 0%N => d _ H /= h.
rewrite subr0 ger0_norm ?frobenius_ge0 // in h.
rewrite reserve_model_badE; apply/or3P; constructor 2.
have half : eta / 2 < eta by lra.
exact: lt_le_trans half h.
Qed.

Theorem reserve_quadratic_scaled_cvg :
  cvg_prob P (fun d H => opnorm (@reserve_matrix_quadratic (N d) (k d) d H) /
    Num.sqrt d%:R) 0.
Proof.
move=> eta eta0.
have half0 : 0 < eta / 2 by rewrite divr_gt0.
apply: negligibleW; first exact: (@reserve_model_bad_negligible (eta / 2) half0).
exists 1%N => d d1 H /= h.
have d0 : (0 : RR) < d%:R by rewrite ltr0n.
have s0 : (0 : RR) < Num.sqrt d%:R by rewrite sqrtr_gt0.
have nn : 0 <= opnorm (reserve_matrix_quadratic H) / Num.sqrt d%:R.
  by rewrite divr_ge0 ?opnorm_ge0 ?sqrtr_ge0.
rewrite subr0 (ger0_norm nn) ler_pdivlMr // in h.
rewrite reserve_model_badE; apply/or3P; constructor 3.
have half : eta / 2 < eta by lra.
apply: lt_le_trans h; by rewrite ltr_pM2r.
Qed.

End correction_limits.
