(* Limits of the reserve certificate. The main and reserve sample sizes
   have fixed positive limiting densities. The reserve fraction is kept
   fixed throughout the dimension limit; it can be made small afterwards.
   All corrections are guarded at singular centered covariance matrices,
   and singularity is retained as a separate exceptional event. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm centered_correction.
From GaussianAnalysis.matrix Require Import psd_part quadric_certificate.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import InProbability.
From EllipsoidUniversality.Shifted Require Import MainMoment ReserveCertificate TranslationError.
From EllipsoidUniversality.Shifted Require Import ReserveModel.
From EllipsoidUniversality.Shifted Require Import ReserveDensity ReserveCorrectionLimit.
From EllipsoidUniversality.Shifted Require Import ResidualLaws.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma reserve_positive_partE (x : RR) : maxr 0 x = (x + `|x|) / 2.
Proof.
have [x0|x0] := leP 0 x.
  rewrite ger0_norm //; field.
rewrite ltr0_norm //; field.
Qed.

Section scalar_limits.
Context {disp : measure_display} {T : nat -> measurableType disp}
  (P : forall d, probability (T d) RR).

Lemma cvg_prob_positive_part {X : forall d, T d -> RR} {x : RR} :
  cvg_prob P X x -> cvg_prob P (fun d z => maxr 0 (X d z)) (maxr 0 x).
Proof.
move=> hX.
have h := cvg_probM (cvg_probD hX (cvg_prob_norm hX)) (cvg_prob_cst P 2^-1).
rewrite -reserve_positive_partE in h.
apply: cvg_prob_eq h; exists 0%N => d _ z.
by rewrite reserve_positive_partE.
Qed.

Definition reserve_limit_value (a b g r h : RR) :=
  (maxr 0 (Num.sqrt a * Num.sqrt g - b*h))^+2 / (1+r^+2).

Lemma reserve_limit_value_cvg
    (a b g r h : forall d, T d -> RR) (a0 b0 g0 : RR) :
  0 <= a0 -> 0 <= g0 ->
  cvg_prob P a a0 -> cvg_prob P b b0 -> cvg_prob P g g0 ->
  cvg_prob P r 0 -> cvg_prob P h 0 ->
  cvg_prob P (fun d z => reserve_limit_value (a d z) (b d z)
    (g d z) (r d z) (h d z)) (a0*g0).
Proof.
move=> a0ge g0ge ha hb hg hr hh.
have hm := cvg_probB (cvg_probM (cvg_prob_sqrt ha) (cvg_prob_sqrt hg))
  (cvg_probM hb hh).
rewrite mulr0 subr0 in hm.
have hp := cvg_prob_positive_part hm.
have nonnegative : 0 <= Num.sqrt a0 * Num.sqrt g0.
  by rewrite mulr_ge0 ?sqrtr_ge0.
rewrite (max_r nonnegative) in hp.
have hn := cvg_probM hp hp.
have hd := cvg_probD (cvg_prob_cst P 1) (cvg_probM hr hr).
rewrite mulr0 addr0 in hd.
have hi := cvg_probV (oner_neq0 RR) hd.
have hv := cvg_probM hn hi.
rewrite invr1 mulr1 -expr2 exprMn (sqr_sqrtr a0ge)
  (sqr_sqrtr g0ge) in hv.
apply: cvg_prob_eq hv; exists 0%N => d _ z.
by rewrite /reserve_limit_value !expr2.
Qed.

Lemma reserve_lower_tail {X Y : forall d, T d -> RR}
    {E : forall d, set (T d)} {l : RR} :
  cvg_prob P X l -> negligible P E ->
  (exists D : nat, forall d, (D <= d)%N ->
    forall z, ~ E d z -> X d z <= Y d z) ->
  forall t : RR, t < l -> negligible P (fun d => [set z | Y d z <= t]).
Proof.
move=> hX hE [D hD] t tl.
have [_ hL] := cvg_probP.1 hX.
apply: negligibleW (negligibleU (hL t tl) hE) _.
exists D => d dD z /= yt.
have [ez|ez] := pselect (E d z); first by right.
left; exact: le_trans (hD d dD z ez) yt.
Qed.

End scalar_limits.

Lemma reserve_limit_value_ge0 (a b g r h : RR) :
  0 <= reserve_limit_value a b g r h.
Proof.
rewrite /reserve_limit_value divr_ge0 ?sqr_ge0 //.
by rewrite addr_ge0 ?sqr_ge0.
Qed.

Lemma reserve_error_positive_margin N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N+k)%N -> (0 < d)%N ->
  0 < reserve_error_bound x H -> 0 < reserve_raw_margin x H.
Proof.
move=> n0 d0 pos; rewrite ltNge; apply/negP => nonpositive.
have zero := reserve_error_bound_nonpositive n0 d0 nonpositive.
by rewrite zero ltxx in pos.
Qed.

Definition reserve_matrix_value n k d (H : 'M[RR]_(n+k,d)) : RR :=
  reserve_limit_value (n%:R/(n+k)%:R) (d%:R/Num.sqrt (n+k)%:R)
    (universality_fitting_error n d (matrix_sample (usubmx H)))
    (frobenius (reserve_matrix_correction H))
    (opnorm (reserve_matrix_quadratic H)/Num.sqrt d%:R).

Lemma reserve_matrix_valueE n k d (H : 'M[RR]_(n+k,d)) :
  (0 < d)%N -> centered_covariance (dsubmx H) \in unitmx ->
  reserve_matrix_value H =
    reserve_error_bound (matrix_sample (usubmx H)) (dsubmx H).
Proof.
move=> d0 Hu.
have sd0 : (0 : RR) < Num.sqrt d%:R by rewrite sqrtr_gt0 ltr0n.
have sdn : (Num.sqrt d%:R : RR) != 0 by rewrite gt_eqF.
have scale (e : RR) : d%:R/Num.sqrt (n+k)%:R * (e/Num.sqrt d%:R) =
    Num.sqrt (d%:R/(n+k)%:R)*e.
  rewrite -(reserve_density_sqrt_product (ler0n RR d) (ler0n RR (n+k))).
  field.
by rewrite /reserve_matrix_value /reserve_limit_value
  (reserve_matrix_correctionE Hu) (reserve_matrix_quadraticE Hu) scale.
Qed.

Section matrix_limits.
Variables N k : nat -> nat.
Variable P : forall d, probability 'M[RR]_(N d+k d,d) RR.
Variables beta gamma e : R.
Hypotheses (beta0 : 0 < beta) (gamma0 : 0 < gamma) (e0 : 0 <= e).
Hypotheses (hN : universality_density_tends_to N beta)
  (hk : universality_density_tends_to k gamma).
Hypothesis bad_probability : forall eps delta : R,
  0 < eps -> 0 < delta -> exists D : nat, forall d, (D <= d)%N ->
    (P d (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Hypothesis main_error_limit : cvg_prob P
  (fun d H => universality_fitting_error (N d) d (matrix_sample (usubmx H))) e.

Theorem reserve_matrix_value_limit :
  cvg_prob P (fun d H => @reserve_matrix_value (N d) (k d) d H)
    (beta/(beta+gamma)*e).
Proof.
have hratio := cvg_prob_seq P (fun d => (N d)%:R/(N d+k d)%:R)
  (beta/(beta+gamma)) (reserve_main_fraction_limit beta0 gamma0 hN hk).
have hscale := cvg_prob_seq P (fun d => d%:R/Num.sqrt (N d+k d)%:R)
  (1/Num.sqrt (beta+gamma)) (reserve_dimension_scale_limit beta0 gamma0 hN hk).
have ratio0 : 0 <= beta/(beta+gamma) by rewrite divr_ge0 ?addr_ge0 ?ltW.
exact: reserve_limit_value_cvg ratio0 e0 hratio hscale main_error_limit
  (reserve_correction_norm_cvg bad_probability)
  (reserve_quadratic_scaled_cvg bad_probability).
Qed.

Theorem reserve_translation_lower_tail (t : R) :
  t < beta/(beta+gamma)*e ->
  negligible P (fun d => [set H |
    translation_fitting_error (N d+k d) d
      (reserve_sample (matrix_sample (usubmx H)) (dsubmx H)) <= t]).
Proof.
move=> tl.
apply: (reserve_lower_tail reserve_matrix_value_limit
  (reserve_matrix_singular_negligible bad_probability)) tl.
have [D hD] := reserve_density_eventually_pos beta0 gamma0 hN hk.
exists D => d dD H nonsingular.
have [d0 N0 k0 nk0] := hD d dD.
have Hu : centered_covariance (dsubmx H) \in unitmx.
  case: (boolP (centered_covariance (dsubmx H) \in unitmx)) => [Hu|Hu].
    by [].
  exfalso; apply: nonsingular; exact Hu.
rewrite (reserve_matrix_valueE d0 Hu).
exact: reserve_certificate_translation_error N0 k0 d0 Hu.
Qed.

Theorem reserve_quadric_bad_negligible : 0 < e ->
  negligible P (fun d => [set H | exists (Q : 'M[RR]_d)
    (v : 'cV[RR]_d) (c : R), psdmx Q /\ Q != 0 /\
    forall i : 'I_(N d+k d), quadric_eval Q v c
      (paper_main_point (reserve_sample (matrix_sample (usubmx H)) (dsubmx H)) i) = 0]).
Proof.
move=> ep.
have pos : 0 < beta/(beta+gamma)*e.
  by rewrite mulr_gt0 // divr_gt0 // addr_gt0.
have [_ hlow] := cvg_probP.1 reserve_matrix_value_limit.
apply: negligibleW (negligibleU (hlow 0 pos)
  (reserve_matrix_singular_negligible bad_probability)) _.
have [D hD] := reserve_density_eventually_pos beta0 gamma0 hN hk.
exists D => d dD H /= [Q [v [c [Qpsd [Qnz fit]]]]].
have [singular|nonsingular] := pselect (@reserve_matrix_singular (N d) (k d) d H).
  by right.
have [small|positive] := leP (reserve_matrix_value H) 0; first by left.
have [d0 N0 k0 nk0] := hD d dD.
have Hu : centered_covariance (dsubmx H) \in unitmx.
  case: (boolP (centered_covariance (dsubmx H) \in unitmx)) => [Hu|Hu].
    by [].
  exfalso; apply: nonsingular; exact Hu.
rewrite (reserve_matrix_valueE d0 Hu) in positive.
have margin := reserve_error_positive_margin nk0 d0 positive.
exfalso; exact: (reserve_certificate_excludes N0 k0 d0 Hu margin Qpsd Qnz fit).
Qed.

Corollary reserve_matrix_translation_lower_tail (t : R) :
  t < beta/(beta+gamma)*e ->
  negligible P (fun d => [set H |
    translation_fitting_error (N d+k d) d (matrix_sample H) <= t]).
Proof.
move=> tl; apply: negligibleW (reserve_translation_lower_tail tl) _.
by exists 0%N => d _ H /=; rewrite reserve_sample_matrix_blocks.
Qed.

Corollary reserve_matrix_quadric_bad_negligible : 0 < e ->
  negligible P (fun d => [set H | exists (Q : 'M[RR]_d)
    (v : 'cV[RR]_d) (c : R), psdmx Q /\ Q != 0 /\
    forall i : 'I_(N d+k d), quadric_eval Q v c
      (paper_main_point (matrix_sample H) i) = 0]).
Proof.
move=> ep; apply: negligibleW (reserve_quadric_bad_negligible ep) _.
by exists 0%N => d _ H /=; rewrite reserve_sample_matrix_blocks.
Qed.

End matrix_limits.
