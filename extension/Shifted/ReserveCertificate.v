(* Main-sample projection weights and a centered reserve correction.
   On invertibility of the reserve covariance, the combined weights kill
   constants and linear functions exactly. Their quadratic margin gives a
   uniform error bound for every translation. A nonpositive margin is
   handled by nonnegativity of the error, not by strengthening a PSD bound. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part psd_splitting opnorm quadric_certificate centered_correction.
From GaussianAnalysis.convex Require Import logdet_barrier.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Shifted Require Import ProjectionCertificate GaussianRows Translations TranslationError.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition reserve_correction {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :=
  centered_correction H (sample_residual_moment x).
Definition reserve_sample {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :=
  sample_of_row_tuple [tuple of sample_row_tuple x ++ [tuple row i H | i < k]].
Definition reserve_weights {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :=
  row_mx (sample_residual_direction x) (- (reserve_correction x H)^T).
Definition reserve_outer_error {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :=
  weighted_outer (fun i => reserve_correction x H i 0)
    (fun i => (row i H)^T).

Lemma paper_main_point_of_row_tuple N d (t : N.-tuple 'rV[RR]_d) (i : 'I_N) :
  paper_main_point (sample_of_row_tuple t) i = (tnth t i)^T.
Proof.
have h := congr1 (fun u => tnth u i) (sample_of_row_tupleK t).
rewrite /sample_row_tuple tnth_mktuple in h.
by move: (congr1 trmx h); rewrite trmxK.
Qed.

Lemma reserve_sample_point_l N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) (i : 'I_N) :
  paper_main_point (reserve_sample x H) (lshift k i) = paper_main_point x i.
Proof.
by rewrite /reserve_sample paper_main_point_of_row_tuple tnth_lshift
  /sample_row_tuple tnth_mktuple trmxK.
Qed.

Lemma reserve_sample_point_r N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) (i : 'I_k) :
  paper_main_point (reserve_sample x H) (rshift N i) = (row i H)^T.
Proof.
by rewrite /reserve_sample paper_main_point_of_row_tuple tnth_rshift tnth_mktuple.
Qed.

Lemma reserve_weights_l N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) (i : 'I_N) :
  reserve_weights x H 0 (lshift k i) = sample_residual_direction x 0 i.
Proof. by rewrite /reserve_weights row_mxEl. Qed.

Lemma reserve_weights_r N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) (i : 'I_k) :
  reserve_weights x H 0 (rshift N i) = - reserve_correction x H i 0.
Proof. by rewrite /reserve_weights row_mxEr !mxE. Qed.

Lemma reserve_weights_sum0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < k)%N -> (0 < d)%N ->
  \sum_(i < N+k) reserve_weights x H 0 i = 0.
Proof.
move=> N0 k0 d0; rewrite big_split_ord /=.
under [X in X + _]eq_bigr do rewrite reserve_weights_l.
under [X in _ + X]eq_bigr do rewrite reserve_weights_r.
by rewrite sumrN sample_residual_sum0 // /reserve_correction
  centered_correction_sum // oppr0 addr0.
Qed.

Lemma reserve_correction_moment_sum N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  \sum_(i < k) reserve_correction x H i 0 *: (row i H)^T =
    H^T *m reserve_correction x H.
Proof.
apply/matrixP => j l; rewrite summxE mxE.
by apply: eq_bigr => i _; rewrite !mxE ord1 mulrC.
Qed.

Lemma reserve_weights_moment0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  centered_covariance H \in unitmx ->
  \sum_(i < N+k) reserve_weights x H 0 i *:
    paper_main_point (reserve_sample x H) i = 0.
Proof.
move=> Hu; rewrite big_split_ord /=.
under [X in X + _]eq_bigr do rewrite reserve_weights_l reserve_sample_point_l.
under [X in _ + X]eq_bigr do rewrite reserve_weights_r reserve_sample_point_r scaleNr.
rewrite sumrN reserve_correction_moment_sum /reserve_correction
  centered_correction_moment //.
by rewrite -/sample_residual_moment subrr.
Qed.

Lemma reserve_outerE N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  weighted_outer (fun i => reserve_weights x H 0 i)
    (fun i => paper_main_point (reserve_sample x H) i) =
  sample_residual_outer x - reserve_outer_error x H.
Proof.
rewrite /weighted_outer big_split_ord /=.
under [X in X + _]eq_bigr do rewrite reserve_weights_l reserve_sample_point_l.
under [X in _ + X]eq_bigr do rewrite reserve_weights_r reserve_sample_point_r scaleNr.
by rewrite sumrN.
Qed.

Lemma reserve_weights_sqnormE N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  \sum_(i < N+k) (reserve_weights x H 0 i) ^+ 2 =
  frobenius (sample_residual_direction x) ^+ 2 +
    frobenius (reserve_correction x H) ^+ 2.
Proof.
rewrite big_split_ord /= !frobenius_sqr /mxdot big_ord1.
congr (_ + _).
- by apply: eq_bigr => i _; rewrite reserve_weights_l expr2.
- by apply: eq_bigr => i _; rewrite reserve_weights_r sqrrN big_ord1 expr2.
Qed.

Lemma reserve_weights_frobeniusE N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  frobenius (reserve_weights x H) ^+ 2 =
  frobenius (sample_residual_direction x) ^+ 2 +
    frobenius (reserve_correction x H) ^+ 2.
Proof.
rewrite -reserve_weights_sqnormE frobenius_sqr /mxdot big_ord1.
by apply: eq_bigr => i _; rewrite expr2.
Qed.

Lemma reserve_weights_sqnorm N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> 0 < universality_fitting_error N d x ->
  \sum_(i < N+k) (reserve_weights x H 0 i) ^+ 2 =
  1 + frobenius (reserve_correction x H) ^+ 2.
Proof.
by move=> N0 d0 g0; rewrite reserve_weights_sqnormE sample_residual_norm // expr1n.
Qed.

Lemma reserve_weights_frobenius N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> 0 < universality_fitting_error N d x ->
  frobenius (reserve_weights x H) ^+ 2 =
  1 + frobenius (reserve_correction x H) ^+ 2.
Proof.
by move=> N0 d0 g0; rewrite reserve_weights_frobeniusE sample_residual_norm // expr1n.
Qed.

Lemma reserve_correction_gamma0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> universality_fitting_error N d x = 0 ->
  reserve_correction x H = 0.
Proof.
move=> N0 d0 g0; rewrite /reserve_correction sample_residual_moment_gamma0 //.
by rewrite /centered_correction /centered_potential !mulmx0.
Qed.

Lemma reserve_weights_gamma0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> universality_fitting_error N d x = 0 ->
  reserve_weights x H = 0.
Proof.
move=> N0 d0 g0; rewrite /reserve_weights sample_residual_direction_gamma0 //
  reserve_correction_gamma0 // trmx0 oppr0.
exact: row_mx0.
Qed.

Lemma reserve_outer_error_gamma0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> universality_fitting_error N d x = 0 ->
  reserve_outer_error x H = 0.
Proof.
move=> N0 d0 g0; rewrite /reserve_outer_error /weighted_outer
  reserve_correction_gamma0 //.
by apply: big1 => i _; rewrite mxE scale0r.
Qed.

Section reserve_margin.
Variable F : realType.

Lemma reserve_psd_margin_perturb d (M D : 'M[F]_d) (a : F) :
  psdmx (M - a%:M) -> D \is symmetricmx ->
  psdmx (M - D - (a - opnorm D)%:M).
Proof.
move=> hM Ds.
have hD : psdmx ((opnorm D)%:M - D).
  split.
  - apply/symmetricmxP.
    by rewrite linearB /= tr_scalar_mx (symmetricmxP _ Ds).
  - move=> x.
    have := (opnorm_symP Ds (opnorm_ge0 D)).2 (lexx _) x.
    rewrite ler_norml => /andP[_ hx].
    rewrite mulmxBl mul_scalar_mx mxdotBr mxdotZr subr_ge0.
    exact: hx.
have -> : M - D - (a - opnorm D)%:M =
    (M - a%:M) + ((opnorm D)%:M - D).
  apply/matrixP => i j; rewrite !mxE; ring.
exact: psdmxD hM hD.
Qed.

Lemma reserve_sqrt_ratio N n d : (0 < n)%N -> (0 < d)%N ->
  Num.sqrt (d%:R / n%:R) * Num.sqrt (N%:R / d%:R) =
  Num.sqrt (N%:R / n%:R) :> F.
Proof.
move=> n0 d0.
have nr0 : (n%:R : F) != 0 by rewrite pnatr_eq0 -lt0n.
have dr0 : (d%:R : F) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite -sqrtrM ?divr_ge0 ?ler0n //.
congr Num.sqrt; field.
Qed.

Lemma reserve_margin_scale N n d (g e : F) : (0 < n)%N -> (0 < d)%N ->
  Num.sqrt (N%:R / n%:R) * Num.sqrt g - Num.sqrt (d%:R / n%:R) * e =
  Num.sqrt (d%:R / n%:R) * (Num.sqrt (N%:R / d%:R) * Num.sqrt g - e).
Proof.
by move=> n0 d0; rewrite mulrBr mulrA reserve_sqrt_ratio.
Qed.

Lemma reserve_margin_square_scale N n d (g e w : F) :
  (0 < n)%N -> (0 < d)%N ->
  d%:R * (Num.sqrt (N%:R / d%:R) * Num.sqrt g - e)^+2 / (n%:R * w) =
  (Num.sqrt (N%:R / n%:R) * Num.sqrt g -
    Num.sqrt (d%:R / n%:R) * e)^+2 / w.
Proof.
move=> n0 d0; rewrite (@reserve_margin_scale N n d g e n0 d0) exprMn.
rewrite sqr_sqrtr ?divr_ge0 ?ler0n // invfM; ring.
Qed.

Lemma reserve_margin_nonnegative N n d (g e : F) :
  (0 < n)%N -> (0 < d)%N ->
  0 <= Num.sqrt (N%:R / d%:R) * Num.sqrt g - e ->
  0 <= Num.sqrt (N%:R / n%:R) * Num.sqrt g -
    Num.sqrt (d%:R / n%:R) * e.
Proof.
move=> n0 d0 ha; rewrite (@reserve_margin_scale N n d g e n0 d0).
exact: mulr_ge0 (sqrtr_ge0 _) ha.
Qed.

Lemma reserve_margin_positive_part_zero N n d (g e : F) :
  (0 < n)%N -> (0 < d)%N ->
  Num.sqrt (N%:R / d%:R) * Num.sqrt g - e <= 0 ->
  Num.max 0 (Num.sqrt (N%:R / n%:R) * Num.sqrt g -
    Num.sqrt (d%:R / n%:R) * e) = 0.
Proof.
move=> n0 d0 ha; rewrite (@reserve_margin_scale N n d g e n0 d0).
apply: max_l; exact: mulr_ge0_le0 (sqrtr_ge0 _) ha.
Qed.

Lemma reserve_margin_positive_part N n d (g e : F) :
  (0 < n)%N -> (0 < d)%N ->
  0 <= Num.sqrt (N%:R / d%:R) * Num.sqrt g - e ->
  Num.max 0 (Num.sqrt (N%:R / n%:R) * Num.sqrt g -
    Num.sqrt (d%:R / n%:R) * e) =
  Num.sqrt (N%:R / n%:R) * Num.sqrt g - Num.sqrt (d%:R / n%:R) * e.
Proof.
move=> n0 d0 ha; apply: max_r.
rewrite (@reserve_margin_scale N n d g e n0 d0).
exact: mulr_ge0 (sqrtr_ge0 _) ha.
Qed.

End reserve_margin.

Definition reserve_raw_margin {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) : RR :=
  Num.sqrt (N%:R / d%:R) * Num.sqrt (universality_fitting_error N d x) -
    opnorm (reserve_outer_error x H).
Definition reserve_scaled_margin {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) : RR :=
  Num.sqrt (N%:R / (N+k)%:R) * Num.sqrt (universality_fitting_error N d x) -
    Num.sqrt (d%:R / (N+k)%:R) * opnorm (reserve_outer_error x H).
Definition reserve_error_bound {N k d : nat}
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) : RR :=
  (maxr 0 (reserve_scaled_margin x H))^+2 /
    (1 + frobenius (reserve_correction x H)^+2).

Lemma reserve_outer_error_symmetric N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) : reserve_outer_error x H \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /reserve_outer_error /weighted_outer linear_sum /=.
apply: eq_bigr => i _.
by rewrite linearZ /= trmx_mul trmxK.
Qed.

Lemma reserve_certificate_margin N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N ->
  psdmx (weighted_outer (fun i => reserve_weights x H 0 i)
    (fun i => paper_main_point (reserve_sample x H) i) -
      (reserve_raw_margin x H)%:M).
Proof.
move=> N0 d0; rewrite reserve_outerE /reserve_raw_margin.
apply: reserve_psd_margin_perturb.
- exact: sample_residual_margin.
- exact: reserve_outer_error_symmetric.
Qed.

Lemma reserve_error_bound_gamma0 N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < d)%N -> universality_fitting_error N d x = 0 ->
  reserve_error_bound x H = 0.
Proof.
move=> N0 d0 g0.
rewrite /reserve_error_bound /reserve_scaled_margin g0 sqrtr0 mulr0.
by rewrite reserve_outer_error_gamma0 // opnorm0 mulr0 subr0 maxxx expr0n mul0r.
Qed.

Lemma reserve_error_bound_nonpositive N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N+k)%N -> (0 < d)%N -> reserve_raw_margin x H <= 0 ->
  reserve_error_bound x H = 0.
Proof.
move=> n0 d0 ha; rewrite /reserve_error_bound /reserve_scaled_margin.
rewrite (reserve_margin_positive_part_zero n0 d0 ha).
by rewrite expr0n mul0r.
Qed.

Theorem reserve_certificate_error N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < k)%N -> (0 < d)%N ->
  centered_covariance H \in unitmx ->
  forall m : 'cV[RR]_d, reserve_error_bound x H <=
    universality_fitting_error (N+k) d (sample_translate m (reserve_sample x H)).
Proof.
move=> N0 k0 d0 Ku m.
have n0 : (0 < N+k)%N by rewrite addn_gt0 N0.
have nonnegative : 0 <= universality_fitting_error (N+k) d
    (sample_translate m (reserve_sample x H)).
  exact: fitting_error_nonnegative.
have gge : 0 <= universality_fitting_error N d x.
  exact: fitting_error_nonnegative.
have [g0|gN] := eqVneq (universality_fitting_error N d x) 0.
  by rewrite (reserve_error_bound_gamma0 H N0 d0 g0).
have gp : 0 < universality_fitting_error N d x.
  by rewrite lt_neqAle eq_sym gN gge.
have [ha|ha] := leP 0 (reserve_raw_margin x H); last first.
  rewrite (reserve_error_bound_nonpositive n0 d0 (ltW ha)); exact: nonnegative.
have wn := reserve_weights_sqnorm H N0 d0 gp.
have wpos : 0 < \sum_(i < N+k) (reserve_weights x H 0 i)^+2.
  rewrite wn; have h := sqr_ge0 (frobenius (reserve_correction x H)); lra.
have h := @translated_sample_certificate_error (N+k) d (reserve_sample x H)
  (fun i => reserve_weights x H 0 i) (reserve_raw_margin x H) n0 d0 ha wpos
  (reserve_weights_sum0 x H N0 k0 d0) (reserve_weights_moment0 x Ku)
  (reserve_certificate_margin x H N0 d0) m.
rewrite wn /reserve_raw_margin reserve_margin_square_scale // in h.
rewrite /reserve_error_bound /reserve_scaled_margin
  (reserve_margin_positive_part n0 d0 ha).
exact: h.
Qed.

Corollary reserve_certificate_translation_error N k d
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < k)%N -> (0 < d)%N ->
  centered_covariance H \in unitmx ->
  reserve_error_bound x H <= translation_fitting_error (N+k) d (reserve_sample x H).
Proof.
move=> N0 k0 d0 Ku; apply: translation_fitting_error_lower_bound => m.
exact: reserve_certificate_error.
Qed.

Theorem reserve_certificate_excludes N k d (x : paper_main_sample N d)
    (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < k)%N -> (0 < d)%N ->
  centered_covariance H \in unitmx -> 0 < reserve_raw_margin x H ->
  forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
    psdmx Q -> Q != 0 ->
    ~ (forall i : 'I_(N+k),
      quadric_eval Q v c (paper_main_point (reserve_sample x H) i) = 0).
Proof.
move=> N0 k0 d0 Ku ha.
exact: (quadric_certificate_excludes
  (reserve_weights_sum0 x H N0 k0 d0) (reserve_weights_moment0 x Ku)
  ha (reserve_certificate_margin x H N0 d0)).
Qed.

Corollary reserve_certificate_no_translated_fit N k d
    (x : paper_main_sample N d) (H : 'M[RR]_(k,d)) :
  (0 < N)%N -> (0 < k)%N -> (0 < d)%N ->
  centered_covariance H \in unitmx -> 0 < reserve_raw_margin x H ->
  forall (m : 'cV[RR]_d) (Q : 'M[RR]_d) (c : R),
    paper_main_psd Q -> Q != 0 ->
    ~ (forall i : 'I_(N+k), paper_main_quadratic_form Q
      (paper_main_point (sample_translate m (reserve_sample x H)) i) = c).
Proof.
move=> N0 k0 d0 Ku ha.
exact: (translated_sample_certificate_no_fit
  (reserve_weights_sum0 x H N0 k0 d0) (reserve_weights_moment0 x Ku)
  ha (reserve_certificate_margin x H N0 d0)).
Qed.
