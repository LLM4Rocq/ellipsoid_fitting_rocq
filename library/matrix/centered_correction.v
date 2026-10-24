From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import sesquilinear reals arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import psd_splitting.

(**md**************************************************************************)
(* # Correcting a linear moment with a centered sample matrix                 *)
(*                                                                            *)
(* H has k sample rows and d coordinate columns; b and the correction r      *)
(* are column vectors. All assertions are deterministic. The inverse bounds *)
(* hold on an explicit near-identity event, and the exact correction         *)
(* identities require invertibility of the centered covariance matrix.      *)
(*                                                                            *)
(* ```                                                                        *)
(* centering_ones k == the column of k ones                                   *)
(* centering_mx k == I - (1/k) 1 1^T                                         *)
(* centered_covariance H == H^T (centering_mx k) H                            *)
(* centered_potential H b == (centered_covariance H)^-1 b                     *)
(* centered_correction H b == (centering_mx k) H (centered_potential H b)     *)
(* ```                                                                        *)
(*                                                                            *)
(* The definitions use MathComp's total invmx. Exact moment reconstruction   *)
(* and inverse estimates require their stated hypotheses. Zero total mass   *)
(* holds without invertibility.                                              *)
(*                                                                            *)
(* The inverse bounds also apply to nonsymmetric square matrices and to     *)
(* zero column dimension. The independent example uses two opposite rows,   *)
(* for which the correction is exactly (b/2, -b/2).                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section inverse_bounds.
Variable R : realType.

Lemma opnorm_sub1_lower n (A : 'M[R]_n) :
  opnorm (A - 1%:M) <= 2^-1 ->
  forall x : 'cV[R]_n, frobenius x <= 2 * frobenius (A *m x).
Proof.
move=> near x.
have e : A *m x - (A - 1%:M) *m x = x.
  by rewrite -mulmxBl subKr mul1mx.
have h := frobeniusB (A *m x) ((A - 1%:M) *m x).
rewrite e in h.
have hE := frobenius_mulmx_opnorm (A - 1%:M) x.
have x0 := frobenius_ge0 x.
have : opnorm (A - 1%:M) * frobenius x <= 2^-1 * frobenius x.
  by rewrite ler_wpM2r.
by move=> hE'; nra.
Qed.

Lemma opnorm_sub1_unit n (A : 'M[R]_n) :
  opnorm (A - 1%:M) <= 2^-1 -> A \in unitmx.
Proof.
move=> near; rewrite -unitmx_tr -row_free_unit.
apply: inj_row_free => y y0.
have Ay0 : A *m y^T = 0.
  by apply/trmx_inj; rewrite trmx_mul trmxK y0 trmx0.
have hy := opnorm_sub1_lower near y^T.
rewrite Ay0 frobenius0 mulr0 frobenius_trmx in hy.
apply/eqP; rewrite -frobenius_eq0; apply/eqP/le_anti.
by rewrite hy frobenius_ge0.
Qed.

Lemma opnorm_inverse_near1 n (A : 'M[R]_n) :
  opnorm (A - 1%:M) <= 2^-1 -> opnorm (invmx A) <= 2.
Proof.
move=> near; have Au := opnorm_sub1_unit near.
apply/opnorm_leP; first by rewrite ler0n.
move=> x; have := opnorm_sub1_lower near (invmx A *m x).
by rewrite mulmxA mulmxV // mul1mx.
Qed.

Lemma opnorm_inverse_sub1 n (A : 'M[R]_n) :
  opnorm (A - 1%:M) <= 2^-1 ->
  opnorm (invmx A - 1%:M) <= 2 * opnorm (A - 1%:M).
Proof.
move=> near; have Au := opnorm_sub1_unit near.
have e : invmx A - 1%:M = invmx A *m (1%:M - A).
  by rewrite mulmxBr mulmx1 mulVmx.
rewrite e; apply: le_trans (opnorm_mulmx _ _) _.
rewrite -[1%:M - A]opprB opnormN.
by rewrite ler_wpM2r ?opnorm_ge0 //; exact: opnorm_inverse_near1.
Qed.

Lemma opnorm_scaled_unit n (A : 'M[R]_n) (a : R) :
  0 < a -> opnorm (a^-1 *: A - 1%:M) <= 2^-1 -> A \in unitmx.
Proof.
move=> a0 /opnorm_sub1_unit.
by rewrite unitmxZ // unitfE invr_eq0 gt_eqF.
Qed.

Lemma opnorm_scaled_inverse n (A : 'M[R]_n) (a : R) :
  0 < a -> opnorm (a^-1 *: A - 1%:M) <= 2^-1 ->
  opnorm (invmx A) <= 2 / a.
Proof.
move=> a0 near; have Au := opnorm_sub1_unit near.
have := opnorm_inverse_near1 near.
rewrite (invmxZ Au) invrK opnormZ (ger0_norm (ltW a0)).
by rewrite ler_pdivlMr // mulrC.
Qed.

Lemma opnorm_scaled_inverse_sub n (A : 'M[R]_n) (a : R) :
  0 < a -> opnorm (a^-1 *: A - 1%:M) <= 2^-1 ->
  opnorm (invmx A - a^-1%:M) <=
    2 * opnorm (a^-1 *: A - 1%:M) / a.
Proof.
move=> a0 near; have Au := opnorm_sub1_unit near.
have e : a *: (invmx A - a^-1%:M) = invmx (a^-1 *: A) - 1%:M.
  rewrite invmxZ // invrK scalerBr scale_scalar_mx mulfV ?gt_eqF //.
have := opnorm_inverse_sub1 near.
rewrite -e opnormZ (ger0_norm (ltW a0)).
by rewrite ler_pdivlMr // mulrC.
Qed.

End inverse_bounds.

Section definitions.
Variable R : realType.

Definition centering_ones k : 'cV[R]_k := const_mx 1.

Definition centering_mx k : 'M[R]_k :=
  1%:M - k%:R^-1 *: (centering_ones k *m (centering_ones k)^T).

Definition centered_covariance k d (H : 'M[R]_(k, d)) : 'M[R]_d :=
  H^T *m centering_mx k *m H.

Definition centered_potential k d (H : 'M[R]_(k, d)) (b : 'cV[R]_d) :=
  invmx (centered_covariance H) *m b.

Definition centered_correction k d (H : 'M[R]_(k, d)) (b : 'cV[R]_d) :=
  centering_mx k *m H *m centered_potential H b.

End definitions.

Arguments centering_ones {R} k.
Arguments centering_mx {R} k.

Section centering.
Variable R : realType.

Lemma centering_ones_gram k :
  (centering_ones k)^T *m centering_ones k = k%:R%:M :> 'M[R]_1.
Proof.
apply/matrixP => i j; rewrite !ord1 /centering_ones !mxE.
under eq_bigr do rewrite !mxE mulr1.
by rewrite sumr_const card_ord eqxx /=.
Qed.

Lemma centering_symmetric k : (centering_mx k : 'M[R]_k) \is symmetricmx.
Proof.
apply/symmetricmxP.
by rewrite /centering_mx linearB /= trmx1 linearZ /= trmx_mul trmxK.
Qed.

Lemma centering_mass k : (0 < k)%N ->
  (centering_ones k)^T *m centering_mx k = 0 :> 'rV[R]_k.
Proof.
move=> k0; have kr0 : (k%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite /centering_mx mulmxBr mulmx1 -scalemxAr mulmxA centering_ones_gram.
by rewrite mul_scalar_mx scalerA mulVf // scale1r subrr.
Qed.

Lemma centering_idempotent k : (0 < k)%N ->
  centering_mx k *m centering_mx k = centering_mx k :> 'M[R]_k.
Proof.
move=> k0.
by rewrite {1}/centering_mx mulmxBl mul1mx -scalemxAl -mulmxA
  centering_mass // mulmx0 scaler0 subr0.
Qed.

Lemma centering_orthoproj k : (0 < k)%N ->
  orthoprojmx (centering_mx k : 'M[R]_k).
Proof. by move=> k0; split; [exact: centering_symmetric | exact: centering_idempotent]. Qed.

Lemma centering_column_sum k (z : 'cV[R]_k) :
  ((centering_ones k)^T *m z) 0 0 = \sum_i z i 0.
Proof.
rewrite mxE; apply: eq_bigr => i _.
by rewrite /centering_ones !mxE mul1r.
Qed.

End centering.

Section correction.
Variables (R : realType) (k d : nat) (H : 'M[R]_(k, d)).

Lemma centered_correction_mass (b : 'cV[R]_d) : (0 < k)%N ->
  (centering_ones k)^T *m centered_correction H b = 0.
Proof.
by move=> k0; rewrite /centered_correction !mulmxA centering_mass // !mul0mx.
Qed.

Lemma centered_correction_sum (b : 'cV[R]_d) : (0 < k)%N ->
  \sum_i centered_correction H b i 0 = 0.
Proof.
by move=> k0; rewrite -centering_column_sum centered_correction_mass // mxE.
Qed.

Lemma centered_correction_moment (b : 'cV[R]_d) :
  centered_covariance H \in unitmx ->
  H^T *m centered_correction H b = b.
Proof.
move=> Ku.
by rewrite /centered_correction /centered_potential !mulmxA
  -/centered_covariance mulmxV // mul1mx.
Qed.

Lemma centered_correction_energy (b : 'cV[R]_d) : (0 < k)%N ->
  centered_covariance H \in unitmx ->
  frobenius (centered_correction H b) ^+ 2 =
    mxdot b (centered_potential H b).
Proof.
move=> k0 Ku.
rewrite /centered_correction frobenius_sqr mxdot_mulmxl trmx_mul.
rewrite (symmetricmxP _ (@centering_symmetric R k)) !mulmxA
  -(mulmxA H^T (centering_mx k) (centering_mx k))
  centering_idempotent // -/centered_covariance.
change (mxdot (centered_potential H b)
  (centered_covariance H *m invmx (centered_covariance H) *m b) =
  mxdot b (centered_potential H b)).
by rewrite mulmxV // mul1mx mxdotC.
Qed.

Lemma centered_potential_bound (b : 'cV[R]_d) : (0 < k)%N ->
  opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <= 2^-1 ->
  frobenius (centered_potential H b) <= 2 * frobenius b / k%:R.
Proof.
move=> k0 near; have kr0 : (0 : R) < k%:R by rewrite ltr0n.
rewrite /centered_potential.
apply: le_trans (frobenius_mulmx_opnorm _ _) _.
rewrite mulrAC ler_wpM2r ?frobenius_ge0 //.
exact: opnorm_scaled_inverse kr0 near.
Qed.

Lemma centered_potential_approx (b : 'cV[R]_d) : (0 < k)%N ->
  opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <= 2^-1 ->
  frobenius (centered_potential H b - k%:R^-1 *: b) <=
    2 * opnorm (k%:R^-1 *: centered_covariance H - 1%:M) *
      frobenius b / k%:R.
Proof.
move=> k0 near; have kr0 : (0 : R) < k%:R by rewrite ltr0n.
rewrite /centered_potential -mul_scalar_mx -mulmxBl.
apply: le_trans (frobenius_mulmx_opnorm _ _) _.
rewrite mulrAC ler_wpM2r ?frobenius_ge0 //.
exact: opnorm_scaled_inverse_sub kr0 near.
Qed.

Theorem centered_correction_bounds (b : 'cV[R]_d) : (0 < k)%N ->
  opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <= 2^-1 ->
  [/\ centered_covariance H \in unitmx,
      (centering_ones k)^T *m centered_correction H b = 0,
      H^T *m centered_correction H b = b &
      frobenius (centered_correction H b) ^+ 2 <=
        2 * frobenius b ^+ 2 / k%:R].
Proof.
move=> k0 near; have kr0 : (0 : R) < k%:R by rewrite ltr0n.
have Ku := opnorm_scaled_unit kr0 near.
split; [exact: Ku | exact: centered_correction_mass |
  exact: centered_correction_moment |].
rewrite centered_correction_energy // /centered_potential.
apply: le_trans (ler_norm _) _.
apply: le_trans (mxdot_opnorm _ _ _) _.
have h := opnorm_scaled_inverse kr0 near.
rewrite -mulrA -expr2.
by rewrite mulrAC ler_wpM2r ?sqr_ge0.
Qed.

End correction.

Section example.
Variable R : realType.

(* Two opposite observations have K = 2 I and correction (b/2, -b/2). *)
Example two_rows_centered_correction (b : 'cV[R]_1) :
  let H : 'M[R]_(2, 1) := \col_i (if i == 0 then 1 else -1) in
  centered_correction H b = 2^-1 *: (H *m b).
Proof.
move=> H.
have mass : (centering_ones 2)^T *m H = 0.
  apply/matrixP => i j; rewrite !ord1 mxE /centering_ones /H.
  by rewrite !big_ord_recr big_ord0 /= !mxE /=; ring.
have PH : centering_mx 2 *m H = H.
  by rewrite /centering_mx mulmxBl mul1mx -scalemxAl -mulmxA mass
    mulmx0 scaler0 subr0.
have K : centered_covariance H = 2%:M.
  rewrite /centered_covariance -mulmxA PH.
  apply/matrixP => i j; rewrite !ord1 mxE /H.
  by rewrite !big_ord_recr big_ord0 /= !mxE /=; ring.
by rewrite /centered_correction PH /centered_potential K invmx_scalar
  mul_scalar_mx -scalemxAr.
Qed.

End example.
