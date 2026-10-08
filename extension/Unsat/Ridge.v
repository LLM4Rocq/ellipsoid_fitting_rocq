(* Removing the ridge: Lemma 2.12 of Koehler and Sohn (arXiv 2608.27372,
   lines 1476-1494 of arxiv_v1.tex, proof lines 4598-4833), in the
   vocabulary of lane B (library/convex/least_squares.v and
   Unsat/LeastSquares.v): features are row vectors of size d * d, the
   objective is ls_objective, the values are unsat_ridge_value and
   unsat_value, the domain is unsat_domain d = R_d^o, the positive definite
   matrices of trace d, and the ridge weight is unsat_lambda kappa d, the
   operator norm of Sigma_kappa = unsat_cov kappa d.

   Proved, for kappa > 1:
   - The covariance: unsat_cov_formE, theta Sigma_kappa theta'^T is
     C_kappa (vec_mx theta, vec_mx theta') (unsat_cov_form, bilinear and
     symmetric: unsat_cov_formC, unsat_cov_formDl, unsat_cov_formZl,
     unsat_cov_form_suml); unsat_cov_sym, Sigma_kappa is symmetric;
     unsat_cov_coercive and unsat_cov_form_le_sym, for A symmetric
     min (2, kappa - 1) / d |A|^2 <= C_kappa(A, A)
       <= max (2, kappa - 1) / d |A|^2
     (eq:feature-covariance-coercivity), and unsat_cov_form_bounds, the
     upper bound for every A through its symmetric part
     (unsat_cov_form_sym_part); unsat_lambda_le, lambda <= max (2, kappa -
     1) / d; unsat_cov_form1, C_kappa(I, I) = kappa - 1.
   - The localization, unsat_ridge_gap_le, deterministic: if every theta in
     R_d and b with scale C_kappa(theta, theta) + b^2 >= s^2
     (unsat_scale) satisfy
       (1/n) sum_i (<Z_i, theta> - b)^2 >= c (C_kappa(theta, theta) + b^2),
     and (1/n) sum_i <Z_i, I>^2 <= B < c s^2, then for every beta >= 0
       unsat_ridge_value kappa n d beta Z - unsat_value n d Z
         <= beta (max (2, kappa - 1) / min (2, kappa - 1) + 1) s^2.
     Near-minimizers of the unregularized problem are used, so no
     minimizer, compactness or density argument is needed; the ridge term
     is bounded through unsat_lambda_coercive,
     lambda |theta|^2 <= max / min C_kappa(theta, theta) on R_d.

   - The augmented features: aug_feature z = (z, -1) and aug_param theta
     b = (theta, b) turn the affine forms <z, theta> - b into linear forms
     (mxdot_aug), of covariance aug_cov Sigma = diag (Sigma, 1)
     (aug_cov_form).
   - The moments of the affine forms when mu is a regular_feature K tau
     with covariance Sigma_kappa: rf_affine_sqr, E (<z, theta> - b)^2 =
     C_kappa(theta, theta) + b^2; rf_affine_pow4, on R_d the fourth moment
     is at most ridge_moment_const kappa K = 8 max (K^4 (max / min)^2, 1)
     times the square of the second, from (F1); rf_form_centered and
     rf_identity_sqr, E <z, I>^2 = kappa - 1.
   - Lemma 4.3 as a Rademacher majorant: ridge_rademacher_bound, for theta
     in R_d of scale C_kappa(theta, theta) + b^2 at least s^2 and signs
     eps,
       |(1/n) sum_k eps_k (<x_k, theta> - b)|
         <= sqrt (C_kappa(theta, theta) + b^2)
              (d / s (1/n) N + |(1/n) sum_k eps_k|)
     whenever N bounds the operator norm of the symmetric part of
     sum_k eps_k vec_mx x_k; ridge_rate, the expectation of this majorant
     for the N of opnorm_sum_subexponential (matrix/random_opnorm.v), with
     Khintchine's inequality for the mean of the signs; ridge_rate_le, its
     operator norm part is at most 96 L0 (2 + 8 / alpha) / s when
     n >= alpha d^2 / 2 and the subexponential constant is L0 / sqrt d.
     The paper has an extra sqrt (log d) from the matrix Bernstein
     inequality.
   - unsat_ridge_gap_prob, for one dimension: for s > 0 and beta >= 0,
     outside an event of probability at most
       512 Kq / 9 r + 1024 Kq (kappa - 1) / (9 s^2),
     with Kq = ridge_moment_const kappa K and r the bound of ridge_rate,
     the ridge adds at most beta (max / min + 1) s^2. The event is the
     union of the failure of small_ball_linear
     (probability/small_ball_method.v) for the affine forms of scale at
     least s^2 and of Markov's inequality for (1/n) sum_i <Z_i, I>^2
     (ridge_markov_identity), at the level c s^2 / 2 with
     c = 9 / (512 Kq).
   - unsat_ridge_removal, Lemma 2.12 in the form that Unsat/Regularized
     (lane B) uses: for features of regular laws mu d (regular_feature
     with covariance unsat_cov kappa d) whose quadratic forms
     z |-> <z, mxvec (v^T v)> (|v| <= 1) are subexponential with constant
     L0 / sqrt d, both for d >= 1 (neither can hold at d = 0),
     n / d^2 -> alpha > 0, measurable gap events and beta d >= 0, the
     probability that unsat_ridge_value - unsat_value exceeds
     C beta d ln d tends to 0, with C = max / min + 1. ln is the logarithm
     of MathComp-Analysis. For a given eps the proof takes a constant s,
     large enough for the bound above to be below eps once
     n d >= alpha d^2 / 2, n d is large and ln d >= s^2, so no limit along
     s_d^2 = ln d is needed. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis Require Import euclidean real_spectral opnorm.
From GaussianAnalysis Require Import least_squares.
From GaussianAnalysis Require Import logdet_barrier gordon gauss_linear.
From GaussianAnalysis Require Import measurable_matrix lindeberg.
From GaussianAnalysis Require Import symmetrization efron_stein subgaussian.
From GaussianAnalysis Require Import random_opnorm small_ball_method.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section covariance.

Lemma unsat_cov_formC (kappa : R) d (A B : 'M[R]_d) :
  unsat_cov_form kappa d A B = unsat_cov_form kappa d B A.
Proof.
rewrite /unsat_cov_form (mxdotC A B) -[mxdot A B^T]mxdot_trmx trmxK.
rewrite (mxdotC A^T B).
by under eq_bigr do rewrite mulrC.
Qed.

Lemma unsat_cov_formDl (kappa : R) d (A A' B : 'M[R]_d) :
  unsat_cov_form kappa d (A + A') B =
  unsat_cov_form kappa d A B + unsat_cov_form kappa d A' B.
Proof.
rewrite /unsat_cov_form ?RplusE ?RmultE ?RminusE !mxdotDl.
under eq_bigr do rewrite mxE mulrDl.
by rewrite big_split /=; ring.
Qed.

Lemma unsat_cov_formZl (kappa a : R) d (A B : 'M[R]_d) :
  unsat_cov_form kappa d (a *: A) B = a * unsat_cov_form kappa d A B.
Proof.
rewrite /unsat_cov_form ?RplusE ?RmultE ?RminusE !mxdotZl.
under eq_bigr do rewrite mxE -mulrA.
by rewrite -mulr_sumr; ring.
Qed.

Lemma unsat_cov_form_suml (kappa : R) d n (c : 'I_n -> R)
    (A : 'I_n -> 'M[R]_d) (B : 'M[R]_d) :
  unsat_cov_form kappa d (\sum_(q < n) c q *: A q) B =
  \sum_(q < n) c q * unsat_cov_form kappa d (A q) B.
Proof.
elim/big_rec2: _ => [|q y z _ <-]; last first.
  by rewrite unsat_cov_formDl unsat_cov_formZl.
have -> : (0 : 'M[R]_d) = 0 *: 0 by rewrite scale0r.
by rewrite unsat_cov_formZl mul0r.
Qed.

(* The matrix unsat_cov represents the form unsat_cov_form. *)
Lemma unsat_cov_formE (kappa : R) d (x y : 'rV[R]_(d * d)) :
  mxdot (x *m unsat_cov kappa d) y =
  unsat_cov_form kappa d (vec_mx x) (vec_mx y).
Proof.
have vsum (u : 'rV[R]_(d * d)) :
    vec_mx u = \sum_(q < d * d) u 0 q *: vec_mx (delta_mx 0 q).
  apply/matrixP => i j; rewrite summxE !mxE.
  rewrite (bigD1 (mxvec_index i j))//=.
  rewrite mxE vec_mx_delta mxE !eqxx /= mulr1 big1 ?addr0// => q qij.
  by rewrite !mxE eqxx /= eq_sym (negbTE qij) mulr0.
rewrite (vsum x) (vsum y) unsat_cov_form_suml /mxdot big_ord1.
under eq_bigr do rewrite mxE mulr_suml.
rewrite exchange_big /=; apply: eq_bigr => q _.
rewrite unsat_cov_formC unsat_cov_form_suml mulr_sumr.
apply: eq_bigr => p _; rewrite unsat_cov_formC /unsat_cov mxE.
by ring.
Qed.

Lemma unsat_cov_sym (kappa : R) d : unsat_cov kappa d \is symmetricmx.
Proof.
by apply/symmetricmxP/matrixP => p q; rewrite !mxE unsat_cov_formC.
Qed.

Lemma diag_sqr_le d (A : 'M[R]_d) :
  0 <= \sum_(j < d) A j j ^+ 2 <= mxdot A A.
Proof.
apply/andP; split; first by apply: sumr_ge0 => j _; exact: sqr_ge0.
rewrite /mxdot; apply: ler_sum => i _.
rewrite (bigD1 i)//= -expr2 lerDl.
by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
Qed.

(* C_kappa on a symmetric matrix A, with diagonal part D = sum_j A_jj^2:
   (2 (|A|^2 - D) + (kappa - 1) D) / d. *)
Lemma unsat_cov_form_symE (kappa : R) d (A : 'M[R]_d) : A^T = A ->
  unsat_cov_form kappa d A A = d%:R^-1 *
    (2 * (mxdot A A - \sum_(j < d) A j j ^+ 2) +
     (kappa - 1) * \sum_(j < d) A j j ^+ 2).
Proof.
move=> AT; rewrite /unsat_cov_form ?RplusE ?RmultE ?RminusE AT.
under [in RHS]eq_bigr do rewrite expr2.
by ring.
Qed.

(* eq:feature-covariance-coercivity *)
Lemma unsat_cov_coercive (kappa : R) d (A : 'M[R]_d) : 1 < kappa -> A^T = A ->
  Num.min 2 (kappa - 1) / d%:R * mxdot A A <= unsat_cov_form kappa d A A.
Proof.
move=> k1 AT; rewrite unsat_cov_form_symE//.
have /andP[D0 DM] := diag_sqr_le d A.
set D := \sum_(j < d) A j j ^+ 2 in D0 DM *.
set M := mxdot A A in DM *.
have m2 : Num.min 2 (kappa - 1) <= 2 by rewrite ge_min lexx.
have mk : Num.min 2 (kappa - 1) <= kappa - 1 by rewrite ge_min lexx orbT.
rewrite mulrAC [X in _ <= X]mulrC; apply: ler_wpM2r; first by rewrite invr_ge0.
nra.
Qed.

Lemma unsat_cov_form_le_sym (kappa : R) d (A : 'M[R]_d) : 1 < kappa ->
  A^T = A ->
  unsat_cov_form kappa d A A <= Num.max 2 (kappa - 1) / d%:R * mxdot A A.
Proof.
move=> k1 AT; rewrite unsat_cov_form_symE//.
have /andP[D0 DM] := diag_sqr_le d A.
set D := \sum_(j < d) A j j ^+ 2 in D0 DM *.
set M := mxdot A A in DM *.
have m2 : 2 <= Num.max 2 (kappa - 1) by rewrite le_max lexx.
have mk : kappa - 1 <= Num.max 2 (kappa - 1) by rewrite le_max lexx orbT.
rewrite mulrAC [X in X <= _]mulrC; apply: ler_wpM2r; first by rewrite invr_ge0.
nra.
Qed.

(* C_kappa (A, A) only depends on the symmetric part of A. *)
Lemma unsat_cov_form_sym_part (kappa : R) d (A : 'M[R]_d) :
  unsat_cov_form kappa d A A =
  unsat_cov_form kappa d (2^-1 *: (A + A^T)) (2^-1 *: (A + A^T)).
Proof.
set S := 2^-1 *: (A + A^T).
have ST : S^T = S by rewrite /S linearZ /= linearD /= trmxK addrC.
have eSS : mxdot S S = 2^-1 * (mxdot A A + mxdot A A^T).
  rewrite /S mxdotZl mxdotZr !mxdotDl !mxdotDr (mxdotC A^T A) mxdot_trmx.
  by field.
have eD : \sum_(j < d) S j j * S j j = \sum_(j < d) A j j * A j j.
  by apply: eq_bigr => j _; rewrite /S !mxE; field.
rewrite /unsat_cov_form ?RplusE ?RmultE ?RminusE ST eSS eD.
by congr (_ * _); field.
Qed.

Lemma unsat_cov_form_bounds (kappa : R) d (A : 'M[R]_d) : 1 < kappa ->
  0 <= unsat_cov_form kappa d A A <= Num.max 2 (kappa - 1) / d%:R * mxdot A A.
Proof.
move=> k1; rewrite unsat_cov_form_sym_part.
set S := 2^-1 *: (A + A^T).
have ST : S^T = S by rewrite /S linearZ /= linearD /= trmxK addrC.
have SA : mxdot S S <= mxdot A A.
  have -> : mxdot S S = 2^-1 * (mxdot A A + mxdot A A^T).
    rewrite /S mxdotZl mxdotZr !mxdotDl !mxdotDr (mxdotC A^T A) mxdot_trmx.
    by field.
  have h := mxdot_le A A^T; rewrite frobenius_trmx -expr2 frobenius_sqr in h.
  move: h; rewrite ler_norml => /andP[_ h].
  by have := mxdot_ge0 A; lra.
have k0 : 0 <= kappa - 1 by rewrite subr_ge0 ltW.
apply/andP; split.
  apply: le_trans (unsat_cov_coercive kappa d S k1 ST).
  apply: mulr_ge0; last exact: mxdot_ge0.
  by apply: divr_ge0; [rewrite le_min k0 andbT|exact: ler0n].
apply: le_trans (unsat_cov_form_le_sym kappa d S k1 ST) _.
apply: ler_wpM2l SA.
by apply: divr_ge0; [rewrite le_max k0 orbT|exact: ler0n].
Qed.

(* lambda = opnorm Sigma_kappa <= max (2, kappa - 1) / d. *)
Lemma unsat_lambda_le (kappa : R) d : 1 < kappa ->
  unsat_lambda kappa d <= Num.max 2 (kappa - 1) / d%:R.
Proof.
move=> k1.
have k0 : 0 <= kappa - 1 by rewrite subr_ge0 ltW.
have b0 : 0 <= Num.max 2 (kappa - 1) / d%:R.
  by apply: divr_ge0; [rewrite le_max k0 orbT|exact: ler0n].
rewrite /unsat_lambda; apply/(opnorm_symP (unsat_cov_sym kappa d) b0) => x.
have -> : mxdot x (unsat_cov kappa d *m x) =
    mxdot (x^T *m unsat_cov kappa d) x^T.
  rewrite -mxdot_trmx trmx_mul.
  by have /symmetricmxP -> := unsat_cov_sym kappa d; rewrite mxdotC.
rewrite unsat_cov_formE -(mxdot_trmx x x) -mxdot_vec_mx.
have /andP[h0 h1] := unsat_cov_form_bounds kappa d (vec_mx x^T) k1.
by rewrite ger0_norm.
Qed.

(* C_kappa(I, I) = kappa - 1. *)
Lemma unsat_cov_form1 (kappa : R) d : (0 < d)%N ->
  unsat_cov_form kappa d 1%:M 1%:M = kappa - 1.
Proof.
move=> d0.
have e1 : mxdot (1%:M : 'M[R]_d) 1%:M = d%:R.
  by rewrite mxdot_trace trmx1 mulmx1 mxtrace1.
have e2 : \sum_(j < d) (1%:M : 'M[R]_d) j j * (1%:M : 'M[R]_d) j j = d%:R.
  by under eq_bigr do rewrite mxE eqxx mulr1; rewrite sumr_const card_ord.
have dne : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite /unsat_cov_form ?RplusE ?RmultE ?RminusE trmx1 e1 e2.
by field.
Qed.

End covariance.

Section localization.

(* C_kappa (theta, theta) + b^2, the variance of <Z, theta> - b. *)
Definition unsat_scale (kappa : R) d (theta : 'rV[R]_(d * d)) (b : R) : R :=
  mxdot (theta *m unsat_cov kappa d) theta + b ^+ 2.

Lemma unsat_domain1 d : (0 < d)%N -> unsat_domain d (mxvec (1%:M : 'M[R]_d)).
Proof.
move=> d0; rewrite /unsat_domain /pd_slice /= mxvecK mxtrace1; split => //.
split; first by apply/symmetricmxP; rewrite trmx1.
by move=> x x0; rewrite mulmx1 mxdot_gt0.
Qed.

(* lambda |theta|^2 <= max / min C_kappa(theta, theta) on the domain. *)
Lemma unsat_lambda_coercive (kappa : R) d (theta : 'rV[R]_(d * d)) :
  1 < kappa -> unsat_domain d theta ->
  unsat_lambda kappa d * mxdot theta theta <=
  Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1) *
  mxdot (theta *m unsat_cov kappa d) theta.
Proof.
move=> k1 [[Ssym _] _].
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have m0 : 0 < Num.min 2 (kappa - 1) by rewrite lt_min k0 andbT.
have mne : Num.min 2 (kappa - 1) != 0 by rewrite gt_eqF.
have M0 : 0 <= Num.max 2 (kappa - 1) by rewrite le_max ltW.
have /symmetricmxP AT := Ssym.
have hc := unsat_cov_coercive kappa d (vec_mx theta) k1 AT.
rewrite mxdot_vec_mx -unsat_cov_formE in hc.
apply: le_trans (ler_wpM2r (mxdot_ge0 theta) (unsat_lambda_le kappa d k1)) _.
apply: (@le_trans _ _ (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1) *
  (Num.min 2 (kappa - 1) / d%:R * mxdot theta theta))).
  rewrite [X in _ <= X]mulrA -[(_ / _ * (_ / _))%R]mulrA (mulKf mne).
  exact: lexx.
by apply: ler_wpM2l hc; rewrite divr_ge0// ltW.
Qed.

(* The localization: if the affine forms of scale at least s have
   empirical second moments at least c times their scale, and the
   empirical second moment at the identity is at most B < c s^2, then the
   ridge adds at most beta (max / min + 1) s^2. *)
Lemma unsat_ridge_gap_le (kappa : R) n d (beta c s B : R)
    (Z : n.-tuple 'rV[R]_(d * d)) :
  1 < kappa -> (0 < n)%N -> (0 < d)%N -> 0 <= beta -> 0 < s ->
  (forall theta b, unsat_domain d theta ->
     s ^+ 2 <= unsat_scale kappa d theta b ->
     c * unsat_scale kappa d theta b <=
     n%:R^-1 * \sum_(i < n) (mxdot (tnth Z i) theta - b) ^+ 2) ->
  n%:R^-1 * \sum_(i < n) mxdot (tnth Z i) (mxvec 1%:M) ^+ 2 <= B ->
  B < c * s ^+ 2 ->
  unsat_ridge_value kappa n d beta Z - unsat_value n d Z <=
    beta * (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1) + 1) * s ^+ 2.
Proof.
move=> k1 n0 d0 b0 s0 hsb hB Bc.
set lam := unsat_lambda kappa d.
have lam0 : 0 <= lam by exact: opnorm_ge0.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have m0 : 0 < Num.min 2 (kappa - 1) by rewrite lt_min k0 andbT.
set Cst := Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1).
have Cst1 : 1 <= Cst.
  by rewrite /Cst ler_pdivlMr// mul1r ge_min !le_max lexx.
have nR : (0 < n%:R :> R) by rewrite ltr0n.
have nne : n%:R != 0 :> R by rewrite gt_eqF.
have obj0 theta b : ls_objective Z 0 0 theta b =
    (n%:R *+ 2)^-1 * \sum_(i < n) (b - mxdot (tnth Z i) theta) ^+ 2.
  by rewrite /ls_objective !mul0r addr0.
have objb theta b : ls_objective Z lam beta theta b =
    ls_objective Z 0 0 theta b + beta * (lam * mxdot theta theta + b ^+ 2).
  by rewrite obj0.
have obj_ge0 l bt theta b :
    0 <= l -> 0 <= bt -> 0 <= ls_objective Z l bt theta b.
  move=> l0 bt0; rewrite /ls_objective; apply: addr_ge0.
    apply: mulr_ge0; first by rewrite invr_ge0.
    by apply: sumr_ge0 => i _; exact: sqr_ge0.
  by apply: mulr_ge0 => //; apply: addr_ge0; [apply: mulr_ge0|exact: sqr_ge0];
    rewrite // mxdot_ge0.
have hS l bt : 0 <= l -> 0 <= bt -> has_lbound
    [set ls_objective Z l bt theta b | theta in unsat_domain d & b in [set: R]].
  by move=> l0 bt0; exists 0 => _ [theta _ [b _ <-]]; exact: obj_ge0.
have I0 := unsat_domain1 d d0.
have hS0n : [set ls_objective Z 0 0 theta b |
    theta in unsat_domain d & b in [set: R]] !=set0.
  exists (ls_objective Z 0 0 (mxvec 1%:M) 0).
  by exists (mxvec 1%:M) => //; exists 0.
have B0 : 0 <= B.
  apply: le_trans hB; apply: mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
(* the identity bounds the unregularized value *)
have hI : unsat_value n d Z <= B / 2.
  rewrite /unsat_value /ls_value.
  apply: le_trans (ge_inf (hS 0 0 (lexx 0) (lexx 0)) _) _.
    by exists (mxvec 1%:M) => //; exists 0.
  under eq_bigr do rewrite sub0r sqrrN.
  set S := \sum_(i < n) _ in hB *.
  have -> : (n%:R *+ 2)^-1 * S = (n%:R^-1 * S) / 2.
    by rewrite -mulr_natr; field.
  lra.
have c0 : 0 < c.
  have s20 : 0 < s ^+ 2 by rewrite exprn_gt0.
  by rewrite -(pmulr_lgt0 _ s20); apply: le_lt_trans Bc.
(* a near-minimizer (theta, b) of the unregularized problem *)
rewrite lerBlDr; apply/ler_addgt0Pr => e e0.
pose eps := Num.min e ((c * s ^+ 2 - B) / 4).
have eps0 : 0 < eps by rewrite lt_min e0 divr_gt0// subr_gt0.
have epse : eps <= e by rewrite ge_min lexx.
have epsB : eps <= (c * s ^+ 2 - B) / 4 by rewrite ge_min lexx orbT.
have [y [theta Dt [b _ <-]] hy] : exists2 y, [set ls_objective Z 0 0 theta b |
    theta in unsat_domain d & b in [set: R]] y & y < unsat_value n d Z + eps.
  by apply: inf_lt => //; rewrite /unsat_value /ls_value; lra.
have e2 : n%:R^-1 * \sum_(i < n) (mxdot (tnth Z i) theta - b) ^+ 2 =
    2 * ls_objective Z 0 0 theta b.
  rewrite obj0.
  have -> : \sum_(i < n) (b - mxdot (tnth Z i) theta) ^+ 2 =
      \sum_(i < n) (mxdot (tnth Z i) theta - b) ^+ 2.
    by apply: eq_bigr => i _; rewrite -sqrrN opprB.
  by rewrite -mulr_natr; field.
(* its scale is below s^2 *)
have hsc : unsat_scale kappa d theta b < s ^+ 2.
  rewrite ltNge; apply/negP => hs.
  have h := hsb theta b Dt hs.
  have h2 : c * s ^+ 2 <= c * unsat_scale kappa d theta b by rewrite ler_pM2l.
  by rewrite e2 in h; lra.
have Cge0 : 0 <= mxdot (theta *m unsat_cov kappa d) theta.
  rewrite unsat_cov_formE.
  by have /andP[] := unsat_cov_form_bounds kappa d (vec_mx theta) k1.
have hlam := unsat_lambda_coercive kappa d theta k1 Dt.
(* hence its ridge term is O(s^2) *)
have hreg : lam * mxdot theta theta + b ^+ 2 <= (Cst + 1) * s ^+ 2.
  move: hsc; rewrite /unsat_scale => hsc.
  have b2 := sqr_ge0 b.
  have Cst0 : 0 <= Cst by apply: le_trans Cst1; exact: ler01.
  rewrite -/lam -/Cst in hlam; rewrite RplusE in hsc.
  nra.
apply: le_trans (ge_inf (hS lam beta lam0 b0) _) _.
  by exists theta => //; exists b.
have := ler_wpM2l b0 hreg.
set t := mxdot theta theta.
lra.
Qed.

End localization.

Section augmented.
Context {RT : realType}.

Lemma mxdot_row_mx m n1 n2 (a c : 'M[RT]_(m, n1)) (b e : 'M[RT]_(m, n2)) :
  mxdot (row_mx a b) (row_mx c e) = mxdot a c + mxdot b e.
Proof. by rewrite !mxdot_trace tr_row_mx mul_row_col mxtraceD. Qed.

(* The affine form <z, theta> - b is the linear form of (theta, b) at the
   augmented feature (z, -1). *)
Definition aug_feature N (z : 'rV[RT]_N) : 'rV[RT]_(N + 1) :=
  row_mx z (const_mx (-1)).

Definition aug_param N (theta : 'rV[RT]_N) (b : RT) : 'rV[RT]_(N + 1) :=
  row_mx theta (const_mx b).

Definition aug_cov N (S : 'M[RT]_N) : 'M[RT]_(N + 1) := block_mx S 0 0 1%:M.

Arguments aug_feature {N} z.
Arguments aug_param {N} theta b.
Arguments aug_cov {N} S.

Lemma mxdot_aug N (z theta : 'rV[RT]_N) (b : RT) :
  mxdot (aug_feature z) (aug_param theta b) = mxdot z theta - b.
Proof.
rewrite /aug_feature /aug_param mxdot_row_mx; congr (_ + _).
by rewrite /mxdot !big_ord1 !mxE mulN1r.
Qed.

Lemma aug_cov_form N (S : 'M[RT]_N) (theta : 'rV[RT]_N) (b : RT) :
  mxdot (aug_param theta b *m aug_cov S) (aug_param theta b) =
  mxdot (theta *m S) theta + b ^+ 2.
Proof.
rewrite /aug_param /aug_cov mul_row_block !mulmx0 addr0 add0r mulmx1.
rewrite mxdot_row_mx; congr (_ + _).
by rewrite /mxdot !big_ord1 !mxE expr2.
Qed.

Lemma mxdot_aug_feature N (z : 'rV[RT]_N) (p : 'rV[RT]_(N + 1)) :
  mxdot (aug_feature z) p = mxdot z (lsubmx p) - rsubmx p 0 0.
Proof.
rewrite -{1}[p]hsubmxK /aug_feature mxdot_row_mx; congr (_ + _).
by rewrite /mxdot !big_ord1 !mxE mulN1r.
Qed.

Lemma aug_paramK N (p : 'rV[RT]_(N + 1)) :
  aug_param (lsubmx p) (rsubmx p 0 0) = p.
Proof.
rewrite /aug_param -[RHS]hsubmxK; congr row_mx.
by apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE.
Qed.

Lemma aug_param_lsub N (theta : 'rV[RT]_N) (b : RT) :
  lsubmx (aug_param theta b) = theta.
Proof. exact: row_mxKl. Qed.

Lemma aug_param_rsub N (theta : 'rV[RT]_N) (b : RT) :
  rsubmx (aug_param theta b) 0 0 = b.
Proof. by rewrite /aug_param row_mxKr mxE. Qed.

(* The quadratic form v^T A v is the Frobenius product of A with v v^T. *)
Lemma mxdot_form_col n (A : 'M[RT]_n) (v : 'cV[RT]_n) :
  mxdot v (A *m v) = mxdot A (v *m v^T).
Proof. by rewrite mxdot_outer mxdot_colE mulmxA. Qed.

End augmented.
Arguments aug_feature {RT N} z.
Arguments aug_param {RT N} theta b.
Arguments aug_cov {RT N} S.

Section ridge_constants.
Context {RT : realType}.

(* The constant of the fourth moments of the affine forms on R_d. *)
Definition ridge_moment_const (kappa K : RT) : RT :=
  8 * Num.max (K ^+ 4 *
    (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1)) ^+ 2) 1.

Lemma ridge_moment_const_gt0 (kappa K : RT) : 0 < ridge_moment_const kappa K.
Proof. by rewrite /ridge_moment_const mulr_gt0// lt_max ltr01 orbT. Qed.

(* When n >= alpha d^2 / 2, the operator norm part of the rate of the
   small-ball method is O(1 / s), for subexponential constants
   L0 / sqrt d. *)
Lemma ridge_rate_le (alpha L0 s : RT) n d :
  0 < alpha -> 0 < L0 -> 0 < s -> (0 < d)%N ->
  alpha * d%:R ^+ 2 <= 2 * n%:R ->
  d%:R / s * (n%:R^-1 * (96 * (L0 / Num.sqrt d%:R) *
    (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R))) <=
  96 * L0 * (2 + 8 / alpha) / s.
Proof.
move=> a0 L0p s0 d0 hn.
set u := Num.sqrt d%:R.
have u0 : 0 < u by rewrite sqrtr_gt0 ltr0n.
have u1 : 1 <= u by rewrite -sqrtr1 ler_sqrt// ler1n.
have du : d%:R = u ^+ 2 by rewrite sqr_sqrtr.
pose v : RT := Num.sqrt n%:R.
have v0 : 0 < v.
  rewrite sqrtr_gt0; have : 0 < alpha * d%:R ^+ 2.
    by rewrite mulr_gt0// exprn_gt0// ltr0n.
  by move=> h; have := lt_le_trans h hn; rewrite pmulr_rgt0.
have nv : n%:R = v ^+ 2 by rewrite sqr_sqrtr.
pose w : RT := Num.sqrt d.+1%:R.
have w0 : 0 <= w by exact: sqrtr_ge0.
have ew : Num.sqrt (n%:R * d.+1%:R) = v * w by rewrite sqrtrM.
have d1 : d.+1%:R = u ^+ 2 + 1 :> RT by rewrite -du -(@natr1 RT d).
have w2 : w <= 2 * u.
  have u2 : 0 <= 2 * u by rewrite mulr_ge0// ltW.
  rewrite -ler_sqr ?nnegrE// /w sqr_sqrtr// d1 exprMn.
  nra.
rewrite ew d1 du nv; rewrite du nv in hn.
have sne : s != 0 by rewrite gt_eqF.
have une : u != 0 by rewrite gt_eqF.
have vne : v != 0 by rewrite gt_eqF.
have ane : alpha != 0 by rewrite gt_eqF.
have -> : u ^+ 2 / s * ((v ^+ 2)^-1 *
    (96 * (L0 / u) * (v * w + (u ^+ 2 + 1)))) =
    96 * L0 / s * (u * (v * w + (u ^+ 2 + 1)) / v ^+ 2).
  by field.
have -> : 96 * L0 * (2 + 8 / alpha) / s =
    96 * L0 / s * ((2 * alpha + 8) / alpha).
  by field.
apply: ler_wpM2l.
  by apply: divr_ge0; [apply: mulr_ge0 => //; exact: ltW | exact: ltW].
rewrite ler_pdivrMr ?exprn_gt0// mulrAC ler_pdivlMr//.
(* alpha u (v w + u^2 + 1) <= (2 alpha + 8) v^2, from alpha u^4 <= 2 v^2 *)
have h1 : alpha * u * v * w <= 2 * alpha * u ^+ 2 * v.
  have : 0 <= alpha * u * v by rewrite !mulr_ge0// ltW.
  by move=> h; have := ler_wpM2l h w2; rewrite expr2; lra.
have h2 : 2 * alpha * u ^+ 2 * v <= v ^+ 2 + alpha ^+ 2 * u ^+ 2 ^+ 2.
  by have := sqr_ge0 (v - alpha * u ^+ 2); rewrite sqrrB; nra.
have h3 : alpha ^+ 2 * u ^+ 2 ^+ 2 <= 2 * alpha * v ^+ 2.
  by have := ler_wpM2l (ltW a0) hn; rewrite !expr2; lra.
have h4 : alpha * u * (u ^+ 2 + 1) <= 2 * alpha * u ^+ 2 ^+ 2.
  have e0 : 0 <= u - 1 by lra.
  have e1 : u ^+ 3 <= u ^+ 4 by rewrite !exprS expr0 !mulr1; nra.
  have e2 : u <= u ^+ 4 by rewrite !exprS expr0 !mulr1; nra.
  have a00 : 0 <= alpha by exact: ltW.
  have e3 : u ^+ 3 = u * u ^+ 2 by rewrite exprS.
  by rewrite -exprM; nra.
have v2 : 0 <= v ^+ 2 by exact: sqr_ge0.
lra.
Qed.

End ridge_constants.

Section regular_moments.
Local Notation RR := (R : realType).
Local Open Scope ereal_scope.

Variables (kappa K tau : R) (d : nat) (mu : probability 'rV[RR]_(d * d) RR).
Hypotheses (k1 : (1 < kappa)%R)
  (rf : regular_feature K tau (unsat_cov kappa d) mu).

Lemma rf_measurable (theta : 'rV[RR]_(d * d)) :
  measurable_fun [set: 'rV[RR]_(d * d)] (fun z => mxdot z theta).
Proof. exact: measurable_mxdot. Qed.

Lemma rf_pow4_fin (theta : 'rV[RR]_(d * d)) :
  \int[mu]_z ((mxdot z theta ^+ 4)%R)%:E < +oo.
Proof.
have [_ rf4 _ _ _] := rf.
have := rf4 theta; rewrite unlock => h.
by apply: le_lt_trans h _; rewrite ltry.
Qed.

(* The variance of the affine form: E (<z, theta> - b)^2 = C_kappa + b^2. *)
Lemma rf_affine_sqr (theta : 'rV[RR]_(d * d)) (b : R) :
  \int[mu]_z (((mxdot z theta - b) ^+ 2)%R)%:E =
  (unsat_scale kappa d theta b)%:E.
Proof.
have [_ _ rf1 rf2 _] := rf.
have mX := rf_measurable theta.
have [i1 i2] := integrable_pow4 mX (rf_pow4_fin theta).
rewrite (integral_affine_sqr _ i1 i2).
have e1 : \int[mu]_z ((mxdot z theta)%R)%:E = 0.
  by have := rf1 theta; rewrite unlock.
have e2 : \int[mu]_z ((mxdot z theta ^+ 2)%R)%:E =
    (mxdot (theta *m unsat_cov kappa d) theta)%:E.
  have := rf2 theta theta; rewrite unlock.
  by under eq_integral do rewrite -expr2.
by rewrite e1 e2 mule0 sube0 /unsat_scale -EFinD RplusE.
Qed.

(* Its fourth moment, on the domain. *)
Lemma rf_affine_pow4 (theta : 'rV[RR]_(d * d)) (b : R) :
  unsat_domain d theta ->
  \int[mu]_z (((mxdot z theta - b) ^+ 4)%R)%:E <=
  ((8 * Num.max (K ^+ 4 *
      (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1)) ^+ 2) 1) *
    unsat_scale kappa d theta b ^+ 2)%:E.
Proof.
move=> Dt.
have [_ rf4 _ _ _] := rf.
have mX := rf_measurable theta.
apply: le_trans (integral_affine_pow4_le _ b mX) _.
have h4 := rf4 theta; rewrite unlock /= in h4.
set C := mxdot (theta *m unsat_cov kappa d) theta.
set t := mxdot theta theta.
set Cst := (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1))%R.
set M := Num.max (K ^+ 4 * Cst ^+ 2)%R 1%R.
have hlam := unsat_lambda_coercive kappa d theta k1 Dt.
rewrite -/C -/t -/Cst in hlam.
apply: le_trans (lee_wpmul2l _ (leeD h4 (lexx (b ^+ 4)%:E))) _.
  by rewrite lee_fin.
rewrite -EFinD -EFinM lee_fin /unsat_scale RplusE -/C -/t.
change (opnorm (unsat_cov kappa d)) with (unsat_lambda kappa d).
set lam := unsat_lambda kappa d in hlam *.
have lam0 : (0 <= lam)%R by exact: opnorm_ge0.
have t0 : (0 <= t)%R by exact: mxdot_ge0.
have lt0 : (0 <= lam * t)%R by rewrite mulr_ge0.
have k0 : (0 < kappa - 1)%R by rewrite subr_gt0.
have Cst0 : (0 < Cst)%R.
  apply: divr_gt0; first by rewrite lt_max k0 orbT.
  by rewrite lt_min k0 andbT.
have C0 : (0 <= C)%R.
  by rewrite -(pmulr_rge0 _ Cst0); apply: le_trans hlam.
have h1 : ((lam * t) ^+ 2 <= (Cst * C) ^+ 2)%R.
  by rewrite ler_sqr ?nnegrE// mulr_ge0// ltW.
have e4 (x : R) : (x ^+ 4 = (x ^+ 2) ^+ 2)%R by rewrite -exprM.
have K40 : (0 <= K ^+ 4)%R by rewrite e4 sqr_ge0.
have h2 : (K ^+ 4 * lam ^+ 2 * t ^+ 2 <= M * C ^+ 2)%R.
  apply: (@le_trans _ _ (K ^+ 4 * Cst ^+ 2 * C ^+ 2)%R).
    rewrite -mulrA -exprMn -[(K ^+ 4 * Cst ^+ 2 * C ^+ 2)%R]mulrA -exprMn.
    exact: ler_wpM2l.
  by apply: ler_wpM2r; [exact: sqr_ge0|rewrite le_max lexx].
have b4 : (0 <= b ^+ 4)%R by rewrite e4 sqr_ge0.
have h3 : (b ^+ 4 <= M * b ^+ 4)%R.
  by rewrite -[X in (X <= _)%R]mul1r ler_wpM2r// le_max lexx orbT.
have h4' : (C ^+ 2 + b ^+ 4 <= (C + b ^+ 2) ^+ 2)%R.
  rewrite e4 sqrrD lerD2r lerDl.
  by rewrite mulrn_wge0// mulr_ge0// sqr_ge0.
have M1 : (1 <= M)%R by rewrite le_max lexx orbT.
nra.
Qed.

(* The quadratic forms of the matrix of a feature are centered. *)
Lemma rf_form_centered (v : 'cV[RR]_d) :
  (\int[mu]_z mxdot v (vec_mx z *m v) = 0)%R.
Proof.
have [_ _ rf1 _ _] := rf.
have e z : (mxdot v (vec_mx z *m v) = mxdot z (mxvec (v *m v^T)))%R.
  by rewrite mxdot_form_col -[in LHS](mxvecK (v *m v^T)) mxdot_vec_mx.
under eq_Rintegral do rewrite e.
by rewrite /Rintegral; have := rf1 (mxvec (v *m v^T)); rewrite unlock => ->.
Qed.

(* E <z, I>^2 = C_kappa(I, I) = kappa - 1. *)
Lemma rf_identity_sqr : (0 < d)%N ->
  \int[mu]_z ((mxdot z (mxvec 1%:M) ^+ 2)%R)%:E = (kappa - 1)%:E.
Proof.
move=> d0; have [_ _ _ rf2 _] := rf.
have := rf2 (mxvec 1%:M) (mxvec 1%:M); rewrite unlock => h.
under eq_integral do rewrite expr2.
by rewrite h unsat_cov_formE mxvecK unsat_cov_form1.
Qed.

End regular_moments.

Section rademacher_majorant.
Local Notation RR := (R : realType).

Lemma posdef_psd_col n (A : 'M[R]_n) : posdefmx A ->
  forall x : 'cV[R]_n, 0 <= mxdot x (A *m x).
Proof.
move=> [/symmetricmxP AT Apos] x.
have -> : mxdot x (A *m x) = mxdot x^T (x^T *m A).
  by rewrite -mxdot_trmx trmx_mul AT.
have [->|x0] := eqVneq x^T 0; first by rewrite mxdot0l.
exact: ltW (Apos _ x0).
Qed.

(* |(1/n) sum_k eps_k (<x_k, theta> - b)| <= sqrt (C + b^2) Psi for theta
   in R_d with scale at least s^2, where Psi bounds d / s times the operator
   norm of the symmetric part of (1/n) sum_k eps_k x_k plus |mean eps|. *)
Lemma ridge_rademacher_bound (kappa : R) n d (x : n.-tuple 'rV[RR]_(d * d))
    (eps : n.-tuple bool) (theta : 'rV[RR]_(d * d)) (b s Nx : R) :
  1 < kappa -> (0 < n)%N -> 0 < s -> unsat_domain d theta ->
  s ^+ 2 <= unsat_scale kappa d theta b ->
  opnorm (sym_part (\sum_(k < n)
    rademacher (nth false eps k) *: vec_mx (tnth x k))) <= Nx ->
  `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k) *
      mxdot (aug_feature (tnth x k)) (aug_param theta b)| <=
  Num.sqrt (unsat_scale kappa d theta b) *
    (d%:R / s * (n%:R^-1 * Nx) +
     `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k)|).
Proof.
move=> k1 n0 s0 Dt hs hN.
have [[Ssym Spos] tr] := Dt.
have Spsd := posdef_psd_col _ _ (conj Ssym Spos).
set v := unsat_scale kappa d theta b in hs *.
set M := \sum_(k < n) rademacher (nth false eps k) *: vec_mx (tnth x k) in hN.
set S := \sum_(k < n) rademacher (tnth eps k).
have eS : \sum_(k < n) rademacher (tnth eps k) *
    mxdot (aug_feature (tnth x k)) (aug_param theta b) =
    mxdot M (vec_mx theta) - b * S.
  under eq_bigr do rewrite mxdot_aug mulrBr.
  rewrite sumrB /M mxdot_suml mulr_sumr; congr (_ - _).
    apply: eq_bigr => k _.
    by rewrite mxdotZl mxdot_vec_mx (tnth_nth false).
  by apply: eq_bigr => k _; rewrite mulrC.
rewrite eS.
(* |<A, theta>| <= opnorm (sym_part A) tr theta *)
have hA : `|mxdot M (vec_mx theta)| <= Nx * d%:R.
  apply: le_trans (mxdot_psd_le M Ssym Spsd) _.
  by rewrite tr ler_wpM2r.
have Nx0 : 0 <= Nx by apply: le_trans hN; exact: opnorm_ge0.
have C0 : 0 <= mxdot (theta *m unsat_cov kappa d) theta.
  rewrite unsat_cov_formE.
  by have /andP[] := unsat_cov_form_bounds kappa d (vec_mx theta) k1.
have vE : v = mxdot (theta *m unsat_cov kappa d) theta + b ^+ 2.
  by rewrite /v /unsat_scale RplusE.
have v0 : 0 <= v by rewrite vE addr_ge0// sqr_ge0.
have sv : s <= Num.sqrt v.
  by rewrite -[X in X <= _](ger0_norm (ltW s0)) -sqrtr_sqr ler_sqrt.
have bv : `|b| <= Num.sqrt v.
  by rewrite -sqrtr_sqr ler_sqrt// vE lerDr.
have nR : 0 < n%:R :> R by rewrite ltr0n.
have ni : 0 < n%:R^-1 :> R by rewrite invr_gt0.
rewrite normrM (gtr0_norm ni) [`|n%:R^-1 * S|]normrM (gtr0_norm ni).
have h1 : `|mxdot M (vec_mx theta) - b * S| <=
    Nx * d%:R + Num.sqrt v * `|S|.
  apply: le_trans (ler_normB _ _) _.
  rewrite normrM; apply: lerD; first exact: hA.
  exact: ler_wpM2r.
have dsN : 0 <= d%:R / s * Nx by rewrite mulr_ge0// divr_ge0// ltW.
have h2 : Nx * d%:R <= Num.sqrt v * (d%:R / s * Nx).
  have sne : s != 0 by rewrite gt_eqF.
  have -> : Nx * d%:R = s * (d%:R / s * Nx) by field.
  exact: ler_wpM2r.
apply: le_trans (ler_wpM2l (ltW ni) h1) _.
rewrite mulrDr mulrDr; apply: lerD.
  apply: le_trans (ler_wpM2l (ltW ni) h2) _.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
by rewrite mulrCA.
Qed.

End rademacher_majorant.

Section ridge_probability.
Local Notation RR := (R : realType).
Local Open Scope ereal_scope.

(* Markov's inequality for (1/n) sum_k <Z_k, I>^2, of mean kappa - 1. *)
Lemma ridge_markov_identity (kappa K tau B : R) n d
    (mu : probability 'rV[RR]_(d * d) RR) :
  (1 < kappa)%R -> (0 < n)%N -> (0 < d)%N -> (0 < B)%R ->
  regular_feature K tau (unsat_cov kappa d) mu ->
  tuple_prod (fun=> mu) n [set Z | (B < n%:R^-1 *
    \sum_(k < n) mxdot (tnth Z k) (mxvec 1%:M) ^+ 2)%R] <=
  ((kappa - 1) / B)%:E.
Proof.
move=> k1 n0 d0 B0 rf.
pose Y (Z : n.-tuple 'rV[RR]_(d * d)) :=
  (n%:R^-1 * \sum_(k < n) mxdot (tnth Z k) (mxvec 1%:M) ^+ 2)%R.
have mI := rf_measurable d (mxvec 1%:M).
have mY : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)] Y.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_sum => k; apply: measurable_funX.
  exact: measurableT_comp mI (measurable_tnth k).
have Y0 Z : (0 <= Y Z)%R.
  by rewrite /Y mulr_ge0 ?invr_ge0// sumr_ge0// => k _; exact: sqr_ge0.
apply: le_trans (markov_ge0 (tuple_prod (fun=> mu) n) mY Y0 B0) _.
have g0 (z : 'rV[RR]_(d * d)) : 0 <= ((mxdot z (mxvec 1%:M) ^+ 2)%R)%:E.
  by rewrite lee_fin sqr_ge0.
have mg : measurable_fun [set: 'rV[RR]_(d * d)]
    (fun z => ((mxdot z (mxvec 1%:M) ^+ 2)%R)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have mgk (k : 'I_n) : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)]
    (fun x => ((mxdot (tnth x k) (mxvec 1%:M) ^+ 2)%R)%:E).
  exact: measurableT_comp mg (measurable_tnth k).
(* each coordinate has law mu, and E <z, I>^2 = kappa - 1 *)
have ES : \int[tuple_prod (fun=> mu) n]_x
    (\sum_(k < n) ((mxdot (tnth x k) (mxvec 1%:M) ^+ 2)%R)%:E) =
    (n%:R * (kappa - 1))%:E.
  rewrite ge0_integral_sum//.
  under eq_bigr => k _ do
    rewrite (ge0_integral_tuple_prod_coord (fun=> mu) k mg g0)
      (rf_identity_sqr _ _ _ _ _ rf d0).
  by rewrite sumEFin sumr_const card_ord mulr_natl.
have EY : \int[tuple_prod (fun=> mu) n]_t (Y t)%:E = (kappa - 1)%:E.
  rewrite /Y; under eq_integral do rewrite EFinM -sumEFin.
  rewrite ge0_integralZl_EFin//.
  - by move=> Z _; apply: sume_ge0 => k _; exact: g0.
  - by apply: emeasurable_sum => k; exact: mgk.
  - have nne : (n%:R != 0 :> R)%R by rewrite pnatr_eq0 -lt0n.
    by rewrite ES -EFinM mulrA mulVf ?mul1r.
by rewrite EY -EFinM lee_fin mulrC.
Qed.

(* The expectation of the Rademacher majorant. *)
Lemma ridge_rate (L s : R) n d (mu : probability 'rV[RR]_(d * d) RR)
    (N : (nat -> R) -> n.-tuple 'rV[RR]_(d * d) -> RR) :
  (0 < n)%N -> (0 < s)%R ->
  (forall a : nat -> R, (forall k, (k < n)%N -> `|a k| <= 1)%R ->
    measurable_fun [set: n.-tuple 'rV[RR]_(d * d)] (N a) /\
    \int[tuple_prod (fun=> mu) n]_x (N a x)%:E <=
      (96 * L * (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R))%:E) ->
  (forall (a : nat -> R) x, (forall k, (k < n)%N -> `|a k| <= 1)%R ->
    0 <= N a x)%R ->
  \int[tuple_prod (fun=> mu) n]_x (rademacher_mean (fun eps : n.-tuple bool =>
    d%:R / s * (n%:R^-1 * N (fun k => rademacher (nth false eps k)) x) +
    `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k)|))%:E <=
  (d%:R / s * (n%:R^-1 * (96 * L * (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R)))
    + Num.sqrt n%:R^-1)%:E.
Proof.
move=> n0 s0 hN N0.
set Cn := (96 * L * (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R))%R.
pose a (eps : n.-tuple bool) (k : nat) : R := rademacher (nth false eps k).
have a1 eps k : (k < n)%N -> (`|a eps k| <= 1)%R.
  by rewrite /a normr_rademacher.
pose G x := rademacher_mean (fun eps : n.-tuple bool => N (a eps) x).
pose H : R := rademacher_mean (fun eps : n.-tuple bool =>
  `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k)|%R).
have eG x : rademacher_mean (fun eps : n.-tuple bool =>
    d%:R / s * (n%:R^-1 * N (a eps) x) +
    `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k)|)%R =
    (d%:R / s * n%:R^-1 * G x + H)%R.
  rewrite rademacher_meanD -rademacher_meanZ; congr (_ + _)%R.
  by congr rademacher_mean; apply/funext => eps; rewrite mulrA.
under eq_integral do rewrite eG.
have mN eps : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)] (N (a eps)).
  exact: (hN (a eps) (a1 eps)).1.
have mG : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)] G.
  exact: measurable_rademacher_mean.
have G0 x : (0 <= G x)%R.
  by apply: rademacher_mean_ge0 => eps; exact: N0 (a1 eps).
have H0 : (0 <= H)%R by apply: rademacher_mean_ge0 => eps.
have c0 : (0 <= d%:R / s / n%:R)%R by rewrite !divr_ge0// ltW.
(* the average over the signs of the bounds on E N *)
have IG : \int[tuple_prod (fun=> mu) n]_x (G x)%:E <= Cn%:E.
  rewrite /G (ge0_integral_rademacher_mean _ mN).
    by move=> eps x; exact: N0 (a1 eps).
  apply: (@le_trans _ _ ((2 ^- n)%:E * \sum_(eps : n.-tuple bool) Cn%:E)).
    apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 exprn_ge0.
    by apply: lee_sum => eps _; exact: (hN (a eps) (a1 eps)).2.
  rewrite sumEFin sumr_const card_tuple card_bool -EFinM lee_fin.
  have -> : (Cn *+ 2 ^ n = (2 ^+ n) * Cn)%R by rewrite -mulr_natl natrX.
  by rewrite mulrA mulVf ?mul1r// expf_neq0.
(* Khintchine's inequality in L^1 for the mean of the signs *)
have HB : (H <= Num.sqrt n%:R^-1)%R.
  rewrite /H; under eq_fun do rewrite mulr_sumr.
  apply: (le_trans (rademacher_mean_abs_sum (fun _ : 'I_n => (n%:R^-1 : R)%R))).
  have nR : (n%:R != 0 :> R)%R by rewrite pnatr_eq0 -lt0n.
  rewrite sumr_const card_ord -(mulr_natl (n%:R^-1 ^+ 2)) expr2 mulrA.
  by rewrite mulfV ?mul1r.
under eq_integral do rewrite EFinD EFinM.
rewrite ge0_integralD//.
- by move=> x _; rewrite -EFinM lee_fin mulr_ge0.
- apply: emeasurable_funM; first exact: measurable_cst.
  exact/measurable_EFinP.
rewrite ge0_integralZl_EFin//.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP.
rewrite integral_cst// [X in _ + _ * X <= _]probability_setT mule1.
rewrite EFinD; apply: leeD; last by rewrite lee_fin.
have -> : (d%:R / s * (n%:R^-1 * Cn) = d%:R / s / n%:R * Cn)%R.
  by rewrite mulrA.
by rewrite EFinM; exact: (lee_wpmul2l _ IG).
Qed.

(* For one dimension d: with probability at least one minus an explicit
   bound, the ridge adds at most beta (max / min + 1) s^2. The event is
   the union of the failure of the small-ball method for the affine forms
   of scale at least s^2 and of Markov's inequality at the identity. *)
Lemma unsat_ridge_gap_prob (kappa K tau L s beta : R) n d
    (mu : probability 'rV[RR]_(d * d) RR) :
  (1 < kappa)%R -> (0 < n)%N -> (0 < d)%N -> (0 < s)%R -> (0 < L)%R ->
  (0 <= beta)%R ->
  regular_feature K tau (unsat_cov kappa d) mu ->
  (forall v : 'rV[RR]_d, (mxdot v v <= 1)%R ->
     subexponential mu (fun z => mxdot z (mxvec (v^T *m v))) L) ->
  exists E : set (n.-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    tuple_prod (fun=> mu) n E <=
      (512 * ridge_moment_const kappa K / 9 *
        (d%:R / s * (n%:R^-1 *
           (96 * L * (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R))) +
         Num.sqrt n%:R^-1) +
       1024 * ridge_moment_const kappa K * (kappa - 1) / (9 * s ^+ 2))%:E &
    forall Z, ~ E Z ->
      (unsat_ridge_value kappa n d beta Z - unsat_value n d Z <=
       beta * (Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1) + 1) * s ^+ 2)%R].
Proof.
move=> k1 n0 d0 s0 Lpos b0 rf sub.
set Kq := ridge_moment_const kappa K.
have Kq0 : (0 < Kq)%R by exact: ridge_moment_const_gt0.
set Cn := (96 * L * (Num.sqrt (n%:R * d.+1%:R) + d.+1%:R))%R.
(* the majorant of the operator norm (Lemma 4.3) *)
have hY (v : 'cV[RR]_d) (k : nat) : (frobenius v <= 1)%R -> (k < n)%N ->
    subexponential ((fun=> mu) k) (fun t => mxdot v (vec_mx t *m v)) L.
  move=> fv _.
  have -> : (fun t : 'rV[RR]_(d * d) => mxdot v (vec_mx t *m v)) =
      (fun t => mxdot t (mxvec (v^T^T *m v^T))).
    apply/funext => t.
    by rewrite trmxK mxdot_form_col -[in LHS](mxvecK (v *m v^T)) mxdot_vec_mx.
  apply: sub; rewrite mxdot_trmx -frobenius_sqr.
  exact: exprn_ile1 (frobenius_ge0 v) fv.
have hY0 (v : 'cV[RR]_d) (k : nat) : (frobenius v <= 1)%R -> (k < n)%N ->
    (\int[(fun=> mu) k]_t mxdot v (vec_mx t *m v) = 0)%R.
  by move=> _ _; exact: (rf_form_centered _ _ _ _ _ rf).
have [N hN] := @opnorm_sum_subexponential _ _ _ (fun=> mu) n d
  (@vec_mx RR d d) L Lpos hY hY0.
have Nle a x : (forall k, (k < n)%N -> `|a k| <= 1)%R ->
    (opnorm (sym_part (\sum_(k < n) a k *: vec_mx (tnth x k))) <= N a x)%R.
  by move=> /hN[_ + _]; apply.
have N0 a x : (forall k, (k < n)%N -> `|a k| <= 1)%R -> (0 <= N a x)%R.
  by move=> ha; apply: le_trans (Nle a x ha); exact: opnorm_ge0.
have hr := ridge_rate L s n d mu N n0 s0
  (fun a ha => let: And3 h1 _ h3 := hN a ha in conj h1 h3) N0.
(* the Rademacher majorant Psi of the small-ball method *)
pose Psi (x : n.-tuple 'rV[RR]_(d * d)) (eps : n.-tuple bool) : RR :=
  (d%:R / s * (n%:R^-1 * N (fun k => rademacher (nth false eps k)) x) +
   `|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k)|)%R.
have a1 (eps : n.-tuple bool) k : (k < n)%N ->
    (`|rademacher (nth false eps k) : RR| <= 1)%R.
  by rewrite normr_rademacher.
have mPsi eps : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)] (Psi ^~ eps).
  apply: measurable_funD; last exact: measurable_cst.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_funM; first exact: measurable_cst.
  by have [] := hN _ (a1 eps).
(* the affine forms of scale at least s^2, as linear forms of the augmented
   features *)
pose D (p : 'rV[RR]_(d * d + 1)) : Prop :=
  unsat_domain d (lsubmx p) /\
  (s ^+ 2 <= unsat_scale kappa d (lsubmx p) (rsubmx p 0 0))%R.
set S := aug_cov (unsat_cov kappa d).
clear hY hY0.
have formE (p : 'rV[RR]_(d * d + 1)) :
    (mxdot (p *m S) p = unsat_scale kappa d (lsubmx p) (rsubmx p 0 0))%R.
  by rewrite -{1 2}(aug_paramK _ p) aug_cov_form /unsat_scale RplusE.
have mF (p : 'rV[RR]_(d * d + 1)) :
    measurable_fun [set: 'rV[RR]_(d * d)] (fun t => mxdot (aug_feature t) p).
  have -> : (fun t => mxdot (aug_feature t) p) =
      (fun t => mxdot t (lsubmx p) - rsubmx p 0 0)%R.
    by apply/funext => t; rewrite mxdot_aug_feature.
  apply: measurable_funB; last exact: measurable_cst.
  exact: rf_measurable.
have Sp p : D p -> (0 < mxdot (p *m S) p)%R.
  by move=> [_ hs]; rewrite formE; apply: lt_le_trans hs; rewrite exprn_gt0.
have h2 p k : D p -> (k < n)%N ->
    \int[(fun=> mu) k]_t ((mxdot (aug_feature t) p ^+ 2)%R)%:E =
    (mxdot (p *m S) p)%:E.
  move=> _ _; rewrite formE -(rf_affine_sqr _ _ _ _ _ rf).
  by apply: eq_integral => t _; rewrite mxdot_aug_feature.
have h4 p k : D p -> (k < n)%N ->
    \int[(fun=> mu) k]_t ((mxdot (aug_feature t) p ^+ 4)%R)%:E <=
    (Kq * mxdot (p *m S) p ^+ 2)%:E.
  move=> [Dp _] _; rewrite formE.
  have -> : \int[mu]_t ((mxdot (aug_feature t) p ^+ 4)%R)%:E =
      \int[mu]_t (((mxdot t (lsubmx p) - rsubmx p 0 0) ^+ 4)%R)%:E.
    by apply: eq_integral => t _; rewrite mxdot_aug_feature.
  exact: (rf_affine_pow4 _ _ _ _ _ k1 rf _ _ Dp).
have hPsi x eps p : D p ->
    (`|n%:R^-1 * \sum_(k < n) rademacher (tnth eps k) *
        mxdot (aug_feature (tnth x k)) p| <=
     Num.sqrt (mxdot (p *m S) p) * Psi x eps)%R.
  move=> [Dp hs]; rewrite formE -{1}(aug_paramK _ p).
  exact: (ridge_rademacher_bound kappa n d x eps (lsubmx p) (rsubmx p 0 0)%R s
    (N (fun k => rademacher (nth false eps k)) x) k1 n0 s0 Dp hs
    (Nle _ x (a1 eps))).
have Cn0 : (0 <= Cn)%R.
  rewrite /Cn; apply: mulr_ge0; first by apply: mulr_ge0 => //; exact: ltW.
  by apply: addr_ge0; [exact: sqrtr_ge0 | exact: ler0n].
set r := (d%:R / s * (n%:R^-1 * Cn) + Num.sqrt n%:R^-1)%R.
have r0 : (0 <= r)%R.
  apply: addr_ge0; last exact: sqrtr_ge0.
  apply: mulr_ge0; first by apply: divr_ge0 => //; exact: ltW.
  by apply: mulr_ge0 => //; rewrite invr_ge0.
(* the small-ball method *)
have [E1 [mE1 PE1 hE1]] := @small_ball_linear _ _ _ (fun=> mu) n (d * d + 1)
  aug_feature S D Kq r Psi n0 Kq0 r0 mF Sp h2 h4 mPsi hPsi hr.
clear hr hPsi h2 h4 Sp mF mPsi Nle N0 hN a1.
(* Markov's inequality at the identity *)
set c := (9 / (512 * Kq))%R.
set B := (c * s ^+ 2 / 2)%R.
have c0 : (0 < c)%R.
  by apply: divr_gt0; [rewrite ltr0n | apply: mulr_gt0 => //; rewrite ltr0n].
have B0 : (0 < B)%R.
  by apply: divr_gt0; [apply: mulr_gt0 => //; exact: exprn_gt0 | exact: ltr0Sn].
pose E2 := [set Z : n.-tuple 'rV[RR]_(d * d) |
  (B < n%:R^-1 * \sum_(k < n) mxdot (tnth Z k) (mxvec 1%:M) ^+ 2)%R].
have mY : measurable_fun [set: n.-tuple 'rV[RR]_(d * d)]
    (fun Z => n%:R^-1 * \sum_(k < n) mxdot (tnth Z k) (mxvec 1%:M) ^+ 2)%R.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_sum => k; apply: measurable_funX.
  exact: measurableT_comp (rf_measurable d (mxvec 1%:M)) (measurable_tnth k).
have mE2 : measurable E2.
  rewrite -[X in measurable X]setTI.
  exact: (measurable_fun_ltr (measurable_cst B) mY measurableT).
have PE2 := ridge_markov_identity kappa K tau B n d mu k1 n0 d0 B0 rf.
exists (E1 `|` E2); split.
- exact: measurableU.
- apply: le_trans (measureU2 _ mE1 mE2) _.
  rewrite EFinD; apply: leeD.
    by apply: le_trans PE1 _; rewrite lee_fin mulrAC.
  apply: le_trans PE2 _; rewrite lee_fin le_eqVlt; apply/orP; left; apply/eqP.
  have Kne : Kq != 0%R by rewrite gt_eqF.
  have sne : s != 0%R by rewrite gt_eqF.
  by rewrite /B /c; field.
(* outside the two events, the localization applies *)
move=> Z /not_orP[nE1 nE2].
apply: (unsat_ridge_gap_le kappa n d beta c s B Z k1 n0 d0 b0 s0).
- move=> theta b Dt hs.
  have Dp : D (aug_param theta b) by rewrite /D aug_param_lsub aug_param_rsub.
  have h := hE1 Z nE1 _ Dp.
  rewrite /S aug_cov_form in h.
  have -> : unsat_scale kappa d theta b =
      (mxdot (theta *m unsat_cov kappa d) theta + b ^+ 2)%R.
    by rewrite /unsat_scale RplusE.
  apply: le_trans h _; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by congr (_ * _)%R; apply: eq_bigr => k _; rewrite mxdot_aug.
- by rewrite leNgt; apply/negP.
- have : (0 < c * s ^+ 2)%R by apply: mulr_gt0 => //; exact: exprn_gt0.
  by rewrite /B; lra.
Qed.

End ridge_probability.

Section ridge_removal.
Local Notation RR := (R : realType).

(* Lemma 2.12. *)
Theorem unsat_ridge_removal (alpha kappa K L0 : R) :
  0 < alpha -> 1 < kappa -> 0 < K -> 0 < L0 ->
  exists2 C : R, 0 < C &
  forall (n : nat -> nat) (mu : forall d, probability 'rV[RR]_(d * d) RR)
         (tau beta : nat -> R),
    universality_density_tends_to n alpha ->
    (forall d, (0 < d)%N ->
       regular_feature K (tau d) (unsat_cov kappa d) (mu d)) ->
    (forall d (v : 'rV[RR]_d), (0 < d)%N -> mxdot v v <= 1 ->
       subexponential (mu d) (fun z => mxdot z (mxvec (v^T *m v)))
         (L0 / Num.sqrt d%:R)) ->
    (forall d c, measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
       c < unsat_ridge_value kappa (n d) d (beta d) Z -
           unsat_value (n d) d Z]) ->
    (forall d, 0 <= beta d) ->
    paper_main_tends_to
      (fun d => tuple_prod (fun=> mu d) (n d)
        [set Z | C * beta d * ln d%:R <
                 unsat_ridge_value kappa (n d) d (beta d) Z -
                 unsat_value (n d) d Z]) 0.
Proof.
move=> a0 k1 K0 L0p.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have m0 : 0 < Num.min 2 (kappa - 1) by rewrite lt_min k0 andbT.
have M0 : 0 < Num.max 2 (kappa - 1) by rewrite lt_max k0 orbT.
set Cst := Num.max 2 (kappa - 1) / Num.min 2 (kappa - 1).
have Cst0 : 0 < Cst by rewrite divr_gt0.
exists (Cst + 1); first by rewrite addr_gt0.
move=> n mu tau beta hn rf sub mev b0 eps e0.
set Kq := ridge_moment_const kappa K.
have Kq0 : 0 < Kq by exact: ridge_moment_const_gt0.
(* s depends on eps only: the bound of unsat_ridge_gap_prob is below eps
   once s is large, n d >= alpha d^2 / 2, n d is large and ln d >= s^2 *)
pose A := 512 * Kq / 9 * (96 * L0 * (2 + 8 / alpha)).
pose Bc := 1024 * Kq * (kappa - 1) / 9.
have A0 : 0 <= A.
  apply: mulr_ge0.
    by apply: divr_ge0; [apply: mulr_ge0 => //; exact: ltW | exact: ler0n].
  apply: mulr_ge0; first by apply: mulr_ge0; [exact: ler0n | exact: ltW].
  apply: addr_ge0; first exact: ler0n.
  by apply: divr_ge0; [exact: ler0n | exact: ltW].
have Bc0 : 0 <= Bc.
  apply: divr_ge0; last exact: ler0n.
  by apply: mulr_ge0; [apply: mulr_ge0 => //; exact: ltW | exact: ltW].
pose s := 1 + 3 * A / eps + 3 * Bc / eps.
have Ae : 0 <= 3 * A / eps.
  by apply: divr_ge0; [apply: mulr_ge0 => //; exact: ler0n | exact: ltW].
have Be : 0 <= 3 * Bc / eps.
  by apply: divr_ge0; [apply: mulr_ge0 => //; exact: ler0n | exact: ltW].
have s1 : 1 <= s by rewrite /s -addrA lerDl addr_ge0.
have s0 : 0 < s by apply: lt_le_trans s1; exact: ltr01.
pose delta := eps / 3 / (512 * Kq / 9).
have delta0 : 0 < delta.
  apply: divr_gt0; first by apply: divr_gt0 => //; exact: ltr0Sn.
  by apply: divr_gt0; [apply: mulr_gt0 => //; exact: ltr0Sn | exact: ltr0Sn].
have a2 : 0 < alpha / 2 by apply: divr_gt0 => //; exact: ltr0Sn.
have [D1 hD1] := hn _ a2.
pose D2 := (archimedean.Num.truncn (2 / (alpha * delta ^+ 2))).+1.
pose D3 := (archimedean.Num.truncn (expR (s ^+ 2))).+1.
exists (maxn (maxn D1 D2) (maxn D3 1)) => d.
rewrite !geq_max => /andP[/andP[dD1 dD2] /andP[dD3 d0]].
have dR : 0 < d%:R :> R by rewrite ltr0n.
have hnd : alpha * d%:R ^+ 2 <= 2 * (n d)%:R.
  have := hD1 d dD1; rewrite /paper_main_density ltr_distl => /andP[h _].
  move: h; rewrite ltr_pdivlMr ?exprn_gt0// => h.
  lra.
have nd0 : (0 < n d)%N.
  rewrite -(ltr0n R).
  have : 0 < alpha * d%:R ^+ 2 by rewrite mulr_gt0// exprn_gt0.
  lra.
have nR : 0 < (n d)%:R :> R by rewrite ltr0n.
have hsq : Num.sqrt (n d)%:R^-1 < delta.
  have hD2 : 2 / (alpha * delta ^+ 2) < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  have ad : 0 < alpha * delta ^+ 2 by rewrite mulr_gt0// exprn_gt0.
  move: hD2; rewrite ltr_pdivrMr// => hD2.
  have d1 : d%:R <= d%:R ^+ 2 :> R.
    have : 1 <= d%:R :> R by rewrite ler1n.
    by rewrite expr2; nra.
  have h1 : 1 < delta ^+ 2 * (n d)%:R.
    have : alpha * d%:R <= alpha * d%:R ^+ 2 by rewrite ler_pM2l.
    nra.
  rewrite -[delta]ger0_norm ?ltW// -sqrtr_sqr ltr_sqrt ?exprn_gt0//.
  by rewrite -div1r ltr_pdivrMr// mulrC.
have hln : s ^+ 2 <= ln d%:R.
  have hD3 : expR (s ^+ 2) < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  rewrite -[s ^+ 2]expRK ler_ln ?posrE ?expR_gt0//.
  exact: ltW.
(* the event of a large gap lies in the exceptional event of dimension d *)
have Lp : 0 < L0 / Num.sqrt d%:R by rewrite divr_gt0// sqrtr_gt0.
have [E [mE PE hE]] := unsat_ridge_gap_prob kappa K (tau d) (L0 / Num.sqrt d%:R)
  s (beta d) (n d) d (mu d) k1 nd0 d0 s0 Lp (b0 d) (rf d d0)
  (fun v => sub d v d0).
have evE : [set Z | (Cst + 1) * beta d * ln d%:R <
    unsat_ridge_value kappa (n d) d (beta d) Z - unsat_value (n d) d Z] `<=` E.
  move=> Z /= hZ; apply: contrapT => nEZ.
  have h := hE Z nEZ; rewrite -/Cst in h.
  have C1 : 0 <= (Cst + 1) * beta d by rewrite mulr_ge0// addr_ge0// ltW.
  have := ler_wpM2l C1 hln.
  rewrite [beta d * _]mulrC in h.
  lra.
rewrite sube0 gee0_abs; first exact: measure_ge0.
apply: le_lt_trans (le_measure _ (mem_set (mev d _)) (mem_set mE) evE) _.
apply: le_lt_trans PE _; rewrite lte_fin -/Kq.
have hX := ridge_rate_le alpha L0 s (n d) d a0 L0p s0 d0 hnd.
move: hX; set X := (d%:R / s * _)%R => hX.
(* each of the three terms is at most eps / 3 *)
have k9 : 0 < 512 * Kq / 9.
  by apply: divr_gt0; [apply: mulr_gt0 => //; exact: ltr0Sn | exact: ltr0Sn].
have ene : eps != 0 by rewrite gt_eqF.
have sne : s != 0 by rewrite gt_eqF.
have es : eps * s = eps + 3 * A + 3 * Bc by rewrite /s; field.
have hA : 512 * Kq / 9 * X <= eps / 3.
  apply: le_trans (ler_wpM2l (ltW k9) hX) _.
  have -> : 512 * Kq / 9 * (96 * L0 * (2 + 8 / alpha) / s) = A / s.
    by rewrite /A mulrA.
  rewrite ler_pdivrMr//.
  lra.
have hB : 1024 * Kq * (kappa - 1) / (9 * s ^+ 2) <= eps / 3.
  have ss : eps * s <= eps * s ^+ 2.
    by rewrite ler_pM2l// expr2 ler_peMl// ltW.
  have e9 : 1024 * Kq * (kappa - 1) = 9 * Bc by rewrite /Bc; field.
  rewrite ler_pdivrMr ?mulr_gt0 ?exprn_gt0// ?ltr0Sn// e9.
  lra.
have hC : 512 * Kq / 9 * Num.sqrt (n d)%:R^-1 < eps / 3.
  have Kne : Kq != 0 by rewrite gt_eqF.
  have <- : 512 * Kq / 9 * delta = eps / 3 by rewrite /delta; field.
  by rewrite ltr_pM2l.
lra.
Qed.

End ridge_removal.
