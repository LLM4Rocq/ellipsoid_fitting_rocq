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

   Main results to prove (stage 1 of phase 5; names come with the proofs).
   The constants depend only on kappa, K, L0 and alpha.
   - Lemma 4.3 in the form of a Rademacher majorant: for independent
     features Z_1, ..., Z_n with a law whose quadratic forms
     z |-> <z, mxvec (v^T v)> (|v| <= 1) are centered and subexponential
     with constant L0 / sqrt d, and a sign vector eps,
     |<(1/n) sum_i eps_i Z_i, theta>| <= d opnorm (sym (vec_mx ...)) for
     theta in R_d, with the measurable majorant of
     matrix/random_opnorm.v of expectation at most
     96 L0 / sqrt d (sqrt (n (d + 1)) + d + 1) / n, which is O(1 / d)
     when n / d^2 -> alpha > 0; the paper has an extra sqrt (log d) from
     the matrix Bernstein inequality.
   - Lemma 2.12, for features of regular laws mu d (regular_feature with
     covariance unsat_cov kappa d) whose quadratic forms are subexponential
     with constant L0 / sqrt d, n / d^2 -> alpha and beta d >= 0: there is
     C such that the probability under tuple_prod (fun=> mu d) (n d) that
     unsat_ridge_value - unsat_value exceeds C beta d ln d tends to 0. The
     statement is in requests/c-to-b.md. Proof: small_ball_linear of
     probability/small_ball_method.v with s_d^2 = ln d, for the affine
     forms <z, theta> - b written as linear forms of the feature augmented
     by a constant coordinate; Markov's inequality for
     (1/n) sum_i <Z_i, I>^2, of mean C_kappa(I, I) = kappa - 1, at the
     level B = c s_d^2 / 2; then the localization. *)

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
From GaussianAnalysis Require Import logdet_barrier gordon.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Unsat Require Import LeastSquares.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section covariance.

Lemma mxdot_vec_mx d (x y : 'rV[R]_(d * d)) :
  mxdot (vec_mx x) (vec_mx y) = mxdot x y.
Proof.
rewrite /mxdot [in RHS]big_ord1 [in RHS]sum_mxvec_index.
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite !mxE.
Qed.

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
