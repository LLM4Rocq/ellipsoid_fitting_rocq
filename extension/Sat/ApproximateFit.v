(* The approximate fit: Proposition 2.1 of Koehler and Sohn, "Universality
   and sharp thresholds for ellipsoid fitting" (arXiv 2608.27372, lines
   725-740, proof lines 4443-4596), at Stdlib's R. Item S1 of stage 3 of
   phase 5 (lane A).

   Setting. kappa > 1, K > 0, alpha > 0 and n d / d^2 -> alpha
   (universality_density_tends_to); for every d the coordinate laws
   nu d j (j < d) are universality_coordinate_law kappa K. The features of
   a sample x are W_i = (x_i x_i^T - I) / sqrt d, given as the rows
   mxvec W_i of unsat_features n d x (Unsat/LeastSquares), of law
   tuple_prod (fun=> data_feature_law (nu d) d) n.

   Main result. approximate_fit: for 0 < alpha < alpha*(kappa) there are
   0 < m < 1 < M and C > 0, depending only on alpha, kappa and K, such
   that for every delta > 0 and eps > 0 and every large d, outside a
   measurable event of probability at most eps (under the law of the n
   features), some S with mxvec S in pd_slice2 d m M (m I < S < M I and
   tr S = d) and some real b satisfy
     sum_i (b - <W_i, S>)^2 <= delta n   and   |b - <W_i, S>| <= C ln d
   for every i. The paper's rates are (ln d / d)^(1/10) and (ln d)^2; the
   form above is what Theorem 1.9 (Sat/Interpolation, lane C) needs: its
   bound C' ((ln d)^4 / sqrt d |y|_oo + |y|_2 / d) tends to 0.

   Hypothesis. gaussian_subcritical_fit kappa alpha is Proposition 1.4 (i)
   for the Gaussian features with intercept 0: some symmetric S with
   m0 I <= S <= M0 I, tr S = d and <G_i, S> = 0 for every i, with
   probability tending to one. It holds below the threshold
   (gaussian_subcritical_fit_holds), by Lemma 5.17
   (gaussian_fit_below_threshold of Gaussian/Subcritical, item G9).

   Route (the paper's, with the barrier kept).
   1. Theorem 2.9 (barrier_lindeberg_concentration of
      convex/barrier_lindeberg.v) on the domain pd_slice2 d m M, with
      m = min (m0, 1) / 2, M = 2 max (M0, 1) and its 2d-self-concordant
      barrier logdet_barrier2 (Lemma 2.8, convex/logdet_barrier.v), for the
      data features and for the Gaussian ones (both regular:
      uni_regular_data and uni_regular_gauss of Unsat/Universality), with
      beta = delta / (2 A0) fixed, A0 = max (2, kappa - 1) M + 1, and
      gamma = 1 / (d sqrt d). Both values Phi_W and Phi_G are within
      beta / 4 of E Phi_G, except on events of vanishing probability.
   2. The Gaussian witness S of the hypothesis is in the domain, with
      b = 0: Phi_G <= beta lambda |S|_F^2 + gamma B(S)
      <= beta max (2, kappa - 1) M + beta / 4. Hence E Phi_G and then Phi_W
      are at most beta A0.
   3. A minimizer (S, b) of the full objective (ls_barrier_minimizer of
      convex/minimizers.v) has sum_i (<W_i, S> - b)^2 <= 2 n Phi_W.
   4. The leave-one-out minimizers (S^(i), b^(i)) are measurable functions
      of the other rows (measurable_ls_min of
      library/probability/measurable_minimizer.v), with
      beta (b^(i))^2 <= Phi_W, so |b^(i)| = O(1), and
      |<W_i, S> - b| <= |<W_i, S^(i)> - b^(i)| (add the two optimality
      inequalities). Given the other rows, <W_i, S^(i)> is subexponential
      with constant L0 = 252 K^2 sqrt M (Hanson-Wright,
      data_feature_subexponential of Features/Regular, as
      |S^(i)|_F^2 <= M d), so a union bound over the n rows gives
      max_i |<W_i, S> - b| <= sqrt A0 + 3 L0 ln d, except on an event of
      probability at most 2 n / d^3.

   Lemmas:
   - slice2_spectral, slice2_frobenius, slice2_witness: the eigenvalues of
     a point of pd_slice2 d m M lie in (m, M), its squared Frobenius norm
     is at most M d, and a symmetric S with m0 I <= S <= M0 I and tr S = d
     (m < m0, M0 < M) is in pd_slice2 d m M with a barrier at most
     d (ln ((1 - m) (M - 1)) - ln (m0 - m) - ln (M - M0)).
   - sat_min, sat_int, sat_value: the minimizers and the value of the
     objective with the barrier on pd_slice2 d m M x R, for the full
     (predT) and the leave-one-out ((j != i)) objectives; sat_valueE,
     sat_loss_le (step 3), sat_loo_compare and sat_loo_int (step 4), and
     sat_loo_tuple_set, measurable_sat_loo.
   - sat_subexp, sat_loo_tail: the bad event of row i (|b^(i)| <= B0 and a
     residual above s0) has probability at most
     2 exp (- (s0 - B0) / (252 K^2 sqrt M)) under the data features.
   - af_conc, af_ref_scale_le, af_value_witness, af_center_le: Theorem 2.9
     on the domain for any regular law with the constants of the Gaussian
     features, the reference scale (1 + 1 / beta) (1 + max (2, kappa - 1)),
     the value at a Gaussian witness, and the bound of E Phi_G.
   - af_at_d: the approximate fit at one large dimension, from the bounds
     af_err_small, af_prob_small, af_wit_small and af_union_small of the
     error terms; af_ev_density, af_ev_tau, af_ev_ge and af_ev_sqrt give
     the dimensions for which these bounds hold. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.probability Require Import lindeberg efron_stein.
From GaussianAnalysis.probability Require Import subgaussian measurable_minimizer.
From GaussianAnalysis.convex Require Import self_concordant least_squares.
From GaussianAnalysis.convex Require Import logdet_barrier minimizers.
From GaussianAnalysis.convex Require Import barrier_lindeberg ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Unsat Require Import Universality FourthMomentThree.
From EllipsoidUniversality.Gaussian Require Import Subcritical.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* Proposition 1.4 (i) for the Gaussian features, in the form that
   approximate_fit takes as its hypothesis. *)
Definition gaussian_subcritical_fit (kappa alpha : R) : Prop :=
  exists m0 M0 : R, [/\ 0 < m0, m0 <= M0 &
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
      forall v : 'rV[R]_d,
        m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
      \tr S = d%:R &
      forall i, mxdot (tnth Z i) (mxvec S) = 0]]].

(* 1. The domain pd_slice2 d m M: the eigenvalues of its points, their
   Frobenius norm, and the barrier at a well-conditioned matrix. *)

Section sat_matrix.
Variable d : nat.

Lemma slice2_spectral (m M : R) (x : 'rV[R]_(d * d)) : pd_slice2 d m M x ->
  exists2 P : 'M[R]_d, P \is orthogonalmx &
    exists2 l : 'rV[R]_d, vec_mx x = P^T *m diag_mx l *m P &
      forall i, m < l 0 i < M.
Proof.
move=> [p1 [p2 xtr]].
have xs : vec_mx x \is symmetricmx.
  move: p1 => [/symmetricmxP xs _]; apply/symmetricmxP; move: xs.
  by rewrite raddfB /= tr_scalar_mx => /addIr.
have [P Po [l AE]] := symmetric_spectral xs.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
have Pu : P \in unitmx by exact: orthogonalmx_unit.
have shift (a b : R) : a%:M + b *: vec_mx x =
    P^T *m diag_mx (\row_i (a + b * l 0 i)) *m P.
  have -> : diag_mx (\row_i (a + b * l 0 i)) = a%:M + b *: diag_mx l.
    apply/matrixP => i j; rewrite !mxE.
    by case: (i == j) => /=; rewrite ?mulr1n ?mulr0n ?mulr0 ?addr0.
  rewrite mulmxDr mulmxDl -scalemxAr -scalemxAl -AE mul_mx_scalar.
  by rewrite -scalemxAl PtP scalemx1.
have E1 : vec_mx x - m%:M = P^T *m diag_mx (\row_i (- m + 1 * l 0 i)) *m P.
  by rewrite -shift scale1r addrC raddfN.
have E2 : M%:M - vec_mx x = P^T *m diag_mx (\row_i (M + -1 * l 0 i)) *m P.
  by rewrite -shift scaleN1r.
move: p1 p2; rewrite E1 E2 !posdefmx_congruence // => q1 q2.
exists P => //; exists l => // i.
have := q1 i; have := q2 i; rewrite !mxE mul1r mulN1r => h2 h1.
by apply/andP; split; lra.
Qed.

(* |A|_F^2 <= M d for A in pd_slice2 d m M with m >= 0. *)
Lemma slice2_frobenius (m M : R) (x : 'rV[R]_(d * d)) : 0 <= m ->
  pd_slice2 d m M x -> mxdot x x <= M * d%:R.
Proof.
move=> m0 hx; have [_ [_ xtr]] := hx.
have [P Po [l AE lb]] := slice2_spectral m M x hx.
have PP : P *m P^T = 1%:M by apply/orthogonalmxP.
have trl : \sum_i l 0 i = d%:R.
  by rewrite -xtr AE mxtrace_mulC mulmxA PP mul1mx mxtrace_diag.
have -> : mxdot x x = mxdot (diag_mx l) (diag_mx l).
  rewrite -[x]vec_mxK mxdot_mxvec AE -mulmxA.
  rewrite mxdot_orthogonalmxl ?trmx_orthogonal //.
  by rewrite mxdot_orthogonalmxr.
have -> : mxdot (diag_mx l) (diag_mx l) = \sum_i l 0 i ^+ 2.
  rewrite /mxdot; apply: eq_bigr => i _.
  rewrite (bigD1 i) //= big1 ?addr0; last by rewrite !mxE eqxx mulr1n expr2.
  by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0n mul0r.
rewrite -trl mulr_sumr; apply: ler_sum => i _.
have /andP[li lM] := lb i.
rewrite expr2; apply: ler_wpM2r; last exact: ltW.
by apply: le_trans m0 (ltW li).
Qed.

(* A symmetric S with m0 I <= S <= M0 I and tr S = d, for m < m0 and
   M0 < M, is in pd_slice2 d m M, with a barrier at most d cB. *)
Lemma slice2_witness (m M m0 M0 : R) (S : 'M[R]_d) :
  m < 1 < M -> m < m0 -> M0 < M -> S \is symmetricmx -> \tr S = d%:R ->
  (forall v : 'rV[R]_d,
     m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v) ->
  pd_slice2 d m M (mxvec S) /\
  logdet_barrier2 d m M (mxvec S) <=
    d%:R * (ln ((1 - m) * (M - 1)) - ln (m0 - m) - ln (M - M0)).
Proof.
move=> mM mm0 M0M Ss Str hS.
have [P Po [l AE]] := symmetric_spectral Ss.
have PtP : P^T *m P = 1%:M by exact: orthogonalmxT.
have Pu : P \in unitmx by exact: orthogonalmx_unit.
have dP : \det P ^+ 2 = 1.
  by rewrite expr2 -{1}det_tr -det_mulmx PtP det1.
have lb i : m0 <= l 0 i <= M0.
  have ev := spectral_eigenvector i Po AE.
  have u1 := orthogonalmx_row_unit i Po.
  rewrite mxdot_trmx in u1.
  have AT : S^T = S by apply/symmetricmxP.
  have q : mxdot (row i P) (row i P *m S) = l 0 i.
    have -> : row i P *m S = l 0 i *: row i P.
      by rewrite -[S]AT -[row i P]trmxK -trmx_mul ev linearZ /= trmxK.
    by rewrite mxdotZr u1 mulr1.
  by have := hS (row i P); rewrite q u1 !mulr1.
have shift (a b : R) : a%:M + b *: S =
    P^T *m diag_mx (\row_i (a + b * l 0 i)) *m P.
  have -> : diag_mx (\row_i (a + b * l 0 i)) = a%:M + b *: diag_mx l.
    apply/matrixP => i j; rewrite !mxE.
    by case: (i == j) => /=; rewrite ?mulr1n ?mulr0n ?mulr0 ?addr0.
  rewrite mulmxDr mulmxDl -scalemxAr -scalemxAl -AE mul_mx_scalar.
  by rewrite -scalemxAl PtP scalemx1.
have E1 : S - m%:M = P^T *m diag_mx (\row_i (- m + 1 * l 0 i)) *m P.
  by rewrite -shift scale1r addrC raddfN.
have E2 : M%:M - S = P^T *m diag_mx (\row_i (M + -1 * l 0 i)) *m P.
  by rewrite -shift scaleN1r.
have q1 i : 0 < (\row_i0 (- m + 1 * l 0 i0)) 0 i.
  by rewrite mxE mul1r; have /andP[h _] := lb i; lra.
have q2 i : 0 < (\row_i0 (M + -1 * l 0 i0)) 0 i.
  by rewrite mxE mulN1r; have /andP[_ h] := lb i; lra.
split.
  by rewrite /pd_slice2 /= mxvecK E1 E2 !posdefmx_congruence.
rewrite /logdet_barrier2 mxvecK E1 E2 !det_congruence dP !mul1r.
have [_ ->] := ln_prod q1.
have [_ ->] := ln_prod q2.
have mm : 0 < m0 - m by rewrite subr_gt0.
have MM : 0 < M - M0 by rewrite subr_gt0.
have S1 : d%:R * ln (m0 - m) <= \sum_i ln ((\row_i0 (- m + 1 * l 0 i0)) 0 i).
  rewrite -[d in d%:R]card_ord mulr_natl -sumr_const; apply: ler_sum => i _.
  have := q1 i; rewrite mxE mul1r => qi.
  rewrite ler_ln ?posrE //; have /andP[h _] := lb i; lra.
have S2 : d%:R * ln (M - M0) <= \sum_i ln ((\row_i0 (M + -1 * l 0 i0)) 0 i).
  rewrite -[d in d%:R]card_ord mulr_natl -sumr_const; apply: ler_sum => i _.
  have := q2 i; rewrite mxE mulN1r => qi.
  rewrite ler_ln ?posrE //; have /andP[_ h] := lb i; lra.
lra.
Qed.

End sat_matrix.

(* 2. The minimizers of the objective with the barrier logdet_barrier2 on
   pd_slice2 d m M x R: the full one (P = predT) and the leave-one-out ones
   (P = (j != i)); the value is the full objective at the full minimizer,
   the residual of row i at the full minimizer is at most the one at the
   leave-one-out minimizer, and the leave-one-out intercepts are bounded by
   the value. *)

Section sat_values.
Variables (m M : R) (d n : nat) (lambda beta gamma : R).
Hypotheses (m0 : 0 < m) (mM : m < 1 < M) (n0 : (0 < n)%N).
Hypotheses (l0 : 0 < lambda) (b0 : 0 < beta) (g0 : 0 < gamma).

Local Notation D := (pd_slice2 d m M).
Local Notation Bar := (logdet_barrier2 d m M).
Local Notation T := (n.-tuple 'rV[RR]_(d * d)).

Lemma sat_DV : rel_open_convex (sym_traceless d) D.
Proof. exact: rel_open_convex_pd_slice2. Qed.

Lemma sat_scB : sc_function (sym_traceless d) D Bar.
Proof. exact: (logdet2_sc_barrier d m M).1. Qed.

Lemma sat_B0 z : D z -> 0 <= Bar z.
Proof. exact: logdet_barrier2_ge0. Qed.

Lemma sat_D0 : D !=set0.
Proof. by exists (mxvec 1%:M); exact: pd_slice2_one. Qed.

Lemma sat_s0 : 0 <= (n%:R *+ 2)^-1 :> R.
Proof. by rewrite invr_ge0 mulrn_wge0 // ler0n. Qed.

Lemma sat_s_gt0 : 0 < (n%:R *+ 2)^-1 :> R.
Proof. by rewrite invr_gt0 mulrn_wgt0 // ltr0n. Qed.

Definition sat_min (P : pred 'I_n) (Z : T) : 'rV[R]_(d * d) :=
  ls_min sat_DV sat_scB sat_B0 sat_D0 P sat_s0 l0 b0 g0 Z.

Definition sat_int (P : pred 'I_n) (Z : T) : R :=
  ls_bopt Z P (n%:R *+ 2)^-1 beta (sat_min P Z).

Definition sat_obj (P : pred 'I_n) (Z : T) (theta : 'rV[R]_(d * d)) (b : R) :=
  ls_barrier_objective Z P (n%:R *+ 2)^-1 lambda beta gamma Bar theta b.

Definition sat_value (Z : T) : R := ls_barrier_value Z lambda beta D gamma Bar.

Lemma sat_min_in P Z : D (sat_min P Z).
Proof. exact: ls_min_in. Qed.

Lemma sat_minP P Z theta b : D theta ->
  sat_obj P Z (sat_min P Z) (sat_int P Z) <= sat_obj P Z theta b.
Proof. exact: ls_minP. Qed.

Lemma sat_valueE Z : sat_value Z = sat_obj predT Z (sat_min predT Z) (sat_int predT Z).
Proof.
rewrite /sat_value /ls_barrier_value.
set S := [set _ | _ in _ & _ in _].
set F := sat_obj predT Z (sat_min predT Z) (sat_int predT Z).
have Slb : lbound S F.
  by move=> _ [th Dth [b _ <-]]; exact: sat_minP.
have SF : S F.
  by exists (sat_min predT Z); [exact: sat_min_in | exists (sat_int predT Z)].
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ge_inf => //; exists F.
by apply: lb_le_inf => //; exists F.
Qed.

Lemma sat_obj_split Z (i : 'I_n) theta b :
  sat_obj predT Z theta b =
  sat_obj (fun j => j != i) Z theta b +
  (n%:R *+ 2)^-1 * (b - mxdot (tnth Z i) theta) ^+ 2.
Proof.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss (bigD1 i) //=.
by rewrite mulrDr; ring.
Qed.

(* The residual of row i at the full minimizer is at most the one at the
   leave-one-out minimizer (add the two optimality inequalities). *)
Lemma sat_loo_compare Z (i : 'I_n) :
  (sat_int predT Z - mxdot (tnth Z i) (sat_min predT Z)) ^+ 2 <=
  (sat_int (fun j => j != i) Z -
     mxdot (tnth Z i) (sat_min (fun j => j != i) Z)) ^+ 2.
Proof.
have h1 := sat_minP predT Z (sat_min (fun j => j != i) Z)
  (sat_int (fun j => j != i) Z) (sat_min_in (fun j => j != i) Z).
have h2 := sat_minP (fun j => j != i) Z (sat_min predT Z) (sat_int predT Z)
  (sat_min_in predT Z).
rewrite !(sat_obj_split Z i) in h1.
have s0 := sat_s_gt0.
move: h1 h2 s0; set s := (n%:R *+ 2)^-1 => h1 h2 s0.
rewrite -(ler_pM2l s0); clearbody s; lra.
Qed.

(* beta (b^(i))^2 <= the value. *)
Lemma sat_loo_int Z (i : 'I_n) :
  beta * sat_int (fun j => j != i) Z ^+ 2 <= sat_value Z.
Proof.
rewrite sat_valueE.
have h2 := sat_minP (fun j => j != i) Z (sat_min predT Z) (sat_int predT Z)
  (sat_min_in predT Z).
have h3 := sat_obj_split Z i (sat_min predT Z) (sat_int predT Z).
have hB := sat_B0 _ (sat_min_in (fun j => j != i) Z).
have hb : beta * sat_int (fun j => j != i) Z ^+ 2 <=
    sat_obj (fun j => j != i) Z (sat_min (fun j => j != i) Z)
      (sat_int (fun j => j != i) Z).
  rewrite /sat_obj /ls_barrier_objective /ls_ridge.
  set thi := sat_min (fun j => j != i) Z in hB *.
  set bi := sat_int (fun j => j != i) Z.
  have hl : 0 <= ls_loss Z (fun j => j != i) thi bi.
    by apply: sumr_ge0 => j _; exact: sqr_ge0.
  have h6 := mulr_ge0 sat_s0 hl.
  have h5 : 0 <= beta * (lambda * mxdot thi thi).
    by rewrite mulr_ge0 ?mulr_ge0 ?mxdot_ge0 // ltW.
  have h4 : 0 <= gamma * Bar thi by rewrite mulr_ge0 // ltW.
  rewrite mulrDr; move: h4 h5 h6.
  set s := (n%:R *+ 2)^-1; clearbody s; lra.
have hs : 0 <= (n%:R *+ 2)^-1 * (sat_int predT Z -
    mxdot (tnth Z i) (sat_min predT Z)) ^+ 2 :> R.
  by rewrite mulr_ge0 ?sat_s0 ?sqr_ge0.
move: hb h2 h3 hs; set s := (n%:R *+ 2)^-1; clearbody s; lra.
Qed.

(* The l2 bound: the average squared residual at the full minimizer is at
   most twice the value. *)
Lemma sat_loss_le Z :
  (n%:R *+ 2)^-1 * \sum_(i < n)
    (sat_int predT Z - mxdot (tnth Z i) (sat_min predT Z)) ^+ 2 <=
  sat_value Z.
Proof.
rewrite sat_valueE /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
have hB := sat_B0 _ (sat_min_in predT Z).
have hm := mxdot_ge0 (sat_min predT Z).
set L := \sum_(i < n | predT i) _.
have h1 : 0 <= beta * (lambda * mxdot (sat_min predT Z) (sat_min predT Z) +
    sat_int predT Z ^+ 2).
  by rewrite mulr_ge0 ?addr_ge0 ?sqr_ge0 ?mulr_ge0 // ltW.
have h2 : 0 <= gamma * Bar (sat_min predT Z) by rewrite mulr_ge0 // ltW.
by rewrite -addrA lerDl addr_ge0.
Qed.

(* The leave-one-out minimizer and intercept do not depend on row i, and
   are measurable functions of the features. *)
Lemma sat_loo_tuple_set Z (i : 'I_n) t :
  sat_min (fun j => j != i) (tuple_set Z i t) = sat_min (fun j => j != i) Z /\
  sat_int (fun j => j != i) (tuple_set Z i t) = sat_int (fun j => j != i) Z.
Proof.
have Pi : ~~ (fun j : 'I_n => j != i) i by rewrite /= eqxx.
have e := @ls_min_tuple_set _ _ _ _ _ sat_DV sat_scB sat_B0 sat_D0 _
  (fun j => j != i) _ _ _ _ sat_s0 l0 b0 g0 Z i t Pi.
split; first exact: e.
rewrite /sat_int /sat_min e.
exact: ls_bopt_tuple_set.
Qed.

Lemma measurable_sat_loo (i : 'I_n) :
  measurable_fun setT (fun Z : T => sat_int (fun j => j != i) Z : RR) /\
  measurable_fun setT
    (fun Z : T => mxdot (tnth Z i) (sat_min (fun j => j != i) Z) : RR).
Proof.
split; first exact: measurable_ls_bopt_min.
exact: measurable_mxdot_ls_min.
Qed.

(* 3. The leave-one-out residuals under the data features. Given the other
   rows, <W_i, S^(i)> is subexponential with constant 252 K^2 sqrt M
   (Hanson-Wright, as |S^(i)|_F^2 <= M d), so the event that the intercept
   b^(i) is at most B0 and the residual of row i exceeds s0 has probability
   at most 2 exp (- (s0 - B0) / (252 K^2 sqrt M)). *)

Variables (kappa K : R) (nu : nat -> probability (measurableTypeR R) R).
Hypotheses (hnu : forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)).
Hypotheses (K0 : 0 < K) (d0 : (0 < d)%N).

Local Notation mu := (data_feature_law nu d).

Definition sat_tail_const : RR := 252 * K ^+ 2 * Num.sqrt M.

Lemma sat_tail_const_gt0 : 0 < sat_tail_const.
Proof.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
apply: mulr_gt0; last by rewrite sqrtr_gt0.
by apply: mulr_gt0; [rewrite ltr0n | rewrite exprn_gt0].
Qed.

Lemma sat_subexp theta : D theta ->
  subexponential mu (fun z => mxdot z theta : RR) sat_tail_const.
Proof.
move=> Dth.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
have dR : 0 < d%:R :> R by rewrite ltr0n.
pose L := 252 * K ^+ 2 * Num.sqrt (M * d%:R).
have L0 : 0 < L.
  apply: mulr_gt0; last by rewrite sqrtr_gt0 mulr_gt0.
  by apply: mulr_gt0; [rewrite ltr0n | rewrite exprn_gt0].
have hL : 252 * K ^+ 2 * frobenius (vec_mx theta) <= L.
  rewrite /L; apply: ler_wpM2l; first by apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0].
  rewrite /frobenius; apply: ler_wsqrtr.
  rewrite -mxdot_mxvec vec_mxK; exact: slice2_frobenius (ltW m0) Dth.
have := data_feature_subexponential kappa K d nu hnu (vec_mx theta) L d0 L0 hL.
rewrite vec_mxK.
have -> : L / Num.sqrt d%:R = sat_tail_const.
  rewrite /L /sat_tail_const sqrtrM ?ltW // mulrA mulfK //.
  by rewrite gt_eqF // sqrtr_gt0.
by [].
Qed.

Definition sat_bad (i : 'I_n) (s0 B0 : R) : set T :=
  [set Z | `|sat_int (fun j => j != i) Z| <= B0 /\
     s0 < `|sat_int (fun j => j != i) Z -
            mxdot (tnth Z i) (sat_min (fun j => j != i) Z)|].

Lemma measurable_sat_bad (i : 'I_n) s0 B0 : measurable (sat_bad i s0 B0).
Proof.
have [mb mt] := measurable_sat_loo i.
have -> : sat_bad i s0 B0 =
    ~` [set Z | B0 < `|sat_int (fun j => j != i) Z| ] `&`
    [set Z | s0 < `|sat_int (fun j => j != i) Z -
            mxdot (tnth Z i) (sat_min (fun j => j != i) Z)|].
  apply/seteqP; split => Z /=.
    by case => h1 h2; split => //; apply/negP; rewrite -leNgt.
  by case => /negP; rewrite -leNgt => h1 h2; split.
apply: measurableI; first apply: measurableC.
  apply: measurable_set_lt.
  exact: measurableT_comp (@normr_measurable RR _) mb.
apply: measurable_set_lt.
by apply: measurableT_comp (@normr_measurable RR _) _; exact: measurable_funB.
Qed.

Lemma sat_loo_tail (i : 'I_n) (s0 B0 : R) :
  (tuple_prod (fun=> mu) n (sat_bad i s0 B0) <=
    (2 * expR (- ((s0 - B0) / sat_tail_const)))%:E)%E.
Proof.
have mE := measurable_sat_bad i s0 B0.
set c := 2 * expR (- ((s0 - B0) / sat_tail_const)).
have c0 : 0 <= c by rewrite mulr_ge0 // expR_ge0.
have mI : measurable_fun setT (fun Z : T => (\1_(sat_bad i s0 B0) Z : RR)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have I0 (Z : T) : (0 <= (\1_(sat_bad i s0 B0) Z : RR)%:E)%E.
  by rewrite lee_fin indicE ler0n.
rewrite -[sat_bad i s0 B0]setIT -integral_indic //.
rewrite (ge0_integral_tuple_prod_set (fun=> mu) i mI I0).
apply: (@le_trans _ _ (\int[tuple_prod (fun=> mu) n]_Z c%:E)%E); last first.
  by rewrite integral_cst //= probability_setT mule1.
apply: ge0_le_integral => //.
- by move=> Z _; apply: integral_ge0 => t _; exact: I0.
- exact: (measurable_tuple_set_integral (fun=> mu) i mI I0).
move=> Z _ /=.
have eth t := (sat_loo_tuple_set Z i t).1.
have eb t := (sat_loo_tuple_set Z i t).2.
set th := sat_min (fun j => j != i) Z in eth *.
set b := sat_int (fun j => j != i) Z in eb *.
have Dth : D th := sat_min_in (fun j => j != i) Z.
have -> : (fun t => (\1_(sat_bad i s0 B0) (tuple_set Z i t) : RR)%:E) =
    (fun t => (\1_[set t : 'rV[RR]_(d * d) |
       `|b| <= B0 /\ s0 < `|b - mxdot t th|] t : RR)%:E).
  apply/funext => t; rewrite !indicE.
  suff -> : (tuple_set Z i t \in sat_bad i s0 B0) =
      (t \in [set t : 'rV[RR]_(d * d) | `|b| <= B0 /\ s0 < `|b - mxdot t th|]).
    by [].
  by apply/idP/idP => /set_mem h; apply/mem_set; move: h;
    rewrite /sat_bad /= (eth t) (eb t) /tuple_set tnth_mktuple eqxx.
have mF : measurable [set t : 'rV[RR]_(d * d) |
    `|b| <= B0 /\ s0 < `|b - mxdot t th|].
  have mlt : measurable [set t : 'rV[RR]_(d * d) | s0 < `|b - mxdot t th|].
    apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
    apply: measurable_funB => //; exact: measurable_mxdotl.
  have [hb|hb] := pselect (`|b| <= B0).
    have -> : [set t : 'rV[RR]_(d * d) | `|b| <= B0 /\ s0 < `|b - mxdot t th|] =
        [set t | s0 < `|b - mxdot t th|].
      by apply/seteqP; split => t /=; [case|split].
    exact: mlt.
  have -> : [set t : 'rV[RR]_(d * d) | `|b| <= B0 /\ s0 < `|b - mxdot t th|] =
      set0.
    by apply/seteqP; split => t //= [h _]; exact: hb h.
  exact: measurable0.
rewrite integral_indic // setIT.
have [hb|hb] := pselect (`|b| <= B0); last first.
  apply: le_trans (_ : (mu set0 <= _)%E); last by rewrite measure0 lee_fin.
  apply: le_measure; rewrite ?inE //.
  by move=> t /= [h _]; exact: hb h.
apply: (@le_trans _ _
  (mu [set t : 'rV[RR]_(d * d) | s0 - B0 <= `|mxdot t th|])).
  apply: le_measure; rewrite ?inE //.
    rewrite -[X in measurable X]setTI; apply: measurable_fun_ler => //.
    apply: measurableT_comp (@normr_measurable RR _) _.
    exact: measurable_mxdotl.
  move=> t /= [_ h]; have := ler_normB b (mxdot t th).
  by move: h hb; move: (`|b - mxdot t th|) (`|b|) (`|mxdot t th|) => x y z; lra.
exact: (subexponential_tail (s0 - B0) (sat_subexp th Dth)).
Qed.

End sat_values.

(* 4. One dimension d: Theorem 2.9 on pd_slice2 d m M for the data features
   and for the Gaussian features, the reference scale, and the value at a
   Gaussian witness. *)

Section af_fixed.
Variables (kappa K : R) (m M : R) (d n : nat) (beta gamma t : R).
Hypotheses (k1 : 1 < kappa) (d0 : (0 < d)%N) (n0 : (0 < n)%N).
Hypotheses (m_pos : 0 < m) (mM : m < 1 < M).
Hypotheses (b0 : 0 < beta) (g0 : 0 < gamma) (t0 : 0 < t).
Hypothesis n36 : 36 <= n%:R * gamma.

Local Notation lam := (opnorm (unsat_cov kappa d)).
Local Notation D := (pd_slice2 d m M).
Local Notation Bar := (logdet_barrier2 d m M).
Local Notation T := (n.-tuple 'rV[RR]_(d * d)).
Local Notation Kf := (uni_K kappa K).
Local Notation tau := (uni_tau kappa K d).
Local Notation Mk := (Num.max 2 (kappa - 1)).

Lemma af_lam_gt0 : 0 < lam.
Proof.
have /andP[h _] := unsat_lambda_bounds kappa d k1 d0.
rewrite /unsat_lambda in h.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
by move: (lt_le_trans k0 h); rewrite pmulr_lgt0 // ltr0n.
Qed.

Lemma af_lam_le : lam * d%:R <= Mk.
Proof.
by have /andP[_ h] := unsat_lambda_bounds kappa d k1 d0; rewrite /unsat_lambda in h.
Qed.

Definition af_value (Z : T) : RR := sat_value m M d n lam beta gamma Z.

Definition af_center : RR :=
  \int[tuple_prod (fun=> gaussian_feature_law kappa d) n]_Z af_value Z.

Definition af_err : RR :=
  100 * (1 + Kf ^+ 4) ^+ 2 * ls_ref_scale lam beta gamma D Bar ^+ 2 *
    ((Num.sqrt (n%:R * gamma))^-1 +
     Num.sqrt (\dim (@sym_traceless RR d))%:R * (tau / lam + 1) / n%:R).

Definition af_prob : RR :=
  4 * (1 + Kf ^+ 4) ^+ 2 * ls_ref_scale lam beta gamma D Bar ^+ 2 /
    (n%:R * t ^+ 2).

(* Theorem 2.9 (2.14) for any regular feature law with the constants of the
   Gaussian features. *)
Lemma af_conc (rho : probability 'rV[RR]_(d * d) RR) :
  regular_feature Kf tau (unsat_cov kappa d) rho ->
  (tuple_prod (fun=> rho) n
     [set Z | (af_err + t < `|af_value Z - af_center|)%R] <= af_prob%:E)%E.
Proof.
move=> rrho.
exact: (barrier_lindeberg_concentration (sat_DV m M d) (sat_scB m M d)
  (sat_B0 m M d mM) (sat_D0 m M d mM) rrho
  (uni_regular_gauss kappa K k1 d d0) (uni_tau_ge0 kappa K d) n0 b0 g0 t0 n36).
Qed.

Lemma measurable_af_value : measurable_fun setT af_value.
Proof.
apply: (measurable_ls_barrier_value (sat_DV m M d) (sat_D0 m M d mM)
  (sat_B0 m M d mM)).
- by move=> z Dz e e0; exact: (sc_function_continuous (sat_DV m M d)
    (sat_scB m M d) Dz e0).
- exact: opnorm_ge0.
- exact: ltW.
- exact: ltW.
Qed.

(* The reference scale, evaluated at the identity. *)
Lemma af_ref_scale_le :
  0 <= ls_ref_scale lam beta gamma D Bar <= (1 + beta^-1) * (1 + Mk).
Proof.
rewrite /ls_ref_scale.
have b1 : 0 <= 1 + beta^-1 by rewrite addr_ge0 // invr_ge0 ltW.
set S := [set _ | _ in _].
have v0 th : D th -> 0 <= lam * mxdot th th + gamma * Bar th.
  move=> Dth; apply: addr_ge0; first by rewrite mulr_ge0 ?mxdot_ge0 ?opnorm_ge0.
  by apply: mulr_ge0; [exact: ltW | exact: (sat_B0 m M d mM)].
have lb : has_lbound S by exists 0 => _ [th Dth <-]; exact: v0.
pose I := mxvec (1%:M : 'M[R]_d).
have DI : D I := pd_slice2_one d mM.
have Sn : S !=set0 by exists (lam * mxdot I I + gamma * Bar I), I.
have I0 : 0 <= inf S by apply: lb_le_inf Sn _ => _ [th Dth <-]; exact: v0.
apply/andP; split; first by rewrite mulr_ge0 // addr_ge0.
apply: ler_wpM2l => //; rewrite lerD2l.
apply: le_trans (ge_inf lb _) _; first by exists I.
rewrite logdet_barrier2_one // mulr0 addr0.
have -> : mxdot I I = d%:R.
  by rewrite mxdot_mxvec mxdot_trace trmx1 mulmx1 mxtrace1.
exact: af_lam_le.
Qed.

(* The value at features with a witness of Proposition 1.4 (i) in the
   domain: beta lambda |S|^2 + gamma B(S). *)
Lemma af_value_witness (Z : T) (S : 'M[R]_d) :
  D (mxvec S) -> (forall i, mxdot (tnth Z i) (mxvec S) = 0) ->
  af_value Z <= beta * Mk * M + gamma * Bar (mxvec S).
Proof.
move=> DS hS.
rewrite /af_value (sat_valueE m M d n lam beta gamma mM af_lam_gt0 b0 g0).
apply: le_trans (sat_minP m M d n lam beta gamma mM af_lam_gt0 b0 g0 predT Z
  (mxvec S) 0 DS) _.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
have -> : \sum_(i < n | predT i) (0 - mxdot (tnth Z i) (mxvec S)) ^+ 2 = 0.
  by apply: big1 => i _; rewrite hS subrr expr0n.
rewrite mulr0 add0r expr0n /= addr0 lerD2r -mulrA.
apply: ler_wpM2l; first exact: ltW.
have hF := slice2_frobenius d m M (mxvec S) (ltW m_pos) DS.
have hl := af_lam_le.
have l0 := af_lam_gt0.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
have h1 : lam * mxdot (mxvec S) (mxvec S) <= lam * (M * d%:R).
  by rewrite ler_wpM2l // ltW.
apply: le_trans h1 _.
rewrite mulrCA [Mk * M]mulrC; apply: ler_wpM2l; first exact: ltW.
exact: hl.
Qed.

(* Bounds of the error and of the probability of Theorem 2.9 that depend
   only on beta, gamma, n, d and the regularity constant tau. *)
Lemma af_err_le :
  af_err <= 100 * (1 + Kf ^+ 4) ^+ 2 * ((1 + beta^-1) * (1 + Mk)) ^+ 2 *
    ((Num.sqrt (n%:R * gamma))^-1 +
     d%:R * (tau * d%:R / (kappa - 1) + 1) / n%:R).
Proof.
rewrite /af_err.
have /andP[Lr0 LrL] := af_ref_scale_le.
set Lr := ls_ref_scale _ _ _ _ _ in Lr0 LrL *.
set L := (1 + beta^-1) * (1 + Mk) in LrL *.
have Lsq : Lr ^+ 2 <= L ^+ 2 by rewrite !expr2 ler_pM.
have l0 := af_lam_gt0.
have hl := af_lam_le.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have nR : 0 < n%:R :> R by rewrite ltr0n.
have /andP[hl1 _] := unsat_lambda_bounds kappa d k1 d0.
rewrite /unsat_lambda in hl1.
have taul : tau / lam <= tau * d%:R / (kappa - 1).
  rewrite -mulrA ler_wpM2l ?uni_tau_ge0 // ler_pdivlMr // mulrC ler_pdivrMr //.
  by rewrite mulrC.
have dimle : Num.sqrt (\dim (@sym_traceless RR d))%:R <= d%:R :> R.
  rewrite -[X in _ <= X]ger0_norm ?ler0n // -sqrtr_sqr.
  rewrite ler_sqrt ?exprn_ge0 ?ler0n // -natrX ler_nat.
  by have := dim_sym_traceless (R := RR) d; rewrite -mulnn.
have K4 : 0 <= 1 + Kf ^+ 4 :> R by rewrite addr_ge0 // exprn_even_ge0.
have A0 : 0 <= 100 * (1 + Kf ^+ 4) ^+ 2 :> R by rewrite mulr_ge0 // exprn_ge0.
have s0 : 0 <= (Num.sqrt (n%:R * gamma))^-1 by rewrite invr_ge0 sqrtr_ge0.
apply: ler_pM; first by rewrite mulr_ge0 // exprn_ge0.
- rewrite addr_ge0 // mulr_ge0 ?invr_ge0 ?ler0n // mulr_ge0 ?sqrtr_ge0 //.
  by rewrite addr_ge0 // divr_ge0 ?uni_tau_ge0 // ltW.
- by rewrite ler_wpM2l.
rewrite lerD2l ler_wpM2r ?invr_ge0 ?ler0n //.
have tl0 : 0 <= tau / lam + 1 by rewrite addr_ge0 // divr_ge0 ?uni_tau_ge0 // ltW.
by apply: ler_pM; [exact: sqrtr_ge0|exact: tl0|exact: dimle|rewrite lerD2r].
Qed.

Lemma af_prob_le :
  af_prob <= 4 * (1 + Kf ^+ 4) ^+ 2 * ((1 + beta^-1) * (1 + Mk)) ^+ 2 /
    (n%:R * t ^+ 2).
Proof.
rewrite /af_prob.
have /andP[Lr0 LrL] := af_ref_scale_le.
set Lr := ls_ref_scale _ _ _ _ _ in Lr0 LrL *.
have Lsq : Lr ^+ 2 <= ((1 + beta^-1) * (1 + Mk)) ^+ 2 by rewrite !expr2 ler_pM.
have nt : 0 <= (n%:R * t ^+ 2)^-1 :> R.
  by rewrite invr_ge0 mulr_ge0 ?ler0n ?exprn_ge0 // ltW.
apply: ler_wpM2r => //; apply: ler_wpM2l => //.
by rewrite mulr_ge0 // exprn_ge0 // addr_ge0 // exprn_even_ge0.
Qed.

(* If some features avoid both a measurable event of Gaussian probability
   at most 1/4 and the event of Theorem 2.9, and every features outside
   the first event have a value at most w, then the center is at most
   w + err + t. *)
Lemma af_center_le (E : set T) (w : R) : measurable E ->
  (tuple_prod (fun=> gaussian_feature_law kappa d) n E <= (1 / 4)%:E)%E ->
  af_prob <= 1 / 4 ->
  (forall Z, ~ E Z -> af_value Z <= w) ->
  af_center <= w + af_err + t.
Proof.
move=> mE PE hp hw.
pose P := tuple_prod (fun=> gaussian_feature_law kappa d) n.
pose F := [set Z : T | (af_err + t < `|af_value Z - af_center|)%R].
have mF : measurable F.
  apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
  by apply: measurable_funB => //; exact: measurable_af_value.
have PF : (P F <= af_prob%:E)%E :=
    af_conc (gaussian_feature_law kappa d) (uni_regular_gauss kappa K k1 d d0).
have [Z [nE nF]] : exists Z, ~ E Z /\ ~ F Z.
  apply: contrapT => hno.
  have cover : [set: T] `<=` E `|` F.
    move=> Z _; apply: contrapT => hZ; apply: hno; exists Z.
    by split => h; apply: hZ; [left|right].
  have h1 : (P [set: T] <= P (E `|` F))%E.
    apply: le_measure; last exact: cover.
    - by rewrite inE.
    - by rewrite inE; exact: measurableU.
  have h2 := measureU2 P mE mF.
  have h3 : (P E + P F <= (1 / 4 + 1 / 4)%:E)%E.
    rewrite EFinD; apply: leeD => //.
    by apply: le_trans PF _; rewrite lee_fin.
  have := le_trans h1 (le_trans h2 h3).
  by rewrite probability_setT lee_fin; lra.
have := hw Z nE.
have : ~ (af_err + t < `|af_value Z - af_center|) := nF.
move/negP; rewrite -leNgt => /ler_normlP [h1 _].
by lra.
Qed.

End af_fixed.

(* 5. Asymptotics. *)

Definition af_eventually (P : nat -> Prop) : Prop :=
  exists D : nat, forall d, (D <= d)%N -> P d.

Lemma af_ev_and (P Q : nat -> Prop) :
  af_eventually P -> af_eventually Q -> af_eventually (fun d => P d /\ Q d).
Proof.
move=> [D1 h1] [D2 h2]; exists (maxn D1 D2) => d.
by rewrite geq_max => /andP[a b]; split; [exact: h1 | exact: h2].
Qed.

Lemma af_ev_mono (P Q : nat -> Prop) :
  (forall d, P d -> Q d) -> af_eventually P -> af_eventually Q.
Proof. by move=> PQ [D h]; exists D => d dD; exact: PQ (h d dD). Qed.

Lemma af_ev_ge (x : RR) : af_eventually (fun d => x <= d%:R).
Proof.
exists (archimedean.Num.truncn (Num.max x 0)).+1 => d hd.
apply: le_trans (_ : Num.max x 0 <= _); first by rewrite le_max lexx.
apply: le_trans (ltW (archimedean.Num.Theory.truncnS_gt _)) _.
by rewrite ler_nat.
Qed.

Lemma af_ev_sqrt (y : RR) : af_eventually (fun d => y <= Num.sqrt d%:R).
Proof.
apply: af_ev_mono (af_ev_ge (y ^+ 2)) => d hd.
have [y0|y0] := leP y 0; first exact: le_trans y0 (sqrtr_ge0 _).
rewrite -[X in X <= _](gtr0_norm y0) -sqrtr_sqr.
exact: ler_wsqrtr.
Qed.

Lemma af_ev_density (n : nat -> nat) (alpha : R) : 0 < alpha ->
  universality_density_tends_to n alpha ->
  af_eventually (fun d => (0 < d)%N /\
    alpha / 2 * d%:R ^+ 2 <= (n d)%:R /\ (n d)%:R <= 2 * alpha * d%:R ^+ 2).
Proof.
move=> a0 hn.
have a2 : 0 < alpha / 2 by rewrite divr_gt0.
have [D hD] := hn _ a2.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1]; split => //.
have := hD d dD; rewrite /paper_main_density RdivE ltr_norml => /andP[h1 h2].
have d2 : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have e1 : alpha / 2 < (n d)%:R / d%:R ^+ 2.
  by move: h1; set q := (n d)%:R / d%:R ^+ 2; clearbody q; lra.
have e2 : (n d)%:R / d%:R ^+ 2 < 2 * alpha.
  by move: h2; set q := (n d)%:R / d%:R ^+ 2; clearbody q; lra.
rewrite ltr_pdivlMr // in e1; rewrite ltr_pdivrMr // in e2.
by split; apply: ltW.
Qed.

Lemma af_ev_tau (kappa K eta : R) : 1 < kappa -> 0 < eta ->
  af_eventually (fun d => uni_tau kappa K d <= eta).
Proof.
move=> k1 e0.
have := af_ev_and _ _ (af_ev_ge (2 ^+ 31 * K ^+ 8 / eta ^+ 2))
  (af_ev_and _ _ (af_ev_ge (Num.sqrt 2 * Num.max 2 (kappa - 1) / eta))
    (af_ev_ge 1)).
apply: af_ev_mono => d [h1 [h2 h3]].
have dR : 0 < d%:R :> R by apply: lt_le_trans h3.
have d0 : (0 < d)%N by rewrite -(ltr_nat RR).
have e2 : 0 < eta ^+ 2 by rewrite exprn_gt0.
rewrite /uni_tau ge_max; apply/andP; split.
  rewrite -[X in _ <= X](gtr0_norm e0) -sqrtr_sqr; apply: ler_wsqrtr.
  by rewrite ler_pdivrMr // [eta ^+ 2 * _]mulrC -ler_pdivrMr.
have hl := af_lam_le kappa d k1 d0.
rewrite ler_pdivrMr // in h2.
have h4 : Num.sqrt 2 * opnorm (unsat_cov kappa d) * d%:R <= eta * d%:R.
  rewrite -mulrA [eta * _]mulrC; apply: le_trans h2.
  by apply: ler_wpM2l; [exact: sqrtr_ge0 | exact: hl].
by rewrite ler_pM2r in h4.
Qed.

(* A finite union bound over the rows. *)
Lemma af_union_le (n d : nat) (P : probability (n.-tuple 'rV[RR]_(d * d)) RR)
    (F : 'I_n -> set (n.-tuple 'rV[RR]_(d * d))) :
  (forall i, measurable (F i)) ->
  measurable (\big[setU/set0]_(i < n) F i) /\
  (P (\big[setU/set0]_(i < n) F i) <= \sum_(i < n) P (F i))%E.
Proof.
move=> mF.
apply: (big_ind2 (fun (A : set (n.-tuple 'rV[RR]_(d * d))) (x : \bar RR) =>
  measurable A /\ (P A <= x)%E)).
- by split; [exact: measurable0 | rewrite measure0].
- move=> A x B y [mA hA] [mB hB]; split; first exact: measurableU.
  by apply: le_trans (measureU2 P mA mB) _; exact: leeD.
- by move=> i _; split.
Qed.

Lemma af_in_bigsetU (n : nat) (T : Type) (F : 'I_n -> set T) (i : 'I_n) :
  F i `<=` \big[setU/set0]_(j < n) F j.
Proof. by move=> x Fx; rewrite (bigD1 i) //=; left. Qed.

(* 6. The constants of the approximate fit, from the constants m0 <= M0 of
   the Gaussian witness: the domain pd_slice2 d m M with m = min (m0, 1) / 2
   and M = 2 max (M0, 1), the bound A0 = max (2, kappa - 1) M + 1 of the
   value over beta, the bound B0 = sqrt A0 of the leave-one-out intercepts,
   the subexponential constant L0 = 252 K^2 sqrt M and C = B0 + 3 L0; and,
   for delta and eps, beta = delta / (2 A0), t = beta / 8,
   gamma = 1 / (d sqrt d), and the thresholds of the dimension. *)

(* Two steps of arithmetic of the assembly. *)
Lemma af_arith_value (be Mk M er ce va : R) : 0 < be ->
  va - ce <= er + be / 8 -> er <= be / 8 ->
  ce <= be * Mk * M + be / 4 + er + be / 8 ->
  va <= be * (Mk * M + 1).
Proof. by move=> *; lra. Qed.

Lemma af_arith_sum (p q e : R) : p <= q -> q <= e / 2 -> p + e / 2 <= e.
Proof. by move=> *; lra. Qed.

Section af_main.
Variables (kappa K alpha m0 M0 : R).
Hypotheses (k1 : 1 < kappa) (K0 : 0 < K) (a0 : 0 < alpha).
Hypotheses (m00 : 0 < m0) (mM0 : m0 <= M0).

Definition af_m : RR := Num.min m0 1 / 2.
Definition af_M : RR := 2 * Num.max M0 1.
Definition af_Mk : RR := Num.max 2 (kappa - 1).
Definition af_A0 : RR := af_Mk * af_M + 1.
Definition af_B0 : RR := Num.sqrt af_A0.
Definition af_L0 : RR := sat_tail_const af_M K.
Definition af_C : RR := af_B0 + 3 * af_L0.

Lemma af_dom : [/\ 0 < af_m, af_m < m0, af_m < 1, M0 < af_M & 1 < af_M].
Proof.
have mn0 : 0 < Num.min m0 1 by rewrite lt_min m00 ltr01.
have mnm0 : Num.min m0 1 <= m0 by rewrite ge_min lexx.
have mn1 : Num.min m0 1 <= 1 by rewrite ge_min lexx orbT.
have MxM0 : M0 <= Num.max M0 1 by rewrite le_max lexx.
have Mx1 : 1 <= Num.max M0 1 by rewrite le_max lexx orbT.
by rewrite /af_m /af_M; split; lra.
Qed.

Lemma af_mM : af_m < 1 < af_M.
Proof. by have [_ _ m1 _ M1] := af_dom; rewrite m1 M1. Qed.

Lemma af_A0_gt0 : 0 < af_A0.
Proof.
have Mk2 : 2 <= af_Mk by rewrite le_max lexx.
have [_ _ _ _ M1] := af_dom.
have : 0 < af_Mk * af_M by apply: mulr_gt0; lra.
by rewrite /af_A0; lra.
Qed.

Lemma af_L0_gt0 : 0 < af_L0.
Proof.
have [_ _ _ _ M1] := af_dom.
rewrite /af_L0 /sat_tail_const; apply: mulr_gt0; last by rewrite sqrtr_gt0; lra.
by apply: mulr_gt0; [rewrite ltr0n | rewrite exprn_gt0].
Qed.

Lemma af_C_gt0 : 0 < af_C.
Proof.
have := af_L0_gt0; have := sqrtr_ge0 af_A0.
by rewrite /af_C /af_B0; lra.
Qed.

Section af_eps.
Variables (delta eps : R).
Hypotheses (dl0 : 0 < delta) (e0 : 0 < eps).

Definition af_beta : RR := delta / (2 * af_A0).
Definition af_t : RR := af_beta / 8.
Definition af_cB : RR :=
  ln ((1 - af_m) * (af_M - 1)) - ln (m0 - af_m) - ln (af_M - M0).
Definition af_cBp : RR := Num.max af_cB 0.
Definition af_L1 : RR := (1 + af_beta^-1) * (1 + af_Mk).
Definition af_A1 : RR := 100 * (1 + uni_K kappa K ^+ 4) ^+ 2 * af_L1 ^+ 2.
Definition af_eta : RR := af_beta / (16 * af_A1).
Definition af_P1 : RR :=
  4 * (1 + uni_K kappa K ^+ 4) ^+ 2 * af_L1 ^+ 2 / af_t ^+ 2.
Definition af_Q : RR := Num.max 4 (2 / eps).
Definition af_gam (d : nat) : RR := (d%:R * Num.sqrt d%:R)^-1.
Definition af_s (d : nat) : RR := af_B0 + 3 * af_L0 * ln d%:R.

Lemma af_beta_gt0 : 0 < af_beta.
Proof.
apply: divr_gt0 => //.
by apply: mulr_gt0; [rewrite ltr0n | exact: af_A0_gt0].
Qed.

Lemma af_t_gt0 : 0 < af_t.
Proof. by apply: divr_gt0; [exact: af_beta_gt0 | rewrite ltr0n]. Qed.

Lemma af_L1_gt0 : 0 < af_L1.
Proof.
have Mk2 : 2 <= af_Mk by rewrite le_max lexx.
apply: mulr_gt0; last by lra.
by apply: addr_gt0; [exact: ltr01 | rewrite invr_gt0 af_beta_gt0].
Qed.

Lemma af_Kf_gt0 : 0 < (1 + uni_K kappa K ^+ 4) ^+ 2.
Proof.
have : 0 <= uni_K kappa K ^+ 4 by rewrite exprn_even_ge0.
by move=> h; rewrite exprn_gt0 //; lra.
Qed.

Lemma af_A1_gt0 : 0 < af_A1.
Proof.
apply: mulr_gt0; last by rewrite exprn_gt0 // af_L1_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: af_Kf_gt0].
Qed.

Lemma af_eta_gt0 : 0 < af_eta.
Proof.
apply: divr_gt0; first exact: af_beta_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: af_A1_gt0].
Qed.

Lemma af_P1_gt0 : 0 < af_P1.
Proof.
apply: divr_gt0; last by rewrite exprn_gt0 // af_t_gt0.
apply: mulr_gt0; last by rewrite exprn_gt0 // af_L1_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: af_Kf_gt0].
Qed.

Lemma af_Q4 : 4 <= af_Q.
Proof. by rewrite le_max lexx. Qed.

Lemma af_Qe : 2 / eps <= af_Q.
Proof. by rewrite le_max lexx orbT. Qed.

Lemma af_gam_gt0 d : (0 < d)%N -> 0 < af_gam d.
Proof.
move=> d0; rewrite invr_gt0.
by apply: mulr_gt0; [rewrite ltr0n | rewrite sqrtr_gt0 ltr0n].
Qed.

(* n gamma >= (alpha / 2) sqrt d. *)
Lemma af_ngam d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  alpha / 2 * Num.sqrt d%:R <= N%:R * af_gam d.
Proof.
move=> d0 h1.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt d%:R :> RR by rewrite sqrtr_gt0.
have ss : Num.sqrt d%:R * Num.sqrt d%:R = d%:R :> RR.
  by rewrite -expr2 sqr_sqrtr // ler0n.
have dsd : 0 < d%:R * Num.sqrt d%:R :> RR by apply: mulr_gt0.
rewrite /af_gam ler_pdivlMr //.
apply: (le_trans _ h1); rewrite le_eqVlt; apply/orP; left; apply/eqP.
transitivity (alpha / 2 * d%:R * (Num.sqrt d%:R * Num.sqrt d%:R)); first by ring.
by rewrite ss expr2 mulrA.
Qed.

Lemma af_n36 d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  72 / alpha <= Num.sqrt d%:R -> 36 <= N%:R * af_gam d.
Proof.
move=> d0 h1 h6; apply: (le_trans _ (af_ngam d N d0 h1)).
by move: h6; rewrite ler_pdivrMr // => h; lra.
Qed.

Lemma af_T1 d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  2 / (alpha * af_eta ^+ 2) <= Num.sqrt d%:R ->
  (Num.sqrt (N%:R * af_gam d))^-1 <= af_eta.
Proof.
move=> d0 h1 h5.
have e0' := af_eta_gt0.
have e2 : 0 < af_eta ^+ 2 by rewrite exprn_gt0.
have h3 : (af_eta ^+ 2)^-1 <= N%:R * af_gam d.
  apply: (le_trans _ (af_ngam d N d0 h1)).
  have ae : 0 < alpha * af_eta ^+ 2 by apply: mulr_gt0.
  move: h5; rewrite ler_pdivrMr // => h.
  rewrite -[X in X <= _]mul1r ler_pdivrMr //.
  by move: h; set y := Num.sqrt d%:R; clearbody y; lra.
have X0 : 0 < N%:R * af_gam d by apply: lt_le_trans h3; rewrite invr_gt0.
have hX : af_eta^-1 <= Num.sqrt (N%:R * af_gam d).
  have ie : 0 < af_eta^-1 by rewrite invr_gt0.
  rewrite -[X in X <= _](gtr0_norm ie) -sqrtr_sqr.
  by apply: ler_wsqrtr; rewrite exprVn.
rewrite -[X in _ <= X]invrK lef_pV2 ?posrE ?invr_gt0 ?sqrtr_gt0 //.
Qed.

Lemma af_T2 d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  uni_tau kappa K d <= (kappa - 1) * alpha * af_eta / 4 ->
  4 / (alpha * af_eta) <= d%:R ->
  d%:R * (uni_tau kappa K d * d%:R / (kappa - 1) + 1) / N%:R <= af_eta.
Proof.
move=> d0 h1 ht h4.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have e0' := af_eta_gt0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have u1 : uni_tau kappa K d * d%:R / (kappa - 1) <= alpha * af_eta * d%:R / 4.
  rewrite ler_pdivrMr //.
  have := ler_wpM2r (ltW dR) ht.
  by move: (uni_tau kappa K d) => u h; lra.
have u2 : 1 <= alpha * af_eta * d%:R / 4.
  have ae : 0 < alpha * af_eta by apply: mulr_gt0.
  by move: h4; rewrite ler_pdivrMr // => h; lra.
rewrite ler_pdivrMr //.
move: u1 u2; set u := uni_tau kappa K d * d%:R / (kappa - 1) => u1 u2.
have hP : d%:R * (u + 1) <= d%:R * (alpha * af_eta * d%:R / 2).
  by apply: ler_wpM2l; [exact: ltW | lra].
have hN : af_eta * (alpha / 2 * d%:R ^+ 2) <= af_eta * N%:R.
  by apply: ler_wpM2l; [exact: ltW | exact: h1].
rewrite expr2 in hN.
by clearbody u; lra.
Qed.

Lemma af_err_small d N : (0 < d)%N -> (0 < N)%N ->
  alpha / 2 * d%:R ^+ 2 <= N%:R ->
  uni_tau kappa K d <= (kappa - 1) * alpha * af_eta / 4 ->
  4 / (alpha * af_eta) <= d%:R -> 2 / (alpha * af_eta ^+ 2) <= Num.sqrt d%:R ->
  af_err kappa K af_m af_M d N af_beta (af_gam d) <= af_beta / 8.
Proof.
move=> d0 N0 h1 ht h4 h5.
apply: le_trans (af_err_le kappa K af_m af_M d N af_beta (af_gam d) k1 d0 N0
  af_mM af_beta_gt0 (af_gam_gt0 d d0)) _.
rewrite -/af_Mk -/af_L1 -/af_A1.
have T12 := lerD (af_T1 d N d0 h1 h5) (af_T2 d N d0 h1 ht h4).
apply: le_trans (_ : af_A1 * (af_eta + af_eta) <= _).
  by apply: ler_wpM2l; [exact: ltW af_A1_gt0 | exact: T12].
have A1n : af_A1 != 0 := lt0r_neq0 af_A1_gt0.
by rewrite /af_eta le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma af_prob_small d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  2 / alpha * af_P1 * af_Q <= d%:R ->
  af_prob kappa K af_m af_M d N af_beta (af_gam d) af_t <= 1 / af_Q.
Proof.
move=> d0 h1 h7.
have dR : 1 <= d%:R :> RR by rewrite ler1n.
have dR0 : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have Q0 : 0 < af_Q by apply: (lt_le_trans _ af_Q4); rewrite ltr0n.
have t0 := af_t_gt0.
apply: le_trans (af_prob_le kappa K af_m af_M d N af_beta (af_gam d) af_t k1 d0
  af_mM af_beta_gt0 (af_gam_gt0 d d0) t0) _.
rewrite -/af_Mk -/af_L1.
have -> : 4 * (1 + uni_K kappa K ^+ 4) ^+ 2 * af_L1 ^+ 2 / (N%:R * af_t ^+ 2) =
    af_P1 / N%:R.
  have Nn : N%:R != 0 :> RR := lt0r_neq0 nR.
  have tn : af_t != 0 := lt0r_neq0 t0.
  by rewrite /af_P1; field.
have hN : af_P1 * af_Q <= N%:R.
  have h : alpha / 2 * (2 / alpha * af_P1 * af_Q) = af_P1 * af_Q.
    have an : alpha != 0 := lt0r_neq0 a0.
    by field.
  rewrite -h; apply: (le_trans _ h1).
  apply: ler_wpM2l; first by apply: ltW; apply: divr_gt0 => //; rewrite ltr0n.
  apply: (le_trans h7); rewrite expr2.
  by apply: ler_peMl; [exact: ler0n | exact: dR].
rewrite ler_pdivrMr // mul1r mulrC ler_pdivlMr //.
Qed.

Lemma af_wit_small d : (0 < d)%N -> 4 * af_cBp / af_beta <= Num.sqrt d%:R ->
  af_gam d * (d%:R * af_cB) <= af_beta / 4.
Proof.
move=> d0 h8.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have sd : 0 < Num.sqrt d%:R :> RR by rewrite sqrtr_gt0.
have b0 := af_beta_gt0.
have cc : af_cB <= af_cBp by rewrite le_max lexx.
have -> : af_gam d * (d%:R * af_cB) = af_cB / Num.sqrt d%:R.
  have dn : d%:R != 0 :> RR := lt0r_neq0 dR.
  have sn : Num.sqrt d%:R != 0 :> RR := lt0r_neq0 sd.
  by rewrite /af_gam; field.
rewrite ler_pdivrMr //.
move: h8; rewrite ler_pdivrMr // => h.
by move: cc h; set y := Num.sqrt d%:R; clearbody y; lra.
Qed.

Lemma af_union_small d N : (0 < d)%N -> N%:R <= 2 * alpha * d%:R ^+ 2 ->
  8 * alpha / eps <= d%:R ->
  N%:R * (2 * expR (- ((af_s d - af_B0) / af_L0))) <= eps / 2.
Proof.
move=> d0 h2 h9.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have L0 := af_L0_gt0.
have -> : expR (- ((af_s d - af_B0) / af_L0)) = (d%:R ^+ 3)^-1.
  have -> : (af_s d - af_B0) / af_L0 = 3%:R * ln d%:R.
    have Ln : af_L0 != 0 := lt0r_neq0 L0.
    by rewrite /af_s; field.
  by rewrite expRN expRM_natl lnK // posrE.
have d3 : 0 < d%:R ^+ 3 :> RR by rewrite exprn_gt0.
have c0 : 0 <= 2 * (d%:R ^+ 3)^-1 :> RR by rewrite mulr_ge0 // invr_ge0 ltW.
apply: le_trans (ler_wpM2r c0 h2) _.
have -> : 2 * alpha * d%:R ^+ 2 * (2 * (d%:R ^+ 3)^-1) = 4 * alpha / d%:R.
  have dn : d%:R != 0 :> RR := lt0r_neq0 dR.
  by field.
rewrite ler_pdivrMr //.
by move: h9; rewrite ler_pdivrMr // => h; lra.
Qed.

(* The event of Theorem 2.9 for the data. *)
Definition af_F1 d N : set (N.-tuple 'rV[RR]_(d * d)) :=
  [set Z | (af_err kappa K af_m af_M d N af_beta (af_gam d) + af_t <
     `|af_value kappa af_m af_M d N af_beta (af_gam d) Z -
       af_center kappa af_m af_M d N af_beta (af_gam d)|)%R].

(* The approximate fit at one large dimension d with N samples, given the
   Gaussian witness at d. *)
Lemma af_at_d (nu : nat -> probability (measurableTypeR R) R) (d N : nat) :
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  (0 < d)%N ->
  alpha / 2 * d%:R ^+ 2 <= N%:R -> N%:R <= 2 * alpha * d%:R ^+ 2 ->
  uni_tau kappa K d <= (kappa - 1) * alpha * af_eta / 4 ->
  4 / (alpha * af_eta) <= d%:R ->
  2 / (alpha * af_eta ^+ 2) <= Num.sqrt d%:R ->
  72 / alpha <= Num.sqrt d%:R ->
  2 / alpha * af_P1 * af_Q <= d%:R ->
  4 * af_cBp / af_beta <= Num.sqrt d%:R ->
  8 * alpha / eps <= d%:R ->
  1 <= ln (d%:R : RR) ->
  (exists E : set (N.-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) N E <= (1 / 4)%:E)%E &
    forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
      forall v : 'rV[R]_d,
        m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
      \tr S = d%:R &
      forall i, mxdot (tnth Z i) (mxvec S) = 0]]) ->
  exists E : set (N.-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> data_feature_law nu d) N E <= eps%:E)%E &
    forall Z, ~ E Z -> exists (theta : 'rV[R]_(d * d)) (b : R), [/\
      pd_slice2 d af_m af_M theta,
      \sum_(i < N) (b - mxdot (tnth Z i) theta) ^+ 2 <= delta * N%:R &
      forall i, `|b - mxdot (tnth Z i) theta| <= af_C * ln d%:R]].
Proof.
move=> hnu d0 h1 h2 ht h4 h5 h6 h7 h8 h9 hl [EG [mEG PEG hEG]].
have [m_pos mm0 m1 M0M M1] := af_dom.
have mM := af_mM.
have b0 := af_beta_gt0.
have t0 := af_t_gt0.
have A0 := af_A0_gt0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have N0 : (0 < N)%N by rewrite -(ltr_nat RR).
have g0 := af_gam_gt0 d d0.
have n36 := af_n36 d N d0 h1 h6.
have l0 : 0 < opnorm (unsat_cov kappa d) := af_lam_gt0 kappa d k1 d0.
have herr := af_err_small d N d0 N0 h1 ht h4 h5.
have hprob := af_prob_small d N d0 h1 h7.
have Q4 := af_Q4.
have Qe := af_Qe.
have Q0 : 0 < af_Q by apply: (lt_le_trans _ Q4); rewrite ltr0n.
have hQ4 : 1 / af_Q <= 1 / 4 by rewrite !div1r lef_pV2 ?posrE ?ltr0n.
have hQe : 1 / af_Q <= eps / 2.
  have p2 : 0 < 2 / eps by rewrite divr_gt0 // ltr0n.
  by rewrite div1r -[eps / 2]invf_div lef_pV2 ?posrE.
(* the center of the Gaussian features *)
have hc : af_center kappa af_m af_M d N af_beta (af_gam d) <=
    af_beta * af_Mk * af_M + af_beta / 4 +
    af_err kappa K af_m af_M d N af_beta (af_gam d) + af_t.
  apply: (af_center_le kappa K af_m af_M d N af_beta (af_gam d) af_t k1 d0 N0 mM
    b0 g0 t0 n36 EG _ mEG PEG); first exact: le_trans hprob hQ4.
  move=> Z nZ; have [S [Ssym hS Str hZS]] := hEG Z nZ.
  have [DS BS] := slice2_witness d af_m af_M m0 M0 S mM mm0 M0M Ssym Str hS.
  apply: le_trans (af_value_witness kappa af_m af_M d N af_beta (af_gam d) k1 d0
    m_pos mM b0 g0 Z S DS hZS) _.
  rewrite /af_Mk lerD2l.
  apply: le_trans (af_wit_small d d0 h8).
  by apply: ler_wpM2l; [exact: ltW | exact: BS].
(* the data value is at most beta A0, except on af_F1 *)
have mF1 : measurable (af_F1 d N).
  apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
  apply: measurable_funB => //.
  exact: (measurable_af_value kappa af_m af_M d N af_beta (af_gam d) mM b0 g0).
have PF1 : (tuple_prod (fun=> data_feature_law nu d) N (af_F1 d N) <=
    (af_prob kappa K af_m af_M d N af_beta (af_gam d) af_t)%:E)%E.
  exact: (af_conc kappa K af_m af_M d N af_beta (af_gam d) af_t k1 d0 N0 mM b0
    g0 t0 n36 _ (uni_regular_data kappa K k1 nu d hnu d0)).
have hV Z : ~ af_F1 d N Z ->
    af_value kappa af_m af_M d N af_beta (af_gam d) Z <= af_beta * af_A0.
  rewrite /af_F1 /= => /negP; rewrite -leNgt => /ler_normlP [_ h].
  exact: (af_arith_value _ _ _ _ _ _ b0 h herr hc).
(* the leave-one-out residuals are at most s, except on F2 *)
have [mF2 PF2] := af_union_le N d (tuple_prod (fun=> data_feature_law nu d) N)
  (fun i => sat_bad af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
    (af_gam d) mM l0 b0 g0 i (af_s d) af_B0)
  (fun i => measurable_sat_bad af_m af_M d N (opnorm (unsat_cov kappa d))
    af_beta (af_gam d) mM l0 b0 g0 i (af_s d) af_B0).
have PF2' : (tuple_prod (fun=> data_feature_law nu d) N
    (\big[setU/set0]_(i < N) sat_bad af_m af_M d N (opnorm (unsat_cov kappa d))
       af_beta (af_gam d) mM l0 b0 g0 i (af_s d) af_B0) <= (eps / 2)%:E)%E.
  apply: le_trans PF2 _.
  apply: le_trans (_ : (\sum_(i < N)
      (2 * expR (- ((af_s d - af_B0) / af_L0)))%:E <= _)%E).
    apply: lee_sum => i _.
    exact: (sat_loo_tail af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
      (af_gam d) m_pos mM l0 b0 g0 kappa K nu hnu K0 d0 i (af_s d) af_B0).
  rewrite sumEFin sumr_const card_ord lee_fin -[X in X <= _]mulr_natl.
  exact: af_union_small d N d0 h2 h9.
exists (af_F1 d N `|` \big[setU/set0]_(i < N) sat_bad af_m af_M d N
  (opnorm (unsat_cov kappa d)) af_beta (af_gam d) mM l0 b0 g0 i (af_s d) af_B0).
split.
- exact: measurableU.
- apply: le_trans (measureU2 _ mF1 mF2) _.
  apply: le_trans (leeD PF1 PF2') _.
  by rewrite -EFinD lee_fin; exact: (af_arith_sum _ _ _ hprob hQe).
move=> Z nZ.
have nF1 : ~ af_F1 d N Z by move=> h; apply: nZ; left.
have hVZ := hV Z nF1.
exists (sat_min af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta (af_gam d)
  mM l0 b0 g0 predT Z).
exists (sat_int af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta (af_gam d)
  mM l0 b0 g0 predT Z).
split.
- exact: sat_min_in.
- have h := sat_loss_le af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
    (af_gam d) mM l0 b0 g0 Z.
  have n2 : 0 < N%:R *+ 2 :> RR by rewrite mulrn_wgt0.
  rewrite ler_pdivrMl // in h.
  apply: le_trans h _.
  apply: le_trans (ler_wpM2l (ltW n2) hVZ) _.
  rewrite /af_beta le_eqVlt; apply/orP; left; apply/eqP.
  have A0n : af_A0 != 0 := lt0r_neq0 A0.
  by rewrite -mulr_natl; field.
move=> i.
have hnb : ~ sat_bad af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
    (af_gam d) mM l0 b0 g0 i (af_s d) af_B0 Z.
  by move=> h; apply: nZ; right; exact: af_in_bigsetU h.
have hb := sat_loo_int af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
  (af_gam d) mM l0 b0 g0 Z i.
have hcmp := sat_loo_compare af_m af_M d N (opnorm (unsat_cov kappa d))
  af_beta (af_gam d) mM N0 l0 b0 g0 Z i.
have hbi : `|sat_int af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
    (af_gam d) mM l0 b0 g0 (fun j => j != i) Z| <= af_B0.
  have h := le_trans hb hVZ.
  rewrite ler_pM2l // in h.
  by rewrite /af_B0 -sqrtr_sqr; apply: ler_wsqrtr.
have hri : `|sat_int af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
    (af_gam d) mM l0 b0 g0 (fun j => j != i) Z -
    mxdot (tnth Z i) (sat_min af_m af_M d N (opnorm (unsat_cov kappa d)) af_beta
      (af_gam d) mM l0 b0 g0 (fun j => j != i) Z)| <= af_s d.
  by rewrite leNgt; apply/negP => h; apply: hnb; split.
apply: (@le_trans _ _ (af_s d)).
  apply: le_trans hri.
  by rewrite -sqrtr_sqr -[X in _ <= X]sqrtr_sqr; apply: ler_wsqrtr.
have hB : af_B0 <= af_B0 * ln (d%:R : RR).
  by rewrite ler_peMr // /af_B0 sqrtr_ge0.
by rewrite /af_s /af_C [(af_B0 + _) * _]mulrDl; apply: lerD.
Qed.

End af_eps.

End af_main.

(* Proposition 1.4 (i) in the form of the hypothesis: Lemma 5.17 of
   Gaussian/Subcritical (item G9, lane B). *)
Lemma gaussian_subcritical_fit_holds (kappa alpha : R) :
  1 < kappa -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  gaussian_subcritical_fit kappa alpha.
Proof. exact: gaussian_fit_below_threshold. Qed.

(* Proposition 2.1, the approximate fit, for the features of the data:
   below the threshold, with probability tending to one, some S with
   m I < S < M I and tr S = d and some b have
     sum_i (b - <W_i, S>)^2 <= delta n   and   |b - <W_i, S>| <= C ln d,
   for every delta > 0, with m, M and C depending only on alpha, kappa
   and K. *)
Theorem approximate_fit (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  exists m M C : R, [/\ 0 < m, m < 1, 1 < M, 0 < C &
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall delta eps : R, 0 < delta -> 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> data_feature_law (nu d) d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> exists (theta : 'rV[R]_(d * d)) (b : R), [/\
      pd_slice2 d m M theta,
      \sum_(i < n d) (b - mxdot (tnth Z i) theta) ^+ 2 <= delta * (n d)%:R &
      forall i, `|b - mxdot (tnth Z i) theta| <= C * ln d%:R]]].
Proof.
move=> k1 K0 a0 aast.
have [m0 [M0 [m00 mM0 hG]]] := gaussian_subcritical_fit_holds kappa alpha k1 a0 aast.
have [m_pos _ m1 _ M1] := af_dom m0 M0 m00.
exists (af_m m0), (af_M M0), (af_C kappa K M0); split => //.
  exact: af_C_gt0.
move=> nu hnu n hn delta eps dl0 e0.
have eta0 := af_eta_gt0 kappa K m0 M0 m00 delta dl0.
have te : 0 < (kappa - 1) * alpha * af_eta kappa K M0 delta / 4.
  apply: divr_gt0; last by rewrite ltr0n.
  by apply: mulr_gt0 => //; apply: mulr_gt0 => //; rewrite subr_gt0.
have q4 : (0 : RR) < 1 / 4 by rewrite divr_gt0 // ltr0n.
have [Dn hDn] := af_ev_density n alpha a0 hn.
have [Dt hDt] := af_ev_tau kappa K _ k1 te.
have [D1 hD1] := af_ev_ge (4 / (alpha * af_eta kappa K M0 delta)).
have [D2 hD2] := af_ev_sqrt (2 / (alpha * af_eta kappa K M0 delta ^+ 2)).
have [D3 hD3] := af_ev_sqrt (72 / alpha).
have [D4 hD4] := af_ev_ge (2 / alpha * af_P1 kappa K M0 delta *
  af_Q eps).
have [D5 hD5] := af_ev_sqrt (4 * af_cBp m0 M0 / af_beta kappa M0 delta).
have [D6 hD6] := af_ev_ge (8 * alpha / eps).
have [DG hDG] := hG n hn (1 / 4)%R q4.
exists (maxn (maxn (maxn Dn Dt) (maxn D1 D2))
  (maxn (maxn D3 D4) (maxn (maxn D5 D6) (maxn DG
     (archimedean.Num.truncn (expR (1 : RR))).+1)))) => d.
rewrite !geq_max => /andP[/andP[/andP[dn dt] /andP[d1 d2]]
  /andP[/andP[d3 d4] /andP[/andP[d5 d6] /andP[dg de]]]].
have [d0 [h1 h2]] := hDn d dn.
exact: (af_at_d kappa K alpha m0 M0 k1 K0 a0 m00 delta eps dl0 e0 (nu d)
  d (n d) (fun j jd => hnu d j jd) d0 h1 h2 (hDt d dt) (hD1 d d1) (hD2 d d2)
  (hD3 d d3) (hD4 d d4) (hD5 d d5) (hD6 d d6) (ln_ge1 d de) (hDG d dg)).
Qed.
