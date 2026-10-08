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

   Hypothesis. gaussian_subcritical_fit kappa alpha is Proposition 1.4 (i)
   (Lemma 5.17, item G9 of lane B, Gaussian/Subcritical) in the form that
   requests/a-to-b.md asks for: there are 0 < m0 <= M0 such that, with
   probability tending to one under the Gaussian features of law
   gaussian_feature_law kappa d, some symmetric S has m0 I <= S <= M0 I,
   tr S = d and <G_i, S> = 0 for every i.

   Planned result (names come with the proofs):
   - approximate_fit: under gaussian_subcritical_fit kappa alpha, there are
     0 < m < 1 < M and C > 0, depending only on alpha, kappa and K, such
     that with probability tending to one some S with mxvec S in
     pd_slice2 d m M (m I < S < M I and tr S = d) and some real b satisfy
       sum_i (<W_i, S> - b)^2 <= C n / ln d   and
       |<W_i, S> - b| <= C ln d for every i.
     The paper's rates are (ln d / d)^(1/10) and (ln d)^2; any rates o(1)
     and o(sqrt d / (ln d)^4) suit Theorem 1.9 (Sat/Interpolation, lane C).

   Route (the paper's, with the barrier kept).
   1. Theorem 2.9 (barrier_lindeberg_concentration of
      convex/barrier_lindeberg.v) on the domain pd_slice2 d m M, with
      m = m0 / 2, M = 2 M0 and its 2d-self-concordant barrier
      logdet_barrier2 (Lemma 2.8, convex/logdet_barrier.v), and with
      beta = 1 / ln d and gamma = 1 / (d ln d), for the data features and
      for the Gaussian ones (both regular: uni_regular_data and
      uni_regular_gauss of Unsat/Universality). Both values Phi_W and Phi_G
      are within O(1 / ln d) of E Phi_G with probability tending to one.
   2. The Gaussian witness S of the hypothesis is in the domain, with
      b = 0: Phi_G <= beta lambda |S|_F^2 + gamma B(S) = O(1 / ln d).
      Hence E Phi_G and then Phi_W are O(1 / ln d) = O(beta).
   3. A minimizer (S, b) of the full objective (ls_barrier_minimizer of
      convex/minimizers.v) has sum_i (<W_i, S> - b)^2 <= 2 n Phi_W.
   4. The leave-one-out minimizers (S^(i), b^(i)) are measurable functions
      of the other rows (measurable_ls_min of
      library/probability/measurable_minimizer.v), with
      beta (b^(i))^2 <= Phi_W, so |b^(i)| = O(1), and
      |<W_i, S> - b| <= |<W_i, S^(i)> - b^(i)| (add the two optimality
      inequalities). Given the other rows, <W_i, S^(i)> is subexponential
      with constant 252 K^2 sqrt M (Hanson-Wright,
      data_feature_subexponential of Features/Regular, as
      |S^(i)|_F^2 <= M d), so a union bound over the n rows gives
      max_i |<W_i, S> - b| = O(ln d).

   Proved so far:
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
   - af_conc, af_ref_scale_le, af_value_witness: Theorem 2.9 on the domain
     for any regular law with the constants of the Gaussian features, the
     reference scale (1 + 1 / beta) (1 + max (2, kappa - 1)), and the value
     at a Gaussian witness. *)

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
From EllipsoidUniversality.Unsat Require Import Universality.

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

End af_fixed.
