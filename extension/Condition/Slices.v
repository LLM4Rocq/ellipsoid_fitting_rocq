(* The approximate fit on finitely many two-sided slices, at Stdlib's R:
   item Q6 of phase 8 (notes/three-extensions-plan.md, sections 2 and 5.2;
   lane A). It generalizes af_at_d of Sat/ApproximateFit.v, which keeps its
   name and statement, as approximate_fit_law does.

   The objective is that of the section sat_values of
   Sat/ApproximateFit.v on pd_slice2 d m M with fixed 0 < m < 1 < M: the
   square loss with an intercept, the ridge and the barrier
   logdet_barrier2, with the weight gamma = af_gam d = 1 / (d sqrt d) in
   section 3. af_value is its value, and af_center its Gaussian center,
   the mean of af_value under the Gaussian features.

   Main results.
   - af_value_approx: the value at an approximate witness. For mxvec S in
     pd_slice2 d m M, af_value Z <= (1 / (2 n)) sum_i <Z_i, S>^2
     + beta Mk M + gamma Bar (mxvec S), with Mk = af_Mk kappa
     = max (2, kappa - 1).
   - af_center_ge: the lower bound of a center. If af_value >= g outside a
     Gaussian event of probability at most 1/2, then af_center >= g / 2.
     af_value is nonnegative, since the barrier is (af_value_ge0), and
     integrable under the Gaussian features (af_value_integrable, from
     int_Phi).
   - af_center_choice: the choice of a slice. Take finitely many slices
     j < J, each with its own m, M, beta and t. Suppose that, outside a
     Gaussian event of probability at most 1/4, the value of some slice j
     is at most w j, and that the probabilities af_prob of Theorem 2.9
     (af_conc) of the J slices sum to at most 1/2. Then some slice j has
     af_center <= w j + af_err + t, with the center, the error and t of
     that slice. This gives a deterministic choice of the slice at each d.
   - slice_at_d: af_at_d on the slice pd_slice2 d m M, with the bound
     af_center <= beta Mk M + beta / 4 + af_err + t on its Gaussian
     center as a hypothesis, in place of an exact Gaussian witness. The
     constants are those of af_main written in m and M: A0 = Mk M + 1
     (sl_A0), B0 = sqrt A0, L0 = sat_tail_const M Ls, C = B0 + 3 L0
     (sl_C), beta = delta / (2 A0) (sl_beta) and t = beta / 8 (sl_t). The
     dimension thresholds are explicit inequalities in these constants,
     so a common threshold for finitely many slices is a maximum. *)

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
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.convex Require Import self_concordant least_squares.
From GaussianAnalysis.convex Require Import logdet_barrier barrier_lindeberg.
From GaussianAnalysis.convex Require Import feature_moments ridge_comparison.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Sat Require Import ApproximateFit.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. One slice and one dimension: the value at an approximate witness and
   the lower bound of the center. *)

Section slice_fixed.
Variables (kappa Kf : R) (m M : R) (d n : nat) (beta gamma tau : R).
Hypotheses (k1 : 1 < kappa) (d0 : (0 < d)%N) (m_pos : 0 < m).
Hypotheses (mM : m < 1 < M) (b0 : 0 < beta) (g0 : 0 < gamma).

Local Notation T := (n.-tuple 'rV[RR]_(d * d)).
Local Notation Bar := (logdet_barrier2 d m M).

(* The value at features for which S, in the slice, is an approximate
   witness: the square loss of S with the intercept 0, the ridge cost and
   the barrier cost of S. *)
Lemma af_value_approx (Z : T) (S : 'M[R]_d) : pd_slice2 d m M (mxvec S) ->
  af_value kappa m M d n beta gamma Z <=
    (n%:R *+ 2)^-1 * \sum_(i < n) mxdot (tnth Z i) (mxvec S) ^+ 2 +
    beta * af_Mk kappa * M + gamma * Bar (mxvec S).
Proof.
move=> DS.
have l0 := af_lam_gt0 kappa d k1 d0.
rewrite /af_value (sat_valueE m M d n _ beta gamma mM l0 b0 g0).
apply: le_trans (sat_minP m M d n _ beta gamma mM l0 b0 g0 predT Z
  (mxvec S) 0 DS) _.
rewrite /sat_obj /ls_barrier_objective /ls_ridge /ls_loss.
rewrite expr0n /= addr0 lerD2r.
apply: lerD.
  apply: ler_wpM2l; first exact: (sat_s0 n).
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_bigr => i _; rewrite sub0r sqrrN.
rewrite -mulrA; apply: ler_wpM2l; first exact: ltW.
have hF := slice2_frobenius d m M (mxvec S) (ltW m_pos) DS.
have hl := af_lam_le kappa d k1 d0.
have M0 : 0 < M by case/andP: mM => _ /(lt_trans ltr01).
have h1 : opnorm (unsat_cov kappa d) * mxdot (mxvec S) (mxvec S) <=
    opnorm (unsat_cov kappa d) * (M * d%:R).
  by rewrite ler_wpM2l // ltW.
apply: le_trans h1 _.
rewrite mulrCA [af_Mk kappa * M]mulrC; apply: ler_wpM2l; first exact: ltW.
exact: hl.
Qed.

Hypothesis hG :
  regular_feature Kf tau (unsat_cov kappa d) (gaussian_feature_law kappa d).

Local Notation P := (tuple_prod (fun=> gaussian_feature_law kappa d) n).

(* The value is nonnegative and integrable under the Gaussian features. *)
Lemma af_value_ge0 (Z : T) : 0 <= af_value kappa m M d n beta gamma Z.
Proof.
apply: ls_barrier_value_ge0; [exact: opnorm_ge0 | exact: ltW | exact: ltW |].
exact: (sat_B0 m M d mM).
Qed.

Lemma af_value_integrable :
  P.-integrable setT (EFin \o af_value kappa m M d n beta gamma).
Proof.
exact: (int_Phi (sat_DV m M d) (sat_scB m M d) (sat_B0 m M d mM)
  (sat_D0 m M d mM) n b0 g0 (fun=> hG)).
Qed.

(* The lower bound of the center: if the value is at least g outside an
   event of Gaussian probability at most 1/2, the center is at least
   g / 2. *)
Lemma af_center_ge (E : set T) (g : R) : measurable E ->
  (P E <= (1 / 2)%:E)%E ->
  (forall Z, ~ E Z -> g <= af_value kappa m M d n beta gamma Z) ->
  g / 2 <= af_center kappa m M d n beta gamma.
Proof.
move=> mE PE hg.
have c0 : 0 <= af_center kappa m M d n beta gamma.
  by apply: Rintegral_ge0 => Z _; exact: af_value_ge0.
have [gle|gpos] := leP g 0.
  by apply: le_trans c0; rewrite pmulr_lle0 // invr_gt0 ltr0n.
have mEc : measurable (~` E) := measurableC mE.
have ii : P.-integrable setT (EFin \o (fun Z => g * \1_(~` E) Z)) :=
  integrableRZl g (f := \1_(~` E)) (integrable_indic P mEc).
have h1 : \int[P]_Z (g * \1_(~` E) Z) <= af_center kappa m M d n beta gamma.
  apply: le_Rintegral => //; first exact: af_value_integrable.
  move=> Z _; rewrite /indic; have [ZE|ZE] := boolP (Z \in ~` E).
    by rewrite mulr1; apply: hg; rewrite inE in ZE.
  by rewrite mulr0; exact: af_value_ge0.
apply: le_trans h1.
rewrite (RintegralZl g measurableT (integrable_indic P mEc)).
have hI : \int[P]_x \1_(~` E) x = fine (P (~` E)).
  by rewrite /Rintegral integral_indic // setIT.
rewrite hI (probability_setC P mE).
have fE : P E \is a fin_num by rewrite ge0_fin_numE // (le_lt_trans PE) ?ltry.
have hE : fine (P E) <= 1 / 2 by rewrite -lee_fin fineK.
rewrite fineB // /=.
apply: ler_wpM2l; first exact: ltW.
by move: hE; lra.
Qed.

End slice_fixed.

(* 2. Finitely many slices: a union bound, and the deterministic choice of
   a slice whose Gaussian center is small. *)

Lemma slice_union_le {J : nat} {dT} {T : measurableType dT}
    (P : probability T RR) {F : 'I_J -> set T} :
  (forall j, measurable (F j)) ->
  measurable (\big[setU/set0]_(j < J) F j) /\
  (P (\big[setU/set0]_(j < J) F j) <= \sum_(j < J) P (F j))%E.
Proof.
move=> mF.
apply: (big_ind2 (fun (A : set T) (x : \bar RR) =>
  measurable A /\ (P A <= x)%E)).
- by split; [exact: measurable0 | rewrite measure0].
- move=> A x B y [mA hA] [mB hB]; split; first exact: measurableU.
  by apply: le_trans (measureU2 P mA mB) _; exact: leeD.
- by move=> j _; split.
Qed.

Section slice_choice.
Variables (kappa Kf : R) (d n : nat) (J : nat).
Variables (ms Ms bs ts : 'I_J -> R) (gamma tau : R).
Hypotheses (n0 : (0 < n)%N) (mM : forall j, ms j < 1 < Ms j).
Hypotheses (b0 : forall j, 0 < bs j) (g0 : 0 < gamma) (t0 : forall j, 0 < ts j).
Hypotheses (n36 : 36 <= n%:R * gamma) (tau0 : 0 <= tau).
Hypothesis hG :
  regular_feature Kf tau (unsat_cov kappa d) (gaussian_feature_law kappa d).

Local Notation T := (n.-tuple 'rV[RR]_(d * d)).
Local Notation P := (tuple_prod (fun=> gaussian_feature_law kappa d) n).
Local Notation value j := (af_value kappa (ms j) (Ms j) d n (bs j) gamma).
Local Notation center j := (af_center kappa (ms j) (Ms j) d n (bs j) gamma).
Local Notation err j := (af_err kappa Kf (ms j) (Ms j) d n (bs j) gamma tau).
Local Notation prob j :=
  (af_prob kappa Kf (ms j) (Ms j) d n (bs j) gamma (ts j)).

(* If, outside a measurable event of Gaussian probability at most 1/4, the
   value of some slice j is at most w j, and the probabilities of Theorem
   2.9 for the J slices sum to at most 1/2, then some slice j has a center
   at most w j + err j + t j. *)
Lemma af_center_choice (E : set T) (w : 'I_J -> R) : measurable E ->
  (P E <= (1 / 4)%:E)%E -> \sum_(j < J) prob j <= 1 / 2 ->
  (forall Z, ~ E Z -> exists j, value j Z <= w j) ->
  exists j, center j <= w j + err j + ts j.
Proof.
move=> mE PE hp hw.
pose F j := [set Z : T | (err j + ts j < `|value j Z - center j|)%R].
have mF j : measurable (F j).
  apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
  apply: measurable_funB => //.
  exact: (measurable_af_value kappa (ms j) (Ms j) d n (bs j) gamma (mM j)
    (b0 j) g0).
have PF j : (P (F j) <= (prob j)%:E)%E.
  exact: (af_conc kappa Kf (ms j) (Ms j) d n (bs j) gamma (ts j) tau n0 (mM j)
    (b0 j) g0 (t0 j) n36 tau0 hG _ hG).
have [mU PU] := slice_union_le P mF.
have [Z [nE nF]] : exists Z, ~ E Z /\ ~ (\big[setU/set0]_(j < J) F j) Z.
  apply: contrapT => hno.
  have cover : [set: T] `<=` E `|` \big[setU/set0]_(j < J) F j.
    move=> Z _; apply: contrapT => hZ; apply: hno; exists Z.
    by split => h; apply: hZ; [left|right].
  have h1 : (P [set: T] <= P (E `|` \big[setU/set0]_(j < J) F j))%E.
    apply: le_measure; last exact: cover.
    - by rewrite inE.
    - by rewrite inE; exact: measurableU.
  have h2 := measureU2 P mE mU.
  have h3 : (P (\big[setU/set0]_(j < J) F j) <= (1 / 2)%:E)%E.
    apply: le_trans PU _.
    apply: le_trans (_ : (\sum_(j < J) (prob j)%:E <= _)%E).
      by apply: lee_sum => j _; exact: PF.
    by rewrite sumEFin lee_fin.
  have := le_trans h1 (le_trans h2 (leeD PE h3)).
  by rewrite probability_setT -EFinD lee_fin; lra.
have [j hj] := hw Z nE.
exists j.
have nFj : ~ F j Z by move=> h; apply: nF; exact: af_in_bigsetU h.
have : ~ (err j + ts j < `|value j Z - center j|) := nFj.
move/negP; rewrite -leNgt => /ler_normlP [h1 _].
by lra.
Qed.

End slice_choice.

(* 3. The approximate fit on one slice pd_slice2 d m M from a bound on the
   Gaussian center, with the constants of af_main of Sat/ApproximateFit.v
   written in m and M: A0 = Mk M + 1, B0 = sqrt A0, L0 = sat_tail_const M Ls,
   C = B0 + 3 L0; for delta and eps, beta = delta / (2 A0), t = beta / 8 and
   gamma = af_gam d = 1 / (d sqrt d). *)

Section slice_main.
Variables (kappa Kf Ls alpha m M : R).
Hypotheses (k1 : 1 < kappa) (Ls0 : 0 < Ls) (a0 : 0 < alpha).
Hypotheses (m_pos : 0 < m) (mM : m < 1 < M).

Definition sl_A0 : RR := af_Mk kappa * M + 1.
Definition sl_B0 : RR := Num.sqrt sl_A0.
Definition sl_L0 : RR := sat_tail_const M Ls.
Definition sl_C : RR := sl_B0 + 3 * sl_L0.

Lemma sl_M_gt0 : 0 < M.
Proof. by case/andP: mM => _ /(lt_trans ltr01). Qed.

Lemma sl_A0_gt0 : 0 < sl_A0.
Proof.
have Mk2 : 2 <= af_Mk kappa by rewrite le_max lexx.
have M0 := sl_M_gt0.
have : 0 < af_Mk kappa * M by apply: mulr_gt0 => //; lra.
by rewrite /sl_A0; lra.
Qed.

Lemma sl_L0_gt0 : 0 < sl_L0.
Proof.
by rewrite /sl_L0 /sat_tail_const; apply: mulr_gt0 => //; rewrite sqrtr_gt0;
  exact: sl_M_gt0.
Qed.

Lemma sl_C_gt0 : 0 < sl_C.
Proof.
have := sl_L0_gt0; have := sqrtr_ge0 sl_A0.
by rewrite /sl_C /sl_B0; lra.
Qed.

Section slice_eps.
Variables (delta eps : R).
Hypotheses (dl0 : 0 < delta) (e0 : 0 < eps).

Definition sl_beta : RR := delta / (2 * sl_A0).
Definition sl_t : RR := sl_beta / 8.
Definition sl_L1 : RR := (1 + sl_beta^-1) * (1 + af_Mk kappa).
Definition sl_A1 : RR := 100 * (1 + Kf ^+ 4) ^+ 2 * sl_L1 ^+ 2.
Definition sl_eta : RR := sl_beta / (16 * sl_A1).
Definition sl_P1 : RR :=
  4 * (1 + Kf ^+ 4) ^+ 2 * sl_L1 ^+ 2 / sl_t ^+ 2.
Definition sl_s (d : nat) : RR := sl_B0 + 3 * sl_L0 * ln d%:R.

Lemma sl_beta_gt0 : 0 < sl_beta.
Proof.
apply: divr_gt0 => //.
by apply: mulr_gt0; [rewrite ltr0n | exact: sl_A0_gt0].
Qed.

Lemma sl_t_gt0 : 0 < sl_t.
Proof. by apply: divr_gt0; [exact: sl_beta_gt0 | rewrite ltr0n]. Qed.

Lemma sl_L1_gt0 : 0 < sl_L1.
Proof.
have Mk2 : 2 <= af_Mk kappa by rewrite le_max lexx.
apply: mulr_gt0; last by lra.
by apply: addr_gt0; [exact: ltr01 | rewrite invr_gt0 sl_beta_gt0].
Qed.

Lemma sl_Kf_gt0 : 0 < (1 + Kf ^+ 4) ^+ 2.
Proof.
have : 0 <= Kf ^+ 4 by rewrite exprn_even_ge0.
by move=> h; rewrite exprn_gt0 //; lra.
Qed.

Lemma sl_A1_gt0 : 0 < sl_A1.
Proof.
apply: mulr_gt0; last by rewrite exprn_gt0 // sl_L1_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: sl_Kf_gt0].
Qed.

Lemma sl_eta_gt0 : 0 < sl_eta.
Proof.
apply: divr_gt0; first exact: sl_beta_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: sl_A1_gt0].
Qed.

Lemma sl_P1_gt0 : 0 < sl_P1.
Proof.
apply: divr_gt0; last by rewrite exprn_gt0 // sl_t_gt0.
apply: mulr_gt0; last by rewrite exprn_gt0 // sl_L1_gt0.
by apply: mulr_gt0; [rewrite ltr0n | exact: sl_Kf_gt0].
Qed.

Lemma sl_T1 d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  2 / (alpha * sl_eta ^+ 2) <= Num.sqrt d%:R ->
  (Num.sqrt (N%:R * af_gam d))^-1 <= sl_eta.
Proof.
move=> d0 h1 h5.
have e0' := sl_eta_gt0.
have e2 : 0 < sl_eta ^+ 2 by rewrite exprn_gt0.
have h3 : (sl_eta ^+ 2)^-1 <= N%:R * af_gam d.
  apply: (le_trans _ (af_ngam alpha d N d0 h1)).
  have ae : 0 < alpha * sl_eta ^+ 2 by apply: mulr_gt0.
  move: h5; rewrite ler_pdivrMr // => h.
  rewrite -[X in X <= _]mul1r ler_pdivrMr //.
  by move: h; set y := Num.sqrt d%:R; clearbody y; lra.
have X0 : 0 < N%:R * af_gam d by apply: lt_le_trans h3; rewrite invr_gt0.
have hX : sl_eta^-1 <= Num.sqrt (N%:R * af_gam d).
  have ie : 0 < sl_eta^-1 by rewrite invr_gt0.
  rewrite -[X in X <= _](gtr0_norm ie) -sqrtr_sqr.
  by apply: ler_wsqrtr; rewrite exprVn.
rewrite -[X in _ <= X]invrK lef_pV2 ?posrE ?invr_gt0 ?sqrtr_gt0 //.
Qed.

Lemma sl_T2 d N tau : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  tau <= (kappa - 1) * alpha * sl_eta / 4 ->
  4 / (alpha * sl_eta) <= d%:R ->
  d%:R * (tau * d%:R / (kappa - 1) + 1) / N%:R <= sl_eta.
Proof.
move=> d0 h1 ht h4.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have e0' := sl_eta_gt0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have u1 : tau * d%:R / (kappa - 1) <= alpha * sl_eta * d%:R / 4.
  rewrite ler_pdivrMr //.
  have := ler_wpM2r (ltW dR) ht.
  by move=> h; lra.
have u2 : 1 <= alpha * sl_eta * d%:R / 4.
  have ae : 0 < alpha * sl_eta by apply: mulr_gt0.
  by move: h4; rewrite ler_pdivrMr // => h; lra.
rewrite ler_pdivrMr //.
move: u1 u2; set u := tau * d%:R / (kappa - 1) => u1 u2.
have hP : d%:R * (u + 1) <= d%:R * (alpha * sl_eta * d%:R / 2).
  by apply: ler_wpM2l; [exact: ltW | lra].
have hN : sl_eta * (alpha / 2 * d%:R ^+ 2) <= sl_eta * N%:R.
  by apply: ler_wpM2l; [exact: ltW | exact: h1].
rewrite expr2 in hN.
by clearbody u; lra.
Qed.

Lemma sl_err_small d N tau : (0 < d)%N -> (0 < N)%N -> 0 <= tau ->
  alpha / 2 * d%:R ^+ 2 <= N%:R ->
  tau <= (kappa - 1) * alpha * sl_eta / 4 ->
  4 / (alpha * sl_eta) <= d%:R -> 2 / (alpha * sl_eta ^+ 2) <= Num.sqrt d%:R ->
  af_err kappa Kf m M d N sl_beta (af_gam d) tau <= sl_beta / 8.
Proof.
move=> d0 N0 tau0 h1 ht h4 h5.
apply: le_trans (af_err_le kappa Kf m M d N sl_beta (af_gam d) tau k1 d0
  N0 mM sl_beta_gt0 (af_gam_gt0 d d0) tau0) _.
rewrite -/(af_Mk kappa) -/sl_L1 -/sl_A1.
have T12 := lerD (sl_T1 d N d0 h1 h5) (sl_T2 d N tau d0 h1 ht h4).
apply: le_trans (_ : sl_A1 * (sl_eta + sl_eta) <= _).
  by apply: ler_wpM2l; [exact: ltW sl_A1_gt0 | exact: T12].
have A1n : sl_A1 != 0 := lt0r_neq0 sl_A1_gt0.
by rewrite /sl_eta le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Lemma sl_prob_small d N : (0 < d)%N -> alpha / 2 * d%:R ^+ 2 <= N%:R ->
  2 / alpha * sl_P1 * af_Q eps <= d%:R ->
  af_prob kappa Kf m M d N sl_beta (af_gam d) sl_t <= 1 / af_Q eps.
Proof.
move=> d0 h1 h7.
have dR : 1 <= d%:R :> RR by rewrite ler1n.
have dR0 : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have Q0 : 0 < af_Q eps by apply: (lt_le_trans _ (af_Q4 eps)); rewrite ltr0n.
have t0 := sl_t_gt0.
apply: le_trans (af_prob_le kappa Kf m M d N sl_beta (af_gam d) sl_t k1
  d0 mM sl_beta_gt0 (af_gam_gt0 d d0) t0) _.
rewrite -/(af_Mk kappa) -/sl_L1.
have -> : 4 * (1 + Kf ^+ 4) ^+ 2 * sl_L1 ^+ 2 / (N%:R * sl_t ^+ 2) =
    sl_P1 / N%:R.
  have Nn : N%:R != 0 :> RR := lt0r_neq0 nR.
  have tn : sl_t != 0 := lt0r_neq0 t0.
  by rewrite /sl_P1; field.
have hN : sl_P1 * af_Q eps <= N%:R.
  have h : alpha / 2 * (2 / alpha * sl_P1 * af_Q eps) = sl_P1 * af_Q eps.
    have an : alpha != 0 := lt0r_neq0 a0.
    by field.
  rewrite -h; apply: (le_trans _ h1).
  apply: ler_wpM2l; first by apply: ltW; apply: divr_gt0 => //; rewrite ltr0n.
  apply: (le_trans h7); rewrite expr2.
  by apply: ler_peMl; [exact: ler0n | exact: dR].
rewrite ler_pdivrMr // mul1r mulrC ler_pdivlMr //.
Qed.

Lemma sl_union_small d N : (0 < d)%N -> N%:R <= 2 * alpha * d%:R ^+ 2 ->
  8 * alpha / eps <= d%:R ->
  N%:R * (2 * expR (- ((sl_s d - sl_B0) / sl_L0))) <= eps / 2.
Proof.
move=> d0 h2 h9.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have L0 := sl_L0_gt0.
have -> : expR (- ((sl_s d - sl_B0) / sl_L0)) = (d%:R ^+ 3)^-1.
  have -> : (sl_s d - sl_B0) / sl_L0 = 3%:R * ln d%:R.
    have Ln : sl_L0 != 0 := lt0r_neq0 L0.
    by rewrite /sl_s; field.
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

(* The event of Theorem 2.9 for the features. *)
Definition sl_F1 d N tau : set (N.-tuple 'rV[RR]_(d * d)) :=
  [set Z | (af_err kappa Kf m M d N sl_beta (af_gam d) tau + sl_t <
     `|af_value kappa m M d N sl_beta (af_gam d) Z -
       af_center kappa m M d N sl_beta (af_gam d)|)%R].

(* af_at_d on the slice pd_slice2 d m M, with the bound on the Gaussian
   center that af_at_d derives from a Gaussian witness as a hypothesis. *)
Lemma slice_at_d (d N : nat) (tau : R) (rho : probability 'rV[RR]_(d * d) RR) :
  regular_feature Kf tau (unsat_cov kappa d) rho ->
  regular_feature Kf tau (unsat_cov kappa d) (gaussian_feature_law kappa d) ->
  0 <= tau ->
  (forall (A : 'M[R]_d) (L : R), 0 < L -> Ls * frobenius A <= L ->
     subexponential rho (fun z => mxdot z (mxvec A) : RR)
       (L / Num.sqrt d%:R)) ->
  (0 < d)%N ->
  alpha / 2 * d%:R ^+ 2 <= N%:R -> N%:R <= 2 * alpha * d%:R ^+ 2 ->
  tau <= (kappa - 1) * alpha * sl_eta / 4 ->
  4 / (alpha * sl_eta) <= d%:R ->
  2 / (alpha * sl_eta ^+ 2) <= Num.sqrt d%:R ->
  72 / alpha <= Num.sqrt d%:R ->
  2 / alpha * sl_P1 * af_Q eps <= d%:R ->
  8 * alpha / eps <= d%:R ->
  1 <= ln (d%:R : RR) ->
  af_center kappa m M d N sl_beta (af_gam d) <=
    sl_beta * af_Mk kappa * M + sl_beta / 4 +
    af_err kappa Kf m M d N sl_beta (af_gam d) tau + sl_t ->
  exists E : set (N.-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> rho) N E <= eps%:E)%E &
    forall Z, ~ E Z -> exists (theta : 'rV[R]_(d * d)) (b : R), [/\
      pd_slice2 d m M theta,
      \sum_(i < N) (b - mxdot (tnth Z i) theta) ^+ 2 <= delta * N%:R &
      forall i, `|b - mxdot (tnth Z i) theta| <= sl_C * ln d%:R]].
Proof.
move=> hreg hG tau0 hsub d0 h1 h2 ht h4 h5 h6 h7 h9 hl hc.
have b0 := sl_beta_gt0.
have t0 := sl_t_gt0.
have A0 := sl_A0_gt0.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have nR : 0 < N%:R :> RR.
  apply: lt_le_trans h1; apply: mulr_gt0; [exact: divr_gt0 | exact: exprn_gt0].
have N0 : (0 < N)%N by rewrite -(ltr_nat RR).
have g0 := af_gam_gt0 d d0.
have n36 := af_n36 alpha a0 d N d0 h1 h6.
have l0 : 0 < opnorm (unsat_cov kappa d) := af_lam_gt0 kappa d k1 d0.
have herr := sl_err_small d N tau d0 N0 tau0 h1 ht h4 h5.
have hprob := sl_prob_small d N d0 h1 h7.
have Q4 := af_Q4 eps.
have Qe := af_Qe eps.
have Q0 : 0 < af_Q eps by apply: (lt_le_trans _ Q4); rewrite ltr0n.
have hQe : 1 / af_Q eps <= eps / 2.
  have p2 : 0 < 2 / eps by rewrite divr_gt0 // ltr0n.
  by rewrite div1r -[eps / 2]invf_div lef_pV2 ?posrE.
(* the value is at most beta A0, except on sl_F1 *)
have mF1 : measurable (sl_F1 d N tau).
  apply: measurable_set_lt; apply: measurableT_comp (@normr_measurable RR _) _.
  apply: measurable_funB => //.
  exact: (measurable_af_value kappa m M d N sl_beta (af_gam d) mM b0 g0).
have PF1 : (tuple_prod (fun=> rho) N (sl_F1 d N tau) <=
    (af_prob kappa Kf m M d N sl_beta (af_gam d) sl_t)%:E)%E.
  exact: (af_conc kappa Kf m M d N sl_beta (af_gam d) sl_t tau N0 mM b0
    g0 t0 n36 tau0 hG _ hreg).
have hV Z : ~ sl_F1 d N tau Z ->
    af_value kappa m M d N sl_beta (af_gam d) Z <= sl_beta * sl_A0.
  rewrite /sl_F1 /= => /negP; rewrite -leNgt => /ler_normlP [_ h].
  exact: (af_arith_value _ _ _ _ _ _ b0 h herr hc).
(* the leave-one-out residuals are at most s, except on F2 *)
have [mF2 PF2] := af_union_le N d (tuple_prod (fun=> rho) N)
  (fun i => sat_bad m M d N (opnorm (unsat_cov kappa d)) sl_beta
    (af_gam d) mM l0 b0 g0 i (sl_s d) sl_B0)
  (fun i => measurable_sat_bad m M d N (opnorm (unsat_cov kappa d))
    sl_beta (af_gam d) mM l0 b0 g0 i (sl_s d) sl_B0).
have PF2' : (tuple_prod (fun=> rho) N
    (\big[setU/set0]_(i < N) sat_bad m M d N (opnorm (unsat_cov kappa d))
       sl_beta (af_gam d) mM l0 b0 g0 i (sl_s d) sl_B0) <= (eps / 2)%:E)%E.
  apply: le_trans PF2 _.
  apply: le_trans (_ : (\sum_(i < N)
      (2 * expR (- ((sl_s d - sl_B0) / sl_L0)))%:E <= _)%E).
    apply: lee_sum => i _.
    exact: (sat_loo_tail m M d N (opnorm (unsat_cov kappa d)) sl_beta
      (af_gam d) m_pos mM l0 b0 g0 Ls rho Ls0 hsub d0 i (sl_s d) sl_B0).
  rewrite sumEFin sumr_const card_ord lee_fin -[X in X <= _]mulr_natl.
  exact: sl_union_small d N d0 h2 h9.
exists (sl_F1 d N tau `|` \big[setU/set0]_(i < N) sat_bad m M d N
  (opnorm (unsat_cov kappa d)) sl_beta (af_gam d) mM l0 b0 g0 i (sl_s d)
  sl_B0).
split.
- exact: measurableU.
- apply: le_trans (measureU2 _ mF1 mF2) _.
  apply: le_trans (leeD PF1 PF2') _.
  rewrite -EFinD lee_fin.
  exact: (af_arith_sum _ _ _ hprob hQe).
move=> Z nZ.
have nF1 : ~ sl_F1 d N tau Z by move=> h; apply: nZ; left.
have hVZ := hV Z nF1.
exists (sat_min m M d N (opnorm (unsat_cov kappa d)) sl_beta (af_gam d)
  mM l0 b0 g0 predT Z).
exists (sat_int m M d N (opnorm (unsat_cov kappa d)) sl_beta (af_gam d)
  mM l0 b0 g0 predT Z).
split.
- exact: sat_min_in.
- have h := sat_loss_le m M d N (opnorm (unsat_cov kappa d)) sl_beta
    (af_gam d) mM l0 b0 g0 Z.
  have n2 : 0 < N%:R *+ 2 :> RR by rewrite mulrn_wgt0.
  rewrite ler_pdivrMl // in h.
  apply: le_trans h _.
  apply: le_trans (ler_wpM2l (ltW n2) hVZ) _.
  rewrite /sl_beta le_eqVlt; apply/orP; left; apply/eqP.
  have A0n : sl_A0 != 0 := lt0r_neq0 A0.
  by rewrite -mulr_natl; field.
move=> i.
have hnb : ~ sat_bad m M d N (opnorm (unsat_cov kappa d)) sl_beta
    (af_gam d) mM l0 b0 g0 i (sl_s d) sl_B0 Z.
  by move=> h; apply: nZ; right; exact: af_in_bigsetU h.
have hb := sat_loo_int m M d N (opnorm (unsat_cov kappa d)) sl_beta
  (af_gam d) mM l0 b0 g0 Z i.
have hcmp := sat_loo_compare m M d N (opnorm (unsat_cov kappa d))
  sl_beta (af_gam d) mM N0 l0 b0 g0 Z i.
have hbi : `|sat_int m M d N (opnorm (unsat_cov kappa d)) sl_beta
    (af_gam d) mM l0 b0 g0 (fun j => j != i) Z| <= sl_B0.
  have h := le_trans hb hVZ.
  rewrite ler_pM2l // in h.
  by rewrite /sl_B0 -sqrtr_sqr; apply: ler_wsqrtr.
have hri : `|sat_int m M d N (opnorm (unsat_cov kappa d)) sl_beta
    (af_gam d) mM l0 b0 g0 (fun j => j != i) Z -
    mxdot (tnth Z i) (sat_min m M d N (opnorm (unsat_cov kappa d)) sl_beta
      (af_gam d) mM l0 b0 g0 (fun j => j != i) Z)| <= sl_s d.
  by rewrite leNgt; apply/negP => h; apply: hnb; split.
apply: (@le_trans _ _ (sl_s d)).
  apply: le_trans hri.
  by rewrite -sqrtr_sqr -[X in _ <= X]sqrtr_sqr; apply: ler_wsqrtr.
have hB : sl_B0 <= sl_B0 * ln (d%:R : RR).
  by rewrite ler_peMr // /sl_B0 sqrtr_ge0.
by rewrite /sl_s /sl_C [(sl_B0 + _) * _]mulrDl; apply: lerD.
Qed.

End slice_eps.

End slice_main.
