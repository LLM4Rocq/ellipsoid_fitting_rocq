From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear interval boolp classical_sets.
From mathcomp Require Import functions reals ereal topology normedtype exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import self_concordant tuple_rows.
From GaussianAnalysis Require Import least_squares feature_moments lindeberg.
From GaussianAnalysis Require Import barrier_lindeberg barrier_removal.

(**md**************************************************************************)
(* # Least squares values with a ridge and without barrier                    *)
(*                                                                            *)
(* The comparison of ridge-regularized least squares values of Koehler and    *)
(* Sohn (arXiv 2608.27372, proposition at lines 6365-6416, proof at lines     *)
(* 6418-6460), as a concentration inequality: Theorem 2.9 for the values with *)
(* a barrier (barrier_lindeberg.v), Lemma 2.11 to remove the barrier          *)
(* (barrier_removal.v), and Markov's inequality for the objective at a        *)
(* reference point. The weight gamma of the barrier and the contraction eps   *)
(* of Lemma 2.11 stay free; the paper fixes them as functions of n.           *)
(*                                                                            *)
(* Setting: D is convex and relatively open with directions V, B is a         *)
(* theta-self-concordant barrier on D with theta >= 0 and B >= 0 on D, and    *)
(* theta_0 is in D; mu and nu are (K, tau)-regular features with the same     *)
(* covariance Sigma, and lambda = opnorm Sigma; n > 0, beta > 0, gamma > 0,   *)
(* 0 < eps < 1 and 36 <= n gamma. Phi_Z(D; beta) is ls_value Z lambda beta D, *)
(* Phi_Z(D, B; beta, gamma) is ls_barrier_value and Lref is ls_ref_scale      *)
(* lambda beta gamma D B (barrier_lindeberg.v).                               *)
(*                                                                            *)
(* - ls_value_barrierE: Phi_Z(D; beta) is the value with a barrier of weight  *)
(*   0; measurable_ls_value: it is a measurable function of Z.                *)
(* - markov_lt: P(f > M) <= E f / M for f >= 0 integrable and M > 0.          *)
(* - ref_objective_mean: under mu^n,                                          *)
(*     E F_Z(theta_0, 0; beta) = theta_0 Sigma theta_0^T / 2                  *)
(*                               + beta lambda |theta_0|^2.                   *)
(* - ridge_comparison: with c = E_(nu^n) Phi_Z(D, B; beta, gamma), for t > 0  *)
(*   and M > 0, the mu^n-probability that                                     *)
(*     |Phi_Z(D; beta) - c| > E + t + eps M + gamma B theta_0                 *)
(*                            + gamma theta ln (1 / eps)                      *)
(*   is at most                                                               *)
(*     4 (1 + K^4)^2 Lref^2 / (n t^2)                                         *)
(*       + (theta_0 Sigma theta_0^T / 2 + beta lambda |theta_0|^2) / M,       *)
(*   where E = 100 (1 + K^4)^2 Lref^2 ((n gamma)^(-1/2) + sqrt (dim V)        *)
(*   (tau / lambda + 1) / n) is the bound of (2.12). The hypotheses are       *)
(*   symmetric in mu and nu, so the same holds under nu^n.                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ls_value_measurable.
Context {R : realType} {N : nat}.

(* Phi_Z(D; beta) is the value with a barrier of weight 0. *)
Lemma ls_value_barrierE n (Z : n.-tuple 'rV[R]_N) (lambda beta : R)
    (D : set 'rV[R]_N) (B : 'rV[R]_N -> R) :
  ls_value Z lambda beta D = ls_barrier_value Z lambda beta D 0 B.
Proof.
rewrite /ls_value /ls_barrier_value; congr inf; apply/seteqP.
by split => _ [th Dth [b _ <-]]; exists th => //; exists b => //;
  rewrite mul0r addr0.
Qed.

Lemma measurable_ls_value (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) n
    (lambda beta : R) :
  rel_open_convex V D -> D !=set0 -> 0 <= lambda -> 0 <= beta ->
  measurable_fun setT
    (fun Z : n.-tuple 'rV[R]_N => ls_value Z lambda beta D).
Proof.
move=> DV D0 l0 b0.
pose B0f := fun _ : 'rV[R]_N => (0 : R).
have -> : (fun Z : n.-tuple 'rV[R]_N => ls_value Z lambda beta D) =
    (fun Z => ls_barrier_value Z lambda beta D 0 B0f).
  by apply/funext => Z; exact: ls_value_barrierE.
have B0 z : D z -> 0 <= B0f z by [].
have Bc z : D z -> forall e : R, 0 < e -> exists2 dl : R, 0 < dl &
    forall y, D y -> `|y - z| < dl -> `|B0f y - B0f z| < e.
  by move=> _ e e0; exists 1 => // y _ _; rewrite /B0f subrr normr0.
exact: (measurable_ls_barrier_value DV D0 B0 Bc (n := n) l0 b0 (lexx 0)).
Qed.

Lemma measurable_set_lt d (T : measurableType d) (f : T -> R) (a : R) :
  measurable_fun setT f -> measurable [set x | a < f x].
Proof.
move=> mf; have := mf measurableT _ (measurable_itv `]a, +oo[).
rewrite setTI; congr measurable; apply/seteqP.
by split => x /=; rewrite in_itv /= andbT.
Qed.

End ls_value_measurable.

Section markov_lt.
Context d (T : measurableType d) (R : realType) (P : probability T R).

(* Markov's inequality, for a strict inequality. *)
Lemma markov_lt (f : T -> R) (M : R) : 0 < M -> measurable_fun setT f ->
  (forall x, 0 <= f x) -> P.-integrable setT (EFin \o f) ->
  (P [set x | (M < f x)%R] <= ((\int[P]_x f x) / M)%:E)%E.
Proof.
move=> M0 mf f0 fi.
pose X : {RV P >-> R} := HB.pack f (isMeasurableFun.Build _ _ _ _ f mf).
have := @markov _ _ _ P X idfun M M0 (@measurable_id _ _ setT)
  (fun r r0 => r0) (fun x y _ _ xy => xy).
rewrite unlock /=.
have -> : (\int[P]_x (`|f x|)%:E = (\int[P]_x f x)%:E)%E.
  rewrite Rintegral_EFin //; apply: eq_integral => x _ /=.
  by rewrite ger0_norm.
have -> : [set x | (M%:E <= `|f x|%:E)%E] = [set x | (M <= f x)%R].
  by apply/seteqP; split => x /=; rewrite lee_fin ger0_norm.
move=> h.
have mS : measurable [set x | (M <= f x)%R].
  have := mf measurableT _ (measurable_itv `[M, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => x /=; rewrite in_itv /= andbT.
have mL : measurable [set x | (M < f x)%R] by exact: measurable_set_lt.
apply: (@le_trans _ _ (P [set x | (M <= f x)%R])).
  by apply: le_measure; rewrite ?inE // => x /= /ltW.
have qf : P [set x | (M <= f x)%R] \is a fin_num.
  rewrite ge0_fin_numE ?measure_ge0 //.
  by rewrite (le_lt_trans (probability_le1 _ _)) ?ltry.
move: h; rewrite -(fineK qf) -EFinM !lee_fin => h.
by rewrite ler_pdivlMr // mulrC.
Qed.

End markov_lt.

Section ref_objective.
Context {R : realType} {N : nat}.
Variables (K tau : R) (Sigma : 'M[R]_N) (mu : probability 'rV[R]_N R).
Hypothesis rmu : regular_feature K tau Sigma mu.

Lemma ref_objectiveE n (Z : n.-tuple 'rV[R]_N) (lambda beta : R)
    (thr : 'rV[R]_N) :
  ls_objective Z lambda beta thr 0 =
  (n%:R *+ 2)^-1 * \sum_(j < n) mxdot (tnth Z j) thr ^+ 2 +
  beta * lambda * mxdot thr thr.
Proof.
rewrite /ls_objective; under eq_bigr do rewrite sub0r sqrrN.
by rewrite expr0n /= addr0 mulrA.
Qed.

Lemma ref_objective_int n (lambda beta : R) (thr : 'rV[R]_N) :
  (tuple_prod (fun=> mu) n).-integrable setT
    (EFin \o (fun Z => ls_objective Z lambda beta thr 0)).
Proof.
have -> : (fun Z : n.-tuple 'rV[R]_N => ls_objective Z lambda beta thr 0) =
    (fun Z => (n%:R *+ 2)^-1 * \sum_(j < n) mxdot (tnth Z j) thr ^+ 2 +
      beta * lambda * mxdot thr thr).
  by apply/funext => Z; exact: ref_objectiveE.
apply: integrableRD; last exact: integrable_cst_prob.
apply: integrableRZl; apply: integrableR_sum => j.
exact: (@integrable_tuple_prod_tnth _ _ _ (fun=> mu) n j
  (fun z => mxdot z thr ^+ 2) (reg_int_sqr rmu thr)).
Qed.

Lemma ref_objective_mean n (lambda beta : R) (thr : 'rV[R]_N) :
  (0 < n)%N ->
  \int[tuple_prod (fun=> mu) n]_Z ls_objective Z lambda beta thr 0 =
  mxdot (thr *m Sigma) thr / 2 + beta * lambda * mxdot thr thr.
Proof.
move=> n0.
have ij (j : 'I_n) : (tuple_prod (fun=> mu) n).-integrable setT
    (EFin \o (fun Z : n.-tuple 'rV[R]_N => mxdot (tnth Z j) thr ^+ 2)).
  exact: (@integrable_tuple_prod_tnth _ _ _ (fun=> mu) n j
    (fun z => mxdot z thr ^+ 2) (reg_int_sqr rmu thr)).
have iS : (tuple_prod (fun=> mu) n).-integrable setT (EFin \o
    (fun Z : n.-tuple 'rV[R]_N => \sum_(j < n) mxdot (tnth Z j) thr ^+ 2)).
  exact: integrableR_sum.
have mg : measurable_fun setT (fun z : 'rV[R]_N => mxdot z thr ^+ 2).
  by apply: measurable_funX; exact: measurable_mxdotl.
have hj (j : 'I_n) : \int[tuple_prod (fun=> mu) n]_x
    mxdot (tnth x j) thr ^+ 2 = mxdot (thr *m Sigma) thr.
  rewrite (@Rintegral_tuple_prod_tnth _ _ _ (fun=> mu) n j _ mg
    (fun z => sqr_ge0 _)).
  by rewrite -(reg_cov rmu thr thr); apply: eq_Rintegral => z _; rewrite expr2.
under eq_Rintegral do rewrite ref_objectiveE.
rewrite RintegralD //; first last.
2: exact: integrable_cst_prob.
2: exact: integrableRZl.
rewrite (RintegralZl _ measurableT iS).
rewrite (@Rintegral_cst_prob _ _ _ (tuple_prod (fun=> mu) n)).
rewrite Rintegral_sumr //.
under eq_bigr do rewrite hj.
rewrite sumr_const card_ord -mulr_natl.
have nn : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

End ref_objective.

Section ridge_comparison.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (theta : R)
  (B : 'rV[R]_N -> R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_barrier V D theta B).
Hypotheses (theta0 : 0 <= theta) (B0 : forall z, D z -> 0 <= B z).
Variables (K tau : R) (Sigma : 'M[R]_N) (mu nu : probability 'rV[R]_N R).
Hypotheses (rmu : regular_feature K tau Sigma mu)
  (rnu : regular_feature K tau Sigma nu) (tau0 : 0 <= tau).
Variables (n : nat) (beta gamma eps : R) (thr : 'rV[R]_N).
Hypotheses (n0 : (0 < n)%N) (b0 : 0 < beta) (g0 : 0 < gamma).
Hypotheses (e01 : 0 < eps < 1) (Dthr : D thr).

Local Notation lambda := (opnorm Sigma).
Local Notation Phi Z := (ls_value Z (opnorm Sigma) beta D).
Local Notation Psi Z := (ls_barrier_value Z (opnorm Sigma) beta D gamma B).
Local Notation Lref := (ls_ref_scale (opnorm Sigma) beta gamma D B).

Theorem ridge_comparison (t M : R) :
  0 < t -> 0 < M -> 36 <= n%:R * gamma ->
  (tuple_prod (fun=> mu) n
     [set Z | (100 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 *
        ((Num.sqrt (n%:R * gamma))^-1 +
         Num.sqrt (\dim V)%:R * (tau / lambda + 1) / n%:R) + t +
        (eps * M + gamma * B thr + gamma * theta * ln eps^-1) <
        `|Phi Z - \int[tuple_prod (fun=> nu) n]_Z Psi Z|)%R] <=
   (4 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 / (n%:R * t ^+ 2) +
    (mxdot (thr *m Sigma) thr / 2 + beta * lambda * mxdot thr thr) / M)%:E)%E.
Proof.
move=> t0 M0 n36.
have D0 : D !=set0 by exists thr.
have [scf _] := scB.
have l0 : 0 <= lambda := opnorm_ge0 Sigma.
have hA := barrier_lindeberg_concentration DV scf B0 D0 rmu rnu tau0 n0 b0 g0
  t0 n36.
set err := 100 * _ * _ * _ in hA *.
set c := \int[tuple_prod (fun=> nu) n]_Z Psi Z in hA *.
set rem := eps * M + gamma * B thr + gamma * theta * ln eps^-1.
(* Markov's inequality for the objective at the reference point *)
set F := fun Z : n.-tuple 'rV[R]_N => ls_objective Z lambda beta thr 0.
have mF : measurable_fun setT F.
  have -> : F = (fun Z => (n%:R *+ 2)^-1 *
      \sum_(j < n) mxdot (tnth Z j) thr ^+ 2 + beta * lambda * mxdot thr thr).
    by apply/funext => Z; rewrite /F ref_objectiveE.
  apply: measurable_funD => //; apply: measurable_funM => //.
  apply: measurable_sum => j; apply: measurable_funX.
  exact: measurable_mxdot_tnth.
have F0 Z : 0 <= F Z by exact: ls_objective_ge0 (ltW b0).
have := markov_lt M0 mF F0 (ref_objective_int rmu n lambda beta thr).
rewrite (ref_objective_mean rmu lambda beta thr n0) => hB.
(* the union bound *)
have mPhi : measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => Phi Z).
  exact: measurable_ls_value DV D0 l0 (ltW b0).
have mPsi : measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => Psi Z).
  have Bc z (Dz : D z) (e : R) (e0 : 0 < e) :=
    sc_function_continuous DV scf Dz e0.
  exact: (measurable_ls_barrier_value DV D0 B0 Bc (n := n) l0 (ltW b0)
    (ltW g0)).
have mabs (f : n.-tuple 'rV[R]_N -> R) : measurable_fun setT f ->
    measurable_fun setT (fun Z => `|f Z - c|).
  by move=> mf; apply: measurableT_comp => //; apply: measurable_funB.
have mL := measurable_set_lt (err + t + rem) (mabs _ mPhi).
have mA := measurable_set_lt (err + t) (mabs _ mPsi).
have mB := measurable_set_lt M mF.
apply: (@le_trans _ _ (tuple_prod (fun=> mu) n
    ([set Z | (err + t < `|Psi Z - c|)%R] `|` [set Z | (M < F Z)%R]))).
  apply: le_measure; rewrite ?inE //; first exact: measurableU.
  move=> Z /= hZ.
  case: (ltP (err + t) `|Psi Z - c|) => hA'; [by left|right].
  rewrite ltNge; apply/negP => hF.
  have /andP[h1 h2] :=
    barrier_removal DV scB theta0 B0 Z 0 Dthr l0 (ltW b0) g0 e01.
  have e0 : 0 <= eps by case/andP: e01 => /ltW.
  have hF' : eps * ls_objective Z lambda beta thr 0 <= eps * M.
    by rewrite ler_wpM2l.
  have hd := ler_distD (Psi Z) (Phi Z) c.
  rewrite /rem in hZ.
  have : `|Phi Z - Psi Z| <=
      eps * M + gamma * B thr + gamma * theta * ln eps^-1.
    by rewrite distrC ger0_norm //; lra.
  by lra.
apply: le_trans (measureU2 _ mA mB) _.
by rewrite EFinD; exact: leeD.
Qed.

End ridge_comparison.
