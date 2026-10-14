From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.
From GaussianAnalysis.probability Require Import commuting_operators.
From GaussianAnalysis.analysis Require Import min_superadditive.
From GaussianApplications.RandomSAT Require Import Model Pivotal.
From GaussianApplications.RandomSAT Require Import Survival Tails CenterBounds.
From GaussianApplications.RandomSAT Require Import Interpolation Transfer.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: comparison of the centers at different sizes               *)
(*                                                                            *)
(* Part of target T9 of phase 13. A Rocq formalization of the credited        *)
(* argument of the subsection 'Comparing centers at different sizes' of the   *)
(* proof of the theorem 'Concentration implies convergence'                   *)
(* (thm:concentration-to-convergence, equations eq:convergence-sum and        *)
(* eq:convergence-neighbor) of 'A Limiting Satisfiability Threshold for Every *)
(* Fixed Clause Size' (family 235 of the OpenAI math collection, revision     *)
(* 1581d4cbd, source/sections/convergence.tex), following the Lean            *)
(* development of the collection (lean/OAI/Probability/RandomSAT):            *)
(* Lean: product_lower_two_deviations (Transfer.lean, line 373)               *)
(* Lean: auxiliary_interpolation_center_lower (CenterComparison.lean)         *)
(* Lean: center_lower_of_auxiliary_probability (CenterComparison.lean)        *)
(* Lean: center_sum_comparison_of_bounds (CenterComparison.lean, line 169)    *)
(* Lean: neighbor_all_left (CenterComparison.lean, line 241)                  *)
(* Lean: center_neighbor_comparison_of_bounds (CenterComparison.lean)         *)
(* Lean: CenterRegular (CenterComparison.lean, line 316)                      *)
(* Lean: center_comparisons (CenterComparison.lean, line 344)                 *)
(*                                                                            *)
(* mu_n = sat_center n k. The density window is sat_dwin n k = n^(-delta_k),  *)
(* so that sat_window n k = n sat_dwin n k (sat_window_dwin), and sat_serr n  *)
(* k = 2^(k+1) n / w_n^2 is the sampling error of a binomial split.           *)
(*                                                                            *)
(* - aux_interpolation_center_lower: if m splits into shares m r/(r+s) and m  *)
(*   s/(r+s) at least two windows below r mu_r and s mu_s, then aux_prob (r + *)
(*   s) k m >= (sat_tfactor k / 2)^2 (1 - sat_serr r k - sat_serr s k). From  *)
(*   aux_interpolation of Interpolation.v, the lower tail of Transfer.v at    *)
(*   both sizes and the binomial variance (binomial_mean_sqr_dev).            *)
(* - center_lower_of_aux_prob: if aux_prob n k (floor(c n)) exceeds sat_err n *)
(*   k, then mu_n > c - 2 n^(-delta_k), by the upper tail.                    *)
(* - center_sum_comparison and center_neighbor_comparison: mu_(r+s) >=        *)
(*   min(mu_r, mu_s) - 4 min(r, s)^(-delta_k) and mu_(s+1) >= mu_s - 4        *)
(*   s^(-delta_k), under the size conditions of center_regular. The neighbor  *)
(*   step interpolates with a block of one variable that receives no clause   *)
(*   (neighbor_all_left, from binomial_mean_last).                            *)
(* - center_regular_eventually: the size conditions hold beyond one explicit  *)
(*   threshold.                                                               *)
(* - center_comparisons: both comparisons for all r, s >= N, in the form of   *)
(*   the hypotheses of min_superadditive_statement (T12) with A = 4 and beta  *)
(*   = delta_k; the sum comparison holds without the comparable-size          *)
(*   condition.                                                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section windows.
Context {R : realType}.

(* The density window n^(-delta_k); the window of Tails.v is n times it. *)
Definition sat_dwin (n k : nat) : R := n%:R `^ (- sat_delta k).

(* The sampling error 2^(k+1) n / w_n^2 of a binomial split. *)
Definition sat_serr (n k : nat) : R :=
  2 ^+ k.+1 * n%:R / sat_window n k ^+ 2.

Lemma sat_dwin_gt0 n k : (0 < n)%N -> 0 < sat_dwin n k.
Proof. by move=> n0; rewrite powR_gt0 // ltr0n. Qed.

Lemma sat_window_dwin n k : (0 < n)%N ->
  sat_window n k = n%:R * sat_dwin n k.
Proof.
move=> n0; have nz : n%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite /sat_window /sat_dwin powRD ?nz ?implybT // powRr1 // ler0n.
Qed.

Lemma sat_window_ge1 n k : (3 <= k)%N -> (0 < n)%N -> 1 <= sat_window n k :> R.
Proof.
move=> k3 n0; have k0 : (0 < k)%N by apply: leq_trans k3.
have hd : sat_delta k < 4^-1 :> R := sat_delta_lt k0.
rewrite /sat_window -[X in X <= _](powRr0 (n%:R : R)).
apply: ler_powR; first by rewrite ler1n.
by move: hd; lra.
Qed.

Lemma sat_dwin_le r s k : (3 <= k)%N -> (0 < r)%N -> (r <= s)%N ->
  sat_dwin s k <= sat_dwin r k :> R.
Proof.
move=> k3 r0 rs; apply: powRN_le; [by rewrite ltr0n | by rewrite ler_nat |].
exact: ltW (sat_delta_gt0 k3).
Qed.

(* The sampling error is 2^(k+1) n^(-(1 - 2 delta_k)). *)
Lemma sat_serrE n k : (0 < n)%N ->
  sat_serr n k = 2 ^+ k.+1 * n%:R `^ (- (1 - 2 * sat_delta k)) :> R.
Proof.
move=> n0; have nz : n%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite /sat_serr.
have -> : sat_window n k ^+ 2 = n%:R `^ ((1 - sat_delta k) * 2) :> R.
  by rewrite /sat_window -powR_mulrn ?powR_ge0 // -powRrM.
rewrite -mulrA; congr (_ * _).
rewrite -[X in X / _](powRr1 (ler0n R n)) -powRB ?nz ?implybT //.
by congr (_ `^ _); ring.
Qed.

End windows.

Section comparisons.
Context {R : realType}.

(* Two deviations: if a >= c as soon as x < 1, and b >= c as soon as y < 1,
   then a b >= c^2 (1 - x - y). *)
Lemma product_lower_two_deviations (c x y a b : R) :
  0 <= c -> 0 <= x -> 0 <= y -> 0 <= a -> 0 <= b ->
  (x < 1 -> c <= a) -> (y < 1 -> c <= b) -> c ^+ 2 * (1 - x - y) <= a * b.
Proof.
move=> c0 x0 y0 a0 b0 hx hy; have ab0 : 0 <= a * b by rewrite mulr_ge0.
case: (ltrP x 1) => x1; last first.
  by apply: le_trans ab0; rewrite mulr_ge0_le0 ?sqr_ge0 //; lra.
case: (ltrP y 1) => y1; last first.
  by apply: le_trans ab0; rewrite mulr_ge0_le0 ?sqr_ge0 //; lra.
apply: le_trans (ler_pM c0 c0 (hx x1) (hy y1)).
by rewrite expr2 -[X in _ <= X]mulr1 ler_wpM2l ?mulr_ge0 //; lra.
Qed.

Lemma aux_prob0 n k : aux_prob n k 0 = 1 :> R.
Proof.
rewrite /aux_prob /= /alive.
have -> : [set: {ffun 'I_n -> bool}] != set0.
  by apply/set0Pn; exists [ffun=> false]; rewrite inE.
by [].
Qed.

Lemma aux_prob_ge0 n k m : 0 <= aux_prob n k m :> R.
Proof.
rewrite /aux_prob; elim: m [set: _] => [|m IH] S /=; first exact: alive_ge0.
by apply: unif_mean_ge0 => c; exact: IH.
Qed.

(* The interpolation with the two lower tails: if m splits into its
   expected shares at least two windows below r mu_r and s mu_s, then
   m auxiliary clauses on r + s variables are satisfiable with probability
   at least the square of half the transfer factor, up to the two sampling
   errors. *)
Lemma aux_interpolation_center_lower r s k m : (3 <= k)%N ->
  (k.+1 <= r)%N -> (k.+1 <= s)%N ->
  2 * 'C(k, 2)%:R <= r%:R :> R -> 2 * 'C(k, 2)%:R <= s%:R :> R ->
  sat_err r k <= 2^-1 :> R -> sat_err s k <= 2^-1 :> R ->
  m%:R <= 2 ^+ k.+1 * (r%:R + s%:R) :> R ->
  m%:R * (r%:R / (r + s)%:R) + 2 * sat_window r k <=
    r%:R * sat_center r k :> R ->
  m%:R * (s%:R / (r + s)%:R) + 2 * sat_window s k <=
    s%:R * sat_center s k :> R ->
  (sat_tfactor k / 2) ^+ 2 * (1 - sat_serr r k - sat_serr s k) <=
    aux_prob (r + s) k m :> R.
Proof.
move=> k3 kr ks hrr hsr her hes hm hgr hgs.
have r0 : (0 < r)%N := leq_ltn_trans (leq0n k) kr.
have s0 : (0 < s)%N := leq_ltn_trans (leq0n k) ks.
have r0' : 0 < r%:R :> R by rewrite ltr0n.
have s0' : 0 < s%:R :> R by rewrite ltr0n.
have rs0 : 0 < (r + s)%:R :> R by rewrite ltr0n addn_gt0 r0.
have rsn : (r + s)%:R != 0 :> R by rewrite gt_eqF.
set p : R := r%:R / (r + s)%:R.
have p0 : 0 <= p by rewrite divr_ge0 ?ler0n.
have p1 : p <= 1 by rewrite ler_pdivrMr // mul1r ler_nat leq_addr.
have hq : 1 - p = s%:R / (r + s)%:R.
  by rewrite /p -[X in X - _](divff rsn) -mulrBl natrD addrAC subrr add0r.
have wr : 0 < sat_window r k :> R := sat_window_gt0 k r0.
have ws : 0 < sat_window s k :> R := sat_window_gt0 k s0.
set tl : R := sat_tfactor k / 2.
have tl0 : 0 <= tl by rewrite divr_ge0 // ltW // sat_tfactor_gt0.
(* For j successes, the two blocks are below their thresholds unless j is a
   window away from its mean m p. *)
have hpoint : forall j, (j <= m)%N ->
    tl ^+ 2 * (1 - (j%:R - m%:R * p) ^+ 2 / sat_window r k ^+ 2
               - (j%:R - m%:R * p) ^+ 2 / sat_window s k ^+ 2)
    <= aux_prob r k j * aux_prob s k (m - j).
  move=> j jm; apply: product_lower_two_deviations => //.
  - by rewrite divr_ge0 ?sqr_ge0 ?exprn_ge0 // ltW.
  - by rewrite divr_ge0 ?sqr_ge0 ?exprn_ge0 // ltW.
  - exact: aux_prob_ge0.
  - exact: aux_prob_ge0.
  - move=> hdev; apply: aux_prob_center_lower => //.
    rewrite ltr_pdivrMr ?exprn_gt0 // mul1r in hdev.
    have hlt : j%:R - m%:R * p < sat_window r k.
      case: (ltrP (j%:R - m%:R * p) (sat_window r k)) => // h.
      by have := ler_pM (ltW wr) (ltW wr) h h; rewrite -!expr2; lra.
    by rewrite -/p in hgr; lra.
  - move=> hdev; apply: aux_prob_center_lower => //.
    rewrite ltr_pdivrMr ?exprn_gt0 // mul1r in hdev.
    have hlt : m%:R * p - j%:R < sat_window s k.
      case: (ltrP (m%:R * p - j%:R) (sat_window s k)) => // h.
      by have := ler_pM (ltW ws) (ltW ws) h h; rewrite -!expr2; lra.
    rewrite natrB // -hq in hgs *.
    by move: hgs; rewrite mulrBr mulr1; lra.
have hp01 : 0 <= p <= 1 by rewrite p0 p1.
have hI := @aux_interpolation R r s k m r0 s0.
apply: le_trans (le_trans (ler_binomial_mean hp01 hpoint) hI).
(* The mean of the squared deviation is the binomial variance V. *)
set V : R := m%:R * p * (1 - p).
have e : binomial_mean m p (fun j => tl ^+ 2 *
    (1 - (j%:R - m%:R * p) ^+ 2 / sat_window r k ^+ 2
       - (j%:R - m%:R * p) ^+ 2 / sat_window s k ^+ 2)) =
    tl ^+ 2 * (1 - V / sat_window r k ^+ 2 - V / sat_window s k ^+ 2).
  transitivity (binomial_mean m p (fun j => tl ^+ 2 * 1 +
    (- (tl ^+ 2 * (sat_window r k ^+ 2)^-1
        + tl ^+ 2 * (sat_window s k ^+ 2)^-1)) * (j%:R - m%:R * p) ^+ 2)).
    by apply: eq_binomial_mean => j _; ring.
  rewrite binomial_meanD binomial_mean_cst binomial_meanZ binomial_mean_sqr_dev.
  by rewrite /V; ring.
rewrite e; apply: ler_wpM2l; first exact: exprn_ge0.
have rsn' : r%:R + s%:R != 0 :> R by rewrite -natrD.
have q0 : 0 <= 1 - p by rewrite subr_ge0.
have mp0 : 0 <= m%:R * p by rewrite mulr_ge0 ?ler0n.
have mq0 : 0 <= m%:R * (1 - p) by rewrite mulr_ge0 ?ler0n.
have hmp : m%:R * p <= 2 ^+ k.+1 * r%:R.
  have := ler_wpM2r p0 hm.
  have -> : 2 ^+ k.+1 * (r%:R + s%:R) * p = 2 ^+ k.+1 * r%:R :> R.
    by rewrite /p natrD; field.
  by [].
have hmq : m%:R * (1 - p) <= 2 ^+ k.+1 * s%:R.
  have := ler_wpM2r q0 hm.
  have -> : 2 ^+ k.+1 * (r%:R + s%:R) * (1 - p) = 2 ^+ k.+1 * s%:R :> R.
    by rewrite hq natrD; field.
  by [].
have hVr : V <= 2 ^+ k.+1 * r%:R.
  apply: le_trans hmp; rewrite /V -[X in _ <= X]mulr1 ler_wpM2l //.
  by rewrite lerBlDr lerDl.
have hVs : V <= 2 ^+ k.+1 * s%:R.
  by apply: le_trans hmq; rewrite /V mulrAC -[X in _ <= X]mulr1 ler_wpM2l.
have dr : V / sat_window r k ^+ 2 <= sat_serr r k.
  by rewrite /sat_serr ler_wpM2r // invr_ge0 exprn_ge0 // ltW.
have ds : V / sat_window s k ^+ 2 <= sat_serr s k.
  by rewrite /sat_serr ler_wpM2r // invr_ge0 exprn_ge0 // ltW.
lra.
Qed.

(* A density c whose auxiliary probability beats the error is at most two
   density windows above the center. *)
Lemma center_lower_of_aux_prob n k (c : R) : (3 <= k)%N -> (k.+1 <= n)%N ->
  0 <= c -> c <= 2 ^+ k.+1 ->
  sat_err n k < aux_prob n k (Num.truncn (c * n%:R)) :> R ->
  c - 2 * sat_dwin n k < sat_center n k.
Proof.
move=> k3 kn c0 cL hp.
have n0 : (0 < n)%N := leq_ltn_trans (leq0n k) kn.
have n0' : 0 < n%:R :> R by rewrite ltr0n.
move: hp; set m := Num.truncn (c * n%:R) => hp.
have cn0 : 0 <= c * n%:R by rewrite mulr_ge0 ?ler0n.
have hm : m%:R <= c * n%:R by rewrite truncn_le.
have hm' : c * n%:R < m.+1%:R := truncnS_gt _.
have mM : (m <= sat_cap k n)%N.
  rewrite -(ler_nat R) /sat_cap natrM natrX; apply: le_trans hm _.
  by rewrite ler_wpM2r ?ler0n.
rewrite ltNge; apply/negP => hc.
have w1 : 1 <= sat_window n k :> R := sat_window_ge1 k3 n0.
have we : sat_window n k = n%:R * sat_dwin n k :> R := sat_window_dwin k n0.
have hgap : n%:R * sat_center n k + sat_window n k <= m%:R :> R.
  have := ler_wpM2l (ltW n0') hc; move: w1 hm'; rewrite we -natr1; lra.
by have := aux_prob_center_upper k3 kn mM hgap; lra.
Qed.

(* The comparison of the center at r + s with the centers at r and s. *)
Lemma center_sum_comparison r s k : (3 <= k)%N ->
  (k.+1 <= r)%N -> (k.+1 <= s)%N ->
  2 * 'C(k, 2)%:R <= r%:R :> R -> 2 * 'C(k, 2)%:R <= s%:R :> R ->
  sat_err r k <= 2^-1 :> R -> sat_err s k <= 2^-1 :> R ->
  sat_serr r k <= 4^-1 :> R -> sat_serr s k <= 4^-1 :> R ->
  sat_err (r + s) k < (sat_tfactor k / 2) ^+ 2 / 2 :> R ->
  2 * sat_dwin (minn r s) k <= Num.min (sat_center r k) (sat_center s k) :> R ->
  Num.min (sat_center r k) (sat_center s k) - 4 * sat_dwin (minn r s) k <=
    sat_center (r + s) k :> R.
Proof.
move=> k3 kr ks hrr hsr her hes hsr4 hss4 hN hlow.
have r0 : (0 < r)%N := leq_ltn_trans (leq0n k) kr.
have s0 : (0 < s)%N := leq_ltn_trans (leq0n k) ks.
have u0 : (0 < minn r s)%N by rewrite leq_min r0 s0.
have r0' : 0 < r%:R :> R by rewrite ltr0n.
have s0' : 0 < s%:R :> R by rewrite ltr0n.
have rs0 : 0 < (r + s)%:R :> R by rewrite ltr0n addn_gt0 r0.
have rsn : r%:R + s%:R != 0 :> R by rewrite -natrD gt_eqF.
move: hlow; set mu := Num.min (sat_center r k) (sat_center s k) => hlow.
have mur : mu <= sat_center r k by rewrite /mu ge_min lexx.
have mus : mu <= sat_center s k by rewrite /mu ge_min lexx orbT.
have du0 : 0 < sat_dwin (minn r s) k :> R := sat_dwin_gt0 k u0.
have dur : sat_dwin r k <= sat_dwin (minn r s) k :> R :=
  sat_dwin_le k3 u0 (geq_minl r s).
have dus : sat_dwin s k <= sat_dwin (minn r s) k :> R :=
  sat_dwin_le k3 u0 (geq_minr r s).
have duN : sat_dwin (r + s) k <= sat_dwin (minn r s) k :> R.
  by apply: sat_dwin_le => //; apply: leq_trans (geq_minl r s) (leq_addr s r).
(* The density c, two density windows below both centers. *)
set c : R := mu - 2 * sat_dwin (minn r s) k.
have c0 : 0 <= c by rewrite subr_ge0.
have hcL : c <= 2 ^+ k.+1 by have := @sat_center_le R r k; rewrite /c; lra.
have hcr : c + 2 * sat_dwin r k <= sat_center r k by rewrite /c; lra.
have hcs : c + 2 * sat_dwin s k <= sat_center s k by rewrite /c; lra.
set m := Num.truncn (c * (r + s)%:R).
have cn0 : 0 <= c * (r + s)%:R by rewrite mulr_ge0 ?ler0n.
have hm : m%:R <= c * (r + s)%:R by rewrite truncn_le.
have hmr : m%:R * (r%:R / (r + s)%:R) <= c * r%:R.
  have := ler_wpM2r (divr_ge0 (ler0n R r) (ler0n R (r + s))) hm.
  have -> : c * (r + s)%:R * (r%:R / (r + s)%:R) = c * r%:R.
    by rewrite natrD; field.
  by [].
have hms : m%:R * (s%:R / (r + s)%:R) <= c * s%:R.
  have := ler_wpM2r (divr_ge0 (ler0n R s) (ler0n R (r + s))) hm.
  have -> : c * (r + s)%:R * (s%:R / (r + s)%:R) = c * s%:R.
    by rewrite natrD; field.
  by [].
have hmL : m%:R <= 2 ^+ k.+1 * (r%:R + s%:R) :> R.
  apply: le_trans hm _; rewrite natrD [X in _ <= X]mulrC [X in X <= _]mulrC.
  by apply: ler_wpM2l; [rewrite addr_ge0 ?ler0n | exact: hcL].
have wr : sat_window r k = r%:R * sat_dwin r k :> R := sat_window_dwin k r0.
have ws : sat_window s k = s%:R * sat_dwin s k :> R := sat_window_dwin k s0.
have gr : m%:R * (r%:R / (r + s)%:R) + 2 * sat_window r k <=
    r%:R * sat_center r k :> R.
  by have := ler_wpM2l (ltW r0') hcr; rewrite wr; lra.
have gs : m%:R * (s%:R / (r + s)%:R) + 2 * sat_window s k <=
    s%:R * sat_center s k :> R.
  by have := ler_wpM2l (ltW s0') hcs; rewrite ws; lra.
have hprob := aux_interpolation_center_lower k3 kr ks hrr hsr her hes hmL gr gs.
have t0 : 0 <= (sat_tfactor k / 2) ^+ 2 :> R.
  by rewrite exprn_ge0 // divr_ge0 // ltW // sat_tfactor_gt0.
have h12 : 2^-1 <= 1 - sat_serr r k - sat_serr s k :> R by lra.
have hhalf : (sat_tfactor k / 2) ^+ 2 / 2 <= aux_prob (r + s) k m :> R.
  by apply: le_trans hprob; apply: ler_wpM2l.
have kN : (k < r + s)%N by apply: leq_trans kr (leq_addr s r).
have hcN := center_lower_of_aux_prob k3 kN c0 hcL (lt_le_trans hN hhalf).
by rewrite /c in hcN; lra.
Qed.

(* One more variable: the interpolation with a block of size one, where all
   the clauses fall on the first block. *)
Lemma neighbor_all_left s k m : (0 < s)%N ->
  (s%:R / s.+1%:R) ^+ m * aux_prob s k m <= aux_prob s.+1 k m :> R.
Proof.
move=> s0; have hI := @aux_interpolation R s 1 k m s0 isT.
rewrite addn1 in hI; apply: le_trans hI.
have p01 : 0 <= (s%:R / s.+1%:R : R) <= 1.
  by rewrite divr_ge0 ?ler0n //= ler_pdivrMr ?ltr0n // mul1r ler_nat.
have f0 j : (j <= m)%N -> 0 <= aux_prob s k j * aux_prob 1 k (m - j) :> R.
  by move=> _; rewrite mulr_ge0 ?aux_prob_ge0.
have := binomial_mean_last p01 f0.
by rewrite subnn aux_prob0 mulr1.
Qed.

Lemma neighbor_pow_lower s k m : (0 < s)%N ->
  m%:R <= 2 ^+ k.+1 * s.+1%:R :> R ->
  expR (- (2 * 2 ^+ k.+1)) <= (s%:R / s.+1%:R) ^+ m :> R.
Proof.
move=> s0 hm; have S0 : 0 < s.+1%:R :> R by rewrite ltr0n.
have Sn : s%:R + 1 != 0 :> R by rewrite natr1 pnatr_eq0.
set x : R := s.+1%:R^-1.
have x0 : 0 <= x by rewrite invr_ge0 ler0n.
have x1 : x <= 2^-1 by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat ltnS.
have hx : 1 - x = s%:R / s.+1%:R by rewrite /x -natr1; field.
have hb := expR_neg2_le x0 x1; rewrite hx in hb.
apply: le_trans (lerXn2r _ _ _ hb);
  rewrite ?nnegrE ?expR_ge0 ?divr_ge0 ?ler0n //.
rewrite -expRM_natr ler_expR mulNr lerN2.
by rewrite -mulrA ler_pM2l // /x mulrC ler_pdivrMr.
Qed.

(* The lower bound of the neighbor comparison. *)
Definition sat_nfactor (k : nat) : R :=
  expR (- (2 * 2 ^+ k.+1)) * (sat_tfactor k / 2).

Lemma sat_nfactor_gt0 k : 0 < sat_nfactor k.
Proof.
by rewrite mulr_gt0 ?expR_gt0 // divr_gt0 // sat_tfactor_gt0.
Qed.

(* The comparison of the center at s + 1 with the center at s. *)
Lemma center_neighbor_comparison s k : (3 <= k)%N -> (k.+1 <= s)%N ->
  2 * 'C(k, 2)%:R <= s%:R :> R -> sat_err s k <= 2^-1 :> R ->
  sat_err s.+1 k < sat_nfactor k :> R ->
  2 * sat_dwin s k <= sat_center s k :> R ->
  2 ^+ k.+1 <= sat_window s k :> R ->
  sat_center s k - 4 * sat_dwin s k <= sat_center s.+1 k :> R.
Proof.
move=> k3 ks hsr hes hN hlow hwin.
have s0 : (0 < s)%N := leq_ltn_trans (leq0n k) ks.
have s0' : 0 < s%:R :> R by rewrite ltr0n.
have d0 : 0 < sat_dwin s k :> R := sat_dwin_gt0 k s0.
(* The density c, two density windows below the center at s. *)
set c : R := sat_center s k - 2 * sat_dwin s k.
have c0 : 0 <= c by rewrite subr_ge0.
have hcL : c <= 2 ^+ k.+1 by have := @sat_center_le R s k; rewrite /c; lra.
set m := Num.truncn (c * s.+1%:R).
have cn0 : 0 <= c * s.+1%:R by rewrite mulr_ge0 ?ler0n.
have hm : m%:R <= c * s.+1%:R by rewrite truncn_le.
have hmL : m%:R <= 2 ^+ k.+1 * s.+1%:R :> R.
  by apply: le_trans hm _; apply: ler_wpM2r; rewrite ?ler0n.
have we : sat_window s k = s%:R * sat_dwin s k :> R := sat_window_dwin k s0.
have hgap : m%:R + sat_window s k <= s%:R * sat_center s k :> R.
  by move: hm hwin hcL; rewrite /c we -natr1; lra.
have hlocal := aux_prob_center_lower k3 ks hsr hes hgap.
have hpow := neighbor_pow_lower s0 hmL.
have hprod : sat_nfactor k <= aux_prob s.+1 k m :> R.
  apply: le_trans (neighbor_all_left k m s0); rewrite /sat_nfactor.
  by apply: ler_pM => //; rewrite ?expR_ge0 ?divr_ge0 ?ltW ?sat_tfactor_gt0.
have kS : (k < s.+1)%N by apply: ltnW.
have hcN := center_lower_of_aux_prob k3 kS c0 hcL (lt_le_trans hN hprod).
have hd : sat_dwin s.+1 k <= sat_dwin s k :> R := sat_dwin_le k3 s0 (leqnSn s).
move: hcN hd; rewrite /c; clear.
by move: (sat_center s k) (sat_dwin s k) (sat_dwin s.+1 k) (sat_center s.+1 k);
  move=> a b d e; lra.
Qed.

End comparisons.

Section regular.
Context {R : realType}.

(* The size conditions under which the two comparisons apply. *)
Record center_regular (k n : nat) : Prop := CenterRegular {
  creg_size : (k.+1 <= n)%N;
  creg_rep : 2 * 'C(k, 2)%:R <= n%:R :> R;
  creg_err : sat_err n k <= 2^-1 :> R;
  creg_serr : sat_serr n k <= 4^-1 :> R;
  creg_sum : sat_err n k < (sat_tfactor k / 2) ^+ 2 / 2 :> R;
  creg_next : sat_err n k < sat_nfactor k :> R;
  creg_center : sat_a0 k <= sat_center n k :> R;
  creg_dwin : 2 * sat_dwin n k <= sat_a0 k :> R;
  creg_window : 2 ^+ k.+1 <= sat_window n k :> R }.

Lemma center_regular_eventually k : (3 <= k)%N ->
  exists N : nat, forall n, (N <= n)%N -> center_regular k n.
Proof.
move=> k3; have k0 : (0 < k)%N by apply: leq_trans k3.
have d0 : 0 < sat_delta k :> R := sat_delta_gt0 k3.
have d4 : sat_delta k < 4^-1 :> R := sat_delta_lt k0.
have tl0 : 0 < sat_tfactor k / 2 :> R by rewrite divr_gt0 ?sat_tfactor_gt0.
have nf0 : 0 < sat_nfactor k :> R := sat_nfactor_gt0 k.
have a00 : 0 < sat_a0 k :> R := sat_a0_gt0 k0.
have V0 : 0 < sat_vconst k :> R.
  rewrite /sat_vconst.
  apply: mulr_gt0; [apply: mulr_gt0; [apply: mulr_gt0 | ] | apply: addr_gt0];
    by rewrite ?exprn_gt0 ?mulr_gt0 ?ltr0n.
(* One bound eps for the three conditions on the error. *)
set eps : R := Num.min 2^-1
  (Num.min ((sat_tfactor k / 2) ^+ 2 / 4) (sat_nfactor k / 2)).
have eps0 : 0 < eps.
  rewrite /eps !lt_min; apply/and3P; split; first by rewrite invr_gt0.
    by rewrite divr_gt0 // exprn_gt0.
  by rewrite divr_gt0.
(* The thresholds of the four powers of n. *)
have [N1 h1] := powRN_small (mulr_gt0 (ltr0n R 2) d0) (divr_gt0 eps0 V0).
have b2 : 0 < 1 - 2 * sat_delta k :> R by lra.
have e2 : 0 < (4 * 2 ^+ k.+1)^-1 :> R by rewrite invr_gt0 mulr_gt0 ?exprn_gt0.
have [N2 h2] := powRN_small b2 e2.
have [N3 h3] := powRN_small d0 (divr_gt0 a00 (ltr0n R 2)).
have b4 : 0 < 1 - sat_delta k :> R by lra.
have e4 : 0 < (2 ^+ k.+1)^-1 :> R by rewrite invr_gt0 exprn_gt0.
have [N4 h4] := powRN_small b4 e4.
pose N5 := (Num.truncn (4 * expR 2 * k%:R : R)).+1.
pose N6 := (2 * 'C(k, 2))%N.
exists (maxn k.+1 (maxn N1 (maxn N2 (maxn N3 (maxn N4 (maxn N5 N6)))))) => n.
rewrite !geq_max => /and3P [hk hn1 /and5P [hn2 hn3 hn4 hn5 hn6]].
have n0 : (0 < n)%N by apply: leq_ltn_trans (leq0n k) hk.
have n0' : 0 < n%:R :> R by rewrite ltr0n.
have herr : sat_err n k <= eps.
  rewrite /sat_err; apply: le_trans (ler_wpM2l (ltW V0) (h1 n hn1)) _.
  by rewrite mulrC divfK ?gt_eqF.
have ehalf : eps <= 2^-1 by rewrite /eps ge_min lexx.
have esum : eps <= (sat_tfactor k / 2) ^+ 2 / 4.
  by rewrite /eps !ge_min lexx orbT.
have enext : eps <= sat_nfactor k / 2 by rewrite /eps !ge_min lexx !orbT.
have t2 : 0 < (sat_tfactor k / 2) ^+ 2 :> R by rewrite exprn_gt0.
split.
- exact: hk.
- by rewrite -natrM ler_nat.
- exact: le_trans herr ehalf.
- rewrite sat_serrE //.
  apply: le_trans (ler_wpM2l (ltW (exprn_gt0 _ _)) (h2 n hn2)) _ => //.
  by rewrite invfM mulrCA mulfV ?mulr1 ?gt_eqF ?exprn_gt0.
- by move: herr esum t2; move: ((sat_tfactor k / 2) ^+ 2) (sat_err n k) => T x;
    clear; lra.
- by move: herr enext nf0; move: (sat_nfactor k) (sat_err n k) => F x;
    clear; lra.
- apply: sat_center_lower => //; first exact: ltnW.
  by apply: le_trans (ltW (truncnS_gt _)) _; rewrite ler_nat.
- by have := h3 n hn3; rewrite /sat_dwin; lra.
- by have := h4 n hn4; rewrite powRN lef_pV2 ?posrE ?exprn_gt0 ?powR_gt0.
Qed.

(* The two comparisons of the centers, in the form of the hypotheses of the
   convergence theorem T12, with A = 4 and beta = delta_k. *)
Theorem center_comparisons k : (3 <= k)%N -> exists N : nat,
  (forall r s, (N <= r)%N -> (N <= s)%N ->
     Num.min (sat_center r k) (sat_center s k)
       - 4 * (minn r s)%:R `^ (- sat_delta k) <= sat_center (r + s) k :> R) /\
  (forall s, (N <= s)%N ->
     sat_center s k - 4 * s%:R `^ (- sat_delta k) <= sat_center s.+1 k :> R).
Proof.
move=> k3; have [N hN] := center_regular_eventually k3.
exists N; split.
- move=> r s Nr Ns.
  have Nu : (N <= minn r s)%N by rewrite leq_min Nr Ns.
  have NT : (N <= r + s)%N by apply: leq_trans Nr (leq_addr s r).
  case: (hN r Nr) => rs rr re rse _ _ rc _ _.
  case: (hN s Ns) => ss sr se sse _ _ sc _ _.
  case: (hN _ Nu) => _ _ _ _ _ _ _ ud _.
  case: (hN _ NT) => _ _ _ _ tsum _ _ _ _.
  apply: center_sum_comparison => //.
  by apply: le_trans ud _; rewrite le_min rc sc.
- move=> s Ns; have NS : (N <= s.+1)%N by apply: leq_trans Ns (leqnSn s).
  case: (hN s Ns) => ss sr se _ _ _ sc sd sw.
  case: (hN _ NS) => _ _ _ _ _ tn _ _ _.
  apply: center_neighbor_comparison => //.
  exact: le_trans sd sc.
Qed.

End regular.
