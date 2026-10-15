From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model Pivotal Variance.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.
From GaussianApplications.RandomSAT Require Import Survival.

(**md**************************************************************************)
(* # Random k-SAT: the two tails around the centers                           *)
(*                                                                            *)
(* Part of target T9 of phase 13 (AGENTS.md, section Phase 13; the plan       *)
(* notes/phase13-plan.md, section 2). A Rocq formalization of the credited    *)
(* argument of the proposition 'Polynomial concentration'                     *)
(* (prop:concentration, equation eq:concentration) of 'A Limiting             *)
(* Satisfiability Threshold for Every Fixed Clause Size' (family 235 of the   *)
(* OpenAI math collection, revision 1581d4cbd,                                *)
(* source/sections/concentration.tex), with the two tail estimates of the     *)
(* proof of the lemma 'Proper-clause transfer'                                *)
(* (source/sections/convergence.tex), following the Lean development of the   *)
(* collection (lean/OAI/Probability/RandomSAT):                               *)
(* Lean: center (Concentration.lean, line 22)                                 *)
(* Lean: concentration_capped (Concentration.lean, line 214)                  *)
(* Lean: properSATProbability_center_upper (Concentration.lean, line 252)     *)
(* Lean: properSATProbability_center_lower (Concentration.lean, line 260)     *)
(*                                                                            *)
(* The clauses have size k and n variables. V_n is the longest satisfiable    *)
(* prefix (sat_prefix_len) of sat_cap k n = 2^(k+1) n independent uniform     *)
(* clauses, and P_n(m) = sat_prob R n k m.                                    *)
(*                                                                            *)
(* - sat_center n k is the center mu_n = E V_n / n, with 0 <= mu_n <= 2^(k+1) *)
(*   (sat_center_ge0, sat_center_le).                                         *)
(* - sat_delta k = (k - 2) / (4 k) is delta_k; sat_window n k = n^(1 -        *)
(*   delta_k) is the window and sat_err n k = C_k n^(-2 delta_k) the error,   *)
(*   with the constant sat_vconst k = 8 4^(k+1) k (3 k + 2^(k+2)) of T7.      *)
(* - sat_concentration: for k >= 3 and n >= k + 1, P(|V_n - n mu_n| >= n^(1 - *)
(*   delta_k)) <= sat_err n k, by Chebyshev's inequality (unif_chebyshev) and *)
(*   the variance bound sat_variance_bound_explicit of T7.                    *)
(* - sat_prob_center_upper: P_n(m) <= sat_err n k when n mu_n + n^(1 -        *)
(*   delta_k) <= m <= sat_cap k n.                                            *)
(* - sat_prob_center_lower: P_n(m) >= 1 - sat_err n k when m + n^(1 -         *)
(*   delta_k) <= n mu_n.                                                      *)
(*                                                                            *)
(* The two tails follow from the survival identity sat_prob_tail of           *)
(* Survival.v. The exponent of the error is 1 + 2/k - 2 (1 - delta_k) = - 2   *)
(* delta_k (sat_exponent), the manuscript's eta_k.                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section tails.
Context {R : realType}.

(* The center mu_n = E V_n / n, with V_n the longest satisfiable prefix of
   sat_cap k n clauses. *)
Definition sat_center (n k : nat) : R :=
  sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
    (sat_prefix_len t)%:R) / n%:R.

Definition sat_delta (k : nat) : R := (k%:R - 2) / (4 * k%:R).

Definition sat_window (n k : nat) : R := n%:R `^ (1 - sat_delta k).

Definition sat_vconst (k : nat) : R :=
  8 * 4 ^+ k.+1 * k%:R * (3 * k%:R + 2 ^+ k.+2).

Definition sat_err (n k : nat) : R :=
  sat_vconst k * n%:R `^ (- (2 * sat_delta k)).

Lemma sat_prefix_len_le n k M (t : M.-tuple (clause n k)) :
  (sat_prefix_len t <= M)%N.
Proof. by apply/bigmax_leqP => m _; rewrite -ltnS (ltn_ord m). Qed.

Lemma sat_center_mul n k : (0 < n)%N ->
  n%:R * sat_center n k =
  sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
    (sat_prefix_len t)%:R : R).
Proof. by move=> n0; rewrite /sat_center mulrC divfK // pnatr_eq0 -lt0n. Qed.

Lemma sat_center_ge0 n k : 0 <= sat_center n k.
Proof.
rewrite /sat_center divr_ge0 // sat_meanE.
by apply: unif_mean_ge0 => t; exact: ler0n.
Qed.

Lemma sat_mean_le_cap n k :
  sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
    (sat_prefix_len t)%:R : R) <= (sat_cap k n)%:R.
Proof.
rewrite sat_meanE.
have [T0|T0] := posnP #|{: (sat_cap k n).-tuple (clause n k)}|.
  by rewrite /unif_mean T0 invr0 mul0r ler0n.
by apply: unif_mean_le => // t; rewrite ler_nat sat_prefix_len_le.
Qed.

Lemma sat_center_le n k : sat_center n k <= 2 ^+ k.+1.
Proof.
have [->|n0] := posnP n; first by rewrite /sat_center invr0 mulr0 exprn_ge0.
rewrite /sat_center ler_pdivrMr ?ltr0n //.
by apply: le_trans (sat_mean_le_cap n k) _; rewrite /sat_cap natrM natrX.
Qed.

Lemma sat_delta_gt0 k : (3 <= k)%N -> 0 < sat_delta k.
Proof.
move=> k3; have k0 : (0 < k)%N by apply: leq_trans k3.
rewrite /sat_delta divr_gt0 ?mulr_gt0 ?ltr0n // subr_gt0.
by rewrite -(ltr_nat R) in k3.
Qed.

Lemma sat_delta_lt k : (0 < k)%N -> sat_delta k < 4^-1.
Proof.
move=> k0; rewrite /sat_delta ltr_pdivrMr ?mulr_gt0 ?ltr0n //.
by rewrite mulrA mulVf ?mul1r ?pnatr_eq0 // ltrBlDr ltrDl ltr0n.
Qed.

Lemma sat_window_gt0 n k : (0 < n)%N -> 0 < sat_window n k.
Proof. by move=> n0; rewrite powR_gt0 // ltr0n. Qed.

Lemma sat_exponent k : (0 < k)%N ->
  1 + 2 / k%:R - (1 - sat_delta k) * 2 = - (2 * sat_delta k) :> R.
Proof.
move=> k0; have k0' : k%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
by rewrite /sat_delta; field.
Qed.

(* Chebyshev's inequality with the variance bound of T7. *)
Lemma sat_concentration n k : (3 <= k)%N -> (k.+1 <= n)%N ->
  sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
    (sat_window n k <=
       `|(sat_prefix_len t)%:R - n%:R * sat_center n k|)%R%:R : R)
  <= sat_err n k.
Proof.
move=> k3 kn; have n0 : (0 < n)%N by apply: leq_trans kn.
have k0 : (0 < k)%N by apply: leq_trans k3.
rewrite sat_center_mul // !sat_meanE.
apply: le_trans (unif_chebyshev _ (sat_window_gt0 k n0)) _.
have hV := sat_variance_bound_explicit (R := R) k3 kn.
have -> : unif_var (fun t : (sat_cap k n).-tuple (clause n k) =>
    (sat_prefix_len t)%:R : R) = sat_capped_var R n k by [].
rewrite ler_pdivrMr ?exprn_gt0 ?sat_window_gt0 //.
apply: le_trans hV _; rewrite /sat_err /sat_vconst -mulrA.
have e : n%:R `^ (1 + 2 / k%:R) =
    n%:R `^ (- (2 * sat_delta k)) * sat_window n k ^+ 2 :> R.
  rewrite /sat_window -powR_mulrn ?powR_ge0 // -powRrM.
  have nz : (- (2 * sat_delta k) + (1 - sat_delta k) * 2 == 0) ==>
      (n%:R != 0 :> R) by rewrite pnatr_eq0 -lt0n n0 implybT.
  by rewrite -(powRD nz) -(sat_exponent k0) subrK.
by rewrite e !mulrA.
Qed.

(* The upper tail: at least the window above n times the center, P_n(m) is
   at most the error. *)
Lemma sat_prob_center_upper n k m : (3 <= k)%N -> (k.+1 <= n)%N ->
  (m <= sat_cap k n)%N ->
  n%:R * sat_center n k + sat_window n k <= m%:R ->
  sat_prob R n k m <= sat_err n k.
Proof.
move=> k3 kn mM hm; have kn' : (k <= n)%N := ltnW kn.
rewrite (sat_prob_tail kn' mM); apply: le_trans (sat_concentration k3 kn).
rewrite !sat_meanE; apply: ler_unif_mean => t.
case: (leqP m (sat_prefix_len t)) => h; last exact: ler0n.
suff -> : (sat_window n k <=
    `|(sat_prefix_len t)%:R - n%:R * sat_center n k|)%R by [].
apply: le_trans (ler_norm _); rewrite lerBrDl.
by apply: le_trans hm _; rewrite ler_nat.
Qed.

(* The lower tail: at least the window below n times the center, P_n(m) is
   at least one minus the error. *)
Lemma sat_prob_center_lower n k m : (3 <= k)%N -> (k.+1 <= n)%N ->
  m%:R + sat_window n k <= n%:R * sat_center n k ->
  1 - sat_err n k <= sat_prob R n k m.
Proof.
move=> k3 kn hm; have kn' : (k <= n)%N := ltnW kn.
have n0 : (0 < n)%N by apply: leq_trans kn.
have w0 := sat_window_gt0 k n0.
have mM : (m <= sat_cap k n)%N.
  rewrite -(ler_nat R); apply: le_trans (sat_mean_le_cap n k).
  rewrite -sat_center_mul //; apply: le_trans hm.
  by rewrite lerDl ltW.
have T0 : (0 < #|{: (sat_cap k n).-tuple (clause n k)}|)%N.
  by rewrite card_tuple expn_gt0 card_clause_gt0.
have h : 1 <= sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
      (m <= sat_prefix_len t)%N%:R : R) +
    sat_mean (fun t : (sat_cap k n).-tuple (clause n k) =>
      (sat_window n k <=
         `|(sat_prefix_len t)%:R - n%:R * sat_center n k|)%R%:R : R).
  rewrite !sat_meanE -unif_meanD -[X in X <= _](unif_mean_cst (1 : R) T0).
  apply: ler_unif_mean => t.
  case: (leqP m (sat_prefix_len t)) => h; first by rewrite lerDl ler0n.
  suff -> : (sat_window n k <=
      `|(sat_prefix_len t)%:R - n%:R * sat_center n k|)%R by rewrite add0r.
  rewrite distrC; apply: le_trans (ler_norm _); rewrite lerBrDl.
  apply: le_trans hm; rewrite lerD2r ltW // ltr_nat.
  exact: h.
have := sat_concentration k3 kn; rewrite (sat_prob_tail kn' mM).
by move: h; set P := sat_mean _; set Q := sat_mean _; lra.
Qed.

End tails.
