From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean topology normedtype sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianAnalysis.analysis Require Import min_superadditive.
From GaussianApplications.RandomSAT Require Import Model Pivotal.
From GaussianApplications.RandomSAT Require Import Survival Tails CenterBounds.
From GaussianApplications.RandomSAT Require Import CenterComparison.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: the limit of the centers and the threshold                 *)
(*                                                                            *)
(* Part of target T9 of phase 13. A Rocq formalization of the credited        *)
(* argument of the theorem 'Concentration implies convergence'                *)
(* (thm:concentration-to-convergence, source/sections/convergence.tex) and of *)
(* the main theorem (thm:main, source/sections/introduction.tex) of 'A        *)
(* Limiting Satisfiability Threshold for Every Fixed Clause Size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd), following the Lean     *)
(* development of the collection (lean/OAI/Probability/RandomSAT):            *)
(* Lean: center_tendsto (Main.lean, line 21)                                  *)
(* Lean: limitingCenter_bounds (Main.lean, line 37)                           *)
(* Lean: subcritical_limit (Main.lean, line 60)                               *)
(* Lean: supercritical_limit (Main.lean, line 109)                            *)
(*                                                                            *)
(* P_n(m) = sat_prob R n k m and mu_n = sat_center n k.                       *)
(*                                                                            *)
(* - sat_center_cvg: for k >= 3 the centers mu_n converge, by                 *)
(*   min_superadditive_cvgn of library/analysis/min_superadditive.v (T12) and *)
(*   the comparisons of CenterComparison.v; they are bounded by 2^(k+1)       *)
(*   (sat_center_bounded).                                                    *)
(* - sat_alpha k is their limit: sat_a0 k <= sat_alpha k <= 2^k + 1           *)
(*   (sat_alpha_ge, sat_alpha_le), in particular 0 < sat_alpha k < 2^(k+1).   *)
(* - sat_subcritical: for 0 <= c < sat_alpha k, P_n(floor(c n)) tends to 1,   *)
(*   by the lower tail of Tails.v.                                            *)
(* - sat_supercritical: for c > sat_alpha k, P_n(floor(c n)) tends to 0, by   *)
(*   the upper tail at the density min(c, 2^(k+1)) and the monotonicity of    *)
(*   P_n (sat_prob_le).                                                       *)
(* - powRN_cvg0: n^(-b) tends to 0 for b > 0; with it the error sat_err n k   *)
(*   and the density window tend to 0.                                        *)
(*                                                                            *)
(* Departure: the manuscript's convergence theorem allows any cap lambda n;   *)
(* this file and the Lean development fix the cap 2^(k+1) n of T7, which      *)
(* suffices for the theorem.                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section threshold.
Context {R : realType}.

(* The limit alpha_k of the centers mu_n = E V_n / n. *)
Definition sat_alpha (k : nat) : R := limn (fun n => sat_center n k).

Lemma sat_center_bounded k : bounded_fun (fun n => sat_center n k : R).
Proof.
exists (2 ^+ k.+1); split; first by rewrite num_real.
move=> M hM n _ /=; rewrite ger0_norm ?sat_center_ge0 //.
exact: le_trans (sat_center_le n k) (ltW hM).
Qed.

Lemma sat_center_cvg k : (3 <= k)%N -> cvgn (fun n => sat_center n k : R).
Proof.
move=> k3; have [N [hs hn]] := @center_comparisons R k k3.
apply: (@min_superadditive_cvgn R _ 4 (sat_delta k) N) => //.
- exact: sat_delta_gt0.
- by move=> r s Nr Ns _ _; exact: hs.
- exact: sat_center_bounded.
Qed.

Lemma sat_alpha_ge k : (3 <= k)%N -> sat_a0 k <= sat_alpha k.
Proof.
move=> k3; apply: limr_ge; first exact: sat_center_cvg.
exists (maxn k (Num.truncn (4 * expR 2 * k%:R : R)).+1) => // n /=.
rewrite geq_max => /andP [kn hn]; apply: sat_center_lower => //.
by apply: le_trans (ltW (truncnS_gt _)) _; rewrite ler_nat.
Qed.

Lemma sat_alpha_le k : (3 <= k)%N -> sat_alpha k <= 2 ^+ k + 1.
Proof.
move=> k3; apply: limr_le; first exact: sat_center_cvg.
have e2 : 2 < expR 1 :> R.
  by have := @expR_gt1Dx R 1 (oner_neq0 _); rewrite (_ : 1 + 1 = 2 :> R).
have q1 : `|2 / expR 1| < 1 :> R.
  by rewrite ger0_norm ?divr_ge0 ?expR_ge0 // ltr_pdivrMr ?expR_gt0 // mul1r.
have hq : \forall n \near \oo, (2 / expR 1) ^+ n < (2 ^+ k.+1)^-1 :> R.
  by apply: (cvgr_lt 0 (cvg_expr q1)); rewrite invr_gt0 exprn_gt0.
near=> n; apply: sat_center_upper.
- by near: n; exact: nbhs_infty_ge.
- by near: n; exact: nbhs_infty_ge.
- rewrite -ler_pdivlMl ?exprn_gt0 // mulr1; apply: ltW.
  by near: n; exact: hq.
Unshelve. all: by end_near.
Qed.

Lemma sat_alpha_gt0 k : (3 <= k)%N -> 0 < sat_alpha k.
Proof.
move=> k3; have k0 : (0 < k)%N by apply: leq_trans k3.
exact: lt_le_trans (sat_a0_gt0 k0) (sat_alpha_ge k3).
Qed.

Lemma powRN_cvg0 (b : R) : 0 < b -> n%:R `^ (- b) @[n --> \oo] --> (0 : R).
Proof.
move=> b0; apply/cvgr0Pnorm_le => e e0; have [N hN] := powRN_small b0 e0.
near=> n; rewrite ger0_norm ?powR_ge0 //; apply: hN.
by near: n; exact: nbhs_infty_ge.
Unshelve. all: by end_near.
Qed.

Lemma sat_err_cvg0 k : (3 <= k)%N -> sat_err n k @[n --> \oo] --> (0 : R).
Proof.
move=> k3; have d0 : 0 < 2 * sat_delta k :> R.
  by rewrite mulr_gt0 ?sat_delta_gt0.
have h := cvgM (cvg_cst (sat_vconst k : R)) (powRN_cvg0 d0).
by rewrite mulr0 in h; exact: h.
Qed.

Lemma sat_dwin_cvg0 k : (3 <= k)%N -> sat_dwin n k @[n --> \oo] --> (0 : R).
Proof.
by move=> k3; apply: powRN_cvg0; exact: sat_delta_gt0.
Qed.

(* Below the limit alpha_k, floor(c n) clauses are satisfiable with
   probability tending to one. *)
Lemma sat_subcritical k (c : R) : (3 <= k)%N -> 0 <= c -> c < sat_alpha k ->
  sat_prob R n k (Num.truncn (c * n%:R)) @[n --> \oo] --> (1 : R).
Proof.
move=> k3 c0 hc.
have hcv : (fun n => sat_center n k - sat_dwin n k) @ \oo --> (sat_alpha k : R).
  rewrite -[sat_alpha k]subr0.
  by apply: cvgB; [exact: sat_center_cvg | exact: sat_dwin_cvg0].
have hev := cvgr_gt (sat_alpha k) hcv c hc.
apply: (@squeeze_cvgr _ _ _ _ (fun n => 1 - sat_err n k) (fun=> 1));
  last exact: cvg_cst.
  near=> n; rewrite sat_prob_le1 andbT.
  have kn : (k < n)%N by near: n; exact: nbhs_infty_ge.
  have n0 : (0 < n)%N := leq_ltn_trans (leq0n k) kn.
  apply: sat_prob_center_lower => //.
  have h1 : c < sat_center n k - sat_dwin n k by near: n; exact: hev.
  have cn0 : 0 <= c * n%:R by rewrite mulr_ge0 ?ler0n.
  have hm : (Num.truncn (c * n%:R))%:R <= c * n%:R :> R by rewrite truncn_le.
  have := ler_wpM2r (ler0n R n) (ltW h1).
  by rewrite (sat_window_dwin k n0); lra.
by have := cvgB (cvg_cst (1 : R)) (sat_err_cvg0 k3); rewrite subr0; exact.
Unshelve. all: by end_near.
Qed.

(* Above alpha_k, with probability tending to zero. *)
Lemma sat_supercritical k (c : R) : (3 <= k)%N -> sat_alpha k < c ->
  sat_prob R n k (Num.truncn (c * n%:R)) @[n --> \oo] --> (0 : R).
Proof.
move=> k3 hc; have k0 : (0 < k)%N by apply: leq_trans k3.
have h2k : 2 <= 2 ^+ k :> R.
  have : (2 <= 2 ^ k)%N by rewrite -[X in (X <= _)%N]expn1 leq_pexp2l.
  by rewrite -(ler_nat R) natrX.
have hL : sat_alpha k < 2 ^+ k.+1.
  by have := sat_alpha_le k3; rewrite exprS; lra.
(* The density d = min(c, 2^(k+1)) stays below the cap. *)
set d := Num.min c (2 ^+ k.+1).
have hd : sat_alpha k < d by rewrite lt_min hc hL.
have d0 : 0 <= d by apply: ltW (lt_trans (sat_alpha_gt0 k3) hd).
have dc : d <= c by rewrite ge_min lexx.
have dL : d <= 2 ^+ k.+1 by rewrite ge_min lexx orbT.
have hcv : (fun n => sat_center n k + 2 * sat_dwin n k) @ \oo -->
    (sat_alpha k : R).
  rewrite -[sat_alpha k]addr0; apply: cvgD; first exact: sat_center_cvg.
  have h := cvgM (cvg_cst (2 : R)) (sat_dwin_cvg0 k3).
  by rewrite mulr0 in h; exact: h.
have hev : \forall n \near \oo, sat_center n k + 2 * sat_dwin n k < d :=
  cvgr_lt (sat_alpha k) hcv d hd.
apply: (@squeeze_cvgr _ _ _ _ (fun=> 0) (fun n => sat_err n k));
  [|exact: cvg_cst|exact: sat_err_cvg0].
near=> n; rewrite sat_prob_ge0 /=.
have kn : (k < n)%N by near: n; exact: nbhs_infty_ge.
have n0 : (0 < n)%N := leq_ltn_trans (leq0n k) kn.
have dn0 : 0 <= d * n%:R by rewrite mulr_ge0 ?ler0n.
have hdn : (Num.truncn (d * n%:R) <= Num.truncn (c * n%:R))%N.
  by apply: le_truncn; rewrite ler_wpM2r ?ler0n.
apply: le_trans (@sat_prob_le R n k (ltnW kn) _ _ hdn) _.
apply: sat_prob_center_upper => //.
  rewrite -(ler_nat R) /sat_cap natrM natrX.
  apply: (@le_trans _ _ (d * n%:R)); first by rewrite truncn_le.
  by rewrite ler_wpM2r ?ler0n.
have h1 : sat_center n k + 2 * sat_dwin n k < d by near: n; exact: hev.
have w1 : 1 <= sat_window n k :> R := sat_window_ge1 k3 n0.
have hm := truncnS_gt (d * n%:R).
have := ler_wpM2r (ler0n R n) (ltW h1).
by move: w1 hm; rewrite (sat_window_dwin k n0) -natr1; lra.
Unshelve. all: by end_near.
Qed.

End threshold.
