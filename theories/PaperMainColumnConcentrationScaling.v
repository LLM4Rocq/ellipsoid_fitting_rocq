(* Eventual scalar frame premises for the non-backtracking column remainder (A37).

   1. Binomial normalization. With M = 'C(d, 2), 2 M = d (d - 1)
      (pmccf_bin2). For d >= 2 and 0 < N <= d^2: 0 < M and N <= 4 M, since
      d^2 <= 2 d (d - 1) when d >= 2.
   2. Entry radius. For c, C0, r > 0 put A = C0 c r^2 > 0. If c d^2 <= N and
      1 <= A d, then d <= A d^2 <= C0 N r^2. If N(d) has eventual density
      >= c, then for all large d (d >= 1 / A and past the density threshold)
      d <= C0 N(d) r^2. No upper density is needed.
   Deterministic; no probability premise. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainColumnConcentrationFrame.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Binomial normalization. *)
Lemma paper_main_frame_binomial_twice (d : nat) :
  ('C(d, 2))%:R * 2 = d%:R * (d%:R - 1) :> R.
Proof.
have := congr1 (fun n : nat => n%:R : R) (pmccf_bin2 d); rewrite /= !natrM => ->.
case: d => [|d]; first by rewrite /= !mul0r.
by rewrite -subn1 natrB.
Qed.

Theorem paper_main_frame_binomial_bounds (N d : nat) :
  (2 <= d)%N -> (0 < N)%N -> (N <= d ^ 2)%N ->
  0 < ('C(d, 2))%:R :> R /\ N%:R <= 4 * ('C(d, 2))%:R :> R.
Proof.
move=> Hd HN HNd.
have HM := paper_main_frame_binomial_twice d.
have Hk : 2 <= d%:R :> R by rewrite (ler_nat R 2 d).
have HNR : N%:R <= d%:R ^+ 2 :> R by rewrite -natrX ler_nat.
split; first by rewrite ltr0n bin_gt0.
have Hp : 0 <= d%:R * (d%:R - 2) :> R by rewrite mulr_ge0 // ?subr_ge0 //; lra.
lra.
Qed.

(* 2. Entry radius. *)
Lemma paper_main_frame_entry_radius_det (N d : nat) (c C0 r : R) :
  0 < c -> 0 < C0 -> 0 < r -> c * d%:R ^+ 2 <= N%:R -> 1 <= C0 * c * r ^+ 2 * d%:R ->
  d%:R <= C0 * N%:R * r ^+ 2.
Proof.
move=> Hc HC0 Hr HcN HA.
have Hd0 : 0 <= d%:R :> R by exact: ler0n.
have H1 : d%:R <= C0 * c * r ^+ 2 * d%:R * d%:R.
  by rewrite -[X in X <= _]mul1r; apply: ler_wpM2r.
have Hr2 : 0 <= C0 * r ^+ 2 by rewrite mulr_ge0 // ?exprn_ge0 // ltW.
have H2 := ler_wpM2l Hr2 HcN.
have E1 : C0 * c * r ^+ 2 * d%:R * d%:R = C0 * r ^+ 2 * (c * d%:R ^+ 2) by ring.
have E2 : C0 * N%:R * r ^+ 2 = C0 * r ^+ 2 * N%:R by ring.
by rewrite E2; apply: le_trans H1 _; rewrite E1.
Qed.

Theorem paper_main_frame_entry_radius (N : nat -> nat) (c C0 r : R) :
  0 < c -> 0 < C0 -> 0 < r -> paper_main_eventually_ge (paper_main_density N) c ->
  exists D : nat, forall d, (D <= d)%N -> d%:R <= C0 * (N d)%:R * r ^+ 2.
Proof.
move=> Hc HC0 Hr [D1 HD1].
have HA : 0 < C0 * c * r ^+ 2 by rewrite !mulr_gt0 // exprn_gt0.
have [K HK] := INR_unbounded (1 / (C0 * c * r ^+ 2))%R.
exists (maxn D1 (maxn 1 K)) => d Hd.
rewrite !geq_max in Hd; case/andP: Hd => HdD1 /andP [Hd1 HdK].
have Hd0R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0 // ltr0n.
have HcN : c * d%:R ^+ 2 <= (N d)%:R.
  by have := HD1 d HdD1; rewrite /paper_main_density ler_pdivlMr.
apply: (paper_main_frame_entry_radius_det (N d) d c C0 r) => //.
have HK' : 1 / (C0 * c * r ^+ 2) < K%:R by rewrite -[K%:R]INRE; apply/RltP; exact: HK.
have HKd : K%:R <= d%:R :> R by rewrite ler_nat.
have H1 := ler_wpM2l (ltW HA) HKd.
have H2 : C0 * c * r ^+ 2 * (1 / (C0 * c * r ^+ 2)) < C0 * c * r ^+ 2 * K%:R.
  by rewrite ltr_pM2l.
have E : C0 * c * r ^+ 2 * (1 / (C0 * c * r ^+ 2)) = 1 by rewrite mul1r divff ?gt_eqF.
rewrite E in H2; lra.
Qed.
