(* A scalar tolerance for the non-backtracking column remainder.

   The remainder constant (paper_main_remainder_constant) is
     C_k(h) = (k + 2) (2 h)^(k + 2) + 4^(k + 1) h + 2^k,
   nonnegative for h >= 0. At h = 2 C0 it is the constant of
   paper_main_column_remainder_frame_scaled. For K and eta > 0 put
     S = sum_(k < K) C_k(h),   delta = min(1, eta / (1 + S))
   (paper_main_remainder_tolerance). paper_main_remainder_tolerance_spec:
   0 < delta <= 1 and C_k(h) delta <= eta for every k < K, since
   0 <= C_k(h) <= S < 1 + S. K = 0 is included (S = 0, delta = min(1, eta)).
   Scalar inequalities only. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition paper_main_remainder_constant (k : nat) (h : R) : R :=
  ((k + 2)%:R * (2 * h) ^+ (k + 2) + 4 ^+ (k + 1) * h + 2 ^+ k)%R.

Lemma paper_main_remainder_constant_ge0 (k : nat) (h : R) :
  0 <= h -> 0 <= paper_main_remainder_constant k h.
Proof.
move=> Hh; rewrite /paper_main_remainder_constant.
apply: addr_ge0; first apply: addr_ge0.
- by apply: mulr_ge0; [exact: ler0n | apply: exprn_ge0; rewrite mulr_ge0].
- by apply: mulr_ge0 => //; exact: exprn_ge0.
- exact: exprn_ge0.
Qed.

Lemma paper_main_remainder_constant_le_sum (K k : nat) (h : R) :
  0 <= h -> (k < K)%N -> paper_main_remainder_constant k h <= \sum_(j < K) paper_main_remainder_constant j h.
Proof.
move=> Hh Hk.
rewrite (bigD1 (Ordinal Hk)) //= lerDl.
by apply: sumr_ge0 => j _; exact: paper_main_remainder_constant_ge0.
Qed.

Definition paper_main_remainder_tolerance (K : nat) (h eta : R) : R :=
  (Num.min 1 (eta / (1 + \sum_(k < K) paper_main_remainder_constant k h)))%R.

Theorem paper_main_remainder_tolerance_spec (K : nat) (h eta : R) :
  0 <= h -> 0 < eta ->
  0 < paper_main_remainder_tolerance K h eta /\ paper_main_remainder_tolerance K h eta <= 1 /\
  forall k, (k < K)%N -> paper_main_remainder_constant k h * paper_main_remainder_tolerance K h eta <= eta.
Proof.
move=> Hh Heta.
set S := \sum_(k < K) paper_main_remainder_constant k h.
have HS : 0 <= S by apply: sumr_ge0 => k _; exact: paper_main_remainder_constant_ge0.
have H1S : 0 < 1 + S by lra.
have Hq : 0 < eta / (1 + S) by rewrite divr_gt0.
rewrite /paper_main_remainder_tolerance -/S.
split; first by rewrite lt_min ltr01 Hq.
split; first by rewrite ge_min lexx.
move=> k Hk.
have HC0 := paper_main_remainder_constant_ge0 k h Hh.
have HCS := paper_main_remainder_constant_le_sum K k h Hh Hk.
apply: le_trans (_ : paper_main_remainder_constant k h * (eta / (1 + S)) <= _).
  by apply: ler_wpM2l => //; rewrite ge_min lexx orbT.
rewrite mulrA ler_pdivrMr //.
rewrite -/S in HCS.
have H : 0 <= (1 + S - paper_main_remainder_constant k h) * eta.
  by apply: mulr_ge0; [rewrite subr_ge0; lra | exact: ltW].
lra.
Qed.
