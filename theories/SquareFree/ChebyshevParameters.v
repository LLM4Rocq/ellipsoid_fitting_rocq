(* The scalar parameter choice of the final Chebyshev step of the lower
   spectral edge. Deterministic.

   For theta > 2 and A >= 0, with K = 2^(k+1) and tau = A (K + 1), the
   power theta^K beats 2^K tau: 2^K tau < theta^K as soon as
   3 A <= 2^k u^2, u = theta / 2 - 1 > 0, hence for every large k.
   Route: with q = theta / 2 = 1 + u and m = 2^k, theta^K = 2^K q^K and
   q^K = (q^m)^2 >= (1 + m u)^2 by Bernoulli's inequality, and
   (1 + m u)^2 > m^2 u^2 >= 3 A m >= A (2 m + 1) when m u^2 >= 3 A and
   m >= 1. Dyadic lengths are unbounded because k < 2^k.

   The statements use MathComp's ring_scope at Stdlib's R, in the form of
   the hypothesis of pmlo_cheb_box (SquareFree.EdgeLower):
   K is the natural number 2 ^ k.+1, 2 ^+ K and theta ^+ K are real powers
   at natural exponents, and tau is A * (K%:R + 1).
   - pmchp_bernoulli: Bernoulli's inequality 1 + m u <= (1 + u)^m.
   - pmchp_power_at, pmchp_dyadic_at: the explicit criterion
     3 A <= 2^k u^2 at a given k.
   - pmchp_dyadic_eventually: for A >= 0, some k0 works for every k >= k0.
   - pmchp_dyadic_strict: for A >= 1, some k gives 2^K tau < theta^K.
   - paper_main_chebyshev_parameters: for A >= 1, some k and g > 0 give
     2^K tau + g <= theta^K. *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* Bernoulli's inequality, linear form. *)
Lemma pmchp_bernoulli (u : R) (m : nat) : 0 <= u -> 1 + m%:R * u <= (1 + u) ^+ m.
Proof.
move=> Hu; elim: m => [|m IH]; first by rewrite mul0r addr0 expr0.
have Hm : 0 <= m%:R :> R by exact: ler0n.
have Hmuu : 0 <= m%:R * u * u by rewrite !mulr_ge0.
have Hprod := ler_wpM2l Hu IH.
rewrite exprS -natr1.
lra.
Qed.

(* Dyadic lengths are unbounded: every real is below 2^k for large k. *)
Lemma pmchp_dyadic_unbounded (x : R) :
  exists k0 : nat, forall k : nat, (k0 <= k)%N -> x < (2 ^ k)%:R.
Proof.
have [N HN] : exists N : nat, x < N%:R.
  exists (archimedean.Num.bound `|x|).
  apply: le_lt_trans (ler_norm x) _.
  exact: archimedean.Num.Theory.archi_boundP (normr_ge0 x).
exists N => k Hk.
apply: lt_le_trans HN _.
rewrite ler_nat.
apply: leq_trans Hk _.
exact: ltnW (ltn_expl k (ltnSn 1)).
Qed.

(* The explicit criterion for q > 1: 3 A <= 2^k (q - 1)^2 gives
   A (K + 1) < q^K, K = 2^(k+1). *)
Lemma pmchp_power_at (q A : R) (k : nat) : 1 < q -> 0 <= A ->
  3 * A <= (2 ^ k)%:R * ((q - 1) * (q - 1)) ->
  A * ((2 ^ k.+1)%:R + 1) < q ^+ (2 ^ k.+1).
Proof.
move=> Hq HA Hmu.
set u := q - 1 in Hmu *.
have Hu : 0 < u by rewrite /u subr_gt0.
have Hm1 : 1 <= (2 ^ k)%:R :> R by rewrite ler1n expn_gt0.
have HB := pmchp_bernoulli u (2 ^ k) (ltW Hu).
have Hq1 : q = 1 + u by rewrite /u addrC subrK.
rewrite expnSr exprM natrM Hq1.
set m := (2 ^ k)%:R in Hmu Hm1 HB *.
set X := (1 + u) ^+ (2 ^ k) in HB *.
have Hl : 0 <= 1 + m * u by apply: addr_ge0 => //; apply: mulr_ge0 => //; lra.
have HX2 : (1 + m * u) * (1 + m * u) <= X * X by exact: ler_pM.
have H1 : m * (3 * A) <= m * (m * (u * u)) by apply: ler_wpM2l => //; lra.
have H2 : A <= A * m by exact: ler_peMr.
have H3 : 0 <= m * u by apply: mulr_ge0 => //; lra.
rewrite expr2.
lra.
Qed.

(* The explicit criterion for theta > 2: 3 A <= 2^k (theta / 2 - 1)^2
   gives 2^K tau < theta^K. *)
Lemma pmchp_dyadic_at (theta A : R) (k : nat) : 2 < theta -> 0 <= A ->
  3 * A <= (2 ^ k)%:R * ((theta / 2 - 1) * (theta / 2 - 1)) ->
  2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) < theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA Hk.
have H2 : 0 < 2 :> R by rewrite ltr0n.
have Hq : 1 < theta / 2 by rewrite ltr_pdivlMr // mul1r.
have -> : theta = 2 * (theta / 2) by rewrite mulrC divfK // pnatr_eq0.
rewrite exprMn (ltr_pM2l (exprn_gt0 _ H2)).
exact: pmchp_power_at.
Qed.

(* For theta > 2 and A >= 0, eventually in k: 2^K tau < theta^K. *)
Theorem pmchp_dyadic_eventually (theta A : R) : 2 < theta -> 0 <= A ->
  exists k0 : nat, forall k : nat, (k0 <= k)%N ->
    2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) < theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA.
have H2 : 0 < 2 :> R by rewrite ltr0n.
have Hq : 1 < theta / 2 by rewrite ltr_pdivlMr // mul1r.
have Hu : 0 < theta / 2 - 1 by rewrite subr_gt0.
have Huu : 0 < (theta / 2 - 1) * (theta / 2 - 1) by exact: mulr_gt0.
have [k0 Hk0] :=
  pmchp_dyadic_unbounded (3 * A / ((theta / 2 - 1) * (theta / 2 - 1))).
exists k0 => k Hk.
apply: pmchp_dyadic_at => //.
by apply: ltW; rewrite -ltr_pdivrMr //; exact: Hk0.
Qed.

(* theta > 2 and A >= 1 give some k with 2^K tau < theta^K,
   K = 2^(k+1), tau = A (K + 1). *)
Theorem pmchp_dyadic_strict (theta A : R) : 2 < theta -> 1 <= A ->
  exists k : nat, 2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) < theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA.
have HA0 : 0 <= A by apply: le_trans HA; exact: ler01.
have [k0 Hk0] := pmchp_dyadic_eventually _ _ Hth HA0.
by exists k0; apply: Hk0.
Qed.

(* The stronger form with a positive gap g: 2^K tau + g <= theta^K. *)
Theorem paper_main_chebyshev_parameters (theta A : R) : 2 < theta -> 1 <= A ->
  exists k : nat, exists g : R, 0 < g /\
    2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) + g <= theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA.
have [k Hk] := pmchp_dyadic_strict _ _ Hth HA.
exists k, (theta ^+ (2 ^ k.+1) - 2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1))).
split; first by rewrite subr_gt0.
by rewrite addrC subrK lexx.
Qed.
