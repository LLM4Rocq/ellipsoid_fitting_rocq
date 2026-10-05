(* The scalar part of the final Chebyshev step of the lower spectral edge
   (task L1, part 2): the remainder bound pmlo_rho of
   PaperMainSquarefreeEdgeLower and the choice of eta. Scalars only; no
   matrix or probability statement.

   pmlo_rho beta rho K, with rho_0 = 0 and rho_(K+1) = beta rho_K + 2^K rho,
   is nonnegative for beta, rho >= 0, additive and homogeneous in rho, so
   pmlo_rho beta rho K = rho * pmlo_rho beta 1 K, and nondecreasing in rho
   for beta >= 0. Given 2^K tau + g <= theta^K with g > 0, tau >= 0 and
   beta >= 0, eta = g / (1 + 3 K tau pmlo_rho beta 1 K) > 0 gives
   pmlo_rho beta rho K <= g, hence 2^K tau + pmlo_rho beta rho K <= theta^K,
   for every 0 <= rho <= 3 K eta tau, in particular rho = 3 K eta tau.
   With PaperMainChebyshevParameters, for theta > 2 and A >= 1, k comes
   first (K = 2^(k+1), tau = A (K + 1)), then eta for every beta >= 0. The
   radius 3 * K%:R * eta * tau is the one of the recurrence bound.
   - pmchpe_rho_ge0, pmchpe_rhoZ, pmchpe_rhoD, pmchpe_rho_lin,
     pmchpe_rho_le: the properties of pmlo_rho.
   - pmchpe_eta_explicit, pmchpe_eta_gap, pmchpe_combine: the choice of eta.
   - paper_main_chebyshev_edge_parameters (every 0 <= rho <= 3 K eta tau)
     and paper_main_chebyshev_edge_parameters_exact (rho = 3 K eta tau).
   - paper_main_chebyshev_edge_parameters_concrete_beta (theta = 49/24,
     A = 12, k = 17, K = 2^18, every beta >= 0),
     paper_main_chebyshev_edge_parameters_concrete (beta = tau + 1) and
     paper_main_chebyshev_edge_parameters_concrete_exact (beta = tau + 1,
     rho = 3 K eta tau). *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainSquarefreeEdgeLower PaperMainChebyshevParameters.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The remainder bound pmlo_rho. *)

(* Nonnegative for beta, rho >= 0. *)
Lemma pmchpe_rho_ge0 (beta rho : R) (K : nat) : 0 <= beta -> 0 <= rho ->
  0 <= pmlo_rho beta rho K.
Proof.
move=> Hb Hr; elim: K => [|K IH] /=; first exact: lexx.
apply: addr_ge0; first exact: mulr_ge0.
by apply: mulr_ge0 => //; apply: exprn_ge0; rewrite ler0n.
Qed.

(* Homogeneous in rho. *)
Lemma pmchpe_rhoZ (beta c rho : R) (K : nat) :
  pmlo_rho beta (c * rho) K = c * pmlo_rho beta rho K.
Proof.
elim: K => [|K IH] /=; first by rewrite mulr0.
by rewrite IH; ring.
Qed.

(* Linear in rho: rho times the value at rho = 1. *)
Lemma pmchpe_rho_lin (beta rho : R) (K : nat) :
  pmlo_rho beta rho K = rho * pmlo_rho beta 1 K.
Proof. by rewrite -pmchpe_rhoZ mulr1. Qed.

(* 2. The choice of eta. *)

(* eta = g / (1 + 3 K tau rho_1) is positive and keeps rho_K <= g for
   every 0 <= rho <= 3 K eta tau. *)
Lemma pmchpe_eta_explicit (beta tau g : R) (K : nat) : 0 <= beta -> 0 <= tau -> 0 < g ->
  0 < g / (1 + 3 * K%:R * tau * pmlo_rho beta 1 K) /\
  forall rho : R, 0 <= rho ->
    rho <= 3 * K%:R * (g / (1 + 3 * K%:R * tau * pmlo_rho beta 1 K)) * tau ->
    pmlo_rho beta rho K <= g.
Proof.
move=> Hb Htau Hg.
have Hr1 : 0 <= pmlo_rho beta 1 K by apply: pmchpe_rho_ge0 => //; exact: ler01.
have Hc : 0 <= 3 * K%:R * tau * pmlo_rho beta 1 K.
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; apply: mulr_ge0 => //; rewrite ler0n.
set c := 3 * K%:R * tau * pmlo_rho beta 1 K in Hc *.
have Hc1 : 0 < 1 + c by apply: lt_le_trans (ltr01) _; rewrite lerDl.
have He0 : 0 < g / (1 + c) by exact: divr_gt0.
split => // rho H0 Hle.
set e := g / (1 + c) in He0 Hle *.
have He : e * (1 + c) = g by rewrite /e divfK // lt0r_neq0.
have H1 : rho * pmlo_rho beta 1 K <= 3 * K%:R * e * tau * pmlo_rho beta 1 K.
  exact: ler_wpM2r.
have Hlin : 3 * K%:R * e * tau * pmlo_rho beta 1 K = e * c by rewrite /c; ring.
rewrite pmchpe_rho_lin.
lra.
Qed.

(* The same with eta existential. *)
Lemma pmchpe_eta_gap (beta tau g : R) (K : nat) : 0 <= beta -> 0 <= tau -> 0 < g ->
  exists eta : R, 0 < eta /\
    forall rho : R, 0 <= rho -> rho <= 3 * K%:R * eta * tau ->
      pmlo_rho beta rho K <= g.
Proof.
move=> Hb Htau Hg.
have [He Hrho] := pmchpe_eta_explicit _ _ _ K Hb Htau Hg.
by exists (g / (1 + 3 * K%:R * tau * pmlo_rho beta 1 K)); split.
Qed.

(* A gap 2^K tau + g <= theta^K absorbs the remainder bound. *)
Lemma pmchpe_combine (theta tau beta g : R) (K : nat) :
  0 <= beta -> 0 <= tau -> 0 < g -> 2 ^+ K * tau + g <= theta ^+ K ->
  exists eta : R, 0 < eta /\
    forall rho : R, 0 <= rho -> rho <= 3 * K%:R * eta * tau ->
      2 ^+ K * tau + pmlo_rho beta rho K <= theta ^+ K.
Proof.
move=> Hb Htau Hg Hgap.
have [eta [He Hrho]] := pmchpe_eta_gap _ _ _ K Hb Htau Hg.
exists eta; split => // rho H0 Hle.
apply: le_trans Hgap; rewrite lerD2l; exact: Hrho.
Qed.

(* 3. The endpoints. K = 2^(k+1), tau = A (K + 1). *)

(* k first, then eta for every beta >= 0; every 0 <= rho <= 3 K eta tau. *)
Theorem paper_main_chebyshev_edge_parameters (theta A : R) : 2 < theta -> 1 <= A ->
  exists k : nat, forall beta : R, 0 <= beta -> exists eta : R, 0 < eta /\
    forall rho : R, 0 <= rho ->
      rho <= 3 * (2 ^ k.+1)%:R * eta * (A * ((2 ^ k.+1)%:R + 1)) ->
      2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) + pmlo_rho beta rho (2 ^ k.+1)
      <= theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA.
have [k [g [Hg Hgap]]] := paper_main_chebyshev_parameters _ _ Hth HA.
exists k => beta Hb.
have HA0 : 0 <= A by lra.
have Htau : 0 <= A * ((2 ^ k.+1)%:R + 1).
  by apply: mulr_ge0 => //; apply: addr_ge0; [exact: ler0n | exact: ler01].
exact: pmchpe_combine Hb Htau Hg Hgap.
Qed.

(* The task form, at rho = 3 K eta tau. *)
Corollary paper_main_chebyshev_edge_parameters_exact (theta A : R) : 2 < theta -> 1 <= A ->
  exists k : nat, forall beta : R, 0 <= beta -> exists eta : R, 0 < eta /\
    2 ^+ (2 ^ k.+1) * (A * ((2 ^ k.+1)%:R + 1)) +
    pmlo_rho beta (3 * (2 ^ k.+1)%:R * eta * (A * ((2 ^ k.+1)%:R + 1))) (2 ^ k.+1)
    <= theta ^+ (2 ^ k.+1).
Proof.
move=> Hth HA.
have [k Hk] := paper_main_chebyshev_edge_parameters _ _ Hth HA.
exists k => beta Hb.
have [eta [He Hrho]] := Hk beta Hb.
exists eta; split => //.
have HA0 : 0 <= A by lra.
have Htau : 0 <= A * ((2 ^ k.+1)%:R + 1).
  by apply: mulr_ge0 => //; apply: addr_ge0; [exact: ler0n | exact: ler01].
have H3K : 0 <= 3 * (2 ^ k.+1)%:R * eta.
  by apply: mulr_ge0; [apply: mulr_ge0; [exact: ler0n | exact: ler0n] | exact: ltW].
apply: Hrho; last exact: lexx.
exact: mulr_ge0.
Qed.
