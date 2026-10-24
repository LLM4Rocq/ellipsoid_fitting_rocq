(* A deterministic split of every sample size into a main block and a
   reserve block. Rounding costs less than one row. The two limiting
   densities are fixed before the dimension tends to infinity. *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition split_main_count (rho : RR) (n : nat) : nat :=
  archimedean.Num.truncn (rho*n%:R).
Definition split_reserve_count (rho : RR) (n : nat) : nat :=
  n-split_main_count rho n.

Lemma split_main_le (rho : RR) n :
  0 <= rho -> rho <= 1 -> (split_main_count rho n <= n)%N.
Proof.
move=> rho0 rho1; rewrite -(ler_nat RR) /split_main_count.
apply: le_trans (_ : rho*n%:R <= n%:R).
- by rewrite archimedean.Num.Theory.truncn_le mulr_ge0 ?ler0n.
- by rewrite -[X in _ <= X]mul1r ler_wpM2r ?ler0n.
Qed.

Lemma split_count_sum (rho : RR) n : 0 <= rho -> rho <= 1 ->
  (split_main_count rho n + split_reserve_count rho n = n)%N.
Proof.
move=> rho0 rho1; rewrite /split_reserve_count addnC.
exact: subnK (split_main_le n rho0 rho1).
Qed.

Lemma split_main_rounding (rho : RR) n : 0 <= rho ->
  `|(split_main_count rho n)%:R-rho*n%:R| < 1.
Proof.
move=> rho0.
have rn0 : 0 <= rho*n%:R by rewrite mulr_ge0 ?ler0n.
have /andP[lo hi] := archimedean.Num.Theory.truncn_itv rn0.
rewrite -/(split_main_count rho n) in lo hi.
rewrite -addn1 natrD in hi.
rewrite distrC ger0_norm ?subr_ge0 //.
clear -hi; lra.
Qed.

Lemma split_inverse_square_small (x eps : RR) :
  1 <= x -> 0 < eps -> 2/eps < x -> 1/x^+2 < eps/2.
Proof.
move=> x1 eps0 hx.
have xp : 0 < x by lra.
have x2p : 0 < x^+2 by rewrite exprn_gt0.
rewrite ltr_pdivrMr //.
move: hx; rewrite ltr_pdivrMr // => hx.
nra.
Qed.

Lemma split_main_density (n : nat -> nat) (alpha rho : RR) :
  0 <= rho -> rho <= 1 -> universality_density_tends_to n alpha ->
  universality_density_tends_to (fun d => split_main_count rho (n d)) (rho*alpha).
Proof.
move=> rho0 rho1 hn eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [Dn hDn] := hn (eps/2) e20.
pose b := 2/eps.
exists (maxn 1 (maxn Dn (archimedean.Num.truncn b).+1)) => d.
rewrite !geq_max => /andP[d1 /andP[dN db]].
have dR1 : (1 : RR) <= d%:R by rewrite -[1]/(1%:R) ler_nat.
have dR0 : (0 : RR) < d%:R by rewrite ltr0n.
have d2p : (0 : RR) < d%:R^+2 by rewrite exprn_gt0.
have bd : b < d%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have invsmall : (1 : RR)/d%:R^+2 < eps/2.
  exact: split_inverse_square_small dR1 eps0 bd.
have h := hDn d dN.
rewrite /paper_main_density RdivE in h *.
have round := split_main_rounding (n d) rho0.
have he : (split_main_count rho (n d))%:R/d%:R^+2-rho*alpha =
  ((split_main_count rho (n d))%:R-rho*(n d)%:R)/d%:R^+2 +
  rho*((n d)%:R/d%:R^+2-alpha) by ring.
rewrite he; apply: le_lt_trans (ler_normD _ _) _.
rewrite normrM normfV (ger0_norm (ltW d2p))
  [X in _ + X < _]normrM (ger0_norm rho0).
have hround : `|(split_main_count rho (n d))%:R-rho*(n d)%:R| / d%:R^+2 < eps/2.
  apply: lt_trans invsmall.
  by rewrite ltr_pM2r ?invr_gt0.
have hmain : rho*`|(n d)%:R/d%:R^+2-alpha| < eps/2.
  apply: le_lt_trans (_ : _ <= `|(n d)%:R/d%:R^+2-alpha|) h.
  by rewrite -[X in _ <= X]mul1r ler_wpM2r ?normr_ge0.
have hh := ltrD hround hmain.
have ee : eps/2+eps/2 = eps by field.
by rewrite ee in hh.
Qed.

Lemma split_reserve_density (n : nat -> nat) (alpha rho : RR) :
  0 <= rho -> rho <= 1 -> universality_density_tends_to n alpha ->
  universality_density_tends_to (fun d => split_reserve_count rho (n d))
    (alpha-rho*alpha).
Proof.
move=> rho0 rho1 hn eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [D1 h1] := hn (eps/2) e20.
have [D2 h2] := split_main_density rho0 rho1 hn e20.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have hN := h1 d d1; have hM := h2 d d2.
rewrite /paper_main_density RdivE in hN hM *.
rewrite /split_reserve_count natrB ?split_main_le //.
have he : ((n d)%:R-(split_main_count rho (n d))%:R)/d%:R^+2-
    (alpha-rho*alpha) = ((n d)%:R/d%:R^+2-alpha)-
    ((split_main_count rho (n d))%:R/d%:R^+2-rho*alpha) :> RR by ring.
rewrite he; apply: le_lt_trans (ler_normB _ _) _.
have hh := ltrD hN hM.
have ee : eps/2+eps/2 = eps by field.
by rewrite ee in hh.
Qed.

Theorem sample_split_density (n : nat -> nat) (alpha beta : RR) :
  0 < beta -> beta < alpha -> universality_density_tends_to n alpha ->
  exists N k : nat -> nat,
    (forall d, (N d+k d = n d)%N) /\
    universality_density_tends_to N beta /\
    universality_density_tends_to k (alpha-beta).
Proof.
move=> beta0 ba hn.
have alpha0 : 0 < alpha := lt_trans beta0 ba.
have an : alpha != 0 by rewrite gt_eqF.
have rho0 : 0 <= beta/alpha by rewrite divr_ge0 ?ltW.
have rho1 : beta/alpha <= 1 by rewrite ler_pdivrMr // mul1r ltW.
exists (fun d => split_main_count (beta/alpha) (n d)),
  (fun d => split_reserve_count (beta/alpha) (n d)); split.
- by move=> d; exact: split_count_sum rho0 rho1.
- have hm := split_main_density rho0 rho1 hn.
  have hk := split_reserve_density rho0 rho1 hn.
  have eqb : beta/alpha*alpha = beta by field.
  change (universality_density_tends_to
    (fun d => split_main_count (beta/alpha) (n d)) (beta/alpha*alpha)) in hm.
  change (universality_density_tends_to
    (fun d => split_reserve_count (beta/alpha) (n d)) (alpha-beta/alpha*alpha)) in hk.
  split.
  - exact (eq_rect _ (fun a : RR => universality_density_tends_to
      (fun d => split_main_count (beta/alpha) (n d)) a) hm _ eqb).
  - exact (eq_rect _ (fun a : RR => universality_density_tends_to
      (fun d => split_reserve_count (beta/alpha) (n d)) (alpha-a)) hk _ eqb).
Qed.
