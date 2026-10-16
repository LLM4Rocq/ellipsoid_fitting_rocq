(* Density coefficients for splitting a sample into main and reserve blocks.
   The explicit epsilon limits can be passed directly to cvg_prob_seq.
   Scalar identities are stated over an arbitrary real type; the sample
   densities use the existing frozen definition at Stdlib's real numbers. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences realfun.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Sat Require Import ApproximateFit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section reserve_density_scalars.
Context {F : realType}.

Lemma reserve_density_sqrt_product (x n : F) :
  0 <= x -> 0 <= n ->
  Num.sqrt (x / n) * Num.sqrt x = x / Num.sqrt n.
Proof.
by move=> x0 n0; rewrite sqrtrM // sqrtrV // mulrAC -expr2 sqr_sqrtr.
Qed.

Lemma reserve_density_ratio_scale (a b d : F) :
  d != 0 -> a / b = (a / d ^+ 2) / (b / d ^+ 2).
Proof.
move=> dn.
by rewrite [(b / d ^+ 2)^-1]invfM invrK mulrACA mulVf ?expf_neq0 // mulr1.
Qed.

Lemma reserve_density_sqrt_ratio (d n : F) :
  0 <= d -> d / Num.sqrt n = 1 / Num.sqrt (n / d ^+ 2).
Proof.
move=> d0.
rewrite [n / d ^+ 2]mulrC sqrtrM ?invr_ge0 ?sqr_ge0 //.
by rewrite sqrtrV ?sqr_ge0 // sqrtr_sqr ger0_norm // invfM invrK mul1r mulrC.
Qed.

End reserve_density_scalars.

Section explicit_limits.
Context {R : realType}.

Definition reserve_scalar_tends (u : nat -> R) (a : R) : Prop :=
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    `|u d - a| < eps.

Lemma reserve_scalar_tends_cvg (u : nat -> R) (a : R) :
  reserve_scalar_tends u a <-> u @ \oo --> a.
Proof.
split.
- move=> hu; apply/cvgrPdistC_lt => eps eps0.
  have [D hD] := hu eps eps0.
  by exists D.
- move=> /cvgrPdistC_lt hu eps eps0.
  have [D _ hD] := hu eps eps0.
  by exists D.
Qed.

Lemma reserve_scalar_tends_div (u v : nat -> R) (a b : R) :
  b != 0 -> reserve_scalar_tends u a -> reserve_scalar_tends v b ->
  reserve_scalar_tends (fun d => u d / v d) (a/b).
Proof.
move=> b0 /reserve_scalar_tends_cvg hu /reserve_scalar_tends_cvg hv.
apply/reserve_scalar_tends_cvg.
exact: cvgM hu (cvgV b0 hv).
Qed.

Lemma reserve_scalar_tends_one_div_sqrt (v : nat -> R) (b : R) :
  0 < b -> reserve_scalar_tends v b ->
  reserve_scalar_tends (fun d => 1 / Num.sqrt (v d)) (1 / Num.sqrt b).
Proof.
move=> b0 /reserve_scalar_tends_cvg hv.
have hs : (fun d => Num.sqrt (v d)) @ \oo --> Num.sqrt b.
  apply: continuous_cvg hv.
  exact: sqrt_continuous.
have sb0 : Num.sqrt b != 0 by rewrite gt_eqF // sqrtr_gt0.
apply/reserve_scalar_tends_cvg; apply: cvgM; first exact: cvg_cst.
exact: cvgV sb0 hs.
Qed.

Lemma reserve_scalar_tends_eventually_eq (u v : nat -> R) (a : R) :
  (exists D : nat, forall d, (D <= d)%N -> u d = v d) ->
  reserve_scalar_tends u a -> reserve_scalar_tends v a.
Proof.
move=> [D hD] hu eps eps0.
have [N hN] := hu eps eps0.
exists (maxn D N) => d; rewrite geq_max => /andP[dD dN].
by rewrite -(hD d dD); exact: hN.
Qed.

End explicit_limits.

Lemma reserve_density_sum (N k : nat -> nat) (beta gamma : R) :
  universality_density_tends_to N beta ->
  universality_density_tends_to k gamma ->
  universality_density_tends_to (fun d => (N d+k d)%N) (beta+gamma).
Proof.
move=> hN hk eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [DN hDN] := hN _ e20.
have [Dk hDk] := hk _ e20.
exists (maxn DN Dk) => d; rewrite geq_max => /andP[dN dk].
have h1 := hDN d dN; have h2 := hDk d dk.
rewrite /paper_main_density RdivE in h1 h2 *.
rewrite natrD !RdivE mulrDl.
have he : (N d)%:R / d%:R^+2 + (k d)%:R / d%:R^+2 - (beta+gamma) =
    ((N d)%:R/d%:R^+2-beta)+((k d)%:R/d%:R^+2-gamma) :> RR by ring.
rewrite he.
apply: le_lt_trans (ler_normD _ _) _.
have := ltrD h1 h2.
by have -> : eps/2+eps/2 = eps by field.
Qed.

Lemma reserve_density_eventually_pos (N k : nat -> nat) (beta gamma : R) :
  0 < beta -> 0 < gamma ->
  universality_density_tends_to N beta ->
  universality_density_tends_to k gamma ->
  exists D : nat, forall d, (D <= d)%N ->
    [/\ (0 < d)%N, (0 < N d)%N, (0 < k d)%N & (0 < N d+k d)%N ].
Proof.
move=> beta0 gamma0 hN hk.
have [DN hDN] := af_ev_density N beta beta0 hN.
have [Dk hDk] := af_ev_density k gamma gamma0 hk.
exists (maxn DN Dk) => d; rewrite geq_max => /andP[dN dk].
have [d0 [Nlo _]] := hDN d dN.
have [_ [klo _]] := hDk d dk.
have dR0 : (0 : RR) < d%:R by rewrite ltr0n.
have d20 : (0 : RR) < d%:R^+2 by rewrite exprn_gt0.
have b20 : 0 < beta/2 by rewrite divr_gt0.
have g20 : 0 < gamma/2 by rewrite divr_gt0.
have NR0 := lt_le_trans (mulr_gt0 b20 d20) Nlo.
have kR0 := lt_le_trans (mulr_gt0 g20 d20) klo.
have N0 : (0 < N d)%N by move: NR0; rewrite ltr0n.
have k0 : (0 < k d)%N by move: kR0; rewrite ltr0n.
split=> //.
exact: leq_trans N0 (leq_addr _ _).
Qed.

Lemma reserve_density_scalar_limit (N : nat -> nat) (beta : R) :
  universality_density_tends_to N beta ->
  reserve_scalar_tends (fun d => (N d)%:R/d%:R^+2 : RR) beta.
Proof.
move=> h eps eps0; have [D hD] := h eps eps0.
exists D => d dD.
by have := hD d dD; rewrite /paper_main_density RdivE.
Qed.

Theorem reserve_main_fraction_limit (N k : nat -> nat) (beta gamma : R) :
  0 < beta -> 0 < gamma ->
  universality_density_tends_to N beta ->
  universality_density_tends_to k gamma ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    `|(N d)%:R/(N d+k d)%:R - beta/(beta+gamma)| < eps.
Proof.
move=> beta0 gamma0 hN hk.
have bg0 : 0 < beta+gamma := addr_gt0 beta0 gamma0.
have bgn : beta+gamma != 0 by rewrite gt_eqF.
have hsum := reserve_density_scalar_limit (reserve_density_sum hN hk).
have h := reserve_scalar_tends_div bgn
  (reserve_density_scalar_limit hN) hsum.
apply: (reserve_scalar_tends_eventually_eq _ h).
exists 1%N => d d1.
have dR0 : (0 : RR) < d%:R by rewrite ltr0n.
have dRn : (d%:R : RR) != 0 by rewrite gt_eqF.
by rewrite -(reserve_density_ratio_scale _ _ dRn).
Qed.

Theorem reserve_dimension_scale_limit (N k : nat -> nat) (beta gamma : R) :
  0 < beta -> 0 < gamma ->
  universality_density_tends_to N beta ->
  universality_density_tends_to k gamma ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    `|d%:R/Num.sqrt (N d+k d)%:R - 1/Num.sqrt (beta+gamma)| < eps.
Proof.
move=> beta0 gamma0 hN hk.
have bg0 : 0 < beta+gamma := addr_gt0 beta0 gamma0.
have hsum := reserve_density_scalar_limit (reserve_density_sum hN hk).
have h := reserve_scalar_tends_one_div_sqrt bg0 hsum.
move=> eps eps0; have [D hD] := h eps eps0.
exists D => d dD.
rewrite reserve_density_sqrt_ratio ?ler0n //.
exact: hD.
Qed.
