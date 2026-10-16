(* Complement dimensions for a vanishing coordinate fraction.
   If h(d)/d tends to zero, p(d)=d-h(d) tends to infinity and preserves
   quadratic sample density. The combined density and head-fraction
   statistic is the scalar input to family_eventually_reindex. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences realfun exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.analysis Require Import family_reindexing.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Shifted Require Import ReserveDensity.
From EllipsoidUniversality.Sat Require Import SparseLimit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section scalar_limits.
Context {F : realType}.

Lemma sparse_ratio_scale (a b d : F) :
  d != 0 -> a/b = (a/d)/(b/d).
Proof.
move=> dn.
by rewrite [(b/d)^-1]invfM invrK mulrACA mulVf // mulr1.
Qed.

Lemma sparse_square_limit (u : nat -> F) (a : F) :
  family_sequence_limit u a ->
  family_sequence_limit (fun d => u d ^+2) (a^+2).
Proof.
move=> hu; apply/reserve_scalar_tends_cvg; rewrite !expr2.
apply: cvgM; apply/reserve_scalar_tends_cvg; exact: hu.
Qed.

Lemma sparse_error_stat_limit (u v : nat -> F) (a : F) :
  (forall d, 0 <= v d) ->
  (family_sequence_limit (fun d => `|u d-a|+v d) 0 <->
    family_sequence_limit u a /\ family_sequence_limit v 0).
Proof.
move=> v0; split.
- move=> h; split=> eps eps0; have [D hD] := h eps eps0;
    exists D => d dD; have hd := hD d dD;
    rewrite subr0 ger0_norm ?addr_ge0 ?normr_ge0 // in hd.
  - apply: le_lt_trans _ hd.
    by rewrite lerDl.
  - rewrite subr0 ger0_norm //.
    apply: le_lt_trans _ hd.
    by rewrite lerDr normr_ge0.
- move=> [hu hv] eps eps0.
  have e20 : 0 < eps/2 by rewrite divr_gt0.
  have [Du hDu] := hu _ e20.
  have [Dv hDv] := hv _ e20.
  exists (maxn Du Dv) => d; rewrite geq_max => /andP[du dv].
  have h1 := hDu d du; have h2 := hDv d dv.
  rewrite subr0 ger0_norm // in h2.
  rewrite subr0 ger0_norm ?addr_ge0 ?normr_ge0 //.
  have := ltrD h1 h2.
  by have -> : eps/2+eps/2=eps by field.
Qed.

End scalar_limits.

Lemma sparse_combined_stat_decompose (n h p : nat -> nat) (alpha : RR) :
  (family_sequence_limit
      (fun d => `|(n d)%:R/(p d)%:R^+2-alpha|+(h d)%:R/(p d)%:R : RR) 0 <->
    family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha /\
    family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0).
Proof.
apply: sparse_error_stat_limit => d.
by rewrite divr_ge0 ?ler0n.
Qed.

Lemma sparse_relative_head_limit (h p : nat -> nat) :
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  family_sequence_limit (fun d => (p d)%:R/d%:R : RR) 1 ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0.
Proof.
move=> hh hp.
have hq := reserve_scalar_tends_div (oner_neq0 RR) hh hp.
rewrite divr1 in hq.
apply: (reserve_scalar_tends_eventually_eq _ hq).
exists 1%N => d d1.
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite -(sparse_ratio_scale _ _ dn).
Qed.

Lemma sparse_relative_density_limit (n p : nat -> nat) (alpha : RR) :
  universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (p d)%:R/d%:R : RR) 1 ->
  family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha.
Proof.
move=> hn hp.
have hden := sparse_square_limit hp.
rewrite expr1n in hden.
have hq := reserve_scalar_tends_div (oner_neq0 RR)
  (reserve_density_scalar_limit hn) hden.
rewrite divr1 in hq.
apply: (reserve_scalar_tends_eventually_eq _ hq).
exists 1%N => d d1.
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite exprMn exprVn.
by rewrite -(reserve_density_ratio_scale _ _ dn).
Qed.

Lemma sparse_complement_ratio_limit (h : nat -> nat) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  family_sequence_limit (fun d => (d-h d)%:R/d%:R : RR) 1.
Proof.
move=> hb hs eps eps0.
have [D hD] := hs eps eps0.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have dn : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
have he : (d-h d)%:R/d%:R - 1 = - ((h d)%:R/d%:R) :> RR.
  by rewrite natrB ?hb // mulrBl divff //; ring.
rewrite he normrN.
by have := hD d dD; rewrite subr0.
Qed.

Lemma sparse_complement_cofinal (h : nat -> nat) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  family_cofinal (fun d => (d-h d)%N).
Proof.
move=> hb hs Q.
have half0 : 0 < (1/2 : RR) by rewrite divr_gt0.
have [D hD] := sparse_complement_ratio_limit hb hs half0.
exists (maxn D (maxn 1 (2*Q))) => d.
rewrite !geq_max => /andP[dD /andP[d1 dQ]].
have d0 : (0 : RR) < d%:R by rewrite ltr0n.
have near1 := hD d dD.
have rel : 1/2 < (d-h d)%:R/d%:R :> RR.
  move: near1; rewrite ltr_norml => /andP[lo _].
  have he : - (1/2 : RR) + 1 = 1/2 by field.
  by move: lo; rewrite ltrBrDr he.
rewrite ltr_pdivlMr // in rel.
have dQR : (2*Q)%:R <= d%:R :> RR by rewrite ler_nat.
rewrite natrM in dQR.
rewrite -(ler_nat RR).
have hmul := ler_wpM2l (ltW half0) dQR.
have hh : (1/2 : RR)*2 = 1 by field.
rewrite mulrA hh !mul1r in hmul.
rewrite !mul1r in rel.
exact: le_trans hmul (ltW rel).
Qed.

Lemma sparse_complement_eventually_pos (h : nat -> nat) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  exists D : nat, forall d, (D <= d)%N -> (0 < d-h d)%N.
Proof.
move=> hb hs.
exact: sparse_complement_cofinal hb hs 1%N.
Qed.

Theorem sparse_head_complement_limit (h : nat -> nat) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  family_sequence_limit (fun d => (h d)%:R/(d-h d)%:R : RR) 0.
Proof.
move=> hb hs.
exact: sparse_relative_head_limit hs (sparse_complement_ratio_limit hb hs).
Qed.

Theorem sparse_complement_density_limit (n h : nat -> nat) (alpha : RR) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (n d)%:R/(d-h d)%:R^+2 : RR) alpha.
Proof.
move=> hb hs hn.
exact: sparse_relative_density_limit hn (sparse_complement_ratio_limit hb hs).
Qed.

Theorem sparse_combined_stat_limit (n h : nat -> nat) (alpha : RR) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  universality_density_tends_to n alpha ->
  family_sequence_limit
    (fun d => `|(n d)%:R/(d-h d)%:R^+2-alpha|+(h d)%:R/(d-h d)%:R : RR) 0.
Proof.
move=> hb hs hn.
apply: (sparse_combined_stat_decompose n h (fun d => (d-h d)%N) alpha).2.
split.
- exact: sparse_complement_density_limit hb hs hn.
- exact: sparse_head_complement_limit hb hs.
Qed.
Lemma sparse_log_sqrt_limit (a : nat) :
  family_sequence_limit
    (fun q => ln (q%:R : RR) ^+ a / Num.sqrt q%:R) 0.
Proof.
move=> eps eps0.
have c0 : (0 : RR) < 2 / eps by rewrite divr_gt0.
have [D hD] := ln_pow_le_sqrt (2 / eps) a c0.
exists (maxn 1 D) => q.
rewrite geq_max => /andP[q1 qD].
have qR1 : (1 : RR) <= q%:R by rewrite -[1]/(1%:R) ler_nat.
have qR0 : (0 : RR) < q%:R by rewrite ltr0n.
have sq0 : (0 : RR) < Num.sqrt q%:R by rewrite sqrtr_gt0.
have l0 : (0 : RR) <= ln (q%:R : RR) := ln_ge0 qR1.
have pow0 : (0 : RR) <= ln (q%:R : RR) ^+ a by rewrite exprn_ge0.
have h := hD q qD.
have hh : ln (q%:R : RR) ^+ a <= Num.sqrt q%:R / (2 / eps).
  by rewrite ler_pdivlMr // mulrC.
have hb : ln (q%:R : RR) ^+ a / Num.sqrt q%:R <= eps / 2.
  rewrite ler_pdivrMr //.
  by move: hh; rewrite invf_div mulrC.
have ratio0 : (0 : RR) <= ln (q%:R : RR) ^+ a / Num.sqrt q%:R.
  exact: divr_ge0 pow0 (ltW sq0).
rewrite subr0 (ger0_norm ratio0).
apply: le_lt_trans hb _.
by clear -eps0; lra.
Qed.

Lemma sparse_log_sqrt_cofinal (p : nat -> nat) :
  family_cofinal p -> forall a : nat,
  family_sequence_limit
    (fun d => ln ((p d)%:R : RR) ^+ a / Num.sqrt (p d)%:R) 0.
Proof.
move=> hp a eps eps0.
have [Q hQ] := sparse_log_sqrt_limit a eps0.
have [D hD] := hp Q.
exists D => d dD; exact: hQ (p d) (hD d dD).
Qed.


Theorem sparse_log_power_limit (h : nat -> nat) (a : nat) :
  (forall d, (h d <= d)%N) ->
  family_sequence_limit (fun d => (h d)%:R/d%:R : RR) 0 ->
  family_sequence_limit
    (fun d => ln ((d-h d)%:R : RR)^+a/Num.sqrt (d-h d)%:R) 0.
Proof.
move=> hb hs.
exact: sparse_log_sqrt_cofinal (sparse_complement_cofinal hb hs) a.
Qed.
