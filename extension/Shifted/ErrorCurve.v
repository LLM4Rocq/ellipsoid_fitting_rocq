(* Continuity and left approximation of the frozen fitting-error curve.
   The inverse energy cutoff is continuous at every positive density.
   Taking the positive part preserves continuity at the fitting threshold,
   so a vanishing reserve fraction recovers the full limiting error. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences realfun.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import semicircle_law variational.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section left_approximation.
Context {F : realType}.

Lemma continuous_positive_left_above (g : F -> F) (a t : F) :
  0 < a -> {for a, continuous g} -> t < g a ->
  exists b : F, 0 < b /\ b < a /\ t < g b.
Proof.
move=> a0 gc ta.
have e0 : 0 < g a - t by rewrite subr_gt0.
have /cvgrPdist_lt /(_ _ e0) /(@nbhs_normP F F a)
  [delta delta0 hdelta] := gc.
pose h := Num.min (a / 2) (delta / 2).
have a20 : 0 < a / 2 by rewrite divr_gt0.
have d20 : 0 < delta / 2 by rewrite divr_gt0.
have h0 : 0 < h by rewrite /h lt_min a20 d20.
have ha : h <= a / 2 by rewrite /h ge_min lexx.
have hd : h <= delta / 2 by rewrite /h ge_min lexx orbT.
have b0 : 0 < a - h by lra.
have ba : a - h < a by lra.
have bd : `|a - (a - h)| < delta.
  have -> : a - (a - h) = h by ring.
  rewrite ger0_norm ?ltW //.
  by lra.
have hb := hdelta (a - h) bd.
move: hb; rewrite /ball_ /= => hb.
exists (a - h); split=> //; split=> //.
have hnorm := ler_norm (g a - g (a - h)).
by lra.
Qed.

Lemma continuous_weighted_positive_left (f : F -> F) (a t : F) :
  0 < a -> {for a, continuous f} -> t < f a ->
  exists b : F, 0 < b /\ b < a /\ t < (b / a) * f b.
Proof.
move=> a0 fc tf.
pose g b := (b / a) * f b.
have gc : {for a, continuous g}.
  rewrite /g.
  apply: continuousM; last exact: fc.
  apply: continuousM; first exact: cvg_id.
  exact: cst_continuous.
have ga : g a = f a by rewrite /g divff ?gt_eqF // mul1r.
apply: (continuous_positive_left_above a0 gc).
by rewrite ga.
Qed.

End left_approximation.


Lemma shifted_energy_positive (kappa w : RR) :
  1 < kappa -> w < Num.sqrt 2%:R ->
  0 < universality_energy kappa w.
Proof.
move=> k1 ws.
have h := universality_energy_lt kappa w (Num.sqrt 2%:R) k1 ws (lexx _).
by rewrite universality_energy_out in h.
Qed.

Lemma shifted_level_cutoff_energyK (kappa w : RR) :
  1 < kappa -> w < Num.sqrt 2%:R ->
  universality_level_cutoff (universality_energy kappa w) kappa = w.
Proof.
move=> k1 ws.
have E0 := shifted_energy_positive k1 ws.
have [_ _ uniq] := universality_level_cutoff_spec
  (universality_energy kappa w) kappa E0 k1.
symmetry; exact: uniq w ws erefl.
Qed.

Lemma shifted_level_cutoff_continuous (alpha kappa : RR) :
  0 < alpha -> 1 < kappa ->
  (fun a : RR => universality_level_cutoff a kappa) @ alpha -->
    universality_level_cutoff alpha kappa.
Proof.
move=> a0 k1.
have [ws Ew _] := universality_level_cutoff_spec alpha kappa a0 k1.
pose w := universality_level_cutoff alpha kappa.
have fK : {near w, cancel (universality_energy kappa)
    (fun a : RR => universality_level_cutoff a kappa)}.
  have nearws : \forall v \near w, v < Num.sqrt 2%:R.
    exact: (@cvgr_lt RR RR (nbhs w) (nbhs_filter w) id w cvg_id _ ws).
  apply: filterS nearws => v vs.
  exact: shifted_level_cutoff_energyK k1 vs.
have fct : {near w, continuous (universality_energy kappa)}.
  near=> v; exact: universality_energy_continuous.
have hg := near_can_continuous fK fct.
rewrite /w Ew in hg.
exact: nbhs_singleton hg.
Unshelve. all: by end_near.
Qed.

Lemma shifted_level_cutoff_epsilon (alpha kappa : RR) :
  0 < alpha -> 1 < kappa ->
  forall eps : RR, 0 < eps -> exists delta : RR,
    0 < delta /\ forall a : RR, `|a-alpha| < delta ->
      `|universality_level_cutoff a kappa -
        universality_level_cutoff alpha kappa| < eps.
Proof.
move=> a0 k1 eps eps0.
have hc := shifted_level_cutoff_continuous a0 k1.
move: hc => /(@cvgrPdistC_lt RR RR^o) /(_ eps eps0) hn.
move/(@nbhs_normP RR RR^o alpha): hn => [delta delta0 hdelta].
exists delta; split=> // a ha.
apply: hdelta; by rewrite /ball_ /= distrC.
Qed.

Lemma shifted_m_lipschitz (x y : R) :
  `|universality_m x-universality_m y| <= `|x-y|.
Proof.
case: (leP x y) => xy.
- have /andP[h0 h1] := upper_moment1_lipschitz threshold_law2 xy.
  rewrite -!universality_mE in h0 h1.
  rewrite (ger0_norm h0) [`|x-y|]distrC ger0_norm ?subr_ge0 //.
- have /andP[h0 h1] := upper_moment1_lipschitz threshold_law2 (ltW xy).
  rewrite -!universality_mE in h0 h1.
  rewrite [`|universality_m x-universality_m y|]distrC
    (ger0_norm h0) ger0_norm ?subr_ge0 // ltW //.
Qed.

Lemma shifted_m_continuous : continuous (universality_m : RR -> RR).
Proof.
move=> x; apply/(@cvgrPdist_lt RR RR^o) => eps eps0.
apply/(@nbhs_normP RR RR^o x); exists eps => // y hy.
exact: le_lt_trans (shifted_m_lipschitz _ _) hy.
Qed.

Lemma shifted_e_star_ge0 (alpha kappa : R) :
  0 < alpha -> 0 <= universality_e_star alpha kappa.
Proof.
move=> alpha0; rewrite universality_e_starE.
apply: mulr_ge0; last exact: sqr_ge0.
by rewrite divr_ge0 ?ler0n ?ltW.
Qed.

Lemma shifted_e_star_eq0_iff (alpha kappa : R) :
  0 < alpha -> 1 < kappa ->
  (universality_e_star alpha kappa = 0 <-> alpha <= universality_alpha_star kappa).
Proof.
move=> alpha0 kappa1.
have e0 := shifted_e_star_ge0 kappa alpha0.
have ep := universality_e_star_gt0 alpha kappa alpha0 kappa1.
split.
- move=> ez; move: ep; rewrite ez ltxx => ep.
  by rewrite leNgt -ep.
- move=> ha; apply/eqP; by rewrite eq_le e0 andbT leNgt ep ltNge ha.
Qed.

Theorem shifted_e_star_continuous (alpha kappa : RR) :
  0 < alpha -> 1 < kappa ->
  (fun a : RR => universality_e_star a kappa) @ alpha -->
    universality_e_star alpha kappa.
Proof.
move=> alpha0 kappa1.
have an : alpha != 0 by rewrite gt_eqF.
have hw := shifted_level_cutoff_continuous alpha0 kappa1.
have hm : (fun a : RR => universality_m (universality_level_cutoff a kappa))
    @ alpha --> universality_m (universality_level_cutoff alpha kappa).
  apply: continuous_cvg hw.
  exact: shifted_m_continuous.
have hz : (fun a : RR => cone_shift kappa *
    universality_m (universality_level_cutoff a kappa) -
    universality_level_cutoff a kappa) @ alpha -->
    cone_shift kappa * universality_m (universality_level_cutoff alpha kappa)
      - universality_level_cutoff alpha kappa.
  apply: (@cvgB RR RR^o RR (nbhs alpha) (nbhs_filter alpha)); last exact: hw.
  apply: cvgM; [exact: cvg_cst | exact: hm].
have hp : (fun a : RR => Num.max (cone_shift kappa *
    universality_m (universality_level_cutoff a kappa) -
    universality_level_cutoff a kappa) 0) @ alpha -->
    Num.max (cone_shift kappa * universality_m (universality_level_cutoff alpha kappa)
      - universality_level_cutoff alpha kappa) 0.
  apply: (@continuous_max RR RR^o
    (fun a : RR => cone_shift kappa * universality_m (universality_level_cutoff a kappa)
      - universality_level_cutoff a kappa) (fun _ : RR => 0) alpha);
    [exact: hz | exact: cvg_cst].
have hs : (fun a : RR => Num.max (cone_shift kappa *
    universality_m (universality_level_cutoff a kappa) -
    universality_level_cutoff a kappa) 0 ^+2) @ alpha -->
    Num.max (cone_shift kappa * universality_m (universality_level_cutoff alpha kappa)
      - universality_level_cutoff alpha kappa) 0 ^+2.
  rewrite !expr2.
  apply: cvgM; exact: hp.
have -> : (fun a : RR => universality_e_star a kappa) =
    (fun a : RR => 2%:R/a * Num.max (cone_shift kappa *
      universality_m (universality_level_cutoff a kappa) -
      universality_level_cutoff a kappa) 0 ^+2).
  by apply/funext=>a; rewrite universality_e_starE.
rewrite universality_e_starE.
apply: cvgM; last exact: hs.
apply: cvgM; first exact: cvg_cst.
apply: cvgV; [exact: an | exact: cvg_id].
Qed.

Lemma shifted_e_star_epsilon (alpha kappa : RR) :
  0 < alpha -> 1 < kappa ->
  forall eps : RR, 0 < eps -> exists delta : RR,
    0 < delta /\ forall a : RR, `|a-alpha| < delta ->
      `|universality_e_star a kappa-universality_e_star alpha kappa| < eps.
Proof.
move=> alpha0 kappa1 eps eps0.
have hc := shifted_e_star_continuous alpha0 kappa1.
move: hc => /(@cvgrPdistC_lt RR RR^o) /(_ eps eps0) hn.
move/(@nbhs_normP RR RR^o alpha): hn => [delta delta0 hdelta].
exists delta; split=> // a ha.
apply: hdelta; by rewrite /ball_ /= distrC.
Qed.

Theorem shifted_e_star_left_approx (alpha kappa t : RR) :
  0 < alpha -> 1 < kappa -> t < universality_e_star alpha kappa ->
  exists beta : RR, 0 < beta /\ beta < alpha /\
    t < (beta/alpha)*universality_e_star beta kappa.
Proof.
move=> alpha0 kappa1 tE.
exact: continuous_weighted_positive_left alpha0
  (shifted_e_star_continuous alpha0 kappa1) tE.
Qed.
