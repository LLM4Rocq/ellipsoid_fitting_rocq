(* The threshold alpha*(kappa) and the cutoffs of Koehler and Sohn (arXiv
   2608.27372, lines 343-404 and section 5.3, lines 5115-5400 of
   arxiv_v1.tex), over the frozen definitions of UniversalityDefinitions.

   The semicircle law nu of density sqrt (2 - x^2)/pi is threshold_law, that
   is semicircle_prob (sqrt 2) of the library (probability/semicircle_law.v),
   and the functions m, s and E_kappa of the frozen definitions are the upper
   partial moments and the energy of the library's scalar variational problem
   (probability/variational.v) at c = c_kappa = cone_shift kappa =
   (kappa - 3)/2. The paper's chi_kappa(z) is upper_value threshold_law
   c_kappa z: it is nondecreasing in z, and strictly increasing where it is
   positive (upper_value_nondecr, upper_value_incr). This file transports the
   library's results to the frozen definitions and adds what is specific to
   nu. The results hold for kappa > 1, and for alpha > 0 where alpha
   appears.

   The bridge:
   - threshold_densityE, threshold_integralE: the frozen density is
     semicircle_pdf (sqrt 2), and universality_semicircle_integral f is the
     integral of f against threshold_law for nu-integrable f;
     threshold_semicircle_integrable: continuous functions are
     universality_semicircle_integrable.
   - universality_mE, universality_sE, universality_energyE,
     universality_cutoffE, universality_alpha_starE: m, s, E_kappa,
     omega_kappa and alpha*(kappa) are upper_moment threshold_law 1 and 2,
     upper_energy threshold_law c_kappa, upper_cutoff threshold_law c_kappa
     0 and upper_value threshold_law c_kappa 0.

   The semicircle facts (lines 5281-5283 and 5384-5391):
   - universality_semicircle_mass, universality_semicircle_second: nu has
     mass one and int x^2 dnu = 1/2; universality_m_sym,
     universality_s_sym: m(-w) = m(w) + w and s(-w) + s(w) = 1/2 + w^2.
   - universality_m_gt0: m(w) > 0 for w < sqrt 2; universality_m_out,
     universality_s_out: m(w) = s(w) = 0 for w >= sqrt 2;
     universality_m_left, universality_s_left, universality_energy_left: for
     w <= -sqrt 2, m(w) = -w, s(w) = 1/2 + w^2 and
     E_kappa(w) = (kappa - 1)/2 w^2 + 1/2.

   The cutoffs (lines 373-376 and 401-404, Proposition 5.10 (i)):
   - universality_cutoff_spec: omega_kappa lies in [-sqrt 2, sqrt 2],
     solves w = c_kappa m(w), and is the only real number that does;
     universality_cutoff_lt: omega_kappa < sqrt 2.
   - universality_energy_lt: E_kappa is strictly decreasing on
     ]-oo, sqrt 2]; universality_energy_continuous;
     universality_energy_out: E_kappa(sqrt 2) = 0.
   - universality_level_cutoff_spec: omega_{alpha,kappa} < sqrt 2 solves
     E_kappa(w) = alpha, and is the only w < sqrt 2 that does.
   - universality_level_value: with z_{alpha,kappa} =
     c_kappa m(omega_{alpha,kappa}) - omega_{alpha,kappa},
     chi_kappa(z_{alpha,kappa}) = alpha; universality_level_shift_gt0:
     z_{alpha,kappa} > 0 if and only if alpha > alpha*(kappa);
     universality_e_starE, universality_e_star_gt0 (line 188):
     e*(alpha, kappa) = (2/alpha) ((z_{alpha,kappa})_+)^2, which is
     positive if and only if alpha > alpha*(kappa).

   The threshold:
   - universality_alpha_star3 (line 377): alpha*(3) = 1/4, the threshold
     of Corollary 1.3.
   - universality_alpha_star_gt0, universality_alpha_star_lt, and
     universality_alpha_star_dual (Proposition 5.10 (iii)):
     0 < alpha*(kappa) < 1/2 and alpha*(kappa) + alpha*(kappa^vee) = 1/2,
     with kappa^vee = kappa_dual kappa.
   - universality_alpha_star_variationalE (Proposition 5.10 (ii)):
     universality_alpha_star_variational kappa =
     universality_alpha_star kappa. A frozen admissible f is only known to
     make f times the density integrable; its restriction to
     ]-sqrt 2, sqrt 2[ (semicircle_restrict) is measurable and has the same
     integrals, and the ratio without positive part is bounded because nu
     is symmetric (upper_variational_sym_le). The bound is attained at
     (x - omega_kappa)_+ / m(omega_kappa).
   - Lemma 5.9, the scalar part: universality_cutoff_dual,
     universality_value_dual: with z^vee = -2 z/(kappa - 1), the cutoff of
     (kappa^vee, z^vee) is minus that of (kappa, z), and
     chi_kappa(z) + chi_{kappa^vee}(z^vee) = 1/2 + 2 z^2/(kappa - 1). The
     claim of Lemma 5.9 that -G_{d,kappa}(z) and G_{d,kappa^vee}(z^vee) have
     the same law is about the Gaussian matrices of section 5.2 and goes
     with them (stage 2, G8).

   Definitions:
     threshold_law == semicircle_prob (sqrt 2), the law nu (a notation) *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability normal_distribution.
From mathcomp Require Import sequences trigo realfun.
From GaussianAnalysis.probability Require Import semicircle_law variational.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* The law nu of the paper: the semicircle law of radius sqrt 2. *)
Notation threshold_law := (@semicircle_prob R (Num.sqrt 2%:R)).

Section threshold_bridge.

Let s2 : Num.sqrt 2%:R != 0 :> R.
Proof. by rewrite gt_eqF// sqrtr_gt0 ltr0n. Qed.

Let s2sqr : Num.sqrt 2%:R ^+ 2 = 2%:R :> R.
Proof. by rewrite sqr_sqrtr// ler0n. Qed.

Lemma threshold_densityE (x : R) :
  universality_semicircle_density x = semicircle_pdf (Num.sqrt 2%:R) x.
Proof.
rewrite semicircle_pdfE// s2sqr /universality_semicircle_density RdivE.
have pi0 : pi != 0 :> R by rewrite gt_eqF// pi_gt0.
by move: (pi : R) pi0 => p p0; field.
Qed.

Lemma threshold_integralE (f : R -> R) :
  threshold_law.-integrable [set: R] (EFin \o f) ->
  universality_semicircle_integral f = \int[threshold_law]_x f x.
Proof.
move=> fi; rewrite /universality_semicircle_integral /Rintegral.
rewrite integral_semicircle_prob//; congr fine.
by apply: eq_integral => x _; rewrite threshold_densityE /= EFinM.
Qed.

Lemma threshold_integrable_continuous (f : R -> R) : continuous f ->
  threshold_law.-integrable [set: R] (EFin \o f).
Proof. exact: integrable_semicircle_continuous. Qed.

Lemma continuous_upper_part (w : R) k :
  continuous (fun x : R => Num.max (x - w) 0 ^+ k).
Proof.
move=> x; apply: (@continuous_comp _ _ _ (fun y : R => Num.max (y - w) 0)
  (fun y => y ^+ k)); last exact: exprn_continuous.
apply: continuous_max; last exact: cvg_cst.
by apply: cvgB; [exact: cvg_id|exact: cvg_cst].
Qed.

Lemma universality_mE (w : R) :
  universality_m w = upper_moment threshold_law 1 w.
Proof.
rewrite /universality_m threshold_integralE.
  have := threshold_integrable_continuous _ (continuous_upper_part w 1).
  by apply: eq_integrable => // x _; rewrite /= expr1.
by apply: eq_Rintegral => x _; rewrite expr1.
Qed.

Lemma universality_sE (w : R) :
  universality_s w = upper_moment threshold_law 2 w.
Proof.
rewrite /universality_s threshold_integralE//.
exact: threshold_integrable_continuous _ (continuous_upper_part w 2).
Qed.

Lemma universality_energyE (kappa w : R) :
  universality_energy kappa w = upper_energy threshold_law (cone_shift kappa) w.
Proof. by rewrite /universality_energy universality_mE universality_sE. Qed.

Lemma universality_cutoffE (kappa : R) :
  universality_cutoff kappa = upper_cutoff threshold_law (cone_shift kappa) 0.
Proof.
rewrite /universality_cutoff /upper_cutoff; congr sup.
by apply/seteqP; split => w /=; rewrite addr0 universality_mE.
Qed.

Lemma universality_alpha_starE (kappa : R) :
  universality_alpha_star kappa =
  upper_value threshold_law (cone_shift kappa) 0.
Proof.
by rewrite /universality_alpha_star universality_cutoffE universality_energyE.
Qed.

End threshold_bridge.

Section threshold_semicircle.

Let s2 : Num.sqrt 2%:R != 0 :> R.
Proof. by rewrite gt_eqF// sqrtr_gt0 ltr0n. Qed.

Let s2sqr : Num.sqrt 2%:R ^+ 2 = 2%:R :> R.
Proof. by rewrite sqr_sqrtr// ler0n. Qed.

Lemma threshold_law2 : threshold_law.-integrable [set: R]
  (EFin \o (fun x : measurableTypeR R => (x : R) ^+ 2)).
Proof.
apply: (threshold_integrable_continuous (fun x => x ^+ 2)).
exact: exprn_continuous.
Qed.

Lemma threshold_law_sym (A : set (measurableTypeR R)) : measurable A ->
  threshold_law ((fun x => - x) @^-1` A) = threshold_law A.
Proof. exact: semicircle_prob_sym. Qed.

Lemma threshold_second : \int[threshold_law]_x ((x : R) ^+ 2) = 2%:R^-1.
Proof. by rewrite semicircle_moment2// s2sqr; field. Qed.

Lemma universality_semicircle_mass :
  universality_semicircle_integral (fun _ => 1) = 1.
Proof.
rewrite threshold_integralE ?Rintegral_prob_cst//.
exact: finite_measure_integrable_cst.
Qed.

Lemma universality_semicircle_second :
  universality_semicircle_integral (fun x => x ^+ 2) = 2%:R^-1.
Proof.
rewrite threshold_integralE; last exact: threshold_second.
apply: (threshold_integrable_continuous (fun x => x ^+ 2)).
exact: exprn_continuous.
Qed.

Lemma universality_m_sym (w : R) :
  universality_m (- w) = universality_m w + w.
Proof.
rewrite !universality_mE.
exact: (upper_moment1_sym threshold_law2 threshold_law_sym).
Qed.

Lemma universality_s_sym (w : R) :
  universality_s (- w) + universality_s w = 2%:R^-1 + w ^+ 2.
Proof.
rewrite !universality_sE (upper_moment2_sym threshold_law2 threshold_law_sym).
by rewrite threshold_second.
Qed.

Lemma universality_alpha_star3 : universality_alpha_star 3%:R = 4%:R^-1.
Proof.
rewrite universality_alpha_starE.
have c0 : cone_shift 3%:R = 0.
  by rewrite /cone_shift RdivE RminusE subrr mul0r.
rewrite c0 /upper_value.
have -> : upper_cutoff threshold_law 0 0 = 0.
  symmetry; apply: (upper_cutoff_unique threshold_law2 (ltrN10 _)).
  by rewrite addr0 mul0r.
rewrite /upper_energy mul0r addr0.
have := universality_s_sym 0%:R; rewrite mulr0n RoppE oppr0.
rewrite !universality_sE expr0n /= addr0.
by move: (upper_moment threshold_law 2 0) => S; lra.
Qed.

End threshold_semicircle.

Section threshold_support.

Let s2pos : 0 < Num.sqrt 2%:R :> R.
Proof. by rewrite sqrtr_gt0 ltr0n. Qed.

Let s2 : Num.sqrt 2%:R != 0 :> R.
Proof. by rewrite gt_eqF. Qed.

Let s2abs : `|Num.sqrt 2%:R| = Num.sqrt 2%:R :> R.
Proof. by rewrite ger0_norm// ltW. Qed.

Lemma threshold_support_eq (f g : R -> R) : continuous f -> continuous g ->
  {in `[- Num.sqrt 2%:R, Num.sqrt 2%:R], f =1 g} ->
  \int[threshold_law]_x f x = \int[threshold_law]_x g x.
Proof.
move=> cf cg fg.
rewrite (Rintegral_semicircle s2 (threshold_integrable_continuous _ cf)).
rewrite (Rintegral_semicircle s2 (threshold_integrable_continuous _ cg)) s2abs.
by apply: eq_Rintegral => x xI; rewrite fg.
Qed.

Lemma universality_m_out (w : R) : Num.sqrt 2%:R <= w -> universality_m w = 0.
Proof.
move=> sw; rewrite universality_mE /upper_moment.
have fg : {in `[- Num.sqrt 2%:R, Num.sqrt 2%:R],
    (fun x : R => Num.max (x - w) 0 ^+ 1) =1 (fun _ => 0)}.
  move=> x; rewrite inE /= in_itv /= => /andP[_ xs].
  rewrite expr1; apply/max_idPr; rewrite subr_le0; exact: le_trans xs sw.
rewrite (threshold_support_eq _ (fun=> 0) (continuous_upper_part w 1) _ fg).
  exact: cst_continuous.
exact: Rintegral_prob_cst.
Qed.

Lemma universality_s_out (w : R) : Num.sqrt 2%:R <= w -> universality_s w = 0.
Proof.
move=> sw; rewrite universality_sE /upper_moment.
have fg : {in `[- Num.sqrt 2%:R, Num.sqrt 2%:R],
    (fun x : R => Num.max (x - w) 0 ^+ 2) =1 (fun _ => 0)}.
  move=> x; rewrite inE /= in_itv /= => /andP[_ xs].
  have /max_idPr -> : x - w <= 0 by rewrite subr_le0; exact: le_trans xs sw.
  by rewrite expr0n.
rewrite (threshold_support_eq _ (fun=> 0) (continuous_upper_part w 2) _ fg).
  exact: cst_continuous.
exact: Rintegral_prob_cst.
Qed.

Lemma universality_m_left (w : R) : w <= - Num.sqrt 2%:R ->
  universality_m w = - w.
Proof.
move=> ws; have sw : Num.sqrt 2%:R <= - w by rewrite lerNr.
have := universality_m_sym (- w).
by rewrite !RoppE opprK (universality_m_out _ sw) add0r.
Qed.

Lemma universality_s_left (w : R) : w <= - Num.sqrt 2%:R ->
  universality_s w = 2%:R^-1 + w ^+ 2.
Proof.
move=> ws; have sw : Num.sqrt 2%:R <= - w by rewrite lerNr.
have := universality_s_sym (- w).
by rewrite !RoppE opprK sqrrN (universality_s_out _ sw) addr0.
Qed.

Lemma universality_m_gt0 (w : R) : w < Num.sqrt 2%:R -> 0 < universality_m w.
Proof.
move=> ws; rewrite universality_mE.
pose b := (w + Num.sqrt 2%:R) / 2%:R.
apply: (@upper_moment1_gt0 _ _ threshold_law2 _ b).
  by rewrite /b ltr_pdivlMr// mulrDr mulr1 ltrD2l.
apply: (semicircle_prob_gt0 s2); rewrite s2abs.
by rewrite /b ltr_pdivrMr// mulrDr mulr1 ltrD2r.
Qed.

End threshold_support.

Section threshold_cutoff.

Let s2pos : 0 < Num.sqrt 2%:R :> R.
Proof. by rewrite sqrtr_gt0 ltr0n. Qed.

Lemma universality_cutoff_spec (kappa : R) : 1 < kappa ->
  [/\ - Num.sqrt 2%:R <= universality_cutoff kappa <= Num.sqrt 2%:R,
    universality_cutoff kappa =
      (kappa - 3%:R) / 2%:R * universality_m (universality_cutoff kappa) &
    forall w : R, w = (kappa - 3%:R) / 2%:R * universality_m w ->
      w = universality_cutoff kappa].
Proof.
move=> k1; have c1 := cone_shift_gtN1 _ k1; rewrite -cone_shiftE.
have uniq w : w = cone_shift kappa * universality_m w ->
    w = universality_cutoff kappa.
  rewrite universality_mE universality_cutoffE => e.
  by apply: (upper_cutoff_unique threshold_law2 c1); rewrite addr0.
have E : universality_cutoff kappa =
    cone_shift kappa * universality_m (universality_cutoff kappa).
  rewrite universality_mE universality_cutoffE.
  by have := upper_cutoffE threshold_law2 0 c1; rewrite addr0.
split => //; move: E; set w := universality_cutoff kappa => E.
apply/andP; split; rewrite leNgt; apply/negP => ws.
  rewrite (universality_m_left _ (ltW ws)) in E.
  by have := s2pos; move: (cone_shift kappa) c1 E => c c1' E s0; nra.
rewrite (universality_m_out _ (ltW ws)) mulr0 in E.
by move: ws; rewrite E ltNge (ltW s2pos).
Qed.

Lemma universality_energy_left (kappa w : R) : w <= - Num.sqrt 2%:R ->
  universality_energy kappa w = (kappa - 1) / 2%:R * w ^+ 2 + 2%:R^-1.
Proof.
move=> ws; rewrite universality_energyE /upper_energy -universality_sE.
rewrite -universality_mE universality_s_left// universality_m_left//.
by rewrite cone_shiftE sqrrN; field.
Qed.

Lemma universality_energy_out (kappa : R) :
  universality_energy kappa (Num.sqrt 2%:R) = 0.
Proof.
rewrite universality_energyE /upper_energy -universality_sE -universality_mE.
by rewrite universality_s_out// universality_m_out// expr0n mulr0 addr0.
Qed.

Lemma universality_energy_lt (kappa w1 w2 : R) : 1 < kappa ->
  w1 < w2 -> w2 <= Num.sqrt 2%:R ->
  universality_energy kappa w2 < universality_energy kappa w1.
Proof.
move=> k1 w12 w2s; have c1 := cone_shift_gtN1 _ k1.
rewrite !universality_energyE.
pose v := (w1 + w2) / 2%:R.
have w1v : w1 < v by rewrite /v; lra.
have vw2 : v < w2 by rewrite /v; lra.
have mv : 0 < upper_moment threshold_law 1 v.
  rewrite -universality_mE; apply: universality_m_gt0.
  exact: lt_le_trans w2s.
apply: le_lt_trans (upper_energy_lt threshold_law2 c1 w1v mv).
have h := upper_energy_decr threshold_law2 c1 (ltW vw2).
have m0 := @upper_moment_ge0 _ threshold_law 1 w2.
have c0 : 0 <= Num.min 1 (1 + cone_shift kappa).
  by rewrite le_min ler01 addrC -lerBlDr sub0r ltW.
have d0 : 0 <= w2 - v by rewrite subr_ge0 ltW.
by rewrite -subr_ge0; apply: le_trans h; rewrite !mulr_ge0.
Qed.

Lemma universality_energy_continuous (kappa : R) :
  continuous (universality_energy kappa).
Proof.
have -> : universality_energy kappa =
    upper_energy threshold_law (cone_shift kappa).
  by apply/funext => w; rewrite universality_energyE.
exact: upper_energy_continuous threshold_law2 _.
Qed.

Lemma universality_level_cutoff_spec (alpha kappa : R) :
  0 < alpha -> 1 < kappa ->
  [/\ universality_level_cutoff alpha kappa < Num.sqrt 2%:R,
    universality_energy kappa (universality_level_cutoff alpha kappa) = alpha &
    forall w : R, w < Num.sqrt 2%:R -> universality_energy kappa w = alpha ->
      w = universality_level_cutoff alpha kappa].
Proof.
move=> a0 k1; pose t := 2%:R * alpha / (kappa - 1) + 1.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have t1 : 1 <= t by rewrite /t lerDr divr_ge0 ?mulr_ge0// ltW.
pose w0 := - Num.sqrt 2%:R - t.
have w0s : w0 <= - Num.sqrt 2%:R by rewrite /w0 lerBlDr lerDl; lra.
have Ew0 : alpha <= universality_energy kappa w0.
  rewrite universality_energy_left//.
  have tE : (kappa - 1) / 2%:R * t = alpha + (kappa - 1) / 2%:R.
    by rewrite /t; have := lt0r_neq0 k0; move: (kappa - 1) => k kn; field.
  have tw : t <= - w0 by rewrite /w0; have := s2pos; lra.
  have wt : t <= w0 ^+ 2 by rewrite -sqrrN; nra.
  have kk : 0 <= (kappa - 1) / 2%:R by rewrite divr_ge0 ?ltW.
  have h2 : 0 <= 2%:R^-1 :> R by rewrite invr_ge0.
  by nra.
have w0s2 : w0 <= Num.sqrt 2%:R by rewrite /w0; have := s2pos; lra.
have E0 := universality_energy_out kappa.
have mm : minr (universality_energy kappa w0)
    (universality_energy kappa (Num.sqrt 2%:R)) <= alpha <=
    maxr (universality_energy kappa w0)
    (universality_energy kappa (Num.sqrt 2%:R)).
  by rewrite E0 ge_min le_max Ew0 /= (ltW a0) orbT.
have [w wI Ew] := @IVT _ (universality_energy kappa) w0 (Num.sqrt 2%:R) alpha
  w0s2 (continuous_subspaceT (universality_energy_continuous kappa)) mm.
have ws : w < Num.sqrt 2%:R.
  move: wI; rewrite in_itv /= => /andP[_]; rewrite le_eqVlt => /orP[/eqP wE|//].
  by move: a0; rewrite -Ew [in X in X -> _]wE E0 ltxx.
have ub v : v < Num.sqrt 2%:R -> alpha <= universality_energy kappa v -> v <= w.
  move=> vs av; rewrite leNgt; apply/negP => wv.
  have := universality_energy_lt kappa w v k1 wv (ltW vs).
  by rewrite Ew ltNge av.
have L : universality_level_cutoff alpha kappa = w.
  apply/eqP; rewrite eq_le; apply/andP; split.
    apply: ge_sup; first by exists w; split; rewrite ?Ew.
    by move=> v [vs av]; exact: ub.
  apply: ub_le_sup; last by split; rewrite ?Ew.
  by exists w => v [vs av]; exact: ub.
rewrite L; split => // v vs Ev.
apply/eqP; rewrite eq_le ub ?Ev//= leNgt; apply/negP => vw.
by have := universality_energy_lt kappa v w k1 vw (ltW ws); rewrite Ev Ew ltxx.
Qed.

Lemma universality_cutoff_lt (kappa : R) : 1 < kappa ->
  universality_cutoff kappa < Num.sqrt 2%:R.
Proof.
move=> k1; have [/andP[_ ws] E _] := universality_cutoff_spec kappa k1.
rewrite lt_neqAle ws andbT; apply/negP => /eqP wE.
move: E; rewrite wE universality_m_out// mulr0 => s0.
by move: s2pos; rewrite s0 ltxx.
Qed.

Lemma universality_alpha_star_gt0 (kappa : R) : 1 < kappa ->
  0 < universality_alpha_star kappa.
Proof.
move=> k1; rewrite /universality_alpha_star universality_energyE.
apply: lt_le_trans (upper_energy_ge threshold_law2 _ _).
have c0 : 0 < 1 + cone_shift kappa by have := cone_shift_gtN1 _ k1; lra.
rewrite mulr_gt0// exprn_gt0// -universality_mE universality_m_gt0//.
exact: universality_cutoff_lt.
Qed.

Lemma universality_level_value (alpha kappa : R) : 0 < alpha -> 1 < kappa ->
  upper_value threshold_law (cone_shift kappa)
    (cone_shift kappa * universality_m (universality_level_cutoff alpha kappa)
     - universality_level_cutoff alpha kappa) = alpha.
Proof.
move=> a0 k1; have c1 := cone_shift_gtN1 _ k1.
have [_ Ew _] := universality_level_cutoff_spec alpha kappa a0 k1.
move: Ew; set w := universality_level_cutoff alpha kappa => Ew.
have e : w + (cone_shift kappa * universality_m w - w) =
    cone_shift kappa * upper_moment threshold_law 1 w.
  by rewrite addrC subrK universality_mE.
by rewrite /upper_value -(upper_cutoff_unique threshold_law2 c1 e)
  -universality_energyE.
Qed.

Lemma universality_level_shift_gt0 (alpha kappa : R) : 0 < alpha -> 1 < kappa ->
  (0 < cone_shift kappa * universality_m (universality_level_cutoff alpha kappa)
       - universality_level_cutoff alpha kappa) =
  (universality_alpha_star kappa < alpha).
Proof.
move=> a0 k1; have c1 := cone_shift_gtN1 _ k1.
have := universality_level_value alpha kappa a0 k1.
set z := _ - _ => Vz.
have V0 := universality_alpha_starE kappa.
have A0 := universality_alpha_star_gt0 kappa k1.
apply/idP/idP => h.
  rewrite -Vz V0; apply: (upper_value_incr threshold_law2 c1 h).
  by rewrite -V0.
rewrite ltNge; apply/negP => z0.
have := upper_value_nondecr threshold_law2 c1 z0.
by rewrite Vz -V0 leNgt h.
Qed.

Lemma universality_e_starE (alpha kappa : R) :
  universality_e_star alpha kappa =
  2%:R / alpha * Num.max (cone_shift kappa *
    universality_m (universality_level_cutoff alpha kappa)
    - universality_level_cutoff alpha kappa) 0 ^+ 2.
Proof.
rewrite /universality_e_star /universality_positive_part cone_shiftE.
by rewrite !RdivE RmultE RminusE.
Qed.

Lemma universality_e_star_gt0 (alpha kappa : R) : 0 < alpha -> 1 < kappa ->
  (0 < universality_e_star alpha kappa) =
  (universality_alpha_star kappa < alpha).
Proof.
move=> a0 k1; rewrite -universality_level_shift_gt0// universality_e_starE.
move: (_ - _) => z; rewrite pmulr_rgt0 ?divr_gt0//.
by case: (leP z 0) => z0; rewrite ?expr0n ?ltxx// exprn_gt0.
Qed.

End threshold_cutoff.

Section threshold_duality.

Lemma universality_cutoff_dual (kappa z : R) : 1 < kappa ->
  upper_cutoff threshold_law (cone_shift (kappa_dual kappa))
    (- 2%:R * z / (kappa - 1)) =
  - upper_cutoff threshold_law (cone_shift kappa) z.
Proof.
move=> k1; have c1 := cone_shift_gtN1 _ k1.
have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
have -> : - 2%:R * z / (kappa - 1) = - z / (1 + cone_shift kappa).
  by rewrite cone_shiftD1; field.
rewrite cone_shift_dual//.
exact: (upper_cutoff_dual threshold_law2 threshold_law_sym).
Qed.

Lemma universality_value_dual (kappa z : R) : 1 < kappa ->
  upper_value threshold_law (cone_shift kappa) z +
  upper_value threshold_law (cone_shift (kappa_dual kappa))
    (- 2%:R * z / (kappa - 1)) =
  2%:R^-1 + 2%:R * z ^+ 2 / (kappa - 1).
Proof.
move=> k1; have c1 := cone_shift_gtN1 _ k1.
have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
have -> : - 2%:R * z / (kappa - 1) = - z / (1 + cone_shift kappa).
  by rewrite cone_shiftD1; field.
rewrite cone_shift_dual//.
rewrite (upper_value_dual threshold_law2 threshold_law_sym _ c1).
rewrite [X in X + _ = _](_ : _ = 2%:R^-1); first exact: threshold_second.
by rewrite cone_shiftD1; field.
Qed.

Lemma universality_alpha_star_dual (kappa : R) : 1 < kappa ->
  universality_alpha_star kappa + universality_alpha_star (kappa_dual kappa) =
  2%:R^-1.
Proof.
move=> k1; rewrite !universality_alpha_starE.
have := universality_value_dual kappa 0 k1.
by rewrite mulr0 mul0r expr0n /= mulr0 mul0r addr0.
Qed.

Lemma universality_alpha_star_lt (kappa : R) : 1 < kappa ->
  0 < universality_alpha_star kappa < 2%:R^-1.
Proof.
move=> k1; rewrite universality_alpha_star_gt0//=.
rewrite -(universality_alpha_star_dual kappa k1) ltrDl.
by apply: universality_alpha_star_gt0; exact: kappa_dual_gt1.
Qed.

End threshold_duality.

Section threshold_variational.

Let s2 : Num.sqrt 2%:R != 0 :> R.
Proof. by rewrite gt_eqF// sqrtr_gt0 ltr0n. Qed.

Lemma threshold_semicircle_integrable (f : R -> R) : continuous f ->
  universality_semicircle_integrable f.
Proof.
move=> cf; have := integrable_semicircle_pdfM s2 cf.
by apply: eq_integrable => // x _; rewrite threshold_densityE.
Qed.

Lemma universality_alpha_star_variationalE (kappa : R) : 1 < kappa ->
  universality_alpha_star_variational kappa = universality_alpha_star kappa.
Proof.
move=> k1; have c1 := cone_shift_gtN1 _ k1.
have dE x : universality_semicircle_density x =
    semicircle_pdf (Num.sqrt 2%:R) x by exact: threshold_densityE.
rewrite /universality_alpha_star_variational -cone_shiftE.
have A0 := universality_alpha_star_gt0 kappa k1.
rewrite universality_alpha_starE in A0 *.
set V := upper_value _ _ _ in A0 *.
set S := [set r | _].
(* Every ratio of the frozen set is at most V: replace f by its
   restriction g to ]-sqrt 2, sqrt 2[, which is measurable and has the same
   integrals against nu, and bound the ratio of g without positive part. *)
have ub : ubound S V.
  move=> _ [f [f0 [fi [f2i [f1 ->]]]]].
  have fi' : lebesgue_measure.-integrable [set: R]
      (fun x => (f x * semicircle_pdf (Num.sqrt 2%:R) x)%:E).
    by move: fi; apply: eq_integrable => // x _; rewrite dE.
  have f2i' : lebesgue_measure.-integrable [set: R]
      (fun x => (f x ^+ 2 * semicircle_pdf (Num.sqrt 2%:R) x)%:E).
    by move: f2i; apply: eq_integrable => // x _; rewrite dE.
  have [g [mg gf g0f]] := semicircle_restrict s2 fi'.
  have g0 x : 0 <= g x by case: (g0f x) => ->.
  have g2f x : g x ^+ 2 * semicircle_pdf (Num.sqrt 2%:R) x =
      f x ^+ 2 * semicircle_pdf (Num.sqrt 2%:R) x.
    rewrite !expr2 -!mulrA gf; case: (g0f x) => gx; last by rewrite gx.
    by move: (gf x); rewrite gx !mul0r => <-; rewrite mulr0.
  have xgf x : x * g x * semicircle_pdf (Num.sqrt 2%:R) x =
      x * f x * semicircle_pdf (Num.sqrt 2%:R) x by rewrite -!mulrA gf.
  have gi := semicircle_integrable_eq mg gf fi'.
  have g2i := semicircle_integrable_eq (measurable_funX 2 mg) g2f f2i'.
  have xgi := @integrable_mul_sqr _ threshold_law (fun x => x) g
    (@measurable_id _ _ _) mg threshold_law2 g2i.
  have Eg : \int[threshold_law]_x g x = 1.
    rewrite (semicircle_integral_eq gi gf) -[RHS]f1.
    by rewrite /universality_semicircle_integral; apply: eq_Rintegral => x _;
      rewrite dE.
  have Eg2 : \int[threshold_law]_x (g x ^+ 2) =
      universality_semicircle_integral (fun x => f x ^+ 2).
    rewrite (semicircle_integral_eq g2i g2f) /universality_semicircle_integral.
    by apply: eq_Rintegral => x _; rewrite dE.
  have Exg : \int[threshold_law]_x (x * g x) =
      universality_semicircle_integral (fun x => x * f x).
    rewrite (semicircle_integral_eq xgi xgf) /universality_semicircle_integral.
    by apply: eq_Rintegral => x _; rewrite dE.
  have H := upper_variational_sym_le threshold_law2 threshold_law_sym c1 mg g0
    g2i.
  rewrite Eg expr1n mulr1 in H.
  have D : 0 < \int[threshold_law]_x (g x ^+ 2) + cone_shift kappa.
    have := Rintegral_sqr_le gi g2i; rewrite Eg expr1n => h.
    by have := c1; lra.
  by rewrite -Exg -Eg2 ler_pdivrMr.
(* V is attained at f0 = (x - omega_kappa)_+ / m(omega_kappa). *)
pose w := upper_cutoff threshold_law (cone_shift kappa) 0.
have ws : w < Num.sqrt 2%:R.
  by rewrite /w -universality_cutoffE; exact: universality_cutoff_lt.
pose M := upper_moment threshold_law 1 w.
have M0 : 0 < M by rewrite /M -universality_mE; exact: universality_m_gt0.
pose f0 (x : R) := Num.max (x - w) 0 / M.
have cf0 : continuous f0.
  move=> x; apply: cvgM; last exact: cvg_cst.
  exact: (continuous_upper_part w 1 x).
have cf02 : continuous (fun x => f0 x ^+ 2).
  move=> x; apply: (@continuous_comp _ _ _ f0 (fun y => y ^+ 2)).
    exact: cf0.
  exact: exprn_continuous.
have cxf0 : continuous (fun x : R => x * f0 x).
  by move=> x; apply: cvgM; [exact: cvg_id|exact: cf0].
have mE : \int[threshold_law]_x Num.max (x - w) 0 = M.
  by rewrite /M /upper_moment; apply: eq_Rintegral => x _; rewrite expr1.
have I1 : universality_semicircle_integral f0 = 1.
  rewrite threshold_integralE.
    exact: threshold_integrable_continuous _ cf0.
  rewrite /f0 RintegralZr//.
    exact: threshold_integrable_continuous _ (continuous_upper_part w 1).
  by rewrite mE mulfV// gt_eqF.
have I2 : universality_semicircle_integral (fun x => f0 x ^+ 2) =
    upper_moment threshold_law 2 w / M ^+ 2.
  rewrite threshold_integralE.
    exact: threshold_integrable_continuous _ cf02.
  under eq_Rintegral do rewrite /f0 expr_div_n.
  rewrite RintegralZr//.
  exact: threshold_integrable_continuous _ (continuous_upper_part w 2).
have cxm : continuous (fun x : R => x * Num.max (x - w) 0).
  move=> x; apply: cvgM; first exact: cvg_id.
  exact: (continuous_upper_part w 1 x).
have VE : \int[threshold_law]_x (x * Num.max (x - w) 0) = V.
  apply: (eq_trans _ (upper_variational_attained threshold_law2 0 c1)).
  by apply: eq_Rintegral => x _; rewrite addr0.
have I3 : universality_semicircle_integral (fun x => x * f0 x) = V / M.
  rewrite threshold_integralE.
    exact: threshold_integrable_continuous _ cxf0.
  under eq_Rintegral do rewrite /f0 mulrA.
  rewrite RintegralZr// ?VE//; exact: threshold_integrable_continuous _ cxm.
have VsE : V = upper_moment threshold_law 2 w + cone_shift kappa * M ^+ 2 by [].
have Mn : M != 0 by rewrite gt_eqF.
have Vn : V != 0 by rewrite gt_eqF.
have Vin : S V.
  exists f0; split.
    by move=> x; rewrite /f0 divr_ge0 ?le_max ?lexx ?orbT// ltW.
  split; first exact: threshold_semicircle_integrable _ cf0.
  split; first exact: threshold_semicircle_integrable _ cf02.
  split; first exact: I1.
  rewrite I2 I3.
  have -> : upper_moment threshold_law 2 w / M ^+ 2 + cone_shift kappa =
      V / M ^+ 2 by rewrite VsE; field.
  by field.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ge_sup => //; exists V.
by apply: ub_le_sup => //; exists V.
Qed.

End threshold_variational.
