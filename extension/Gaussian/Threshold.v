(* The threshold alpha*(kappa) and the cutoffs of Koehler and Sohn (arXiv
   2608.27372, lines 343-404 and section 5.3, lines 5115-5400 of
   arxiv_v1.tex), over the frozen definitions of UniversalityDefinitions.

   The semicircle law nu of density sqrt (2 - x^2)/pi is threshold_law, that
   is semicircle_prob (sqrt 2) of the library (probability/semicircle_law.v),
   and the functions m, s and E_kappa of the frozen definitions are the upper
   partial moments and the energy of the library's scalar variational problem
   (probability/variational.v) at c = c_kappa = (kappa - 3)/2. This file
   transports the library's results to the frozen definitions and adds what
   is specific to nu.

   Proved:
   - threshold_densityE, threshold_integralE: the frozen density is
     semicircle_pdf (sqrt 2), and universality_semicircle_integral f is the
     integral of f against threshold_law for nu-integrable f;
     universality_mE, universality_sE, universality_energyE,
     universality_cutoffE, universality_alpha_starE: m, s, E_kappa, omega_kappa
     and alpha*(kappa) are upper_moment threshold_law 1, upper_moment
     threshold_law 2, upper_energy threshold_law c_kappa, upper_cutoff
     threshold_law c_kappa 0 and upper_value threshold_law c_kappa 0.
   - The semicircle facts: universality_semicircle_mass (nu has mass one),
     universality_semicircle_second (int x^2 dnu = 1/2), universality_m_sym
     and universality_s_sym (m(-w) = m(w) + w and s(-w) + s(w) =
     1/2 + w^2, lines 5281-5283).
   - universality_alpha_star3 (line 377, Corollary 1.3):
     universality_alpha_star 3 = 1/4, from omega_3 = 0 and
     s(0) = (1/2) int x^2 dnu = 1/4.

   To prove (stage 1 of phase 5), for kappa > 1:
   - m(w) > 0 for w < sqrt 2 and m(w) = s(w) = 0 for w >= sqrt 2; for
     w <= -sqrt 2, m(w) = -w, s(w) = w^2 + 1/2 and
     E_kappa(w) = (kappa - 1)/2 w^2 + 1/2 (lines 5384-5391).
   - The paper's unique solution (lines 373-376): omega_kappa lies in
     [-sqrt 2, sqrt 2], satisfies omega_kappa = c_kappa m(omega_kappa), and
     is the only real number that does.
   - Proposition 5.10 (i) (lines 401-404): E_kappa is strictly decreasing on
     ]-oo, sqrt 2]; for alpha > 0, omega_{alpha,kappa} =
     universality_level_cutoff alpha kappa is < sqrt 2, satisfies
     E_kappa(omega_{alpha,kappa}) = alpha, and is the only w < sqrt 2 that
     does; chi_kappa(z) = upper_value nu c_kappa z is nondecreasing and
     strictly increasing where it is positive; with z_{alpha,kappa} =
     c_kappa m(omega_{alpha,kappa}) - omega_{alpha,kappa},
     chi_kappa(z_{alpha,kappa}) = alpha, and z_{alpha,kappa} > 0 if and only
     if alpha > alpha*(kappa).
   - Proposition 5.10 (ii): universality_alpha_star_variational kappa =
     universality_alpha_star kappa.
   - Lemma 5.9, the scalar part: with kappa^vee = kappa_dual kappa and
     z^vee = -2 z/(kappa - 1), the cutoff of (kappa^vee, z^vee) is minus that
     of (kappa, z), and chi_kappa(z) + chi_{kappa^vee}(z^vee) =
     1/2 + 2 z^2/(kappa - 1). The claim of Lemma 5.9 that -G_{d,kappa}(z) and
     G_{d,kappa^vee}(z^vee) have the same law is about the Gaussian matrices
     of section 5.2 and goes with them (stage 2, G8).
   - Proposition 5.10 (iii): 0 <= alpha*(kappa) <= 1/2 and
     alpha*(kappa) + alpha*(kappa^vee) = 1/2.
   - Proposition 5.10 (i), line 188: for alpha > 0, e*(alpha, kappa) > 0 if
     and only if alpha > alpha*(kappa).

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

Lemma cpos (w : R) k : continuous (fun x : R => Num.max (x - w) 0 ^+ k).
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
  have := threshold_integrable_continuous _ (cpos w 1).
  by apply: eq_integrable => // x _; rewrite /= expr1.
by apply: eq_Rintegral => x _; rewrite expr1.
Qed.

Lemma universality_sE (w : R) :
  universality_s w = upper_moment threshold_law 2 w.
Proof.
rewrite /universality_s threshold_integralE//.
exact: threshold_integrable_continuous _ (cpos w 2).
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
