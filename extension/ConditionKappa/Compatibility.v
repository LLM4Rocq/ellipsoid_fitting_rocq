(* The curve at fourth moment kappa = 3 and the theorems of phases 8 and 10,
   at Stdlib's R: items S4 and A4 of phase 11 (notes/phase11-plan.md,
   section 5; lane B). The definitions are those of ConditionKappaDefinitions
   and ConditionDefinitions; the root is item S1 (Scalar).

   At kappa = 3, c = r = 0, so L(u) = u / C and F(u) = m(-u / C) - C m(u).

   Proved.
   - S4. condition_t_root: m(-t_C) = C m(C t_C) for C > 1, from
     condition_t_spec of Condition/Curve.v (the two inequalities on each
     side of t_C) and the 1-Lipschitz property of m. condition_kappa_u3,
     condition_kappa_ell3: for C > 1, u_{C,3} = C t_C and ell_{C,3} = t_C,
     by the uniqueness of the zero of F in [0, sqrt 2]
     (condition_kappa_u_spec). condition_kappa_alpha3: for C > 1,
     alpha(C, 3) = condition_alpha C, since J(t) - J(C t) =
     1/2 - v(-t) - v(C t) when m(-t) = C m(C t), by m(-t) = m(t) + t and
     v(-t) + v(t) = 1/2 + t^2 (universality_m_sym, universality_s_sym).
     condition_kappa_star3: C_star(alpha, 3) = condition_star alpha for every
     alpha, since the two sets of the infimum contain only C > 1, where the
     curves agree. condition_kappa_three_holds: conjunct (f) of the curve
     statement, condition_kappa_three.
   - A4. condition_theorem_of_kappa : condition_kappa_theorem_statement ->
     condition_theorem_statement and robust_condition_theorem_of_kappa :
     condition_kappa_robust_theorem_statement ->
     robust_condition_theorem_statement: the new statements at kappa = 3,
     with alpha(C, 3) = condition_alpha C, C_star(alpha, 3) =
     condition_star alpha and alpha*(3) = 1/4 (universality_alpha_star3). *)

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
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionStatement.
From EllipsoidUniversality Require Import ConditionRobustStatement.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality Require Import ConditionKappaStatement.
From EllipsoidUniversality Require Import ConditionKappaRobustStatement.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Condition Require Import Curve.
From EllipsoidUniversality.ConditionKappa Require Import Scalar.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation um := universality_m.
Local Notation us := universality_s.
Local Notation sq2 := (Num.sqrt 2%:R : R).

(* 1. Item S4: the curve at kappa = 3. *)

(* t_C solves m(-t) = C m(C t). *)
Lemma condition_t_root (C : R) : 1 < C ->
  um (- condition_t C)%R = C * um (C * condition_t C).
Proof.
move=> C1; have [t0 tlt lo hi] := condition_t_spec C C1.
have C0 : 0 < C := lt_trans ltr01 C1.
set t := condition_t C in t0 tlt lo hi *.
have hge : C * um (C * t) <= um (- t)%R.
  by have := hi t (lexx _); rewrite !universality_mE.
apply/eqP; rewrite eq_le hge andbT.
(* m(-t) <= C m(C s) + (1 + C^2) (t - s) for 0 <= s < t *)
have K0 : 0 < 1 + C ^+ 2 by rewrite ltr_pwDl // sqr_ge0.
rewrite leNgt; apply/negP => hlt.
set g := um (- t)%R - C * um (C * t).
have g0 : 0 < g by rewrite /g subr_gt0.
pose s := t - Num.min t (g / (2 * (1 + C ^+ 2))).
have e0 : 0 < Num.min t (g / (2 * (1 + C ^+ 2))).
  by rewrite lt_min t0 /= divr_gt0 // mulr_gt0.
have s0 : 0 <= s by rewrite /s subr_ge0 ge_min lexx.
have st : s < t by rewrite /s ltrBlDr ltrDl.
have hs : um (- s)%R <= C * um (C * s).
  by have := lo s s0 st; rewrite !universality_mE.
have l1 : - t <= - s by rewrite lerN2 ltW.
have /andP[_ m1] := kappa_m_lip _ _ l1.
have l2 : C * s <= C * t by rewrite ler_pM2l // ltW.
have /andP[_ m2] := kappa_m_lip _ _ l2.
have m2' : C * um (C * s) - C * um (C * t) <= C * (C * t - C * s).
  by rewrite -mulrBr ler_wpM2l // ltW.
have hts : t - s <= g / (2 * (1 + C ^+ 2)).
  by rewrite /s opprB addrC subrK ge_min lexx orbT.
have hK : (1 + C ^+ 2) * (t - s) <= g / 2.
  have := ler_wpM2l (ltW K0) hts.
  have -> : (1 + C ^+ 2) * (g / (2 * (1 + C ^+ 2))) = g / 2.
    by have := lt0r_neq0 K0; move=> kn; field.
  by [].
have e : C * (C * t - C * s) = C ^+ 2 * (t - s) by ring.
rewrite e in m2'.
move: m1 m2' hs hK g0; rewrite /g.
move: (um (- t)%R) (um (- s)%R) (um (C * s)) (um (C * t)) => a b c f.
move=> m1 m2' hs hK g0; rewrite opprK in m1.
have : (1 + C ^+ 2) * (t - s) = (t - s) + C ^+ 2 * (t - s) by ring.
by move=> h; nra.
Qed.

(* At kappa = 3, L(u) = u / C. *)
Lemma condition_kappa_L3 (C u : R) : condition_kappa_L C 3%:R u = u / C.
Proof. by rewrite /condition_kappa_L subrr !mul0r addr0. Qed.

Lemma condition_kappa_u3 (C : R) : 1 < C ->
  condition_kappa_u C 3%:R = C * condition_t C.
Proof.
move=> C1; have k3 : 1 < 3%:R :> R by rewrite ltr1n.
have C0 : 0 < C := lt_trans ltr01 C1.
have [_ _ _ uniq] := condition_kappa_u_spec C 3%:R C1 k3.
have [t0 tlt _ _] := condition_t_spec C C1.
symmetry; apply: uniq.
  apply/andP; split; first by rewrite mulr_ge0 // ltW.
  by rewrite -(ler_pdivlMl _ _ C0) ltW // mulrC.
rewrite /condition_kappa_F condition_kappa_L3.
have -> : C * condition_t C / C = condition_t C.
  by rewrite mulrC mulKf // gt_eqF.
by rewrite -condition_t_root // subrr.
Qed.

Lemma condition_kappa_ell3 (C : R) : 1 < C ->
  condition_kappa_ell C 3%:R = condition_t C.
Proof.
move=> C1; rewrite /condition_kappa_ell condition_kappa_u3 //.
rewrite condition_kappa_L3 mulrC mulKf // gt_eqF //.
exact: lt_trans ltr01 C1.
Qed.

(* J(t) - J(C t) = 1/2 - v(-t) - v(C t) when m(-t) = C m(C t). *)
Lemma condition_kappa_alpha3 (C : R) : 1 < C ->
  condition_kappa_alpha C 3%:R = condition_alpha C.
Proof.
move=> C1; rewrite /condition_kappa_alpha condition_kappa_ell3 //.
rewrite condition_kappa_u3 // /condition_kappa_J /condition_alpha.
have hr := condition_t_root C C1.
set t := condition_t C in hr *.
have hm := universality_m_sym t.
have hs := universality_s_sym t.
rewrite !RoppE in hm hs hr *.
have e : C * t * um (C * t) = t * (um t + t).
  by rewrite -hm hr; ring.
rewrite e.
move: hs; move: (us (- t)) (us t) (us (C * t)) (um t) => a b c f hs.
by rewrite !RminusE; lra.
Qed.

Lemma condition_kappa_star3 (alpha : R) :
  condition_kappa_star alpha 3%:R = condition_star alpha.
Proof.
rewrite /condition_kappa_star /condition_star; congr inf.
apply/seteqP; split => C [C1 aC]; split => //.
  by rewrite -condition_kappa_alpha3.
by rewrite condition_kappa_alpha3.
Qed.

(* Conjunct (f) of the curve statement. *)
Theorem condition_kappa_three_holds : condition_kappa_three.
Proof.
split => [C C1|alpha a0 a4]; first exact: condition_kappa_alpha3.
exact: condition_kappa_star3.
Qed.

(* 2. Item A4: the new statements give the frozen ones at kappa = 3. *)

Theorem condition_theorem_of_kappa :
  condition_kappa_theorem_statement -> condition_theorem_statement.
Proof.
move=> [h20 h21 c20 c21]; have k3 : 1 < 3%:R :> R by rewrite ltr1n.
have a3 (alpha : R) : alpha < 4%:R^-1 -> alpha < universality_alpha_star 3%:R.
  by rewrite universality_alpha_star3.
split.
- move=> K C alpha K0 C1 a0.
  have [hm hc] := h20 3%:R K C alpha k3 K0 C1 a0.
  split => // N w mu hfam h4 n hn.
  by rewrite -(condition_kappa_alpha3 C C1); exact: hc.
- move=> K alpha K0 a0 a4 N w mu hfam h4 n hn eps delta e0 d0.
  rewrite -condition_kappa_star3.
  exact: (h21 3%:R K alpha k3 K0 a0 (a3 _ a4) N w mu hfam h4 n hn eps delta
    e0 d0).
- move=> K C alpha K0 C1 a0.
  have [hm hc] := c20 3%:R K C alpha k3 K0 C1 a0.
  split => // w mu hfam h4 n hn.
  by rewrite -(condition_kappa_alpha3 C C1); exact: hc.
- move=> K alpha K0 a0 a4 w mu hfam h4 n hn eps delta e0 d0.
  rewrite -condition_kappa_star3.
  exact: (c21 3%:R K alpha k3 K0 a0 (a3 _ a4) w mu hfam h4 n hn eps delta
    e0 d0).
Qed.

Theorem robust_condition_theorem_of_kappa :
  condition_kappa_robust_theorem_statement ->
  robust_condition_theorem_statement.
Proof.
move=> [r20 r21 _ _]; have k3 : 1 < 3%:R :> R by rewrite ltr1n.
split.
- move=> K C alpha K0 C1 a0 w mu hfam h4 P hP n hn.
  rewrite -(condition_kappa_alpha3 C C1).
  exact: (r20 3%:R K C alpha k3 K0 C1 a0 w mu hfam h4 P hP n hn).
- move=> K alpha K0 a0 a4 w mu hfam h4 P hP n hn eps delta e0 d0.
  rewrite -condition_kappa_star3.
  have a4' : alpha < universality_alpha_star 3%:R.
    by rewrite universality_alpha_star3.
  exact: (r21 3%:R K alpha k3 K0 a0 a4' w mu hfam h4 P hP n hn eps delta e0
    d0).
Qed.
