(* The optimal profile, the curve alpha(C, kappa) as a variational value,
   and its dual form, at Stdlib's R: item S2 of phase 11
   (notes/phase11-plan.md, sections 3.2 and 5; the math plan
   notes/general-fourth-moment-condition-plan.md, section 3; lane C), and
   item S3 to come. The definitions are those of ConditionKappaDefinitions;
   the root is item S1 (Scalar); the generic results are those of
   library/probability/clip_profile.v, applied to the semicircle law nu
   (threshold_law of Gaussian/Threshold).

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1, C > 1; m = universality_m,
   v = universality_s, u = u_{C,kappa}, ell = ell_{C,kappa}, J and V_c as in
   ConditionKappaDefinitions.

   Proved (S2).
   - The optimal profile q_s(z) = min (max (z - c mu_s) t_s) (C t_s)
     (condition_kappa_opt), with mean mu_s = (C - 1) m(u) / (1 + c)
     (condition_kappa_mean) and level t_s = (u - ell) / (C - 1)
     (condition_kappa_level): t_s > 0 (condition_kappa_level_gt0),
     ell = t_s + c mu_s and u = C t_s + c mu_s (condition_kappa_ellE,
     condition_kappa_uE), the residual balance m(-ell) = C m(u)
     (condition_kappa_balance), and E q_s = mu_s (condition_kappa_opt_mean),
     the fixed point of clip_profile.v.
   - condition_kappa_opt_value: V_c(q_s) = J(ell) - J(u) = alpha(C, kappa);
     condition_kappa_objectiveE: the frozen objective is V_c of
     clip_profile.v on the admissible profiles (condition_kappa_profileP);
     condition_kappa_value_alpha: alpha(C, kappa) is the value of the
     variational problem, attained at q_s, since q_s maximizes V_c
     (clip_optimal); condition_kappa_variational_holds: conjunct (b) of
     the frozen curve statement.
   - Interface I2 (used by item M4, GaussianLimit, lane A). The dual
     function below is
       condition_kappa_dual C kappa mu
         = 1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)),
     the limit of (1/d) (|Pi_K(H - c mu I)|_F^2 + c d mu^2) for
     H = G / sqrt d and K = cond_cone C; it is clip_dual of the semicircle
     law (condition_kappa_dualE), since the inner infimum is the mean
     squared distance from z - c mu to [t, C t] (clip_energy_shiftE). For
     C > 1 and kappa > 1:
     condition_kappa_dual_opt: some mu0, 0 <= mu0 <= 1 / (sqrt 2 a0) with
     a0 = min(1, (kappa - 1) / 2), has condition_kappa_dual C kappa mu0 =
     alpha(C, kappa) (mu0 = mu_s);
     condition_kappa_dual_le: if kappa <= 3, condition_kappa_dual C kappa mu
     <= alpha(C, kappa) for every mu;
     condition_kappa_dual_ge: if 3 <= kappa, alpha(C, kappa) <=
     condition_kappa_dual C kappa mu for every mu.
     So alpha(C, kappa) is the maximum of the dual for c < 0 and its
     minimum for c > 0; at c = 0 the dual does not depend on mu.

   To prove here (S3). C |-> alpha(C, kappa) is continuous and strictly
   increasing on (1, oo), with limit 0 at 1 and limit alpha*(kappa) at oo
   (through universality_alpha_star_variationalE of Gaussian/Threshold.v and
   the equivalence of the quadratic and ratio forms);
   0 < alpha(C, kappa) < alpha*(kappa) < 1/2; the inverse C_star(alpha,
   kappa) and its order characterization; the analogues of
   condition_alpha_left and condition_alpha_right of Condition/Curve.v.
   These are interface I3, used by items D1 and D2 (Sat, Unsat, lane B)
   and A1 (Theorem). *)

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
From GaussianAnalysis.probability Require Import clip_profile.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.ConditionKappa Require Import Scalar.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation um := universality_m.
Local Notation us := universality_s.
Local Notation sq2 := (Num.sqrt 2%:R : R).

(* The dual function of interface I2: with c = (kappa - 3) / 2,
   1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)). *)
Definition condition_kappa_dual (C kappa mu : R) :=
  2%:R^-1 + (kappa - 3%:R) / 2%:R * (1 + (kappa - 3%:R) / 2%:R) * mu ^+ 2
  - inf [set universality_s (- t - (kappa - 3%:R) / 2%:R * mu)%R
             + universality_s (C * t + (kappa - 3%:R) / 2%:R * mu)%R
         | t in [set t : R | 0 <= t]].

(* The optimal profile: its mean mu_s = (C - 1) m(u) / (1 + c), its level
   t_s = (u - ell) / (C - 1), and
   q_s(z) = min (max (z - c mu_s) t_s) (C t_s). *)
Definition condition_kappa_mean (C kappa : R) :=
  (C - 1) * um (condition_kappa_u C kappa) / (1 + (kappa - 3%:R) / 2%:R).

Definition condition_kappa_level (C kappa : R) :=
  (condition_kappa_u C kappa - condition_kappa_ell C kappa) / (C - 1).

Definition condition_kappa_opt (C kappa : R) : R -> R :=
  clip_profile C ((kappa - 3%:R) / 2%:R * condition_kappa_mean C kappa)
    (condition_kappa_level C kappa).

Section kappa_profile.
Variables (C kappa : R).
Hypotheses (C1 : 1 < C) (k1 : 1 < kappa).

Local Notation c := ((kappa - 3%:R) / 2%:R).
Local Notation u := (condition_kappa_u C kappa).
Local Notation ell := (condition_kappa_ell C kappa).
Local Notation mus := (condition_kappa_mean C kappa).
Local Notation ts := (condition_kappa_level C kappa).
Local Notation qs := (condition_kappa_opt C kappa).

Let C0 : 0 < C := lt_trans ltr01 C1.
Let C10 : 0 < C - 1.
Proof. by rewrite subr_gt0. Qed.
Let c1 : -1 < c.
Proof. by have := cone_shift_gtN1 _ k1; rewrite cone_shiftE. Qed.
Let c10 : 0 < 1 + c.
Proof. by rewrite -ltrBlDl sub0r. Qed.

Lemma condition_kappa_level_gt0 : 0 < ts.
Proof.
have /andP[_ lu] := condition_kappa_ell_spec C kappa C1 k1.
by rewrite /condition_kappa_level divr_gt0 // subr_gt0.
Qed.

(* ell = t_s + c mu_s and u = C t_s + c mu_s. *)
Lemma condition_kappa_ellE : ell = ts + c * mus.
Proof.
have hL := condition_kappa_LE C kappa u C0.
rewrite -/(condition_kappa_ell C kappa) in hL.
rewrite /condition_kappa_level /condition_kappa_mean.
have k0 : kappa - 1 != 0 by rewrite subr_eq0 gt_eqF.
have hc : 1 + (kappa - 3%:R) / 2%:R != 0 by rewrite gt_eqF.
have hC : C - 1 != 0 by rewrite gt_eqF.
move: hL; set M := um u => hL.
have h1c : 1 + (kappa - 3%:R) / 2%:R = (kappa - 1) / 2%:R by field.
have hr : (kappa - 3%:R) / 2%:R / (1 + (kappa - 3%:R) / 2%:R) =
    (kappa - 3%:R) / (kappa - 1).
  rewrite h1c invf_div mulrA -[(kappa - 3%:R) / 2%:R * 2%:R]mulrA.
  by rewrite mulVf ?pnatr_eq0 // mulr1.
have e2 : (kappa - 3%:R) / 2%:R * ((C - 1) * M / (1 + (kappa - 3%:R) / 2%:R)) =
    (C - 1) * M * ((kappa - 3%:R) / 2%:R / (1 + (kappa - 3%:R) / 2%:R)).
  by ring.
rewrite e2 hr.
apply: (mulfI hC).
rewrite mulrDr [(C - 1) * ((u - ell) / (C - 1))]mulrC divfK //.
move: hL; set r := (kappa - 3%:R) / (kappa - 1) => hL.
by move: hL; lra.
Qed.

Lemma condition_kappa_uE : u = C * ts + c * mus.
Proof.
have hC : C - 1 != 0 by rewrite gt_eqF.
have e : (C - 1) * ts = u - ell.
  by rewrite /condition_kappa_level mulrC divfK.
have := condition_kappa_ellE; move: e; rewrite mulrBl mul1r.
by move: (C * ts) ts (c * mus) u ell => a b d f g; lra.
Qed.

(* The residual balance m(-ell) = C m(u). *)
Lemma condition_kappa_balance :
  um (- (ts + c * mus))%R = C * um (C * ts + c * mus)%R.
Proof.
rewrite -condition_kappa_ellE -condition_kappa_uE.
have [_ _ Fu _] := condition_kappa_u_spec C kappa C1 k1.
move: Fu; rewrite /condition_kappa_F -/(condition_kappa_ell C kappa) => Fu.
by apply/eqP; rewrite -subr_eq0 Fu.
Qed.

(* The fixed point: E q_s = mu_s. *)
Lemma condition_kappa_opt_mean : \int[threshold_law]_x qs x = mus.
Proof.
have t0 := ltW condition_kappa_level_gt0.
rewrite /condition_kappa_opt (clip_profile_mean threshold_law2 _ (ltW C1) t0).
rewrite -!universality_mE -condition_kappa_ellE -condition_kappa_uE.
have hs := universality_m_sym ell.
rewrite RoppE in hs.
have hb := condition_kappa_balance.
rewrite -condition_kappa_ellE -condition_kappa_uE in hb.
have hmu : (1 + c) * mus = (C - 1) * um u.
  by rewrite /condition_kappa_mean mulrC divfK // gt_eqF.
have he := condition_kappa_ellE.
move: hs hb hmu he; move: (um ell) (um (- ell)%R) (um u) => a b d.
by move=> hs hb hmu he; lra.
Qed.

Let t0 : 0 <= ts := ltW condition_kappa_level_gt0.
Let C1' : 1 <= C := ltW C1.

Let bal : upper_moment threshold_law 1 (- (ts + c * mus)) =
  C * upper_moment threshold_law 1 (C * ts + c * mus).
Proof. by rewrite -!universality_mE; exact: condition_kappa_balance. Qed.

Let fixpt : c * mus = c * \int[threshold_law]_x clip_profile C (c * mus) ts x.
Proof.
by have := condition_kappa_opt_mean; rewrite /condition_kappa_opt => ->.
Qed.

(* V_c(q_s) = alpha(C, kappa). *)
Lemma condition_kappa_opt_value :
  clip_objective threshold_law c qs = condition_kappa_alpha C kappa.
Proof.
rewrite /condition_kappa_opt.
rewrite (clip_objectiveE threshold_law2 threshold_law_sym C1' t0 bal fixpt).
rewrite -!universality_sE -!universality_mE.
by rewrite -condition_kappa_ellE -condition_kappa_uE.
Qed.

(* The frozen objective is V_c on the admissible profiles. *)
Lemma condition_kappa_objectiveE (q : R -> R) :
  clip_admissible C q -> condition_kappa_objective kappa q =
  clip_objective threshold_law c q.
Proof.
move=> hq; have [B B0 qB] := clip_admissible_bounded hq.
case: (hq) => mq _.
rewrite /condition_kappa_objective /clip_objective.
rewrite !threshold_integralE //.
- exact: (clip_integrable_id_bounded threshold_law2 mq qB).
- exact: (clip_integrable_sq threshold_law2 mq qB).
- exact: (clip_integrable_bounded threshold_law2 mq qB).
Qed.

Lemma condition_kappa_profileP (q : R -> R) :
  condition_kappa_profile C q <-> clip_admissible C q.
Proof. by []. Qed.

(* Conjunct (b): alpha(C, kappa) is the value of the variational
   problem, attained at q_s. *)
Lemma condition_kappa_value_alpha :
  condition_kappa_alpha C kappa = condition_kappa_value C kappa.
Proof.
rewrite /condition_kappa_value -condition_kappa_opt_value.
have qsA : clip_admissible C qs := clip_profile_admissible _ C1' t0.
set A := [set condition_kappa_objective kappa q | q in condition_kappa_profile C].
set v := clip_objective threshold_law c qs.
have Aq : A v by exists qs => //; rewrite condition_kappa_objectiveE.
have ub : ubound A v.
  move=> _ [q hq <-]; rewrite condition_kappa_objectiveE //.
  exact: (clip_optimal threshold_law2 threshold_law_sym C1' t0 bal c1 fixpt hq).
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: sup_upper_bound => //; split; [exists v | exists v].
by apply: ge_sup => //; exists v.
Qed.

(* The dual function of I2 is clip_dual of the semicircle law. *)
Lemma condition_kappa_dualE (mu0 : R) :
  condition_kappa_dual C kappa mu0 = clip_dual threshold_law c C mu0.
Proof.
rewrite /condition_kappa_dual /clip_dual threshold_second.
congr (_ - inf _).
apply/seteqP; split => _ [t' t'0 <-]; exists t' => //;
  by rewrite /clip_energy_shift !universality_sE.
Qed.

(* Interface I2. The dual function is attained at mu_s, in the window
   0 <= mu_s <= 1 / (sqrt 2 a0), a0 = min(1, (kappa - 1) / 2). *)
Lemma condition_kappa_dual_opt : exists mu0 : R,
  [/\ 0 <= mu0, mu0 <= 1 / (Num.sqrt 2%:R * Num.min 1 ((kappa - 1) / 2%:R)) &
      condition_kappa_dual C kappa mu0 = condition_kappa_alpha C kappa].
Proof.
exists mus.
have [w0 w1] :=
  clip_dual_window threshold_law2 threshold_law_sym C1' t0 bal c1 fixpt.
have hm := condition_kappa_opt_mean; rewrite /condition_kappa_opt in hm.
rewrite hm threshold_second in w1; rewrite hm in w0.
have h1c : 1 + (kappa - 3%:R) / 2%:R = (kappa - 1) / 2%:R by field.
rewrite h1c in w1.
split => //.
  set k := Num.min 1 ((kappa - 1) / 2%:R) in w1 *.
  have k0 : 0 < k by rewrite lt_min ltr01 /= divr_gt0 // subr_gt0.
  have s0 : 0 < Num.sqrt 2%:R :> R by rewrite sqrtr_gt0 ltr0n.
  have s2 : Num.sqrt 2%:R ^+ 2 = 2%:R :> R by rewrite sqr_sqrtr // ler0n.
  rewrite ler_pdivlMr ?mulr_gt0 //.
  move: w0 w1; move: (mus) => b w0 w1.
  have p0 : 0 <= b * (Num.sqrt 2%:R * k) by rewrite mulr_ge0 // mulr_ge0 // ltW.
  have p2 : (b * (Num.sqrt 2%:R * k)) ^+ 2 <= 1.
    have -> : (b * (Num.sqrt 2%:R * k)) ^+ 2 =
        Num.sqrt 2%:R ^+ 2 * (k ^+ 2 * b ^+ 2) by ring.
    rewrite s2; move: w1; move: (k ^+ 2 * b ^+ 2) => z w1.
    have h2 : (2%:R : R) * 2^-1 = 1 by rewrite mulfV // pnatr_eq0.
    by nra.
  by move: p0 p2; move: (b * (Num.sqrt 2%:R * k)) => z; nra.
rewrite condition_kappa_dualE -[in LHS]hm.
rewrite (clip_dual_opt threshold_law2 threshold_law_sym C1' t0 bal fixpt).
exact: condition_kappa_opt_value.
Qed.

(* Interface I2: for kappa <= 3 the dual is at most alpha(C, kappa). *)
Lemma condition_kappa_dual_le : kappa <= 3%:R ->
  forall mu0, condition_kappa_dual C kappa mu0 <= condition_kappa_alpha C kappa.
Proof.
move=> k3 mu0; rewrite condition_kappa_dualE -condition_kappa_opt_value.
apply: (clip_dual_le threshold_law2 threshold_law_sym C1' t0 bal c1 fixpt).
by rewrite pmulr_lle0 ?invr_gt0 ?ltr0n // subr_le0.
Qed.

(* Interface I2: for kappa >= 3 the dual is at least alpha(C, kappa). *)
Lemma condition_kappa_dual_ge : 3%:R <= kappa ->
  forall mu0, condition_kappa_alpha C kappa <= condition_kappa_dual C kappa mu0.
Proof.
move=> k3 mu0; rewrite condition_kappa_dualE -condition_kappa_opt_value.
apply: (clip_dual_ge threshold_law2 threshold_law_sym _ C1' t0).
by rewrite divr_ge0 ?ler0n // subr_ge0.
Qed.

End kappa_profile.

(* Conjunct (b) of the curve statement. *)
Theorem condition_kappa_variational_holds (kappa : R) : 1 < kappa ->
  condition_kappa_variational kappa.
Proof. by move=> k1 C C1; exact: condition_kappa_value_alpha. Qed.

