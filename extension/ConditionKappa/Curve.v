(* The optimal profile, the curve alpha(C, kappa) as a variational value,
   its dual form, and the shape of the curve and of its inverse, at
   Stdlib's R: items S2 and S3 of phase 11 (notes/phase11-plan.md, sections
   3.2 and 5; the math plan notes/general-fourth-moment-condition-plan.md,
   section 3; lane C). The definitions are those of
   ConditionKappaDefinitions; the root is item S1 (Scalar); the generic
   results are those of library/probability/clip_profile.v, applied to the
   semicircle law nu (threshold_law of Gaussian/Threshold).

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
   - The almost-everywhere class, for all reals C and kappa: on the
     measurable profiles q with t <= q <= C t nu-almost everywhere for
     some t >= 0 (clip_admissible_ae threshold_law C), the frozen
     objective is V_c (condition_kappa_objective_aeE), and its least upper
     bound over them is condition_kappa_value C kappa
     (condition_kappa_value_ae), by clip_objective_ae_set of
     clip_profile.v: the clipped profile min(max(q, t), C t) is
     admissible, equals q almost everywhere and has the value of q.
     condition_kappa_alpha_ae: for C > 1 and kappa > 1, alpha(C, kappa) is
     also the value of the problem with almost-everywhere bounds.
   - Interface I2, used by kappa_quad_close of GaussianLimit (item M4).
     The dual function below is
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

   Proved (S3), for kappa > 1 (section kappa_curve).
   - The bounds by the optimal value: condition_kappa_alpha_ub, V_c(q) <=
     alpha(C, kappa) for every profile q admissible for C;
     condition_kappa_V_le_star, V_c(q) <= alpha*(kappa) for every
     admissible q (upper_variational_sym_le of variational.v).
   - Monotonicity: condition_kappa_alpha_le (alpha is nondecreasing in C,
     since the admissible profiles grow with C) and condition_kappa_alpha_lt
     (it is increasing: adding to q_s a small multiple of the indicator of
     ]v, oo[, with u < v < sqrt 2, gives a profile admissible for C' > C
     with a larger value).
   - Continuity: condition_kappa_alpha_lip, for 1 < C <= C' and t' the
     level at C', alpha(C') - alpha(C) <= 2 (C' - C) t'
     (1 + (1 + |c|) C' t'), by clipping the optimal profile at C' to C t'
     (clip_objective_add); with t' < 2 sqrt 2 / (C' - 1)
     (condition_kappa_level_lt) this gives a local Lipschitz bound
     (condition_kappa_alpha_lip_loc) and condition_kappa_alpha_cont.
   - The limits: condition_kappa_alpha_near1, alpha(C, kappa) <=
     (C - 1)^2 / (1 + c), hence condition_kappa_alpha_lim1;
     condition_kappa_alpha_liminf: with w the cutoff of alpha*(kappa)
     (upper_cutoff), the profile eps + min((z - w)_+, sqrt 2 + |w|) is
     admissible for C >= 2 + (sqrt 2 + |w|) / eps, and its value is
     alpha*(kappa) - (1 + c) (eps^2 + 2 eps m(w)). The computation uses
     threshold_integral_support: two integrable functions that agree on
     ]-sqrt 2, sqrt 2[ have the same integral against nu.
   - condition_kappa_alpha_gt0, condition_kappa_alpha_lt_star:
     0 < alpha(C, kappa) < alpha*(kappa); condition_kappa_range_holds:
     conjunct (d) of the frozen curve statement.
   - Interface I3, in the forms that condition_kappa_sat and
     condition_kappa_unsat (Sat, Unsat) take as hypotheses, and that
     ConditionKappaTheorem.v supplies to condition_kappa_statement_of_I3
     (Theorem):
     condition_kappa_alpha_left (if alpha' < alpha(C', kappa), some Cm in
     ]1, C'[ has alpha' < alpha(Cm, kappa)), condition_kappa_alpha_right
     (if alpha(C', kappa) < alpha', some Cp > C' has alpha(Cp, kappa) <
     alpha') and condition_kappa_alpha_half (alpha(C, kappa) < 1/2, since
     alpha*(kappa) < 1/2).
   - condition_kappa_inverse_holds: conjunct (e), for 0 < alpha <
     alpha*(kappa): 1 < C_star(alpha, kappa), alpha(C_star, kappa) = alpha,
     and for C > 1, alpha < alpha(C, kappa) iff C_star < C. *)

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

(* q_s maximizes V_c over the admissible profiles for C. *)
Lemma condition_kappa_opt_optimal (q : measurableTypeR R -> R) :
  clip_admissible C q ->
  clip_objective threshold_law c q <= clip_objective threshold_law c qs.
Proof. exact: (clip_optimal threshold_law2 threshold_law_sym C1' t0 bal c1 fixpt). Qed.

(* The radial identity at q_s: V_c(q_s) = E q_s^2 + c (E q_s)^2. *)
Lemma condition_kappa_opt_radial :
  clip_objective threshold_law c qs =
  \int[threshold_law]_x (qs x ^+ 2) + c * (\int[threshold_law]_x qs x) ^+ 2.
Proof.
exact: (clip_objective_radial threshold_law2 threshold_law_sym C1' t0 bal fixpt).
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

(* The profiles admissible almost everywhere under nu: the measurable q
   with t <= q <= C t nu-almost everywhere for some t >= 0
   (clip_admissible_ae threshold_law C). On them the frozen objective is
   V_c, and its least upper bound over them is condition_kappa_value C
   kappa, for all reals C and kappa. *)
Lemma condition_kappa_objective_aeE (C kappa : R) (q : R -> R) :
  clip_admissible_ae threshold_law C q ->
  condition_kappa_objective kappa q =
  clip_objective threshold_law ((kappa - 3%:R) / 2%:R) q.
Proof.
move=> hq.
have [i1 i2 i3] := clip_admissible_ae_integrable threshold_law2 hq.
by rewrite /condition_kappa_objective /clip_objective !threshold_integralE.
Qed.

Lemma condition_kappa_value_ae (C kappa : R) :
  sup [set condition_kappa_objective kappa q
      | q in clip_admissible_ae threshold_law C] =
  condition_kappa_value C kappa.
Proof.
rewrite /condition_kappa_value; congr sup.
have E (P : set (measurableTypeR R -> R)) :
    P `<=` clip_admissible_ae threshold_law C ->
    [set condition_kappa_objective kappa q | q in P] =
    [set clip_objective threshold_law ((kappa - 3%:R) / 2%:R) q | q in P].
  move=> PA; apply/seteqP; split => _ [q hq <-]; exists q => //;
    by rewrite (condition_kappa_objective_aeE _ _ _ (PA q hq)).
rewrite (E _ (fun q hq => hq)).
rewrite (E (condition_kappa_profile C) (@clip_admissible_ae_sub _ threshold_law C)).
exact: clip_objective_ae_set.
Qed.

(* For C > 1 and kappa > 1, alpha(C, kappa) is also the value of the
   problem with almost-everywhere bounds. *)
Lemma condition_kappa_alpha_ae (C kappa : R) : 1 < C -> 1 < kappa ->
  condition_kappa_alpha C kappa =
  sup [set condition_kappa_objective kappa q
      | q in clip_admissible_ae threshold_law C].
Proof.
move=> C1 k1; rewrite condition_kappa_value_ae.
exact: condition_kappa_value_alpha.
Qed.

Section kappa_curve.
Variable kappa : R.
Hypothesis k1 : 1 < kappa.

Local Notation c := ((kappa - 3%:R) / 2%:R).
Local Notation alpha C := (condition_kappa_alpha C kappa).
Local Notation V := (clip_objective threshold_law ((kappa - 3%:R) / 2%:R)).

Let c1 : -1 < c.
Proof. by have := cone_shift_gtN1 _ k1; rewrite cone_shiftE. Qed.

(* Every admissible profile for C has V_c at most alpha(C, kappa). *)
Lemma condition_kappa_alpha_ub (C : R) (q : measurableTypeR R -> R) :
  1 < C -> clip_admissible C q -> V q <= alpha C.
Proof.
move=> C1 hq.
rewrite -(condition_kappa_opt_value C kappa C1 k1).
exact: (condition_kappa_opt_optimal C kappa C1 k1 q hq).
Qed.

(* C |-> alpha(C, kappa) is nondecreasing on (1, oo). *)
Lemma condition_kappa_alpha_le (C C' : R) : 1 < C -> C <= C' ->
  alpha C <= alpha C'.
Proof.
move=> C1 CC; have C1' := lt_le_trans C1 CC.
rewrite -(condition_kappa_opt_value C kappa C1 k1).
apply: condition_kappa_alpha_ub => //.
apply: clip_admissible_le CC _.
apply: clip_profile_admissible; first exact: ltW.
exact: ltW (condition_kappa_level_gt0 C kappa C1 k1).
Qed.

(* alpha(C, kappa) > 0: V_c(q_s) = E q_s^2 + c (E q_s)^2 >= (1 + c) mu_s^2. *)
Lemma condition_kappa_alpha_gt0 (C : R) : 1 < C -> 0 < alpha C.
Proof.
move=> C1.
rewrite -(condition_kappa_opt_value C kappa C1 k1).
rewrite (condition_kappa_opt_radial C kappa C1 k1).
have t0 := ltW (condition_kappa_level_gt0 C kappa C1 k1).
have [B B0 qB] := clip_profile_bounded
  ((kappa - 3%:R) / 2%:R * condition_kappa_mean C kappa) (ltW C1) t0.
have mq := measurable_clip_profile C
  ((kappa - 3%:R) / 2%:R * condition_kappa_mean C kappa)
  (condition_kappa_level C kappa).
have iq := clip_integrable_bounded threshold_law2 mq qB.
have iq2 := clip_integrable_sq threshold_law2 mq qB.
have hJ := Rintegral_sqr_le iq iq2.
rewrite /condition_kappa_opt in hJ *.
rewrite (condition_kappa_opt_mean C kappa C1 k1) in hJ *.
have m0 : 0 < condition_kappa_mean C kappa.
  rewrite /condition_kappa_mean divr_gt0 //.
    rewrite mulr_gt0 ?subr_gt0 //; apply: universality_m_gt0.
    by have [_ us _ _] := condition_kappa_u_spec C kappa C1 k1.
  by rewrite -ltrBlDl sub0r.
have c10 : 0 < 1 + (kappa - 3%:R) / 2%:R by rewrite -ltrBlDl sub0r.
have hp : 0 < (1 + (kappa - 3%:R) / 2%:R) * condition_kappa_mean C kappa ^+ 2.
  by rewrite mulr_gt0 // exprn_gt0.
move: hJ hp.
move: (\int[threshold_law]_x (clip_profile C
  ((kappa - 3%:R) / 2%:R * condition_kappa_mean C kappa)
  (condition_kappa_level C kappa) x ^+ 2)) (condition_kappa_mean C kappa) => Q M.
by move=> hJ hp; nra.
Qed.

(* alpha*(kappa) is the value of the library problem at c and z = 0. *)
Let astarE : universality_alpha_star kappa =
  upper_value threshold_law ((kappa - 3%:R) / 2%:R) 0.
Proof. by rewrite universality_alpha_starE cone_shiftE. Qed.

(* V_c(q) <= alpha*(kappa) for every admissible q. *)
Lemma condition_kappa_V_le_star (C : R) (q : measurableTypeR R -> R) :
  clip_admissible C q -> V q <= universality_alpha_star kappa.
Proof.
move=> hq; have [B B0 qB] := clip_admissible_bounded hq.
case: (hq) => mq [t t0 hb].
have q0 : forall x, 0 <= q x.
  by move=> x; have /andP[h _] := hb x; exact: le_trans t0 h.
have iq := clip_integrable_bounded threshold_law2 mq qB.
have iq2 := clip_integrable_sq threshold_law2 mq qB.
have hs := upper_variational_sym_le threshold_law2 threshold_law_sym c1 mq q0 iq2.
have hD := upper_form_ge0 c1 iq iq2.
have a0 := universality_alpha_star_gt0 kappa k1.
rewrite -astarE in hs; rewrite /clip_objective.
move: hs hD a0.
move: (\int[threshold_law]_x ((x : R) * q x)) (\int[threshold_law]_x (q x ^+ 2))
  (\int[threshold_law]_x q x) (universality_alpha_star kappa) => A Q M a.
move=> hs hD a0.
have -> : 2 * A - Q - c * M ^+ 2 = 2 * A - (Q + c * M ^+ 2) by ring.
move: hs hD; move: (Q + c * M ^+ 2) => D hs hD.
have := sqr_ge0 (A - a).
by nra.
Qed.

Lemma condition_kappa_alpha_le_star (C : R) : 1 < C ->
  alpha C <= universality_alpha_star kappa.
Proof.
move=> C1; rewrite -(condition_kappa_opt_value C kappa C1 k1).
apply: (condition_kappa_V_le_star C); apply: clip_profile_admissible.
  exact: ltW.
exact: ltW (condition_kappa_level_gt0 C kappa C1 k1).
Qed.

(* E |X| <= 1 for the semicircle law. *)
Lemma threshold_abs_le1 : \int[threshold_law]_x `|(x : R)| <= 1.
Proof.
have ia : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => `|(x : R)|)).
  apply: (integrable_quad_bound threshold_law2 (a := 1) (b := 1)).
    exact: normr_measurable.
  move=> x; rewrite normr_id.
  rewrite -[(x : R) ^+ 2]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
have i0 : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun _ : measurableTypeR R => (2^-1 : R))).
  apply: (clip_integrable_bounded threshold_law2 (B := 2^-1));
    [exact: measurable_cst | by move=> x; rewrite ger0_norm // invr_ge0 ler0n].
have i2 : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => 2^-1 * (x : R) ^+ 2)).
  apply: (integrable_quad_bound threshold_law2 (a := 0) (b := 2^-1)).
    by apply: measurable_funM; [exact: measurable_cst | exact: measurable_funX].
  move=> x; rewrite add0r ger0_norm //.
  by rewrite mulr_ge0 ?invr_ge0 ?ler0n ?sqr_ge0.
have i3 := integrableD measurableT i0 i2.
have i3' : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => 2^-1 + 2^-1 * (x : R) ^+ 2)).
  by move: i3; apply: eq_integrable => // x _ /=; rewrite EFinD.
apply: (@le_trans _ _ (\int[threshold_law]_x (2^-1 + 2^-1 * (x : R) ^+ 2))).
  apply: le_Rintegral => // x _.
  rewrite -[(x : R) ^+ 2]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
rewrite RintegralD // Rintegral_prob_cst RintegralZl ?threshold_second //.
  exact: threshold_law2.
have h2 : (2%:R : R) != 0 by rewrite pnatr_eq0.
have e : (2^-1 : R) + 2^-1 / 2%:R = 3%:R / 4%:R by field.
by rewrite e ler_pdivrMr ?ltr0n // mul1r ler_nat.
Qed.

(* alpha(C, kappa) <= (C - 1)^2 / (1 + c). *)
Lemma condition_kappa_alpha_near1 (C : R) : 1 < C ->
  alpha C <= (C - 1) ^+ 2 / (1 + c).
Proof.
move=> C1.
have t0 := condition_kappa_level_gt0 C kappa C1 k1.
rewrite -(condition_kappa_opt_value C kappa C1 k1) /condition_kappa_opt.
set a := (kappa - 3%:R) / 2%:R * condition_kappa_mean C kappa.
set ts := condition_kappa_level C kappa in t0 *.
have [B B0 qB] := clip_profile_bounded a (ltW C1) (ltW t0).
have mq := measurable_clip_profile C a ts.
set q := clip_profile C a ts in qB mq *.
have iq := clip_integrable_bounded threshold_law2 mq qB.
have iq2 := clip_integrable_sq threshold_law2 mq qB.
have ixq := clip_integrable_id_bounded threshold_law2 mq qB.
have hb x : ts <= q x <= C * ts := clip_profile_bounds a (ltW C1) (ltW t0) x.
have ic : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun _ : measurableTypeR R => ts)).
  apply: (clip_integrable_bounded threshold_law2 (B := ts));
    [exact: measurable_cst | by move=> x; rewrite ger0_norm // ltW].
have hM : ts <= \int[threshold_law]_x q x.
  rewrite -[X in X <= _](Rintegral_prob_cst threshold_law).
  by apply: le_Rintegral => // x _; have /andP[] := hb x.
have hJ := Rintegral_sqr_le iq iq2.
(* E[X q] = E[X (q - t_s)] <= (C - 1) t_s E |X| <= (C - 1) t_s *)
have ix := integrable_idR threshold_law2.
have itx : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => ts * (x : R))).
  by move: (integrableZl measurableT ts ix); apply: eq_integrable => // x _ /=; rewrite EFinM.
have ia : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => `|(x : R)|)).
  apply: (integrable_quad_bound threshold_law2 (a := 1) (b := 1)).
    exact: normr_measurable.
  move=> x; rewrite normr_id.
  rewrite -[(x : R) ^+ 2]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
have mr : measurable_fun [set: measurableTypeR R]
    (fun x : measurableTypeR R => q x - ts).
  by apply: measurable_funB => //; exact: measurable_cst.
have rB : forall x : measurableTypeR R, `|q x - ts| <= B + ts.
  move=> x; apply: le_trans (ler_normB _ _) _; apply: lerD => //.
  by rewrite ger0_norm // ltW.
have ixr := clip_integrable_id_bounded threshold_law2 mr rB.
have hX : \int[threshold_law]_x ((x : R) * q x) <= (C - 1) * ts.
  have -> : \int[threshold_law]_x ((x : R) * q x) =
      \int[threshold_law]_x ((x : R) * (q x - ts)) +
      \int[threshold_law]_x (ts * (x : R)).
    by rewrite -RintegralD //; apply: eq_Rintegral => x _; ring.
  rewrite RintegralZl // (Rintegral_id_sym threshold_law2 threshold_law_sym).
  rewrite mulr0 addr0.
  have iaC : threshold_law.-integrable [set: measurableTypeR R]
      (EFin \o (fun x : measurableTypeR R => (C - 1) * ts * `|(x : R)|)).
    by move: (integrableZl measurableT ((C - 1) * ts) ia);
      apply: eq_integrable => // x _ /=; rewrite EFinM.
  apply: (@le_trans _ _
    (\int[threshold_law]_x ((C - 1) * ts * `|(x : R)|))).
    apply: le_Rintegral => // x _.
    have /andP[h1 h2] := hb x.
    have r0 : 0 <= q x - ts by rewrite subr_ge0.
    have r1 : q x - ts <= (C - 1) * ts by rewrite mulrBl mul1r lerD2r.
    have := ler_norm (x : R); have := normr_ge0 (x : R).
    by nra.
  rewrite RintegralZl //.
  have Ct0 : 0 <= (C - 1) * ts by rewrite mulr_ge0 // ?subr_ge0 ?ltW.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l // threshold_abs_le1.
have c10 : 0 < 1 + (kappa - 3%:R) / 2%:R by rewrite -ltrBlDl sub0r.
rewrite ler_pdivlMr // /clip_objective.
move: hM hJ hX.
move: (\int[threshold_law]_x ((x : R) * q x)) (\int[threshold_law]_x q x)
  (\int[threshold_law]_x (q x ^+ 2)) => X M Q hM hJ hX.
have h1 : (1 + (kappa - 3%:R) / 2%:R) * ts ^+ 2 <=
    Q + (kappa - 3%:R) / 2%:R * M ^+ 2.
  have : ts ^+ 2 <= M ^+ 2 by rewrite lerXn2r ?nnegrE ?(ltW t0) //; apply: le_trans hM; exact: ltW.
  by move=> h; nra.
have := sqr_ge0 ((1 + (kappa - 3%:R) / 2%:R) * ts - (C - 1)).
by nra.
Qed.

(* The level of the optimal profile: t_s < 2 sqrt 2 / (C - 1). *)
Lemma condition_kappa_level_lt (C : R) : 1 < C ->
  condition_kappa_level C kappa < 2%:R * sq2 / (C - 1).
Proof.
move=> C1.
have [_ us _ _] := condition_kappa_u_spec C kappa C1 k1.
have /andP[le _] := condition_kappa_ell_spec C kappa C1 k1.
rewrite /condition_kappa_level ltr_pM2r ?invr_gt0 ?subr_gt0 //.
by move: us le; lra.
Qed.

(* A Lipschitz bound: for 1 < C <= C', with t' the level at C',
   alpha(C') - alpha(C) <= 2 (C' - C) t' (1 + (1 + |c|) C' t'). *)
Lemma condition_kappa_alpha_lip (C C' : R) : 1 < C -> C <= C' ->
  alpha C' - alpha C <=
  2%:R * ((C' - C) * condition_kappa_level C' kappa) *
  (1 + (1 + `|c|) * C' * condition_kappa_level C' kappa).
Proof.
move=> C1 CC; have C1' := lt_le_trans C1 CC.
have t0 := condition_kappa_level_gt0 C' kappa C1' k1.
rewrite -(condition_kappa_opt_value C' kappa C1' k1) /condition_kappa_opt.
set a := (kappa - 3%:R) / 2%:R * condition_kappa_mean C' kappa.
set t := condition_kappa_level C' kappa in t0 *.
have hb x : t <= clip_profile C' a t x <= C' * t :=
  clip_profile_bounds a (ltW C1') (ltW t0) x.
have mq := measurable_clip_profile C' a t.
pose qt x := Num.min (clip_profile C' a t x) (C * t).
have mqt : measurable_fun [set: measurableTypeR R] qt.
  by apply: measurable_minr => //; exact: measurable_cst.
have Ct : t <= C * t by rewrite -[X in X <= _]mul1r ler_wpM2r // ?ltW.
have hqt x : t <= qt x <= C * t.
  have /andP[h1 _] := hb x.
  by rewrite /qt le_min h1 Ct ge_min lexx orbT.
have qtB : forall x : measurableTypeR R, `|qt x| <= C * t.
  move=> x; have /andP[h1 h2] := hqt x.
  by rewrite ger0_norm // (le_trans (ltW t0) h1).
pose h x := clip_profile C' a t x - qt x.
have mh : measurable_fun [set: measurableTypeR R] h by exact: measurable_funB.
have hh x : 0 <= h x <= (C' - C) * t.
  have /andP[h1 h2] := hb x; rewrite /h /qt.
  case: (leP (clip_profile C' a t x) (C * t)) => hl.
    by rewrite subrr lexx /= mulr_ge0 // ?subr_ge0 // ltW.
  by rewrite subr_ge0 (ltW hl) /= mulrBl lerD2r.
have hB : forall x : measurableTypeR R, `|h x| <= (C' - C) * t.
  by move=> x; have /andP[h1 h2] := hh x; rewrite ger0_norm.
have eq' : clip_profile C' a t = (fun x => qt x + h x).
  by apply/funext => x; rewrite /h addrC subrK.
rewrite eq' (clip_objective_add threshold_law2 ((kappa - 3%:R) / 2%:R) mqt mh qtB hB).
have ub : clip_objective threshold_law ((kappa - 3%:R) / 2%:R) qt <= alpha C.
  apply: condition_kappa_alpha_ub => //; split => //; exists t => //; exact: ltW.
have ih := clip_integrable_bounded threshold_law2 mh hB.
have ih2 := clip_integrable_sq threshold_law2 mh hB.
have Qh := upper_form_ge0 c1 ih ih2.
have iqt := clip_integrable_bounded threshold_law2 mqt qtB.
have ic (r : R) : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun _ : measurableTypeR R => r)).
  apply: (clip_integrable_bounded threshold_law2 (B := `|r|));
    [exact: measurable_cst | by move=> x].
have hM : 0 <= \int[threshold_law]_y qt y <= C * t.
  apply/andP; split.
    apply: Rintegral_ge0 => x _; have /andP[h1 _] := hqt x.
    exact: le_trans (ltW t0) h1.
  rewrite -[X in _ <= X](Rintegral_prob_cst threshold_law).
  by apply: le_Rintegral => // x _; have /andP[] := hqt x.
set M := \int[threshold_law]_y qt y in hM *.
have ires := clip_integrable_res_mul threshold_law2 (c * M) mqt mh qtB hB.
have ia : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => `|(x : R)|)).
  apply: (integrable_quad_bound threshold_law2 (a := 1) (b := 1)).
    exact: normr_measurable.
  move=> x; rewrite normr_id.
  rewrite -[(x : R) ^+ 2]real_normK ?num_real //.
  by have := sqr_ge0 (`|(x : R)| - 1); nra.
set d := (C' - C) * t.
have d0 : 0 <= d by rewrite /d mulr_ge0 // ?subr_ge0 // ltW.
set K0 := (1 + `|c|) * (C * t).
have iad : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => d * `|(x : R)|)).
  by move: (integrableZl measurableT d ia).
have iaK : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => d * `|(x : R)| + d * K0)).
  have := integrableD measurableT iad (ic (d * K0)).
  by apply: eq_integrable => // x _ /=; rewrite EFinD.
have hR : \int[threshold_law]_x (((x : R) - c * M - qt x) * h x) <= d * (1 + K0).
  apply: (@le_trans _ _ (\int[threshold_law]_x (d * `|(x : R)| + d * K0))).
    apply: le_Rintegral => // x _.
    have /andP[h0 h1] := hh x; have /andP[q0 q1] := hqt x.
    have nc : `|c * M| <= `|c| * (C * t).
      by rewrite normrM ler_wpM2l // ger0_norm; [case/andP: hM | case/andP: hM].
    have nx : `|(x : R) - c * M - qt x| <= `|(x : R)| + K0.
      apply: le_trans (ler_normB _ _) _.
      apply: le_trans (lerD (ler_normB _ _) (lexx _)) _.
      by have := qtB x; rewrite /K0; nra.
    have h1' : h x <= d := h1.
    have Ctp : 0 <= C * t by rewrite mulr_ge0 // ltW // (lt_trans ltr01 C1).
    have K0p : 0 <= K0 by rewrite /K0 mulr_ge0 // addr_ge0.
    apply: le_trans (ler_norm _) _; rewrite normrM (ger0_norm h0).
    have := normr_ge0 ((x : R) - c * M - qt x).
    have := normr_ge0 (x : R).
    nra.
  rewrite RintegralD // Rintegral_prob_cst RintegralZl //.
  have hx := threshold_abs_le1.
  rewrite mulrDr mulr1 lerD2r.
  exact: ler_piMr.
have hK : d * (1 + K0) <= d * (1 + (1 + `|c|) * C' * t).
  apply: ler_wpM2l => //.
  by rewrite lerD2l /K0 mulrA ler_wpM2r ?(ltW t0) // ler_wpM2l.
by move: hR Qh ub hK; lra.
Qed.

(* C |-> alpha(C, kappa) is increasing on (1, oo): adding to the optimal
   profile at C a small multiple of the indicator of a half-line above
   its upper cutoff gives an admissible profile at C' with a larger value. *)
Lemma condition_kappa_alpha_lt (C C' : R) : 1 < C -> C < C' ->
  alpha C < alpha C'.
Proof.
move=> C1 CC; have C1' := lt_trans C1 CC.
have t0 := condition_kappa_level_gt0 C kappa C1 k1.
have [u0 us _ _] := condition_kappa_u_spec C kappa C1 k1.
have uE := condition_kappa_uE C kappa C1 k1.
have hmean := condition_kappa_opt_mean C kappa C1 k1.
rewrite -(condition_kappa_opt_value C kappa C1 k1).
have hq x : condition_kappa_level C kappa <= condition_kappa_opt C kappa x <=
    C * condition_kappa_level C kappa :=
  clip_profile_bounds _ (ltW C1) (ltW t0) x.
have mq := measurable_clip_profile C (c * condition_kappa_mean C kappa)
  (condition_kappa_level C kappa).
have hqu x : condition_kappa_u C kappa < x ->
    condition_kappa_opt C kappa x = C * condition_kappa_level C kappa.
  move=> ux; rewrite /condition_kappa_opt /clip_profile.
  have ct : condition_kappa_level C kappa <= C * condition_kappa_level C kappa.
    by rewrite -[X in X <= _]mul1r ler_wpM2r // ?ltW.
  have xa : C * condition_kappa_level C kappa <
      x - c * condition_kappa_mean C kappa by rewrite ltrBrDr -uE.
  have -> : maxr (x - c * condition_kappa_mean C kappa)
      (condition_kappa_level C kappa) = x - c * condition_kappa_mean C kappa.
    by apply/max_idPl; exact: le_trans ct (ltW xa).
  by apply/min_idPr; exact: ltW.
set q := condition_kappa_opt C kappa in hmean hq hqu *.
set u := condition_kappa_u C kappa in u0 us uE hqu *.
set t := condition_kappa_level C kappa in t0 uE hq hqu mq *.
set mus := condition_kappa_mean C kappa in uE hmean mq *.
pose v := (u + sq2) / 2%:R.
have uv : u < v by rewrite /v; lra.
have vs : v < sq2 by rewrite /v; lra.
pose A := `]v, +oo[%classic : set (measurableTypeR R).
have mA : measurable A by exact: measurable_itv.
have PA : (0 < threshold_law A)%E.
  have s2 : sq2 != 0 by rewrite gt_eqF // kappa_sq2_gt0.
  have s2abs : `|sq2| = sq2 by rewrite ger0_norm // ltW // kappa_sq2_gt0.
  by apply: (semicircle_prob_gt0 s2); rewrite s2abs.
have fA : threshold_law A \is a fin_num.
  by rewrite ge0_fin_numE // (le_lt_trans (probability_le1 _ mA) (ltry 1)).
set pA := fine (threshold_law A).
have pA0 : 0 < pA.
  by rewrite /pA fine_gt0 // PA /= (le_lt_trans (probability_le1 _ mA) (ltry 1)).
have pA1 : pA <= 1 by rewrite -lee_fin /pA fineK // probability_le1.
pose K := 1 + `|c|.
have K0 : 0 < K by rewrite /K; have := normr_ge0 c; lra.
pose eps := Num.min ((C' - C) * t) ((v - u) / K).
have e0 : 0 < eps.
  by rewrite /eps lt_min mulr_gt0 ?subr_gt0 // divr_gt0 // subr_gt0.
have e1 : eps <= (C' - C) * t by rewrite /eps ge_min lexx.
have e2 : eps * K <= v - u by rewrite -ler_pdivlMr // /eps ge_min lexx orbT.
pose h (x : measurableTypeR R) : (R : realType) := eps * numfun.indic A x.
have mh : measurable_fun [set: measurableTypeR R] h.
  by apply: measurable_funM; [exact: measurable_cst | exact: measurable_indic].
have hge x : 0 <= h x by rewrite /h mulr_ge0 ?(ltW e0).
have hle x : h x <= eps.
  rewrite /h /numfun.indic; case: (x \in A) => /=; rewrite ?mulr1 ?mulr0 //.
  exact: ltW.
have hB : forall x : measurableTypeR R, `|h x| <= eps.
  by move=> x; rewrite ger0_norm.
have qB : forall x : measurableTypeR R, `|q x| <= C * t.
  move=> x; have /andP[h1 h2] := hq x.
  by rewrite ger0_norm // (le_trans (ltW t0) h1).
have adm : clip_admissible C' (fun x => q x + h x).
  split; first exact: measurable_funD.
  exists t; first exact: ltW.
  move=> x /=; have /andP[h1 h2] := hq x; have h3 := hge x; have h4 := hle x.
  apply/andP; split; first by lra.
  by move: e1; lra.
have ub := condition_kappa_alpha_ub C' (fun x => q x + h x) C1' adm.
apply: lt_le_trans ub.
rewrite (clip_objective_add threshold_law2 c mq mh qB hB).
rewrite -addrA ltrDl.
have hM : \int[threshold_law]_y clip_profile C (c * mus) t y = mus := hmean.
rewrite hM.
have hqu' x : u < x -> clip_profile C (c * mus) t x = C * t := hqu x.
have iA : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => numfun.indic A x : R)) by exact: integrable_indic.
have EA : \int[threshold_law]_x (numfun.indic A x : R) = pA.
  by rewrite /Rintegral integral_indic // setIT.
have Eh : \int[threshold_law]_x h x = eps * pA by rewrite /h RintegralZl // EA.
have Eh2 : \int[threshold_law]_x (h x ^+ 2) = eps ^+ 2 * pA.
  rewrite -EA -RintegralZl //; apply: eq_Rintegral => x _.
  rewrite /h exprMn /numfun.indic.
  by case: (x \in A) => /=; rewrite ?expr1n ?expr0n.
rewrite Eh Eh2.
have iZ : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => eps * (v - u) * numfun.indic A x)).
  have -> : (EFin \o (fun x : measurableTypeR R =>
      eps * (v - u) * numfun.indic A x)) =
      (fun x => (eps * (v - u))%:E * (EFin \o numfun.indic A) x)%E.
    by apply/funext => x /=; rewrite EFinM.
  by apply: integrableZl.
have ires := clip_integrable_res_mul threshold_law2 (c * mus) mq mh qB hB.
have I1 : eps * (v - u) * pA <= \int[threshold_law]_x
    (((x : R) - c * mus - clip_profile C (c * mus) t x) * h x).
  rewrite -EA -RintegralZl //; apply: le_Rintegral => //.
  move=> x _; rewrite /h /numfun.indic; case: (boolP (x \in A)) => xA /=.
    have xv : v < x by move: xA; rewrite inE /A /= in_itv /= andbT.
    rewrite (hqu' x (lt_trans uv xv)).
    have : v - u <= x - c * mus - C * t by move: uv xv; rewrite uE; lra.
    by have := e0; nra.
  by rewrite !mulr0.
have cX : c * (eps * pA) ^+ 2 <= `|c| * (eps ^+ 2 * pA).
  apply: le_trans (ler_wpM2r (sqr_ge0 _) (ler_norm c)) _.
  rewrite ler_wpM2l // exprMn ler_wpM2l ?sqr_ge0 // expr2.
  exact: ler_piMr (ltW pA0) pA1.
have e3 : eps * pA * (eps * K) <= eps * pA * (v - u).
  by rewrite ler_wpM2l // mulr_ge0 // ltW.
have pos : 0 < eps * (v - u) * pA by rewrite !mulr_gt0 // subr_gt0.
by move: I1 cX e3 pos; rewrite /K; lra.
Qed.

(* A local Lipschitz bound: for 1 < a <= b with C <= b <= C + 1,
   alpha(b) - alpha(a) <= L (b - a), where L depends only on C and kappa. *)
Lemma condition_kappa_alpha_lip_loc (C : R) : 1 < C ->
  exists2 L : R, 0 < L & forall a b : R, 1 < a -> a <= b -> C <= b ->
    b <= C + 1 -> alpha b - alpha a <= L * (b - a).
Proof.
move=> C1.
have s20 := kappa_sq2_gt0.
pose T := 2%:R * sq2 / (C - 1).
have T0 : 0 < T by rewrite /T divr_gt0 ?mulr_gt0 // subr_gt0.
pose X := 1 + `|c|.
have X0 : 0 < X by rewrite /X; have := normr_ge0 c; lra.
have C0 : 0 < C + 1 by have := C1; lra.
have XC : 0 < X * (C + 1) by exact: mulr_gt0.
have XCT : 0 < X * (C + 1) * T by exact: mulr_gt0.
have T2 : 0 < 2%:R * T by exact: mulr_gt0.
have P1 : 0 < 1 + X * (C + 1) * T by lra.
exists (2%:R * T * (1 + X * (C + 1) * T)); first exact: mulr_gt0.
move=> a b a1 ab Cb bC.
have b1 : 1 < b := lt_le_trans a1 ab.
have tb0 := condition_kappa_level_gt0 b kappa b1 k1.
have tbT : condition_kappa_level b kappa <= T.
  apply: ltW; apply: lt_le_trans (condition_kappa_level_lt b b1) _.
  by rewrite /T ler_pM2l ?mulr_gt0 // lef_pV2 ?posrE ?subr_gt0 // lerD2r.
apply: le_trans (condition_kappa_alpha_lip a b a1 ab) _.
set tb := condition_kappa_level b kappa in tb0 tbT *.
have ba : 0 <= b - a by rewrite subr_ge0.
have b0 : 0 <= b by have := b1; lra.
have h1 : X * b * tb <= X * (C + 1) * T.
  rewrite -!mulrA ler_wpM2l ?(ltW X0) //.
  exact: ler_pM b0 (ltW tb0) bC tbT.
have h2 : 2%:R * ((b - a) * tb) <= 2%:R * ((b - a) * T).
  by rewrite ler_wpM2l // ler_wpM2l.
have h3 : 0 <= X * b * tb.
  by apply: mulr_ge0; [exact: mulr_ge0 (ltW X0) b0 | exact: ltW].
have h4 : 0 <= 2%:R * ((b - a) * tb) by rewrite mulr_ge0 // mulr_ge0 // ltW.
have h5 : 1 + X * b * tb <= 1 + X * (C + 1) * T by rewrite lerD2l.
have h6 : 0 <= 1 + X * b * tb by lra.
apply: le_trans (ler_pM h4 h6 h2 h5) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* C |-> alpha(C, kappa) is continuous on (1, oo). *)
Lemma condition_kappa_alpha_cont (C : R) : 1 < C ->
  forall e : R, 0 < e -> exists2 delta : R, 0 < delta &
    forall C' : R, 1 < C' -> `|C' - C| < delta -> `|alpha C' - alpha C| < e.
Proof.
move=> C1 e e0.
have [L L0 hL] := condition_kappa_alpha_lip_loc C C1.
exists (Num.min 1 (e / L)); first by rewrite lt_min ltr01 divr_gt0.
move=> C' C1' hd.
have hd1 : `|C' - C| < 1 by apply: lt_le_trans hd _; rewrite ge_min lexx.
have hdL : `|C' - C| * L < e.
  by rewrite -ltr_pdivlMr // (lt_le_trans hd) // ge_min lexx orbT.
have [CC|CC] := leP C C'.
  have m := condition_kappa_alpha_le C C' C1 CC.
  rewrite ger0_norm ?subr_ge0 // in hd1 hdL.
  have k : alpha C' - alpha C <= L * (C' - C).
    by apply: hL => //; lra.
  by rewrite ger0_norm ?subr_ge0 //; lra.
have m := condition_kappa_alpha_le C' C C1' (ltW CC).
rewrite ler0_norm ?subr_le0 ?(ltW CC) // in hd1 hdL.
have k : alpha C - alpha C' <= L * (C - C').
  by apply: hL => //; [exact: ltW | lra].
by rewrite ler0_norm ?subr_le0 //; lra.
Qed.

(* alpha(C, kappa) tends to 0 as C decreases to 1. *)
Lemma condition_kappa_alpha_lim1 (e : R) : 0 < e ->
  exists2 delta : R, 0 < delta &
    forall C : R, 1 < C -> C < 1 + delta -> alpha C < e.
Proof.
move=> e0.
have c10 : 0 < 1 + c by have := c1; lra.
exists (Num.min 1 (e * (1 + c))); first by rewrite lt_min ltr01 mulr_gt0.
move=> C C1 Cd.
have m1 : Num.min 1 (e * (1 + c)) <= 1 by rewrite ge_min lexx.
have m2 : Num.min 1 (e * (1 + c)) <= e * (1 + c) by rewrite ge_min lexx orbT.
have h0 : 0 < C - 1 by rewrite subr_gt0.
have h1 : C - 1 < 1 by move: Cd m1; lra.
have h2 : C - 1 < e * (1 + c) by move: Cd m2; lra.
apply: le_lt_trans (condition_kappa_alpha_near1 C C1) _.
rewrite ltr_pdivrMr //.
by nra.
Qed.

(* Two integrable functions that agree on ]-sqrt 2, sqrt 2[ have the same
   integral against the semicircle law. *)
Lemma threshold_integral_support (f g : R -> R) :
  threshold_law.-integrable [set: R] (EFin \o f) ->
  threshold_law.-integrable [set: R] (EFin \o g) ->
  (forall x : R, x ^+ 2 < 2%:R -> f x = g x) ->
  \int[threshold_law]_x f x = \int[threshold_law]_x g x.
Proof.
move=> fi gi fg.
have s2 : sq2 != 0 by rewrite gt_eqF // kappa_sq2_gt0.
have H : forall x, g x * semicircle_pdf sq2 x = f x * semicircle_pdf sq2 x.
  move=> x; have [x2|x2] := ltP (x ^+ 2) 2%:R; first by rewrite fg.
  by rewrite semicircle_pdf_out // ?mulr0 // sqr_sqrtr // ler0n.
have Ef := @semicircle_integral_eq _ sq2 f f fi (fun x => erefl).
have Eg := @semicircle_integral_eq _ sq2 f g gi H.
by rewrite Ef Eg.
Qed.

(* alpha(C, kappa) tends to alpha*(kappa) as C tends to infinity: with w the
   cutoff of alpha*(kappa) and B = sqrt 2 + |w|, the profile
   eps + min((x - w)_+, B) is admissible for C >= 2 + B / eps, and its value
   is alpha*(kappa) - (1 + c) (eps^2 + 2 eps m(w)). *)
Lemma condition_kappa_alpha_liminf (e : R) : 0 < e ->
  exists2 C0 : R, 1 < C0 & forall C : R, C0 <= C ->
    universality_alpha_star kappa - alpha C < e.
Proof.
move=> e0.
have c10 : 0 < 1 + c by have := c1; lra.
set w := upper_cutoff threshold_law c 0.
pose p (x : measurableTypeR R) : (R : realType) := Num.max ((x : R) - w) 0.
have p0 x : 0 <= p x by rewrite /p le_max lexx orbT.
have mp : measurable_fun [set: measurableTypeR R] p.
  apply: measurable_maxr; last exact: measurable_cst.
  by apply: measurable_funB => //; exact: measurable_cst.
set m := upper_moment threshold_law 1 w.
set s := upper_moment threshold_law 2 w.
have m0 : 0 <= m by exact: upper_moment_ge0.
have astar : universality_alpha_star kappa = s + c * m ^+ 2 by rewrite astarE.
have p2i : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => p x ^+ 2)).
  exact: (integrable_upper_pow threshold_law2 w (isT : (2 <= 2)%N)).
have p1i : threshold_law.-integrable [set: measurableTypeR R] (EFin \o p).
  have := integrable_upper_pow threshold_law2 w (isT : (1 <= 2)%N).
  by apply: eq_integrable => // x _ /=; rewrite expr1.
have Ep : \int[threshold_law]_x p x = m.
  by apply: eq_Rintegral => x _; rewrite /p expr1.
have Ep2 : \int[threshold_law]_x (p x ^+ 2) = s by [].
have ix := integrable_idR threshold_law2.
have xpi : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => (x : R) * p x)).
  have mx : measurable_fun [set: measurableTypeR R]
      (fun x : measurableTypeR R => (x : (R : realType))) by exact: measurable_id.
  exact: (integrable_mul_sqr mx mp threshold_law2 p2i).
have Exp : \int[threshold_law]_x ((x : R) * p x) = universality_alpha_star kappa.
  rewrite astarE -(@upper_variational_attained _ threshold_law threshold_law2 c 0 c1).
  by apply: eq_Rintegral => x _; rewrite addr0.
have Ex : \int[threshold_law]_x (x : R) = 0.
  exact: (Rintegral_id_sym threshold_law2 threshold_law_sym).
have ic (r : R) : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun _ : measurableTypeR R => r)).
  apply: (clip_integrable_bounded threshold_law2 (B := `|r|));
    [exact: measurable_cst | by move=> x].
pose B := sq2 + `|w|.
have B0 : 0 < B by rewrite /B; have := normr_ge0 w; have := kappa_sq2_gt0; lra.
pose K := (1 + c) * (1 + 2%:R * m).
have m1 : 0 < 1 + 2%:R * m by lra.
have K0 : 0 < K by rewrite /K mulr_gt0.
have K20 : 0 < 2%:R * K by rewrite mulr_gt0.
pose eps := Num.min 1 (e / (2%:R * K)).
have ep0 : 0 < eps by rewrite /eps lt_min ltr01 divr_gt0.
have ep1 : eps <= 1 by rewrite /eps ge_min lexx.
have epK : eps * (2%:R * K) <= e by rewrite -ler_pdivlMr // /eps ge_min lexx orbT.
have Be0 : 0 <= B / eps by rewrite divr_ge0 // ltW.
exists (2%:R + B / eps); first by lra.
move=> C CC.
have C1 : 1 < C by lra.
have BeC : eps + B <= C * eps.
  have h : (2%:R + B / eps) * eps <= C * eps by rewrite ler_wpM2r // ltW.
  rewrite mulrDl divfK ?gt_eqF // in h.
  by lra.
pose q (x : measurableTypeR R) : (R : realType) := eps + Num.min (p x) B.
have mq : measurable_fun [set: measurableTypeR R] q.
  apply: measurable_funD; first exact: measurable_cst.
  by apply: measurable_minr => //; exact: measurable_cst.
have hq x : eps <= q x <= C * eps.
  rewrite /q; apply/andP; split.
    by rewrite lerDl le_min p0 /= ltW.
  by apply: le_trans BeC; rewrite lerD2l ge_min lexx orbT.
have qB : forall x : measurableTypeR R, `|q x| <= C * eps.
  move=> x; have /andP[h1 h2] := hq x.
  by rewrite ger0_norm // (le_trans (ltW ep0) h1).
have adm : clip_admissible C q.
  by split => //; exists eps; [exact: ltW | exact: hq].
have ub := condition_kappa_alpha_ub C q C1 adm.
have supp (x : R) : x ^+ 2 < 2%:R -> q x = eps + p x.
  move=> x2; rewrite /q; congr (_ + _); apply/min_idPl.
  have hx : `|x| < sq2 by rewrite -(sqrtr_sqr x) ltr_sqrt // ltr0n.
  have h1 : p x <= `|x| + `|w|.
    rewrite /p ge_max (le_trans (ler_norm _) (ler_normB _ _)) /=.
    by rewrite addr_ge0.
  by rewrite /B; move: h1 hx; lra.
have iq := clip_integrable_bounded threshold_law2 mq qB.
have iq2 := clip_integrable_sq threshold_law2 mq qB.
have ixq := clip_integrable_id_bounded threshold_law2 mq qB.
have ipe : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => eps + p x)).
  have := integrableD measurableT (ic eps) p1i.
  by apply: eq_integrable => // x _ /=; rewrite EFinD.
have I1 : \int[threshold_law]_x q x = eps + m.
  rewrite (threshold_integral_support q (fun x => eps + p x) iq ipe supp).
  by rewrite RintegralD // Rintegral_prob_cst Ep.
have i2p : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => 2%:R * eps * p x)).
  by move: (integrableZl measurableT (2%:R * eps) p1i).
have i3p : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => eps ^+ 2 + 2%:R * eps * p x)).
  have := integrableD measurableT (ic (eps ^+ 2)) i2p.
  by apply: eq_integrable => // x _ /=; rewrite EFinD.
have ipe2 : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => (eps + p x) ^+ 2)).
  have := integrableD measurableT i3p p2i.
  by apply: eq_integrable => // x _ /=; rewrite -EFinD; congr EFin; ring.
have supp2 (x : R) : x ^+ 2 < 2%:R -> q x ^+ 2 = (eps + p x) ^+ 2.
  by move=> x2; rewrite supp.
have I2 : \int[threshold_law]_x (q x ^+ 2) = eps ^+ 2 + 2%:R * eps * m + s.
  rewrite (threshold_integral_support (fun x => q x ^+ 2)
    (fun x => (eps + p x) ^+ 2) iq2 ipe2 supp2).
  have -> : (fun x => (eps + p x) ^+ 2) =
      (fun x => (eps ^+ 2 + 2%:R * eps * p x) + p x ^+ 2).
    by apply/funext => x; ring.
  by rewrite RintegralD // RintegralD // Rintegral_prob_cst RintegralZl // Ep.
have iex : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x : measurableTypeR R => eps * (x : R))).
  by move: (integrableZl measurableT eps ix).
have ixpe : threshold_law.-integrable [set: measurableTypeR R]
    (EFin \o (fun x => (x : R) * (eps + p x))).
  have := integrableD measurableT iex xpi.
  by apply: eq_integrable => // x _ /=; rewrite -EFinD; congr EFin; ring.
have supp3 (x : R) : x ^+ 2 < 2%:R -> x * q x = x * (eps + p x).
  by move=> x2; rewrite supp.
have I3 : \int[threshold_law]_x ((x : R) * q x) = universality_alpha_star kappa.
  rewrite (threshold_integral_support (fun x => x * q x)
    (fun x => x * (eps + p x)) ixq ixpe supp3).
  have -> : (fun x => x * (eps + p x)) = (fun x => eps * x + x * p x).
    by apply/funext => x; ring.
  by rewrite RintegralD // RintegralZl // Ex mulr0 add0r Exp.
have Vq : V q = universality_alpha_star kappa -
    (1 + c) * (eps ^+ 2 + 2%:R * eps * m).
  by rewrite /clip_objective I1 I2 I3 astar; ring.
rewrite Vq in ub.
have h1 : eps ^+ 2 <= eps by rewrite expr2 ler_piMr // ltW.
have h2 : (1 + c) * (eps ^+ 2 + 2%:R * eps * m) <=
    (1 + c) * (eps + 2%:R * eps * m) by rewrite ler_wpM2l ?(ltW c10) // lerD2r.
have h3 : (1 + c) * (eps + 2%:R * eps * m) = eps * K by rewrite /K; ring.
have h4 : 0 < eps * K by rewrite mulr_gt0.
by move: ub h2 h3 h4 epK; lra.
Qed.

(* 0 < alpha(C, kappa) < alpha*(kappa) for C > 1. *)
Lemma condition_kappa_alpha_lt_star (C : R) : 1 < C ->
  alpha C < universality_alpha_star kappa.
Proof.
move=> C1; have C2 : C < C + 1 by rewrite ltrDl.
apply: lt_le_trans (condition_kappa_alpha_lt C (C + 1)%R C1 C2) _.
by apply: condition_kappa_alpha_le_star; lra.
Qed.

(* Interface I3, in the forms of condition_kappa_sat and
   condition_kappa_unsat: below alpha(C', kappa) there is a smaller Cm with
   alpha' < alpha(Cm, kappa); above it there is a larger Cp with
   alpha(Cp, kappa) < alpha'; and alpha(C', kappa) < 1/2.
   ConditionKappaTheorem.v supplies the three lemmas to
   condition_kappa_statement_of_I3. *)
Lemma condition_kappa_alpha_left (C' alpha' : R) : 1 < C' ->
  alpha' < alpha C' -> exists2 Cm : R, 1 < Cm < C' & alpha' < alpha Cm.
Proof.
move=> C1 aC.
have e0 : 0 < alpha C' - alpha' by rewrite subr_gt0.
have [delta d0 hd] := condition_kappa_alpha_cont C' C1 _ e0.
pose Cm := Num.max ((1 + C') / 2%:R) (C' - delta / 2%:R).
have h1 : (1 + C') / 2%:R <= Cm by rewrite le_max lexx.
have h2 : C' - delta / 2%:R <= Cm by rewrite le_max lexx orbT.
have Cm1 : 1 < Cm by apply: lt_le_trans h1; lra.
have CmC : Cm < C'.
  by rewrite gt_max; apply/andP; split; lra.
exists Cm; first by rewrite Cm1 CmC.
have hd' : `|Cm - C'| < delta by rewrite ltr0_norm ?subr_lt0 //; lra.
have := hd Cm Cm1 hd'; rewrite ltr_norml => /andP[h3 h4].
by lra.
Qed.

Lemma condition_kappa_alpha_right (C' alpha' : R) : 1 < C' ->
  alpha C' < alpha' -> exists2 Cp : R, C' < Cp & alpha Cp < alpha'.
Proof.
move=> C1 aC.
have e0 : 0 < alpha' - alpha C' by rewrite subr_gt0.
have [delta d0 hd] := condition_kappa_alpha_cont C' C1 _ e0.
pose Cp := C' + delta / 2%:R.
have d2 : 0 < delta / 2%:R by rewrite divr_gt0.
have CCp : C' < Cp by rewrite /Cp ltrDl.
exists Cp => //.
have Cp1 : 1 < Cp := lt_trans C1 CCp.
have hd' : `|Cp - C'| < delta.
  by rewrite /Cp addrC addKr ger0_norm ?ltW //; lra.
have := hd Cp Cp1 hd'; rewrite ltr_norml => /andP[h3 h4].
by lra.
Qed.

Lemma condition_kappa_alpha_half (C' : R) : 1 < C' -> alpha C' < 2^-1.
Proof.
move=> C1; have /andP[_ h] := universality_alpha_star_lt kappa k1.
exact: le_lt_trans (condition_kappa_alpha_le_star C' C1) h.
Qed.

(* Conjunct (d) of the curve statement. *)
Theorem condition_kappa_range_holds : condition_kappa_range kappa.
Proof.
split.
- move=> C C1; apply/andP; split; first exact: condition_kappa_alpha_gt0.
  exact: condition_kappa_alpha_lt_star.
- exact: condition_kappa_alpha_lt.
- exact: condition_kappa_alpha_cont.
- exact: condition_kappa_alpha_lim1.
- exact: condition_kappa_alpha_liminf.
Qed.

(* Conjunct (e): C_star(a, kappa) inverts the curve on 0 < a < alpha*. *)
Theorem condition_kappa_inverse_holds : condition_kappa_inverse kappa.
Proof.
move=> a a0 aS.
pose S := [set C : R | 1 < C /\ a <= alpha C].
have SE : condition_kappa_star a kappa = inf S by [].
(* S is not empty, by the limit at infinity *)
have e0 : 0 < universality_alpha_star kappa - a by rewrite subr_gt0.
have [C0 C01 hC0] := condition_kappa_alpha_liminf _ e0.
have SC0 : S C0.
  by split => //; have := hC0 C0 (lexx C0); lra.
(* S lies above 1 + delta, by the limit at 1 *)
have [delta d0 hdelta] := condition_kappa_alpha_lim1 _ a0.
have lbS : lbound S (1 + delta).
  move=> C [C1 aC]; rewrite leNgt; apply/negP => Cd.
  by have := hdelta C C1 Cd; lra.
have nS : S !=set0 by exists C0.
have hasS : has_inf S by split; [exact: nS | exists (1 + delta)].
have st1 : 1 < condition_kappa_star a kappa.
  by rewrite SE; apply: lt_le_trans (lb_le_inf nS lbS); lra.
have below C : 1 < C -> C < condition_kappa_star a kappa -> alpha C < a.
  move=> C1 Cs; rewrite ltNge; apply/negP => aC.
  have SC : S C by split.
  by have := ge_inf (proj2 hasS) SC; rewrite -SE; lra.
have above C : condition_kappa_star a kappa < C -> a < alpha C.
  move=> sC.
  have e1 : 0 < C - inf S by rewrite subr_gt0 -SE.
  have [C' [C1' aC'] C'C] := inf_adherent e1 hasS.
  have CC : C' < C by move: C'C; rewrite addrC subrK.
  exact: le_lt_trans aC' (condition_kappa_alpha_lt C' C C1' CC).
have eqa : alpha (condition_kappa_star a kappa) = a.
  apply/eqP; rewrite eq_le; apply/andP; split.
    rewrite leNgt; apply/negP => aS'.
    have [Cm /andP[Cm1 CmS] aCm] := condition_kappa_alpha_left _ _ st1 aS'.
    by have := below Cm Cm1 CmS; lra.
  rewrite leNgt; apply/negP => aS'.
  have [Cp sCp aCp] := condition_kappa_alpha_right _ _ st1 aS'.
  by have := above Cp sCp; lra.
split => // C C1; split => [aC|]; last exact: above.
rewrite ltNge; apply/negP; rewrite le_eqVlt => /orP[/eqP Ce|Cs].
  by move: aC; rewrite Ce eqa ltxx.
by have := below C C1 Cs; lra.
Qed.

End kappa_curve.
