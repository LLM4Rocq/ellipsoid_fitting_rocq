(* The measurability of the events of universality_statement, at Stdlib's R
   (item U11 of extension/README.md), for all n and d.

   Results:
   - paper_main_fit_event n d is measurable: pm_fit_event_measurable of
     theories/Measurability/Fit.v, which does not depend on the law.
   - Z |-> unsat_value n d Z is a measurable function of the n features:
     measurable_unsat_value of Unsat/Regularized.
   - measurable_fitting_error: the optimal squared fitting error
     universality_fitting_error n d is a measurable function of the sample:
     for d >= 1 it is twice unsat_value of the features of the sample
     (unsat_fitting_error of Unsat/LeastSquares, measurable_unsat_features
     of Model/Rows), and for d = 0 the sample has no coordinates, so the
     function is constant. Hence measurable_error_event:
     universality_error_event n d e eps is measurable for all e and eps.
   - measurable_pd_fit_event and measurable_conditioned_fit_event: the
     events of Theorem 1.2 (i), universality_pd_fit_event n d and
     universality_conditioned_fit_event n d c, are measurable for all n, d
     and c.

   The route of the last two is that of theories/Measurability/Fit.v and
   Conditioned.v. For d >= 1, scaling a fit S by d turns the value 1 into
   the value d of those modules (uni_pd_fit_scale, uni_cond_fit_scale).
   Each event is then the union over m of the levels uni_level: for every
   k, some symmetric rational matrix q with entries at most m and
   q(v) >= (1 / (m + 1) - 1 / (k + 1)) |v|^2 for every v has a fit residual
   below 1 / (k + 1). The conditioned event also asks
   q(v) |w|^2 - c q(w) |v|^2 <= (1 + |c|) |v|^2 |w|^2 / (k + 1), the
   condition lambda_max(q) <= c lambda_min(q) with a tolerance. A positive
   definite fit has S >= I / (m + 1) for some m (pm_pd_uniform), and its
   rational approximations (uni_fit_approx) satisfy these conditions. A
   cluster point of rational witnesses (pm_fit_cluster) is a fit with
   S >= I / (m + 1); for the conditioned event, the infimum lm of
   S(w) / |w|^2 over w != 0 satisfies lm I <= S <= c lm I. For d = 0 the
   sample space has one point, so every set of samples is measurable
   (uni_sample0_measurable). *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix rat.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability measurable_realfun.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.convex Require Import ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Coordinates Measurability.Box
  Measurability.Compact Measurability.Countable Measurability.Fit
  Measurability.Conditioned Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Model Require Import Rows.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* The optimal squared fitting error is a measurable function of the
   sample: twice unsat_value of the features for d >= 1, and constant for
   d = 0, where the sample has no coordinates. *)
Lemma measurable_fitting_error n d :
  measurable_fun [set: paper_main_sample n d]
    (fun x => universality_fitting_error n d x : RR).
Proof.
case: (posnP d) => [->|d0].
  pose x0 : paper_main_sample n 0 := [tuple (0 : R) | i < n * 0].
  have xy (x : paper_main_sample n 0) : x = x0.
    by apply: eq_from_tnth => i; have := leq_trans (ltn_ord i) (eq_leq (muln0 n)).
  rewrite (_ : (fun x => universality_fitting_error n 0 x : RR) =
    cst (universality_fitting_error n 0 x0)); last exact: measurable_cst.
  by apply/funext => x; rewrite (xy x).
rewrite (_ : (fun x => universality_fitting_error n d x : RR) =
    fun x => 2 * unsat_value n d (unsat_features n d x)).
  by apply/funext => x; rewrite unsat_fitting_error.
apply: measurable_funM => //.
exact: measurableT_comp (measurable_unsat_value n d)
  (measurable_unsat_features n d).
Qed.

(* The error event of universality_statement is measurable. *)
Lemma measurable_error_event n d (e eps : R) :
  measurable (universality_error_event n d e eps).
Proof.
apply: (measurable_set_lt (f := fun x : paper_main_sample n d =>
  `|universality_fitting_error n d x - e| : RR)).
apply: (measurableT_comp (f := fun r : RR => `|r|)) => //.
by apply: measurable_funB => //; exact: measurable_fitting_error.
Qed.

(* The sample space of dimension 0 has a single point, so every set of
   samples is measurable. *)
Lemma uni_sample0_measurable n (A : set (paper_main_sample n 0)) : measurable A.
Proof.
pose x0 : paper_main_sample n 0 := [tuple (0 : R) | i < n * 0].
have xy (x : paper_main_sample n 0) : x = x0.
  by apply: eq_from_tnth => i; have := leq_trans (ltn_ord i) (eq_leq (muln0 n)).
have [Ax0|nAx0] := pselect (A x0).
  have -> : A = setT by apply/seteqP; split=> // x _; rewrite (xy x).
  exact: measurableT.
have -> : A = set0.
  by apply/seteqP; split=> // x Ax; apply: nAx0; rewrite -(xy x).
exact: measurable0.
Qed.

(* Scaling the matrix scales the quadratic form; the Loewner conditions
   against multiples of the identity as bounds on the quadratic form. *)
Lemma uni_qf_scalemx d (c : R) (S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form (c *: S) v = c * paper_main_quadratic_form S v.
Proof.
rewrite /paper_main_quadratic_form mulr_sumr; apply: eq_bigr => a _.
rewrite mulr_sumr; apply: eq_bigr => b _.
by rewrite mxE; ring.
Qed.

Lemma uni_sym_scale d (c : R) (S : 'M[R]_d) :
  paper_main_symmetric S -> paper_main_symmetric (c *: S).
Proof. by move=> Ssym a b; rewrite !mxE Ssym. Qed.

Lemma uni_loewner_geP d (lm : R) (S : 'M[R]_d) :
  paper_main_loewner_le (lm *: 1%:M) S <->
  paper_main_symmetric S /\
  forall v, lm * pm_sqnorm d v <= paper_main_quadratic_form S v.
Proof.
split=> [[Ssym Spsd]|[Ssym Slo]]; split.
- by move=> a b; have := Ssym a b; rewrite !mxE (eq_sym a b) => /addIr.
- by move=> v; have := Spsd v; rewrite pm_qf_sub pm_qf_scalar subr_ge0.
- exact: (pm_sym_sub d _ _ Ssym (pm_scalar_sym d lm)).
- by move=> v; rewrite pm_qf_sub pm_qf_scalar subr_ge0; exact: Slo.
Qed.

Lemma uni_loewner_leP d (lp : R) (S : 'M[R]_d) :
  paper_main_loewner_le S (lp *: 1%:M) <->
  paper_main_symmetric S /\
  forall v, paper_main_quadratic_form S v <= lp * pm_sqnorm d v.
Proof.
split=> [[Ssym Spsd]|[Ssym Shi]]; split.
- by move=> a b; have := Ssym a b; rewrite !mxE (eq_sym a b) => /addrI /oppr_inj.
- by move=> v; have := Spsd v; rewrite pm_qf_sub pm_qf_scalar subr_ge0.
- exact: (pm_sym_sub d _ _ (pm_scalar_sym d lp) Ssym).
- by move=> v; rewrite pm_qf_sub pm_qf_scalar subr_ge0; exact: Shi.
Qed.

Section sat_events.
Variables (n d : nat).
Local Notation T := (paper_main_sample n d).
Local Notation V := 'rV[R]_(d * d).

(* The events with the value d in place of 1, as in theories/Measurability,
   and the Loewner conditions as bounds on the quadratic form. *)
Definition uni_pd_fit_d : set T :=
  [set x | exists S : 'M[R]_d, paper_main_pd S /\
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R].

Definition uni_cond_fit_d (c : R) : set T :=
  [set x | exists (S : 'M[R]_d) (lm : R), [/\ 0 < lm, paper_main_symmetric S,
    forall v, lm * pm_sqnorm d v <= paper_main_quadratic_form S v,
    forall v, paper_main_quadratic_form S v <= c * lm * pm_sqnorm d v &
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R]].

Lemma uni_pd_fit_scale : (0 < d)%N -> universality_pd_fit_event n d = uni_pd_fit_d.
Proof.
move=> d0; have dpos : 0 < d%:R :> R by rewrite ltr0n.
have dn0 : d%:R != 0 :> R := lt0r_neq0 dpos.
apply/seteqP; split=> x [S [[Ssym Spd] Sfit]].
- exists (d%:R *: S); split; first split.
  + exact: uni_sym_scale.
  + by move=> v v0; rewrite uni_qf_scalemx; apply: mulr_gt0 => //; exact: Spd.
  + by move=> i; rewrite uni_qf_scalemx Sfit mulr1.
- exists (d%:R^-1 *: S); split; first split.
  + exact: uni_sym_scale.
  + move=> v v0; rewrite uni_qf_scalemx; apply: mulr_gt0; last exact: Spd.
    by rewrite invr_gt0.
  + by move=> i; rewrite uni_qf_scalemx Sfit (mulVf dn0).
Qed.

Lemma uni_cond_fit_scale (c : R) : (0 < d)%N ->
  universality_conditioned_fit_event n d c = uni_cond_fit_d c.
Proof.
move=> d0; have dpos : 0 < d%:R :> R by rewrite ltr0n.
have dn0 : d%:R != 0 :> R := lt0r_neq0 dpos.
have dipos : 0 < d%:R^-1 :> R by rewrite invr_gt0.
apply/seteqP; split=> x.
- move=> [S [lm [lm0 [/uni_loewner_geP [Ssym Slo] [/uni_loewner_leP [_ Shi] Sfit]]]]].
  exists (d%:R *: S), (d%:R * lm); split.
  + exact: mulr_gt0.
  + exact: uni_sym_scale.
  + by move=> v; rewrite uni_qf_scalemx -mulrA (ler_pM2l dpos); exact: Slo.
  + move=> v; rewrite uni_qf_scalemx.
    have -> : c * (d%:R * lm) * pm_sqnorm d v = d%:R * (c * lm * pm_sqnorm d v).
      by ring.
    by rewrite (ler_pM2l dpos); exact: Shi.
  + by move=> i; rewrite uni_qf_scalemx Sfit mulr1.
- move=> [S [lm [lm0 Ssym Slo Shi Sfit]]].
  exists (d%:R^-1 *: S), (d%:R^-1 * lm).
  split; first exact: mulr_gt0.
  split.
    apply/uni_loewner_geP; split; first exact: uni_sym_scale.
    by move=> v; rewrite uni_qf_scalemx -mulrA (ler_pM2l dipos); exact: Slo.
  split.
    apply/uni_loewner_leP; split; first exact: uni_sym_scale.
    move=> v; rewrite uni_qf_scalemx.
    have -> : c * (d%:R^-1 * lm) * pm_sqnorm d v = d%:R^-1 * (c * lm * pm_sqnorm d v).
      by ring.
    by rewrite (ler_pM2l dipos); exact: Shi.
  by move=> i; rewrite uni_qf_scalemx Sfit (mulVf dn0).
Qed.

(* A positive semidefinite fit of value d with entries below m - 1 is
   approximated, at the tolerance 1 / (k + 1), by a symmetric rational
   matrix of the fit index with a small residual, whose quadratic form is
   within |v|^2 / (k + 1) of that of the fit. *)
Lemma uni_fit_approx (x : T) (S : 'M[R]_d) (m k : nat) :
  paper_main_psd S ->
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = d%:R) ->
  (forall a b, `|S a b| + 1 <= m%:R) ->
  exists q : 'M[rat]_d,
    [/\ pm_fit_index d m k q, pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1 &
      forall v : 'cV[R]_d,
        `|paper_main_quadratic_form (pm_rmx d q) v - paper_main_quadratic_form S v|
        <= k.+1%:R^-1 * pm_sqnorm d v].
Proof.
move=> Spsd Sfit SM.
have k0 := pm_inv_gt0 k.
have dd0 : 0 <= (2%:R : R) * (d%:R * d%:R).
  by apply: mulr_ge0; [exact: ler0n | apply: mulr_ge0; exact: ler0n].
pose C := \sum_(i < n) (2 * pm_sqnorm d (paper_main_point x i) * (d%:R * d%:R)) ^+ 2.
have C0 : 0 <= C by apply: sumr_ge0 => i _; exact: sqr_ge0.
pose K := 2 * (d%:R * d%:R) + C + 1.
have K1 : 1 <= K by rewrite /K lerDr; apply: addr_ge0.
have K0 : 0 < K := lt_le_trans ltr01 K1.
have CK : C <= K by rewrite /K addrAC lerDr; apply: addr_ge0 => //; exact: ler01.
have ddK : 2 * (d%:R * d%:R) <= K.
  by rewrite /K -addrA lerDl; apply: addr_ge0 => //; exact: ler01.
pose eta := k.+1%:R^-1 / 2 / K.
have eta0 : 0 < eta.
  by rewrite /eta; apply: divr_gt0 => //; apply: divr_gt0 => //; exact: pm_two_gt0.
have etaK : eta * K = k.+1%:R^-1 / 2 by rewrite /eta (divfK (lt0r_neq0 K0)).
have eta1 : eta <= 1.
  rewrite /eta ler_pdivrMr// mul1r; apply: le_trans _ K1.
  rewrite ler_pdivrMr ?pm_two_gt0// mul1r; apply: le_trans (pm_inv_le1 k) _.
  by rewrite ler1n.
have etad : eta * (2 * (d%:R * d%:R)) <= k.+1%:R^-1.
  apply: le_trans _ (ltW (pm_half_lt k)); rewrite -etaK.
  exact: (ler_wpM2l (ltW eta0) ddK).
have etaC : eta * C < k.+1%:R^-1.
  apply: le_lt_trans (ler_wpM2l (ltW eta0) CK) _; rewrite etaK; exact: pm_half_lt.
have [q [qsym qS]] := pm_rat_sym_approx _ S eta eta0 Spsd.1.
have [idx res] := pm_fit_witness n d S x m k eta q Spsd Sfit SM eta0 eta1 etad etaC qsym qS.
pose D : 'M[R]_d := pm_rmx d q - S.
have Deta : forall i j, `|D i j| <= eta.
  by move=> i j; rewrite /D !mxE distrC; apply/ltW; exact: qS.
exists q; split => // v.
have [h1 h2] := pm_qf_diff_bound d D v eta k (ltW eta0) Deta etad.
by rewrite -pm_qf_sub ler_norml; apply/andP; split; [exact: h1 | exact: h2].
Qed.

(* The countable indices: the fit index of theories/Measurability/Fit.v
   with the lower bound I / (m + 1), and for the conditioned event the
   condition lambda_max <= c lambda_min, both with the tolerance
   1 / (k + 1). *)
Definition uni_pd_index (m k : nat) (q : 'M[rat]_d) : Prop :=
  pm_fit_index d m k q /\
  forall v : 'cV[R]_d,
    - (k.+1%:R^-1 * pm_sqnorm d v)
    <= paper_main_quadratic_form (pm_rmx d q) v - m.+1%:R^-1 * pm_sqnorm d v.

Definition uni_cond_index (c : R) (m k : nat) (q : 'M[rat]_d) : Prop :=
  uni_pd_index m k q /\
  forall v w : 'cV[R]_d,
    paper_main_quadratic_form (pm_rmx d q) v * pm_sqnorm d w
    - c * paper_main_quadratic_form (pm_rmx d q) w * pm_sqnorm d v
    <= (1 + `|c|) * (pm_sqnorm d v * pm_sqnorm d w) * k.+1%:R^-1.

Definition uni_level (P : nat -> 'M[rat]_d -> Prop) : set T :=
  \bigcap_(k : nat) \bigcup_(q : 'M[rat]_d)
    [set x : T | P k q /\ pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1].

Lemma uni_level_measurable (P : nat -> 'M[rat]_d -> Prop) : measurable (uni_level P).
Proof.
apply: pm_bigcap_measurable => k; apply: pm_bigcup_measurable => q.
apply: pm_measurable_guard.
exact: (pm_measurable_lt n d (fun x => pm_fit_residual n d (pm_rmx d q) x)
  (fun _ => k.+1%:R^-1) (pm_fit_residual_measurable n d _) (pm_measurable_cst n d _)).
Qed.

(* The positive definite event of value d is the union of its levels. *)
Lemma uni_pd_fit_sub : uni_pd_fit_d `<=` \bigcup_(m : nat) uni_level (uni_pd_index m).
Proof.
move=> x [S [Spd Sfit]].
have [k0 Sk0] := pm_pd_uniform d S Spd.
have [m0 SM0] := pm_entry_bound d S.
pose m := maxn m0 k0.
have Spsd : paper_main_psd S.
  split; first exact: Spd.1.
  move=> v; apply: le_trans (Sk0 v); apply: mulr_ge0; last exact: pm_sqnorm_ge0.
  by rewrite invr_ge0 ler0n.
have SM : forall a b, `|S a b| + 1 <= m%:R.
  by move=> a b; apply: le_trans (SM0 a b) _; rewrite ler_nat leq_maxl.
have Slo : forall v : 'cV[R]_d,
    m.+1%:R^-1 * pm_sqnorm d v <= paper_main_quadratic_form S v.
  move=> v; apply: le_trans (Sk0 v); apply: ler_wpM2r; first exact: pm_sqnorm_ge0.
  by apply: pm_inv_mono; exact: leq_maxr.
exists m => // k _.
have [q [idx res close]] := uni_fit_approx x S m k Spsd Sfit SM.
exists q => //; split => //; split => // v.
have := close v; rewrite ler_norml => /andP[lo _].
by apply: le_trans lo _; rewrite lerD2l lerN2; exact: Slo.
Qed.

Lemma uni_pd_fit_sup : \bigcup_(m : nat) uni_level (uni_pd_index m) `<=` uni_pd_fit_d.
Proof.
move=> x [m _ Hm].
have /choice[q Hq] : forall k : nat, exists q : 'M[rat]_d,
    uni_pd_index m k q /\ pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1.
  by move=> k; have [q _ Hq] := Hm k Logic.I; exists q.
have Hfit : forall k, pm_fit_index d m k (q k) /\
    pm_fit_residual n d (pm_rmx d (q k)) x < k.+1%:R^-1.
  by move=> k; have [[i1 _] r] := Hq k; split.
have [p [clp [Spsd Sfit]]] := pm_fit_cluster n d x m q Hfit.
pose u : nat -> V := fun k => mxvec (pm_rmx d (q k)).
have uk : forall k, vec_mx (u k) = pm_rmx d (q k) by move=> k; rewrite /u mxvecK.
have clu : forall B : set V, nbhs p B -> forall k0 : nat,
    exists k, (k0 <= k)%nat /\ B (u k).
  exact: clp.
have Slo : forall v : 'cV[R]_d,
    m.+1%:R^-1 * pm_sqnorm d v <= paper_main_quadratic_form (vec_mx p) v.
  move=> v.
  pose g := fun w : V => pm_qf_vec d v w - m.+1%:R^-1 * pm_sqnorm d v.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (pm_qf_vec d v) (fun _ => m.+1%:R^-1 * pm_sqnorm d v) p
      (pm_qf_vec_continuous d v p) (pm_continuous_cst _ _ p)).
  have g0 : 0 <= g p.
    apply: (pm_cluster_value_ge _ u p g 0 (pm_sqnorm d v) gc (pm_sqnorm_ge0 d v) clu) => k.
    have [[_ lo] _] := Hq k.
    by rewrite sub0r mulrC /g /pm_qf_vec uk; exact: lo.
  by move: g0; rewrite /g /pm_qf_vec subr_ge0.
exists (vec_mx p); split; last exact: Sfit.
split; first exact: Spsd.1.
move=> v v0; apply: lt_le_trans (Slo v).
by apply: mulr_gt0; [rewrite invr_gt0 ltr0n | exact: pm_sqnorm_gt0].
Qed.

Lemma uni_pd_fit_eq : uni_pd_fit_d = \bigcup_(m : nat) uni_level (uni_pd_index m).
Proof. by rewrite eqEsubset; split; [exact: uni_pd_fit_sub | exact: uni_pd_fit_sup]. Qed.

(* The vector of ones is not zero when d >= 1. *)
Lemma uni_ones_neq0 : (0 < d)%N -> (const_mx 1 : 'cV[R]_d) != 0.
Proof.
move=> d0; apply/eqP => /matrixP/(_ (Ordinal d0) 0).
by rewrite !mxE => /eqP; rewrite oner_eq0.
Qed.

(* The conditioned event of value d is the union of its levels. *)
Lemma uni_cond_fit_sub (c : R) : (0 < d)%N ->
  uni_cond_fit_d c `<=` \bigcup_(m : nat) uni_level (uni_cond_index c m).
Proof.
move=> d0 x [S [lm [lm0 Ssym Slo Shi Sfit]]].
pose e : 'cV[R]_d := const_mx 1.
have e0 : e != 0 := uni_ones_neq0 d0.
have c1 : 1 <= c.
  have h := le_trans (Slo e) (Shi e).
  have pos : 0 < lm * pm_sqnorm d e := mulr_gt0 lm0 (pm_sqnorm_gt0 d e e0).
  by move: h; rewrite -mulrA -[X in X <= _]mul1r (ler_pM2r pos).
have c0 : 0 <= c := le_trans ler01 c1.
have [k0 Hk0] := pm_inv_small lm lm0.
have [m0 SM0] := pm_entry_bound d S.
pose m := maxn m0 k0.
have Spsd : paper_main_psd S.
  split => // v; apply: le_trans (Slo v).
  exact: mulr_ge0 (ltW lm0) (pm_sqnorm_ge0 d v).
have SM : forall a b, `|S a b| + 1 <= m%:R.
  by move=> a b; apply: le_trans (SM0 a b) _; rewrite ler_nat leq_maxl.
have Sm : forall v : 'cV[R]_d,
    m.+1%:R^-1 * pm_sqnorm d v <= paper_main_quadratic_form S v.
  move=> v; apply: le_trans (Slo v); apply: ler_wpM2r; first exact: pm_sqnorm_ge0.
  by apply: le_trans (ltW Hk0); apply: pm_inv_mono; exact: leq_maxr.
exists m => // k _.
have [q [idx res close]] := uni_fit_approx x S m k Spsd Sfit SM.
exists q => //; split => //; split.
  split => // v.
  have := close v; rewrite ler_norml => /andP[lo _].
  by apply: le_trans lo _; rewrite lerD2l lerN2; exact: Sm.
move=> v w.
have := close v; rewrite ler_norml => /andP[_ hv].
have := close w; rewrite ler_norml => /andP[lw _].
have nv := pm_sqnorm_ge0 d v; have nw := pm_sqnorm_ge0 d w.
have cnv : 0 <= c * pm_sqnorm d v := mulr_ge0 c0 nv.
have p1 := ler_wpM2r nw hv.
have p2 := ler_wpM2r cnv lw.
have p3 := ler_wpM2r nw (Shi v).
have p4 := ler_wpM2r cnv (Slo w).
rewrite ger0_norm //.
set t := k.+1%:R^-1 in p1 p2 *; clearbody t.
lra.
Qed.

Lemma uni_cond_fit_sup (c : R) : (0 < d)%N ->
  \bigcup_(m : nat) uni_level (uni_cond_index c m) `<=` uni_cond_fit_d c.
Proof.
move=> d0 x [m _ Hm].
have /choice[q Hq] : forall k : nat, exists q : 'M[rat]_d,
    uni_cond_index c m k q /\ pm_fit_residual n d (pm_rmx d q) x < k.+1%:R^-1.
  by move=> k; have [q _ Hq] := Hm k Logic.I; exists q.
have Hfit : forall k, pm_fit_index d m k (q k) /\
    pm_fit_residual n d (pm_rmx d (q k)) x < k.+1%:R^-1.
  by move=> k; have [[[i1 _] _] r] := Hq k; split.
have [p [clp [Spsd Sfit]]] := pm_fit_cluster n d x m q Hfit.
pose u : nat -> V := fun k => mxvec (pm_rmx d (q k)).
have uk : forall k, vec_mx (u k) = pm_rmx d (q k) by move=> k; rewrite /u mxvecK.
have clu : forall B : set V, nbhs p B -> forall k0 : nat,
    exists k, (k0 <= k)%nat /\ B (u k).
  exact: clp.
pose S : 'M[R]_d := vec_mx p.
have Sm : forall v : 'cV[R]_d,
    m.+1%:R^-1 * pm_sqnorm d v <= paper_main_quadratic_form S v.
  move=> v.
  pose g := fun w : V => pm_qf_vec d v w - m.+1%:R^-1 * pm_sqnorm d v.
  have gc : {for p, continuous g}.
    exact: (pm_continuous_sub _ (pm_qf_vec d v) (fun _ => m.+1%:R^-1 * pm_sqnorm d v) p
      (pm_qf_vec_continuous d v p) (pm_continuous_cst _ _ p)).
  have g0 : 0 <= g p.
    apply: (pm_cluster_value_ge _ u p g 0 (pm_sqnorm d v) gc (pm_sqnorm_ge0 d v) clu) => k.
    have [[[_ lo] _] _] := Hq k.
    by rewrite sub0r mulrC /g /pm_qf_vec uk; exact: lo.
  by move: g0; rewrite /g /pm_qf_vec subr_ge0.
have Sratio : forall v w : 'cV[R]_d,
    paper_main_quadratic_form S v * pm_sqnorm d w
    <= c * paper_main_quadratic_form S w * pm_sqnorm d v.
  move=> v w.
  pose g := fun z : V =>
    pm_qf_vec d v z * pm_sqnorm d w - c * pm_qf_vec d w z * pm_sqnorm d v.
  have gc : {for p, continuous g}.
    have g1 : {for p, continuous (fun z : V => pm_qf_vec d v z * pm_sqnorm d w)}.
      exact: (pm_continuous_mul _ (pm_qf_vec d v) (fun _ => pm_sqnorm d w) p
        (pm_qf_vec_continuous d v p) (pm_continuous_cst _ _ p)).
    have g2 : {for p, continuous (fun z : V => c * pm_qf_vec d w z * pm_sqnorm d v)}.
      apply: (pm_continuous_mul _ (fun z : V => c * pm_qf_vec d w z)
        (fun _ => pm_sqnorm d v) p _ (pm_continuous_cst _ _ p)).
      exact: (pm_continuous_mul _ (fun _ => c) (pm_qf_vec d w) p
        (pm_continuous_cst _ _ p) (pm_qf_vec_continuous d w p)).
    exact: (pm_continuous_sub _ _ _ p g1 g2).
  have a0 : 0 <= (1 + `|c|) * (pm_sqnorm d v * pm_sqnorm d w).
    apply: mulr_ge0; first exact: addr_ge0.
    by apply: mulr_ge0; exact: pm_sqnorm_ge0.
  have g0 : g p <= 0.
    apply: (pm_cluster_value_le _ u p g 0 _ gc a0 clu) => k.
    have [[_ hr] _] := Hq k.
    by rewrite add0r /g /pm_qf_vec uk; exact: hr.
  by move: g0; rewrite /g /pm_qf_vec subr_le0.
pose e : 'cV[R]_d := const_mx 1.
have e0 : e != 0 := uni_ones_neq0 d0.
pose E := [set r : R | exists2 w : 'cV[R]_d,
  w != 0 & r = paper_main_quadratic_form S w / pm_sqnorm d w].
have En : E !=set0.
  by exists (paper_main_quadratic_form S e / pm_sqnorm d e); exists e.
have Elb : lbound E m.+1%:R^-1.
  move=> r [w w0 ->]; have nw0 := pm_sqnorm_gt0 d w w0.
  by rewrite ler_pdivlMr //; exact: Sm.
have Ehas : has_lbound E by exists m.+1%:R^-1.
pose lm := inf E.
have lm0 : 0 < lm := lt_le_trans (pm_inv_gt0 m) (lb_le_inf En Elb).
have Slo : forall v, lm * pm_sqnorm d v <= paper_main_quadratic_form S v.
  move=> v; have [->|v0] := eqVneq v 0; first by rewrite pm_sqnorm0 pm_qf0 mulr0.
  have nv0 := pm_sqnorm_gt0 d v v0.
  by rewrite -ler_pdivlMr //; apply: ge_inf => //; exists v.
have c1 : 1 <= c.
  have pos : 0 < paper_main_quadratic_form S e * pm_sqnorm d e.
    apply: mulr_gt0; last exact: pm_sqnorm_gt0.
    apply: lt_le_trans (Sm e); apply: mulr_gt0; first exact: pm_inv_gt0.
    exact: pm_sqnorm_gt0.
  by move: (Sratio e e); rewrite -mulrA -[X in X <= _]mul1r (ler_pM2r pos).
have Shi : forall v, paper_main_quadratic_form S v <= c * lm * pm_sqnorm d v.
  move=> v; have [->|v0] := eqVneq v 0; first by rewrite pm_sqnorm0 pm_qf0 mulr0.
  have nv0 := pm_sqnorm_gt0 d v v0.
  have cv0 : 0 < c * pm_sqnorm d v := mulr_gt0 (lt_le_trans ltr01 c1) nv0.
  have : paper_main_quadratic_form S v / (c * pm_sqnorm d v) <= lm.
    apply: lb_le_inf => // r [w w0 ->].
    have nw0 := pm_sqnorm_gt0 d w w0.
    rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
    by apply: le_trans (Sratio v w) _; rewrite -mulrA mulrCA.
  by rewrite ler_pdivrMr // mulrCA mulrA.
by exists S, lm; split => //; exact: Spsd.1.
Qed.

Lemma uni_cond_fit_eq (c : R) : (0 < d)%N ->
  uni_cond_fit_d c = \bigcup_(m : nat) uni_level (uni_cond_index c m).
Proof.
by move=> d0; rewrite eqEsubset; split; [exact: uni_cond_fit_sub | exact: uni_cond_fit_sup].
Qed.

End sat_events.

(* The events of Theorem 1.2 (i) are measurable, for all n, d and c. *)
Theorem measurable_pd_fit_event n d : measurable (universality_pd_fit_event n d).
Proof.
case: (posnP d) => [->|d0]; first exact: uni_sample0_measurable.
rewrite (uni_pd_fit_scale n d d0) uni_pd_fit_eq.
by apply: pm_bigcup_measurable => m; exact: uni_level_measurable.
Qed.

Theorem measurable_conditioned_fit_event n d (c : R) :
  measurable (universality_conditioned_fit_event n d c).
Proof.
case: (posnP d) => [->|d0]; first exact: uni_sample0_measurable.
rewrite (uni_cond_fit_scale n d c d0) (uni_cond_fit_eq n d c d0).
by apply: pm_bigcup_measurable => m; exact: uni_level_measurable.
Qed.
