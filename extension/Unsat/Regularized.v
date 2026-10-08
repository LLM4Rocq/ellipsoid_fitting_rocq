(* Corollary 2.13 (ii) of Koehler and Sohn, "Universality and sharp
   thresholds for ellipsoid fitting" (arXiv 2608.27372, lines 1499-1601), at
   Stdlib's R: the unregularized least squares values Phi_Z(R_d^o) of two
   sequences of feature laws with the same covariance concentrate around the
   same deterministic sequence.

   Setting. kappa > 1, alpha > 0 and n d / d^2 -> alpha
   (universality_density_tends_to). For d >= 1, mu d and nu d are laws on
   'rV[R]_(d * d) that are (K, tau d)-regular features (regular_feature)
   with covariance Sigma_kappa = unsat_cov kappa d (LeastSquares.v), with
   tau d >= 0 and tau d <= C0 (ln d)^-3 for every large d. R_d^o is
   unsat_domain d, lambda = unsat_lambda kappa d and the barrier is -ln det
   (logdet_barrier), a d-self-concordant barrier on R_d^o, nonnegative and
   zero at the identity I.

   Proved:
   - unsat_lambda_bounds: (kappa - 1) / d <= lambda <= max (2, kappa - 1) / d;
     unsat_ref_scale_le: Lref <= L = (1 + 1 / beta) (1 + max (2, kappa - 1)),
     at the reference point I.
   - unsat_value_le_ridge: unsat_value <= unsat_ridge_value; the values and
     the events of a large gap are measurable (measurable_unsat_value,
     measurable_unsat_ridge_value, measurable_unsat_gap).
   - unsat_ridge_concentration: for each d, the inequality of
     convex/ridge_comparison.v on R_d^o with the reference point I: the
     value Phi_Z(R_d^o; beta) of features of law mu d is within
       100 (1 + K^4)^2 L^2 ((n gamma)^(-1/2) + d (tau d / (kappa - 1) + 1) / n)
       + t + eps M + gamma d ln (1 / eps)
     of c = E Phi_G(R_d^o, -ln det; beta, gamma) under nu d (unsat_center),
     except on an event of probability at most
       4 (1 + K^4)^2 L^2 / (n t^2)
       + ((kappa - 1) / 2 + beta max (2, kappa - 1)) / M.
   - unsat_rates: with w = (ln d)^(1/4), beta = 1 / (w ln d) (unsat_beta),
     gamma = 1 / (d (ln d)^2) (unsat_gamma), eps = 1 / d, t = 1 / ln d and
     M = ln d, the two bounds and beta ln d are O(1 / w) as soon as
     n >= alpha d^2 / 2 and tau d <= C0 (ln d)^-3, and 36 <= n gamma: every
     term is a power of w, by (ln d)^10 <= 10! d (rate_bounds, over any
     realType).
   - unsat_value_concentration_law: if moreover removing the ridge costs at
     most Cr beta ln d with probability tending to one (Lemma 2.12,
     Ridge.v), then for every eps > 0 the probability that unsat_value is
     farther than eps from c d tends to 0, under mu d and under nu d.

   The paper takes gamma = d^(-4/3) (ln d)^(-2/3) and
   beta = (q_d / ln d)^(1/3); the choices above keep the exponents
   integral, and any choice with beta ln d -> 0, tau d / beta^2 -> 0 and a
   vanishing barrier cost works. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import self_concordant least_squares.
From GaussianAnalysis Require Import logdet_barrier feature_moments.
From GaussianAnalysis Require Import lindeberg barrier_lindeberg.
From GaussianAnalysis Require Import barrier_removal ridge_comparison.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares Ridge.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

Section unsat_reference.
Variables (kappa : R) (d : nat).
Hypotheses (k1 : 1 < kappa) (d0 : (0 < d)%N).

Lemma unsat_ref_norm : mxdot (mxvec (1%:M : 'M[R]_d)) (mxvec 1%:M) = d%:R.
Proof. by rewrite mxdot_mxvec mxdot_trace trmx1 mulmx1 mxtrace1. Qed.

Lemma unsat_ref_cov :
  mxdot (mxvec (1%:M : 'M[R]_d) *m unsat_cov kappa d) (mxvec 1%:M) =
  kappa - 1.
Proof. by rewrite unsat_cov_formE mxvecK unsat_cov_form1. Qed.

(* (kappa - 1) / d <= lambda <= max (2, kappa - 1) / d. *)
Lemma unsat_lambda_bounds :
  kappa - 1 <= unsat_lambda kappa d * d%:R <= Num.max 2 (kappa - 1).
Proof.
apply/andP; split.
  rewrite -unsat_ref_cov -unsat_ref_norm /unsat_lambda; exact: form_le_opnorm.
by rewrite -ler_pdivlMr ?ltr0n //; exact: unsat_lambda_le.
Qed.

Lemma unsat_ref_scale_le (beta gamma : R) : 0 < beta -> 0 <= gamma ->
  0 <= ls_ref_scale (unsat_lambda kappa d) beta gamma (unsat_domain d)
    (logdet_barrier d) <= (1 + beta^-1) * (1 + Num.max 2 (kappa - 1)).
Proof.
move=> b0 g0; rewrite /ls_ref_scale.
have b1 : 0 <= 1 + beta^-1 by rewrite addr_ge0 // invr_ge0 ltW.
set S := [set _ | _ in _].
have v0 th : unsat_domain d th ->
    0 <= unsat_lambda kappa d * mxdot th th + gamma * logdet_barrier d th.
  move=> Dth.
  by rewrite addr_ge0 ?mulr_ge0 ?mxdot_ge0 ?opnorm_ge0 ?logdet_barrier_ge0.
have lb : has_lbound S by exists 0 => _ [th Dth <-]; exact: v0.
pose I := mxvec (1%:M : 'M[R]_d).
have DI : unsat_domain d I := unsat_domain1 d d0.
have Sn : S !=set0.
  by exists (unsat_lambda kappa d * mxdot I I + gamma * logdet_barrier d I), I.
have I0 : 0 <= inf S by apply: lb_le_inf Sn _ => _ [th Dth <-]; exact: v0.
apply/andP; split; first by rewrite mulr_ge0 // addr_ge0.
apply: ler_wpM2l => //; rewrite lerD2l.
apply: le_trans (ge_inf lb _) _; first by exists I.
rewrite logdet_barrier_one mulr0 addr0 unsat_ref_norm.
by have /andP[] := unsat_lambda_bounds.
Qed.

End unsat_reference.

Section unsat_values.

Lemma unsat_domain_nonempty d : unsat_domain d !=set0.
Proof. by exists (mxvec 1%:M); exact: pd_slice_one. Qed.

Lemma measurable_unsat_ridge_value (kappa beta : R) n d : 0 <= beta ->
  measurable_fun setT
    (fun Z : n.-tuple 'rV[RR]_(d * d) =>
       (unsat_ridge_value kappa n d beta Z : RR)).
Proof.
move=> b0.
apply: (measurable_ls_value (rel_open_convex_pd_slice d d%:R)) => //.
- exact: unsat_domain_nonempty.
- exact: opnorm_ge0.
Qed.

Lemma measurable_unsat_value n d :
  measurable_fun setT
    (fun Z : n.-tuple 'rV[RR]_(d * d) => (unsat_value n d Z : RR)).
Proof.
apply: (measurable_ls_value (rel_open_convex_pd_slice d d%:R)) => //.
exact: unsat_domain_nonempty.
Qed.

Lemma unsat_value_le_ridge (kappa beta : R) n d
    (Z : n.-tuple 'rV[R]_(d * d)) :
  0 <= beta -> unsat_value n d Z <= unsat_ridge_value kappa n d beta Z.
Proof.
move=> b0; rewrite /unsat_value /unsat_ridge_value /ls_value.
set S0 := [set _ | _ in _ & _ in _]; set S1 := [set _ | _ in _ & _ in _].
have S0lb : has_lbound S0.
  exists 0 => _ [th Dth [b _ <-]].
  by apply: ls_objective_ge0; exact: lexx.
have [th0 Dth0] := unsat_domain_nonempty d.
have S1n : S1 !=set0.
  by exists (ls_objective Z (unsat_lambda kappa d) beta th0 0), th0 => //;
    exists 0.
apply: lb_le_inf S1n _ => _ [th Dth [b _ <-]].
apply: le_trans (ge_inf S0lb _) _; first by exists th => //; exists b.
rewrite /ls_objective !mul0r addr0 lerDl mulr_ge0 // addr_ge0 ?sqr_ge0 //.
by rewrite mulr_ge0 ?mxdot_ge0 ?opnorm_ge0.
Qed.

Lemma measurable_unsat_gap (kappa beta c : R) n d : 0 <= beta ->
  measurable [set Z : n.-tuple 'rV[RR]_(d * d) |
    c < unsat_ridge_value kappa n d beta Z - unsat_value n d Z].
Proof.
move=> b0; apply: measurable_set_lt; apply: measurable_funB.
- exact: measurable_unsat_ridge_value.
- exact: measurable_unsat_value.
Qed.

End unsat_values.

(* E Phi_G(R_d^o, -ln det; beta, gamma) for features of law nu. *)
Definition unsat_center (kappa : R) n d (nu : probability 'rV[RR]_(d * d) RR)
    (beta gamma : R) : R :=
  \int[tuple_prod (fun=> nu) n]_Z ls_barrier_value Z (unsat_lambda kappa d)
    beta (unsat_domain d) gamma (logdet_barrier d).

Section unsat_concentration.
Variables (kappa K tau : R) (n d : nat).
Variables (mu nu : probability 'rV[RR]_(d * d) RR).
Hypotheses (k1 : 1 < kappa) (n0 : (0 < n)%N) (d0 : (0 < d)%N).
Hypotheses (tau0 : 0 <= tau)
  (rmu : regular_feature K tau (unsat_cov kappa d) mu)
  (rnu : regular_feature K tau (unsat_cov kappa d) nu).

Theorem unsat_ridge_concentration (beta gamma eps t M : R) :
  0 < beta -> 0 < gamma -> 0 < eps < 1 -> 0 < t -> 0 < M ->
  36 <= n%:R * gamma ->
  (tuple_prod (fun=> mu) n
     [set Z | (100 * (1 + K ^+ 4) ^+ 2 *
         ((1 + beta^-1) * (1 + Num.max 2 (kappa - 1))) ^+ 2 *
         ((Num.sqrt (n%:R * gamma))^-1 +
          d%:R * (tau * d%:R / (kappa - 1) + 1) / n%:R) + t +
         (eps * M + gamma * d%:R * ln eps^-1) <
         `|unsat_ridge_value kappa n d beta Z -
           unsat_center kappa n d nu beta gamma|)%R] <=
   (4 * (1 + K ^+ 4) ^+ 2 *
      ((1 + beta^-1) * (1 + Num.max 2 (kappa - 1))) ^+ 2 / (n%:R * t ^+ 2) +
    ((kappa - 1) / 2 + beta * Num.max 2 (kappa - 1)) / M)%:E)%E.
Proof.
move=> b0 g0 e01 t0 M0 n36.
pose I := mxvec (1%:M : 'M[R]_d).
have DI : unsat_domain d I := unsat_domain1 d d0.
have h := ridge_comparison (rel_open_convex_pd_slice d d%:R)
  (logdet_sc_barrier d d%:R) (ler0n _ d) (@logdet_barrier_ge0 _ d) rmu rnu
  tau0 n0 b0 g0 e01 DI t0 M0 n36.
have hs := unsat_ref_scale_le kappa d k1 d0 beta gamma b0 (ltW g0).
rewrite /unsat_lambda /unsat_domain in hs.
set Lr := ls_ref_scale _ _ _ _ _ in h hs.
set L := (1 + beta^-1) * (1 + maxr 2 (kappa - 1)) in hs *.
have /andP[Lr0 LrL] := hs.
have Lsq : Lr ^+ 2 <= L ^+ 2 by rewrite !expr2 ler_pM.
have hlam := unsat_lambda_bounds kappa d k1 d0.
rewrite /unsat_lambda in hlam.
set lam := opnorm (unsat_cov kappa d) in h hlam.
have /andP[lam1 lam2] := hlam.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have lam0 : 0 < lam.
  have : 0 < lam * d%:R by apply: lt_le_trans lam1.
  by rewrite pmulr_lgt0.
have taul : tau / lam <= tau * d%:R / (kappa - 1).
  rewrite -mulrA ler_wpM2l // ler_pdivlMr // mulrC ler_pdivrMr //.
  by rewrite mulrC.
have dimle : Num.sqrt (\dim (@sym_traceless RR d))%:R <= d%:R :> R.
  rewrite -[X in _ <= X]ger0_norm ?ler0n // -sqrtr_sqr.
  rewrite ler_sqrt ?exprn_ge0 ?ler0n // -natrX ler_nat.
  by have := dim_sym_traceless (R := RR) d; rewrite -mulnn.
have hI : mxdot (I *m unsat_cov kappa d) I = kappa - 1.
  exact: unsat_ref_cov kappa d d0.
have hII : mxdot I I = d%:R := unsat_ref_norm d.
rewrite hI hII logdet_barrier_one mulr0 addr0 in h.
set s := (Num.sqrt (n%:R * gamma))^-1 in h *.
have s0 : 0 <= s by rewrite invr_ge0 sqrtr_ge0.
have nR : 0 < n%:R :> R by rewrite ltr0n.
have K4 : 0 <= 1 + K ^+ 4 :> R by rewrite addr_ge0 // exprn_even_ge0.
have A0 : 0 <= 100 * (1 + K ^+ 4) ^+ 2 :> R by rewrite mulr_ge0 // exprn_ge0.
(* the threshold of Theorem 2.9 is at most ours *)
have thr_le : 100 * (1 + K ^+ 4) ^+ 2 * Lr ^+ 2 *
    (s + Num.sqrt (\dim (@sym_traceless RR d))%:R * (tau / lam + 1) / n%:R)
    <= 100 * (1 + K ^+ 4) ^+ 2 * L ^+ 2 *
    (s + d%:R * (tau * d%:R / (kappa - 1) + 1) / n%:R).
  apply: ler_pM; first by rewrite mulr_ge0 // exprn_ge0.
  - rewrite addr_ge0 // mulr_ge0 ?invr_ge0 ?ler0n // mulr_ge0 ?sqrtr_ge0 //.
    by rewrite addr_ge0 // divr_ge0 // ltW.
  - by rewrite ler_wpM2l.
  rewrite lerD2l ler_wpM2r ?invr_ge0 ?ler0n //.
  have tl0 : 0 <= tau / lam + 1 by rewrite addr_ge0 // divr_ge0 // ltW.
  by apply: ler_pM; [exact: sqrtr_ge0|exact: tl0|exact: dimle|rewrite lerD2r].
have mabs (a : R) : measurable [set Z : n.-tuple 'rV[RR]_(d * d) |
    (a < `|unsat_ridge_value kappa n d beta Z -
           unsat_center kappa n d nu beta gamma|)%R].
  have mf : measurable_fun setT (fun Z : n.-tuple 'rV[RR]_(d * d) =>
      (`|unsat_ridge_value kappa n d beta Z -
         unsat_center kappa n d nu beta gamma| : RR)).
    apply: (measurableT_comp (@normr_measurable RR _)).
    apply: measurable_funB => //.
    exact: measurable_unsat_ridge_value (ltW b0).
  exact: measurable_set_lt mf.
apply: (le_trans (le_measure _ _ _ _) (le_trans h _)).
- by rewrite inE; exact: mabs.
- by rewrite inE; exact: mabs.
- by move=> Z /=; apply: le_lt_trans; rewrite lerD2r lerD2r.
rewrite lee_fin lerD //.
  have nt : 0 <= (n%:R * t ^+ 2)^-1.
    by rewrite invr_ge0 mulr_ge0 ?exprn_ge0 // ltW.
  apply: ler_wpM2r => //; apply: ler_wpM2l => //.
  by rewrite mulr_ge0 // exprn_ge0.
apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
by rewrite lerD2l -mulrA ler_wpM2l // ltW.
Qed.

End unsat_concentration.

Section real_facts.
Variable RT : realType.

(* (ln x)^10 <= 10! x for x >= 1. *)
Lemma ln_pow10_le (x : RT) : 1 <= x -> ln x ^+ 10 <= 10`!%:R * x.
Proof.
move=> x1.
have x0 : 0 < x by apply: lt_le_trans x1.
have := expR_ge1Dxn 9 (ln_ge0 x1).
rewrite lnK ?posrE // => h.
have f0 : 0 < (10`!%:R : RT) by rewrite ltr0n fact_gt0.
have : ln x ^+ 10 / 10`!%:R <= x by apply: le_trans h; rewrite lerDr.
by rewrite ler_pdivrMr // mulrC.
Qed.

Lemma sqrt_le_self (x : RT) : 1 <= x -> Num.sqrt x <= x.
Proof.
move=> x1.
have x0 : 0 <= x by apply: le_trans x1.
have s1 : 1 <= Num.sqrt x by rewrite -sqrtr1 ler_sqrt.
by rewrite -{2}(sqr_sqrtr x0) expr2 ler_peMl // (le_trans ler01 s1).
Qed.

Lemma sqrt4_facts (u : RT) : 1 <= u ->
  [/\ 1 <= Num.sqrt (Num.sqrt u), Num.sqrt (Num.sqrt u) ^+ 2 <= u,
      Num.sqrt (Num.sqrt u) ^+ 4 = u & Num.sqrt (Num.sqrt u) <= u].
Proof.
move=> u1.
have u0 : 0 <= u by apply: le_trans u1.
have s1 : 1 <= Num.sqrt u by rewrite -sqrtr1 ler_sqrt.
have w2 : Num.sqrt (Num.sqrt u) ^+ 2 = Num.sqrt u.
  by rewrite sqr_sqrtr // sqrtr_ge0.
have su := sqrt_le_self u u1.
have ws := sqrt_le_self _ s1.
split.
- by rewrite -sqrtr1 ler_sqrt // sqrtr_ge0.
- by rewrite w2.
- by rewrite -[4%N]/(2 * 2)%N exprM w2 sqr_sqrtr.
- exact: le_trans ws su.
Qed.

Lemma inv_sqrt_le (x y : RT) : 0 < y -> y ^- 2 <= x -> (Num.sqrt x)^-1 <= y.
Proof.
move=> y0 hx.
have y2 : 0 < y ^+ 2 by rewrite exprn_gt0.
have x0 : 0 < x by apply: lt_le_trans hx; rewrite invr_gt0.
have hy : y^-1 <= Num.sqrt x.
  have yi : 0 <= y^-1 by rewrite invr_ge0 ltW.
  rewrite -[y^-1]ger0_norm // -sqrtr_sqr.
  by rewrite ler_sqrt ?exprVn // ltW.
by rewrite -[X in _ <= X]invrK lef_pV2 ?posrE ?sqrtr_gt0 ?invr_gt0.
Qed.

Lemma le_sqrt4 (c u : RT) : 0 <= c -> c ^+ 4 <= u ->
  c <= Num.sqrt (Num.sqrt u).
Proof.
move=> c0 hu.
have c4 : 0 <= c ^+ 4 by rewrite exprn_ge0.
have E : Num.sqrt (Num.sqrt (c ^+ 4)) = c.
  rewrite -[4%N]/(2 * 2)%N exprM sqrtr_sqr ger0_norm ?exprn_ge0 //.
  by rewrite sqrtr_sqr ger0_norm.
rewrite -{1}E ler_sqrt ?sqrtr_ge0 // ler_sqrt //.
exact: le_trans c4 hu.
Qed.

End real_facts.

(* The weights of the ridge and of the barrier, as functions of d. *)
Definition unsat_beta d : R :=
  (ln d%:R * Num.sqrt (Num.sqrt (ln d%:R)))^-1.

Definition unsat_gamma d : R := (d%:R * ln d%:R ^+ 2)^-1.

Section rate_bounds.
Variable RT : realType.
Variables (kappa alpha K C0 F u w D N tau : RT).
Hypotheses (k1 : 1 < kappa) (a0 : 0 < alpha) (C00 : 0 <= C0) (F0 : 0 < F).
Hypotheses (w1 : 1 <= w) (uw : u = w ^+ 4) (d1 : 1 <= D).
Hypotheses (hpow : u ^+ 10 <= F * D) (hn : alpha * D ^+ 2 <= 2 * N).
Hypotheses (tau0 : 0 <= tau) (htau : tau <= C0 / u ^+ 3).

Local Notation Mk := (Num.max 2 (kappa - 1)).
Local Notation A := (1 + K ^+ 4).
Local Notation beta := ((u * w)^-1).
Local Notation gamma := ((D * u ^+ 2)^-1).
Local Notation L := ((1 + beta^-1) * (1 + Mk)).

Lemma rate_pow : w ^+ 40 <= F * D.
Proof. by rewrite -[40%N]/(4 * 10)%N exprM -uw. Qed.

Lemma rate_inv_pow (c : RT) k : 0 <= c -> (0 < k)%N -> c / w ^+ k <= c / w.
Proof.
move=> c0 k0.
have w0 : 0 < w by apply: lt_le_trans w1.
rewrite ler_wpM2l // lef_pV2 ?posrE ?exprn_gt0 //.
case: k k0 => // k _; rewrite exprS.
by apply: ler_peMr; [exact: ltW|exact: exprn_ege1].
Qed.

Lemma rate_L2 : L ^+ 2 <= 4 * (1 + Mk) ^+ 2 * w ^+ 10.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have M0 : 0 <= 1 + Mk by rewrite addr_ge0 // le_max ler0n.
rewrite invrK uw -exprSr.
have w5 : 1 <= w ^+ 5 by exact: exprn_ege1.
have h0 : 0 <= (1 + w ^+ 5) * (1 + Mk).
  by rewrite mulr_ge0 // addr_ge0 // exprn_ge0 // ltW.
have h : (1 + w ^+ 5) * (1 + Mk) <= 2 * w ^+ 5 * (1 + Mk).
  by rewrite ler_wpM2r // mulr_natl mulr2n lerD2r.
apply: le_trans (_ : (2 * w ^+ 5 * (1 + Mk)) ^+ 2 <= _).
  by rewrite !expr2 ler_pM.
have -> : (2 * w ^+ 5 * (1 + Mk)) ^+ 2 = 4 * (1 + Mk) ^+ 2 * w ^+ 10 by ring.
exact: lexx.
Qed.

Lemma rate_ngamma : alpha * w ^+ 32 <= 2 * F * (N * gamma).
Proof.
have D0 : 0 < D by apply: lt_le_trans d1.
have u0 : 0 < u by rewrite uw exprn_gt0 // (lt_le_trans ltr01 w1).
have Du : 0 < D * u ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have -> : w ^+ 32 = u ^+ 8 by rewrite uw -exprM.
have key : alpha * u ^+ 8 * (D * u ^+ 2) <= 2 * F * N.
  have -> : alpha * u ^+ 8 * (D * u ^+ 2) = (alpha * D) * u ^+ 10 by ring.
  apply: le_trans (ler_wpM2l _ hpow) _; first by rewrite mulr_ge0 // ltW.
  have -> : alpha * D * (F * D) = F * (alpha * D ^+ 2) by ring.
  have := ler_wpM2l (ltW F0) hn.
  by have -> : F * (2 * N) = 2 * F * N by ring.
by rewrite mulrA ler_pdivlMr.
Qed.

Lemma rate_n36 : 72 * F / alpha <= u -> 36 <= N * gamma.
Proof.
move=> hu.
have u1 : 1 <= u by rewrite uw exprn_ege1.
have h := rate_ngamma.
have e8 : w ^+ 32 = u ^+ 8 by rewrite uw -exprM.
rewrite e8 in h.
have u8 : u <= u ^+ 8.
  by rewrite -[X in X <= _]expr1; apply: ler_weXn2l.
have h72 : 72 * F <= alpha * u ^+ 8.
  move: hu; rewrite ler_pdivrMr // => hu.
  apply: le_trans hu _; rewrite mulrC.
  by apply: ler_wpM2l; [exact: ltW|exact: u8].
set x := N / (D * u ^+ 2) in h *.
have F2 : 0 < 2 * F by rewrite mulr_gt0.
have e : 2 * F * 36 = 72 * F by ring.
have : 2 * F * 36 <= 2 * F * x by rewrite e; exact: le_trans h72 h.
by rewrite ler_pM2l.
Qed.

Lemma rate_E1 : 100 * A ^+ 2 * L ^+ 2 * (Num.sqrt (N * gamma))^-1
  <= 400 * A ^+ 2 * (1 + Mk) ^+ 2 * (1 + 2 * F / alpha) / w.
Proof.
set c1 := 1 + 2 * F / alpha.
have w0 : 0 < w by apply: lt_le_trans w1.
have wne : w != 0 by rewrite gt_eqF.
have c11 : 1 <= c1 by rewrite lerDl divr_ge0 // ?mulr_ge0 // ltW.
have c10 : 0 < c1 by apply: lt_le_trans c11.
have K4 : 0 <= A by rewrite addr_ge0 // exprn_even_ge0.
have A0 : 0 <= 100 * A ^+ 2 by rewrite mulr_ge0 // exprn_ge0.
have M0 : 0 <= 1 + Mk by rewrite addr_ge0 // le_max ler0n.
have F2 : 0 < 2 * F by rewrite mulr_gt0.
(* (n gamma)^(-1/2) <= c1 / w^16 *)
have hs : (Num.sqrt (N / (D * u ^+ 2)))^-1 <= c1 / w ^+ 16.
  apply: inv_sqrt_le; first by rewrite divr_gt0 // exprn_gt0.
  have h := rate_ngamma.
  apply: le_trans (_ : alpha * w ^+ 32 / (2 * F) <= _); last first.
    by rewrite ler_pdivrMr // [X in _ <= X]mulrC.
  have cne : c1 != 0 by rewrite gt_eqF.
  have Fne : F != 0 by rewrite gt_eqF.
  have -> : (c1 / w ^+ 16) ^- 2 = w ^+ 32 * (c1 ^+ 2)^-1 by field.
  have -> : alpha * w ^+ 32 / (2 * F) = w ^+ 32 * (alpha / (2 * F)).
    by field.
  apply: ler_wpM2l; first by rewrite exprn_ge0 // ltW.
  rewrite ler_pdivlMr // mulrC ler_pdivrMr ?exprn_gt0 //.
  have ane : alpha != 0 by rewrite gt_eqF.
  have e : alpha * c1 = alpha + 2 * F by rewrite /c1; field.
  have cc : c1 <= c1 ^+ 2 by rewrite expr2 ler_peMl // ltW.
  apply: le_trans (_ : alpha * c1 <= _); first by rewrite e lerDr ltW.
  by rewrite ler_wpM2l // ltW.
apply: le_trans (_ : 100 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) *
    (c1 / w ^+ 16) <= _).
  apply: ler_pM.
  - by rewrite mulr_ge0 // sqr_ge0.
  - by rewrite invr_ge0 sqrtr_ge0.
  - by rewrite ler_wpM2l // rate_L2.
  - exact: hs.
have -> : 100 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) * (c1 / w ^+ 16) =
    400 * A ^+ 2 * (1 + Mk) ^+ 2 * c1 / w ^+ 6 by field.
apply: rate_inv_pow => //.
apply: mulr_ge0; last exact: ltW.
apply: mulr_ge0; last exact: exprn_ge0.
by apply: mulr_ge0; [|exact: exprn_ge0].
Qed.

Lemma rate_E2 : 100 * A ^+ 2 * L ^+ 2 * (D * (tau * D / (kappa - 1) + 1) / N)
  <= 800 * A ^+ 2 * (1 + Mk) ^+ 2 * (C0 / (kappa - 1) + F) / alpha / w.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have wne : w != 0 by rewrite gt_eqF.
have D0 : 0 < D by apply: lt_le_trans d1.
have Dne : D != 0 by rewrite gt_eqF.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
have kne : kappa - 1 != 0 by rewrite gt_eqF.
have ane : alpha != 0 by rewrite gt_eqF.
have aD : 0 < alpha * D ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have N0 : 0 < N.
  have : 0 < 2 * N by apply: lt_le_trans hn.
  by rewrite pmulr_rgt0.
have K4 : 0 <= A by rewrite addr_ge0 // exprn_even_ge0.
have A0 : 0 <= 100 * A ^+ 2 by rewrite mulr_ge0 // exprn_ge0.
have M0 : 0 <= 1 + Mk by rewrite addr_ge0 // le_max ler0n.
have X0 : 0 <= D * (tau * D / (kappa - 1) + 1).
  apply: mulr_ge0; first exact: ltW.
  apply: addr_ge0 => //; apply: divr_ge0; last exact: ltW.
  by apply: mulr_ge0 => //; exact: ltW.
(* n >= alpha d^2 / 2 *)
have hDN : D * (tau * D / (kappa - 1) + 1) / N <=
    2 / alpha * (tau / (kappa - 1) + D^-1).
  have hN : N^-1 <= 2 / (alpha * D ^+ 2).
    rewrite -[2]invrK -invfM lef_pV2 ?posrE ?invr_gt0 ?mulr_gt0 //.
    have t2 : (0 : RT) < 2 by [].
    by rewrite mulrC ler_pdivrMr // [N * 2]mulrC.
  apply: le_trans (ler_wpM2l X0 hN) _.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
(* the powers of w *)
have ht : w ^+ 10 * tau <= C0 / w ^+ 2.
  have := ler_wpM2l (exprn_ge0 10 (ltW w0)) htau.
  rewrite uw -exprM.
  by have -> : w ^+ 10 * (C0 / w ^+ (4 * 3)) = C0 / w ^+ 2 by field.
have hD : D^-1 <= F / w ^+ 40.
  rewrite ler_pdivlMr ?exprn_gt0 // mulrC ler_pdivrMr //.
  exact: rate_pow.
have hd : w ^+ 10 * D^-1 <= F / w ^+ 30.
  apply: le_trans (ler_wpM2l (exprn_ge0 10 (ltW w0)) hD) _.
  by have -> : w ^+ 10 * (F / w ^+ 40) = F / w ^+ 30 by field.
have hw : w ^+ 10 * (tau / (kappa - 1) + D^-1) <=
    (C0 / (kappa - 1) + F) / w.
  rewrite mulrDr mulrDl.
  apply: lerD.
    have -> : w ^+ 10 * (tau / (kappa - 1)) =
        (w ^+ 10 * tau) / (kappa - 1) by rewrite mulrA.
    apply: le_trans (ler_wpM2r _ ht) _; first by rewrite invr_ge0 ltW.
    have -> : C0 / w ^+ 2 / (kappa - 1) = C0 / (kappa - 1) / w ^+ 2.
      by field.
    by apply: rate_inv_pow => //; rewrite divr_ge0 // ltW.
  apply: le_trans hd _.
  by apply: rate_inv_pow => //; rewrite ltW.
apply: le_trans (_ : 100 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) *
    (2 / alpha * (tau / (kappa - 1) + D^-1)) <= _).
  apply: ler_pM.
  - by rewrite mulr_ge0 // sqr_ge0.
  - by rewrite divr_ge0 // ltW.
  - by rewrite ler_wpM2l // rate_L2.
  - exact: hDN.
have C1 : 0 <= 800 * A ^+ 2 * (1 + Mk) ^+ 2 / alpha.
  apply: divr_ge0; last exact: ltW.
  by apply: mulr_ge0; [rewrite mulr_ge0 // exprn_ge0|exact: exprn_ge0].
have -> : 100 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) *
    (2 / alpha * (tau / (kappa - 1) + D^-1)) =
    800 * A ^+ 2 * (1 + Mk) ^+ 2 / alpha *
    (w ^+ 10 * (tau / (kappa - 1) + D^-1)) by ring.
apply: le_trans (ler_wpM2l C1 hw) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma rate_E3 : u^-1 + (D^-1 * u + gamma * D * u) <= (2 + F) / w.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have wne : w != 0 by rewrite gt_eqF.
have D0 : 0 < D by apply: lt_le_trans d1.
have Dne : D != 0 by rewrite gt_eqF.
have u0 : 0 < u by rewrite uw exprn_gt0.
have une : u != 0 by rewrite gt_eqF.
have -> : (D * u ^+ 2)^-1 * D * u = u^-1 by field.
have hu : u^-1 <= 1 / w by rewrite uw -div1r rate_inv_pow.
have hD : D^-1 <= F / w ^+ 40.
  rewrite ler_pdivlMr ?exprn_gt0 // mulrC ler_pdivrMr //.
  exact: rate_pow.
have hDu : D^-1 * u <= F / w.
  apply: le_trans (ler_wpM2r (ltW u0) hD) _.
  rewrite uw.
  have -> : F / w ^+ 40 * w ^+ 4 = F / w ^+ 36 by field.
  by apply: rate_inv_pow => //; rewrite ltW.
have -> : (2 + F) / w = 1 / w + (F / w + 1 / w) by field.
by rewrite lerD // lerD.
Qed.

Lemma rate_P1 : 4 * A ^+ 2 * L ^+ 2 / (N * u^-1 ^+ 2)
  <= 32 * A ^+ 2 * (1 + Mk) ^+ 2 * F / alpha / w.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have wne : w != 0 by rewrite gt_eqF.
have D0 : 0 < D by apply: lt_le_trans d1.
have Dne : D != 0 by rewrite gt_eqF.
have u0 : 0 < u by rewrite uw exprn_gt0.
have une : u != 0 by rewrite gt_eqF.
have ane : alpha != 0 by rewrite gt_eqF.
have aD : 0 < alpha * D ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have N0 : 0 < N.
  have : 0 < 2 * N by apply: lt_le_trans hn.
  by rewrite pmulr_rgt0.
have Nne : N != 0 by rewrite gt_eqF.
have K4 : 0 <= A by rewrite addr_ge0 // exprn_even_ge0.
have M0 : 0 <= 1 + Mk by rewrite addr_ge0 // le_max ler0n.
have hD : D^-1 <= F / w ^+ 40.
  rewrite ler_pdivlMr ?exprn_gt0 // mulrC ler_pdivrMr //.
  exact: rate_pow.
have hN : N^-1 <= 2 / alpha * (F / w ^+ 40).
  have h1 : N^-1 <= 2 / (alpha * D ^+ 2).
    rewrite -[2]invrK -invfM lef_pV2 ?posrE ?invr_gt0 ?mulr_gt0 //.
    have t2 : (0 : RT) < 2 by [].
    by rewrite mulrC ler_pdivrMr // [N * 2]mulrC.
  apply: le_trans h1 _.
  have -> : 2 / (alpha * D ^+ 2) = 2 / alpha * (D^-1 * D^-1).
    by rewrite expr2; field.
  apply: ler_wpM2l; first by rewrite divr_ge0 // ltW.
  apply: le_trans hD.
  by rewrite ler_pdivrMr // ler_peMr // invr_ge0 ltW.
have -> : 4 * A ^+ 2 * L ^+ 2 / (N * u^-1 ^+ 2) =
    4 * A ^+ 2 * L ^+ 2 * u ^+ 2 * N^-1 by field.
apply: le_trans (_ : 4 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) * u ^+ 2 *
    (2 / alpha * (F / w ^+ 40)) <= _).
  apply: ler_pM.
  - apply: mulr_ge0; last exact: exprn_ge0 (ltW u0).
    by apply: mulr_ge0; [rewrite mulr_ge0 // exprn_ge0|exact: sqr_ge0].
  - by rewrite invr_ge0 ltW.
  - apply: ler_wpM2r; first exact: exprn_ge0 (ltW u0).
    by apply: ler_wpM2l; [rewrite mulr_ge0 // exprn_ge0|exact: rate_L2].
  - exact: hN.
rewrite uw.
have -> : 4 * A ^+ 2 * (4 * (1 + Mk) ^+ 2 * w ^+ 10) * (w ^+ 4) ^+ 2 *
    (2 / alpha * (F / w ^+ 40)) =
    32 * A ^+ 2 * (1 + Mk) ^+ 2 * F / alpha / w ^+ 22 by field.
apply: rate_inv_pow => //.
apply: divr_ge0; last exact: ltW.
apply: mulr_ge0; last exact: ltW.
by apply: mulr_ge0; [rewrite mulr_ge0 // exprn_ge0|exact: exprn_ge0].
Qed.

Lemma rate_P2 : ((kappa - 1) / 2 + beta * Mk) / u <= ((kappa - 1) / 2 + Mk) / w.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have u1 : 1 <= u by rewrite uw exprn_ege1.
have u0 : 0 < u by apply: lt_le_trans u1.
have M0 : 0 <= Mk by rewrite le_max ler0n.
have uw1 : 1 <= u * w by rewrite -[1]mulr1 ler_pM.
have uw0 : 0 < u * w by apply: lt_le_trans uw1.
have b1 : (u * w)^-1 <= 1 by rewrite invf_le1.
have k0 : 0 <= (kappa - 1) / 2 by rewrite divr_ge0 // subr_ge0 ltW.
apply: le_trans (_ : ((kappa - 1) / 2 + Mk) / u <= _).
  apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
  by rewrite lerD2l ler_piMl // invr_ge0 ltW.
by rewrite uw; apply: rate_inv_pow => //; rewrite addr_ge0.
Qed.

Lemma rate_beta : beta * u = w^-1.
Proof.
have w0 : 0 < w by apply: lt_le_trans w1.
have u0 : 0 < u by rewrite uw exprn_gt0.
have wne : w != 0 by rewrite gt_eqF.
have une : u != 0 by rewrite gt_eqF.
by field.
Qed.

End rate_bounds.

Section unsat_rates.

Lemma unsat_rates (kappa alpha K C0 Cr e : R) :
  1 < kappa -> 0 < alpha -> 0 <= C0 -> 0 <= Cr -> 0 < e ->
  exists2 U : R, 1 <= U & forall (d n : nat) (tau : R),
    U <= ln d%:R -> alpha * d%:R ^+ 2 <= 2 * n%:R -> 0 <= tau ->
    tau <= C0 / ln d%:R ^+ 3 ->
    [/\ 36 <= n%:R * unsat_gamma d,
        100 * (1 + K ^+ 4) ^+ 2 *
          ((1 + (unsat_beta d)^-1) * (1 + Num.max 2 (kappa - 1))) ^+ 2 *
          ((Num.sqrt (n%:R * unsat_gamma d))^-1 +
           d%:R * (tau * d%:R / (kappa - 1) + 1) / n%:R) + (ln d%:R)^-1 +
          (d%:R^-1 * ln d%:R + unsat_gamma d * d%:R * ln (d%:R^-1)^-1) +
          Cr * unsat_beta d * ln d%:R <= e &
        4 * (1 + K ^+ 4) ^+ 2 *
          ((1 + (unsat_beta d)^-1) * (1 + Num.max 2 (kappa - 1))) ^+ 2 /
          (n%:R * (ln d%:R)^-1 ^+ 2) +
          ((kappa - 1) / 2 + unsat_beta d * Num.max 2 (kappa - 1)) /
          ln d%:R <= e].
Proof.
move=> k1 a0 C00 Cr0 e0.
have F0 : 0 < (10`!%:R : R) by rewrite ltr0n fact_gt0.
have K4 : 0 <= 1 + K ^+ 4 by rewrite addr_ge0 // exprn_even_ge0.
have M0 : 0 <= 1 + Num.max 2 (kappa - 1) by rewrite addr_ge0 // le_max ler0n.
have k0 : 0 < kappa - 1 by rewrite subr_gt0.
pose CE := 400 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
    (1 + 2 * 10`!%:R / alpha) +
  800 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
    (C0 / (kappa - 1) + 10`!%:R) / alpha + (2 + 10`!%:R) + Cr.
pose CP := 32 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
    10`!%:R / alpha + ((kappa - 1) / 2 + Num.max 2 (kappa - 1)).
have A2 : 0 <= (1 + K ^+ 4) ^+ 2 by exact: exprn_ge0.
have M2 : 0 <= (1 + Num.max 2 (kappa - 1)) ^+ 2 by exact: exprn_ge0.
have AM c : 0 <= c ->
    0 <= c * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2.
  by move=> c0; apply: mulr_ge0 => //; apply: mulr_ge0.
have Fa : 0 <= 2 * 10`!%:R / alpha :> R.
  by apply: divr_ge0; [apply: mulr_ge0 => //; exact: ltW|exact: ltW].
have CF : 0 <= C0 / (kappa - 1) + 10`!%:R.
  by apply: addr_ge0; [apply: divr_ge0 => //; exact: ltW|exact: ltW].
have CE0 : 0 <= CE.
  have t1 : 0 <= 400 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
      (1 + 2 * 10`!%:R / alpha).
    by apply: mulr_ge0; [apply: AM|apply: addr_ge0].
  have t2 : 0 <= 800 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
      (C0 / (kappa - 1) + 10`!%:R) / alpha.
    apply: divr_ge0; last exact: ltW.
    by apply: mulr_ge0; [apply: AM; exact: ler0n|exact: CF].
  have t3 : 0 <= 2 + 10`!%:R :> R.
    by apply: addr_ge0; [exact: ler0n|exact: ltW].
  exact: (addr_ge0 (addr_ge0 (addr_ge0 t1 t2) t3) Cr0).
have CP0 : 0 <= CP.
  have t1 : 0 <= 32 * (1 + K ^+ 4) ^+ 2 * (1 + Num.max 2 (kappa - 1)) ^+ 2 *
      10`!%:R / alpha.
    apply: divr_ge0; last exact: ltW.
    by apply: mulr_ge0; [apply: AM; exact: ler0n|exact: ltW].
  have t2 : 0 <= (kappa - 1) / 2 + Num.max 2 (kappa - 1).
    apply: addr_ge0; last by rewrite le_max ler0n.
    by apply: divr_ge0; [exact: ltW|exact: ler0n].
  exact: (addr_ge0 t1 t2).
exists (Num.max (Num.max 1 (72 * 10`!%:R / alpha))
                (Num.max ((CE / e) ^+ 4) ((CP / e) ^+ 4))).
  by rewrite !le_max lexx.
move=> d n tau hU hn tau0 htau.
have u1 : 1 <= ln (d%:R : R) by apply: le_trans hU; rewrite !le_max lexx.
have [w1 _ w4 _] := sqrt4_facts _ _ u1.
pose w := Num.sqrt (Num.sqrt (ln (d%:R : R))).
have uw : ln (d%:R : R) = w ^+ 4 by rewrite -w4.
have d1 : 1 <= d%:R :> R.
  have d0 : (0 < d)%N.
    rewrite lt0n; apply/negP => /eqP d0; move: u1; rewrite d0 ln0 //.
    by rewrite ler10.
  by rewrite ler1n.
have hpow := ln_pow10_le _ _ d1.
(* w = (ln d)^(1/4) is at least CE / e and CP / e *)
have hwE : CE / e <= w.
  apply: le_sqrt4; first by apply: divr_ge0 => //; exact: ltW.
  by apply: le_trans hU; rewrite !le_max lexx orbT.
have hwP : CP / e <= w.
  apply: le_sqrt4; first by apply: divr_ge0 => //; exact: ltW.
  by apply: le_trans hU; rewrite !le_max lexx !orbT.
have w0 : 0 < w by apply: lt_le_trans w1.
have hE : CE / w <= e by rewrite ler_pdivrMr // mulrC -ler_pdivrMr.
have hP : CP / w <= e by rewrite ler_pdivrMr // mulrC -ler_pdivrMr.
have h72 : 72 * 10`!%:R / alpha <= ln (d%:R : R).
  by apply: le_trans hU; rewrite !le_max lexx orbT.
split.
- exact: (rate_n36 _ _ _ _ _ _ _ a0 F0 w1 uw d1 hpow hn h72).
- have e1 := rate_E1 _ kappa _ K _ _ _ _ _ a0 F0 w1 uw d1 hpow hn.
  have e2 := rate_E2 _ kappa _ K _ _ _ _ _ _ _ k1 a0 C00 F0 w1 uw d1 hpow hn
    tau0 htau.
  have e3 := rate_E3 _ _ _ _ _ F0 w1 uw d1 hpow.
  have eb : unsat_beta d * ln (d%:R : R) = w^-1 := rate_beta _ _ _ w1 uw.
  rewrite invrK mulrDr -[_ + (ln _)^-1 + _]addrA.
  apply: le_trans hE.
  rewrite /CE (mulrDl _ _ w^-1) (mulrDl _ _ w^-1) (mulrDl _ _ w^-1).
  apply: lerD; last by rewrite -mulrA eb.
  apply: lerD; last exact: e3.
  by apply: lerD; [exact: e1|exact: e2].
- have p1 := rate_P1 _ kappa _ K _ _ _ _ _ a0 F0 w1 uw d1 hpow hn.
  have p2 := rate_P2 _ _ _ _ k1 w1 uw.
  apply: le_trans hP.
  rewrite /CP (mulrDl _ _ w^-1).
  by apply: lerD; [exact: p1|exact: p2].
Qed.

End unsat_rates.

Section unsat_limit.

Lemma unsat_value_concentration_law (kappa alpha K C0 Cr : R)
    (n : nat -> nat) (rho nu : forall d, probability 'rV[RR]_(d * d) RR)
    (tau : nat -> R) :
  1 < kappa -> 0 < alpha -> 0 <= C0 -> 0 <= Cr ->
  universality_density_tends_to n alpha ->
  (forall d, (0 < d)%N ->
     regular_feature K (tau d) (unsat_cov kappa d) (rho d)) ->
  (forall d, (0 < d)%N ->
     regular_feature K (tau d) (unsat_cov kappa d) (nu d)) ->
  (forall d, 0 <= tau d) ->
  (exists D, forall d, (D <= d)%N -> tau d <= C0 / ln d%:R ^+ 3) ->
  paper_main_tends_to (fun d => tuple_prod (fun=> rho d) (n d)
    [set Z | Cr * unsat_beta d * ln d%:R <
       unsat_ridge_value kappa (n d) d (unsat_beta d) Z -
       unsat_value (n d) d Z]) 0 ->
  forall eps : R, 0 < eps ->
    paper_main_tends_to (fun d => tuple_prod (fun=> rho d) (n d)
      [set Z | eps < `|unsat_value (n d) d Z -
         unsat_center kappa (n d) d (nu d) (unsat_beta d) (unsat_gamma d)|])
      0.
Proof.
move=> k1 a0 C00 Cr0 hdens hrho hnu tau0 [Dt hDt] hridge eps eps0 e e0.
have e2 : 0 < e / 2 by rewrite divr_gt0.
have [Dr hDr] := hridge _ e2.
have a2 : 0 < alpha / 2 by rewrite divr_gt0.
have [Da hDa] := hdens _ a2.
have m0 : 0 < Num.min eps (e / 2) by rewrite lt_min eps0 e2.
have [U U1 hU] := unsat_rates kappa alpha K C0 Cr (Num.min eps (e / 2)) k1 a0
  C00 Cr0 m0.
pose Du := (archimedean.Num.truncn (sequences.expR U)).+1.
exists (maxn (maxn Dr Da) (maxn Dt Du)) => d.
rewrite !geq_max => /andP[/andP[dDr dDa] /andP[dDt dDu]].
(* d is large: ln d >= U, n d >= alpha d^2 / 2 and tau d <= C0 (ln d)^-3 *)
have hu : U <= ln (d%:R : R).
  have hD3 : sequences.expR U < d%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  rewrite -[U]expRK ler_ln ?posrE ?expR_gt0 //; last exact: ltW.
  exact: lt_trans (expR_gt0 U) hD3.
have u1 : 1 <= ln (d%:R : R) by apply: le_trans hu.
have d0 : (0 < d)%N by apply: leq_trans dDu.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have d1 : 1 < d%:R :> R.
  rewrite ltNge; apply/negP => d1.
  have : ln (d%:R : R) <= 0 by rewrite ln_le0.
  by move=> h; have := le_trans u1 h; rewrite ler10.
have hnd : alpha * d%:R ^+ 2 <= 2 * (n d)%:R.
  have := hDa d dDa; rewrite /paper_main_density ltr_distl => /andP[h _].
  move: h; rewrite ltr_pdivlMr ?exprn_gt0 // => h.
  lra.
have nd0 : (0 < n d)%N.
  rewrite -(ltr0n R).
  have : 0 < alpha * d%:R ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
  lra.
have [h36 hE hP] := hU d (n d) (tau d) hu hnd (tau0 d) (hDt d dDt).
clear hU hdens hDa hridge.
(* the bound of dimension d *)
have l0 : 0 < ln (d%:R : R) by apply: lt_le_trans u1.
have b0 : 0 < unsat_beta d.
  by rewrite invr_gt0 mulr_gt0 // sqrtr_gt0 sqrtr_gt0.
have g0 : 0 < unsat_gamma d by rewrite invr_gt0 mulr_gt0 // exprn_gt0.
have e01 : 0 < (d%:R : R)^-1 < 1 by rewrite invr_gt0 dR invf_lt1.
have t0 : 0 < (ln (d%:R : R))^-1 by rewrite invr_gt0.
have hc := unsat_ridge_concentration kappa K (tau d) (n d) d (rho d) (nu d) k1
  nd0 d0 (tau0 d) (hrho d d0) (hnu d d0) (unsat_beta d) (unsat_gamma d)
  (d%:R^-1) (ln d%:R)^-1 (ln d%:R) b0 g0 e01 t0 l0 h36.
clear hrho hnu hDt.
set c := unsat_center kappa (n d) d (nu d) (unsat_beta d) (unsat_gamma d)
  in hc *.
set err := (100 * _ * _ * _ + _ + _) in hc hE.
set pb := (4 * _ * _ / _ + _) in hc hP.
clear hu u1 Du dDu.
(* the events *)
have mR := measurable_unsat_ridge_value kappa (unsat_beta d) (n d) d
  (ltW b0).
have mV := measurable_unsat_value (n d) d.
have mA : measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    (err < `|unsat_ridge_value kappa (n d) d (unsat_beta d) Z - c|)%R].
  apply: measurable_set_lt.
  apply: (measurableT_comp (@normr_measurable RR _)).
  exact: measurable_funB.
have mB := measurable_unsat_gap kappa (unsat_beta d)
  (Cr * unsat_beta d * ln d%:R) (n d) d (ltW b0).
have mE : measurable [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    (eps < `|unsat_value (n d) d Z - c|)%R].
  apply: measurable_set_lt.
  apply: (measurableT_comp (@normr_measurable RR _)).
  exact: measurable_funB.
rewrite sube0 gee0_abs; first exact: measure_ge0.
have sub : [set Z : (n d).-tuple 'rV[RR]_(d * d) |
    (eps < `|unsat_value (n d) d Z - c|)%R] `<=`
    [set Z | (err <
      `|unsat_ridge_value kappa (n d) d (unsat_beta d) Z - c|)%R] `|`
    [set Z | (Cr * unsat_beta d * ln d%:R <
      unsat_ridge_value kappa (n d) d (unsat_beta d) Z -
      unsat_value (n d) d Z)%R].
  move=> Z /= hZ.
  case: (ltP err `|unsat_ridge_value kappa (n d) d (unsat_beta d) Z - c|).
    by left.
  move=> hA'; right.
  rewrite ltNge; apply/negP => hB.
  have g0' := unsat_value_le_ridge kappa (unsat_beta d) (n d) d Z (ltW b0).
  have hm : err + Cr * unsat_beta d * ln d%:R <= eps.
    by apply: le_trans hE _; rewrite ge_min lexx.
  have tri := ler_distD (unsat_ridge_value kappa (n d) d (unsat_beta d) Z)
    (unsat_value (n d) d Z) c.
  have e1 : `|unsat_value (n d) d Z -
      unsat_ridge_value kappa (n d) d (unsat_beta d) Z| =
      unsat_ridge_value kappa (n d) d (unsat_beta d) Z -
      unsat_value (n d) d Z.
    by rewrite distrC ger0_norm // subr_ge0.
  rewrite e1 in tri.
  lra.
have h1 := le_measure (tuple_prod (fun=> rho d) (n d)) (mem_set mE)
  (mem_set (measurableU _ _ mA mB)) sub.
apply: le_lt_trans h1 _.
apply: le_lt_trans (measureU2 _ mA mB) _.
have hpb : pb <= e / 2 by apply: le_trans hP _; rewrite ge_min lexx orbT.
have hB := hDr d dDr.
rewrite sube0 gee0_abs in hB; first exact: measure_ge0.
have hA : (tuple_prod (fun=> rho d) (n d) [set Z |
    (err < `|unsat_ridge_value kappa (n d) d (unsat_beta d) Z - c|)%R] <=
    (e / 2)%:E)%E.
  by apply: le_trans hc _; rewrite lee_fin.
rewrite [e]splitr EFinD.
apply: lee_ltD => //.
by rewrite ge0_fin_numE ?measure_ge0 // (le_lt_trans hA) ?ltry.
Qed.

End unsat_limit.
