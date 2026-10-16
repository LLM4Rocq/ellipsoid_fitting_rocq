From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix archimedean.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm quadratic_series_variance.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.

(**md**************************************************************************)
(* # Vanishing centered reserve corrections                                 *)
(* Source: the independent-reserve argument in doc/shifted-gaussian.tex.      *)
(* The matrix and right-hand side have independent laws. All hypotheses and *)
(* conclusions use explicit tolerances and eventual dimension bounds.       *)
(* Tightness constants are selected before the dimension; no event is       *)
(* asserted to control every right-hand side simultaneously.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section event_monotonicity.
Context {R : realType} {k d : nat}.

Lemma reserve_failure_antitone (r1 r2 u1 u2 : R) :
  r1 <= r2 -> u1 <= u2 ->
  (@reserve_failure R k d r2 u2) `<=` reserve_failure r1 u1.
Proof.
move=> rr uu [H b] /or3P[bad|bad|bad]; apply/or3P.
- by constructor 1.
- constructor 2; exact: le_lt_trans rr bad.
- constructor 3; exact: le_lt_trans uu bad.
Qed.

Lemma reserve_failure_measure_antitone (P : probability ('M[R]_(k,d) * 'cV[R]_d)%type R)
    (r1 r2 u1 u2 : R) :
  r1 <= r2 -> u1 <= u2 ->
  (P (reserve_failure r2 u2) <= P (reserve_failure r1 u1))%E.
Proof.
move=> rr uu; apply: le_measure; rewrite ?inE.
- exact: reserve_failure_measurable.
- exact: reserve_failure_measurable.
- exact: reserve_failure_antitone.
Qed.

End event_monotonicity.

Section scalar_bounds.
Variable R : realType.

Definition reserve_variance_scale (L M c : R) :=
  M * (2 * L ^+ 2 + 2 * c) + Num.sqrt (c * (2 * L ^+ 2 + 2 * c)).

Lemma reserve_variance_scale_ge0 L M c :
  0 <= M -> 0 <= c -> 0 <= reserve_variance_scale L M c.
Proof.
move=> M0 c0; rewrite /reserve_variance_scale.
apply: addr_ge0; last exact: sqrtr_ge0.
apply: mulr_ge0 => //; have := sqr_ge0 L; nra.
Qed.

Lemma reserve_variance_scaling (x L M c : R) (k : nat) :
  1 <= x -> 0 <= M -> 0 <= c -> k%:R <= c * x ^+ 2 ->
  M * x * quadratic_fourth_constant k (L * x) +
    Num.sqrt (k%:R * quadratic_fourth_constant k (L * x)) <=
  reserve_variance_scale L M c * x ^+ 3.
Proof.
move=> x1 M0 c0 kc.
have x0 : 0 <= x by lra.
pose F := 2 * L ^+ 2 + 2 * c.
have F0 : 0 <= F by rewrite /F; have := sqr_ge0 L; nra.
have f0 := quadratic_fourth_constant_ge0 k (L * x).
have fB : quadratic_fourth_constant k (L * x) <= F * x ^+ 2.
  rewrite /quadratic_fourth_constant /F exprMn; nra.
have kf : k%:R * quadratic_fourth_constant k (L * x) <= c * F * x ^+ 4.
  have h := ler_pM (ler0n R k) f0 kc fB.
  have e : c * x ^+ 2 * (F * x ^+ 2) = c * F * x ^+ 4 by ring.
  by rewrite e in h.
have root : Num.sqrt (k%:R * quadratic_fourth_constant k (L * x)) <=
    Num.sqrt (c * F) * x ^+ 2.
  have e : c * F * x ^+ 4 = (c * F) * (x ^+ 2) ^+ 2 by ring.
  have h : Num.sqrt (k%:R * quadratic_fourth_constant k (L * x)) <=
      Num.sqrt (c * F * x ^+ 4).
    by rewrite ler_sqrt ?mulr_ge0 ?exprn_ge0.
  by rewrite e (@sqrtrM R (c * F) ((x ^+ 2) ^+ 2)) ?mulr_ge0 //
    sqrtr_sqr ger0_norm ?sqr_ge0 in h.
have mx0 : 0 <= M * x by rewrite mulr_ge0.
have first := ler_wpM2l mx0 fB.
have eqf : M * x * (F * x ^+ 2) = M * F * x ^+ 3 by ring.
rewrite eqf in first.
apply: le_trans (lerD first root) _.
rewrite /reserve_variance_scale -/F mulrDl lerD2l.
apply: ler_wpM2l; first exact: sqrtr_ge0.
rewrite exprS -[leLHS]mul1r; by apply: ler_wpM2r; rewrite ?sqr_ge0.
Qed.


Lemma reserve_variance_root_scaling (x L M c : R) (k : nat) :
  1 <= x -> 0 <= M -> 0 <= c -> k%:R <= c * x ^+ 2 ->
  Num.sqrt (M * x * quadratic_fourth_constant k (L * x) +
    Num.sqrt (k%:R * quadratic_fourth_constant k (L * x))) <=
  Num.sqrt (reserve_variance_scale L M c) * x * Num.sqrt x.
Proof.
move=> x1 M0 c0 kc.
have x0 : 0 <= x by lra.
have V0 := reserve_variance_scale_ge0 L M0 c0.
have h := ler_wsqrtr (@reserve_variance_scaling x L M c k x1 M0 c0 kc).
have e : x ^+ 3 = x ^+ 2 * x by ring.
by rewrite (@sqrtrM R (reserve_variance_scale L M c) (x ^+ 3)) //
  e (@sqrtrM R (x ^+ 2) x) ?sqr_ge0 // sqrtr_sqr ger0_norm // mulrA in h.
Qed.

Definition reserve_tail_scale (L M c C B : R) :=
  40 * B * Num.sqrt (reserve_variance_scale L M C) / c.

Lemma reserve_tail_scale_ge0 L M c C B :
  0 <= c -> 0 <= B -> 0 <= reserve_tail_scale L M c C B.
Proof.
by move=> c0 B0; rewrite /reserve_tail_scale !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?ler0n.
Qed.

Lemma reserve_tail_scaling (k d : nat) (L M c C B : R) :
  (0 < d)%N -> 0 <= M -> 0 < c -> 0 <= C -> 0 <= B ->
  c * d%:R ^+ 2 <= k%:R -> k%:R <= C * d%:R ^+ 2 ->
  @reserve_tail_coefficient R k d (L * d%:R) (M * d%:R) *
      (B * Num.sqrt d%:R) <=
    reserve_tail_scale L M c C B * Num.sqrt (ln (2 * d%:R)).
Proof.
move=> d0 M0 c0 C0 B0 lo hi.
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
have cx0 : 0 < c * d%:R ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have k0 : (0 : R) < k%:R := lt_le_trans cx0 lo.
have invk : k%:R^-1 <= (c * d%:R ^+ 2)^-1.
  by rewrite lef_pV2 ?posrE.
have root := @reserve_variance_root_scaling d%:R L M C k x1 M0 C0 hi.
pose V := Num.sqrt (reserve_variance_scale L M C).
pose l : R := Num.sqrt (ln (2 * d%:R)).
pose s := Num.sqrt (d%:R : R).
have vl0 : 0 <= 40 * l by rewrite /l mulr_ge0 ?ler0n ?sqrtr_ge0.
have bs0 : 0 <= B * s by rewrite /s mulr_ge0 ?sqrtr_ge0.
rewrite /reserve_tail_coefficient -/l -/s.
apply: le_trans (_ : (40 * l * (V * d%:R * s) /
    (c * d%:R ^+ 2)) * (B * s) <= _).
  apply: ler_wpM2r => //.
  apply: ler_pM; [by rewrite mulr_ge0 ?sqrtr_ge0 |
    by rewrite invr_ge0 ltW | | exact: invk].
  by apply: ler_wpM2l.
rewrite invfM.
have e : 40 * l * (V * d%:R * s) * (c^-1 * (d%:R ^+ 2)^-1) * (B * s) =
    (40 * B * V / c * l) * (d%:R * s ^+ 2 / d%:R ^+ 2) by ring.
have dx0 : (d%:R : R) ^+ 2 != 0 by rewrite sqrf_eq0 gt_eqF.
by rewrite e /s (sqr_sqrtr x00) -[d%:R * d%:R]expr2 (divff dx0) mulr1.
Qed.


Lemma reserve_inverse_root_scaling (x c N : R) :
  0 < x -> 0 < c -> c * x ^+ 2 <= N ->
  Num.sqrt (2 / N) <= Num.sqrt (2 / c) / x.
Proof.
move=> x0 c0 lo.
have x00 := ltW x0.
have cx0 : 0 < c * x ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have N0 : 0 < N := lt_le_trans cx0 lo.
have invN : N^-1 <= (c * x ^+ 2)^-1 by rewrite lef_pV2 ?posrE.
have divB : 2 / N <= 2 / (c * x ^+ 2) by apply: ler_wpM2l; rewrite ?ler0n.
have h := ler_wsqrtr divB.
rewrite invfM mulrA in h.
by rewrite (@sqrtrM R (2 / c) ((x ^+ 2)^-1)) ?divr_ge0 ?ler0n ?(ltW c0) //
  sqrtrV ?sqr_ge0 // sqrtr_sqr ger0_norm // in h.
Qed.

Lemma reserve_correction_norm_scaling (k d : nat) (c B : R) :
  (0 < d)%N -> 0 < c -> 0 <= B -> c * d%:R ^+ 2 <= k%:R ->
  Num.sqrt (2 / k%:R) * (B * Num.sqrt d%:R) <=
    (B * Num.sqrt (2 / c)) / Num.sqrt d%:R.
Proof.
move=> d0 c0 B0 lo.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
have s0 : (0 : R) < Num.sqrt d%:R by rewrite sqrtr_gt0.
have root := reserve_inverse_root_scaling x0 c0 lo.
apply: le_trans (ler_wpM2r (_ : 0 <= B * Num.sqrt d%:R) root) _.
  by rewrite mulr_ge0 ?sqrtr_ge0.
have e : Num.sqrt (2 / c) / d%:R * (B * Num.sqrt d%:R) =
    (B * Num.sqrt (2 / c) / Num.sqrt d%:R) *
      (Num.sqrt d%:R ^+ 2 / d%:R).
  rewrite expr2; field by rewrite ?gt_eqF //.
have xn : (d%:R : R) != 0 by rewrite gt_eqF.
by rewrite e (sqr_sqrtr x00) (divff xn) mulr1.
Qed.

Lemma reserve_correction_error_scaling (k d : nat) (c L A B : R) :
  (0 < d)%N -> 0 < c -> 0 <= L -> 0 <= A -> 0 <= B ->
  c * d%:R ^+ 2 <= k%:R ->
  (2 * (B * Num.sqrt d%:R) / k%:R) *
    ((L * d%:R) * (A * d%:R) * (A / Num.sqrt d%:R) +
      (A / Num.sqrt d%:R) * (A * d%:R * Num.sqrt d%:R)) <=
  (2 * B / c) * (L + 1) * A ^+ 2.
Proof.
move=> d0 c0 L0 A0 B0 lo.
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
have s0 : (0 : R) < Num.sqrt d%:R by rewrite sqrtr_gt0.
have sx : Num.sqrt (d%:R : R) <= d%:R.
  have h : d%:R <= (d%:R : R) ^+ 2 by nra.
  have hs := ler_wsqrtr h.
  by rewrite sqrtr_sqr ger0_norm in hs.
have cx0 : 0 < c * d%:R ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have k0 : (0 : R) < k%:R := lt_le_trans cx0 lo.
have invk : k%:R^-1 <= (c * d%:R ^+ 2)^-1 by rewrite lef_pV2 ?posrE.
pose x := (d%:R : R).
pose s := Num.sqrt (d%:R : R).
have e : (2 * (B * s) / k%:R) *
    ((L * x) * (A * x) * (A / s) + (A / s) * (A * x * s)) =
    (2 * B * A ^+ 2) * (L * x ^+ 2 + x * s) / k%:R.
  field by rewrite ?gt_eqF //.
rewrite -/x -/s e.
have n0 : 0 <= 2 * B * A ^+ 2 by rewrite !mulr_ge0 ?ler0n ?sqr_ge0.
have num : L * x ^+ 2 + x * s <= (L + 1) * x ^+ 2.
  have hs := ler_wpM2l x00 sx; rewrite -/x -/s in hs; nra.
have ln0 : 0 <= L * x ^+ 2 + x * s.
  by rewrite addr_ge0 ?mulr_ge0 ?sqr_ge0 ?sqrtr_ge0.
apply: le_trans (_ : (2 * B * A ^+ 2) * ((L + 1) * x ^+ 2) /
    (c * x ^+ 2) <= _).
  apply: ler_pM; [by rewrite mulr_ge0 | by rewrite invr_ge0 ltW | | exact: invk].
  by apply: ler_wpM2l.
have ee : (2 * B * A ^+ 2) * ((L + 1) * x ^+ 2) / (c * x ^+ 2) =
    (2 * B / c) * (L + 1) * A ^+ 2.
  field by rewrite ?gt_eqF //.
by rewrite ee.
Qed.


Lemma reserve_sqrt_log_bound (x : R) :
  1 <= x -> Num.sqrt (ln (2 * x)) <= 2 * Num.sqrt (Num.sqrt x).
Proof.
move=> x1.
have x0 : 0 <= x by lra.
have tx0 : 0 < 2 * x by nra.
have st0 : 0 < Num.sqrt (2 * x) by rewrite sqrtr_gt0.
have txsq := sqr_sqrtr (ltW tx0).
have xsq := sqr_sqrtr x0.
have stB : Num.sqrt (2 * x) <= 2 * Num.sqrt x.
  have lhs0 := sqrtr_ge0 (2 * x).
  have rhs0 : 0 <= 2 * Num.sqrt x by rewrite mulr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite -(@ler_sqr R _ _ lhs0 rhs0) exprMn txsq xsq.
  nra.
have logE : ln (2 * x) = 2 * ln (Num.sqrt (2 * x)).
  rewrite -{1}txsq lnXn // mulr2n; ring.
have sub := ln_sublinear st0.
have logB : ln (2 * x) <= 4 * Num.sqrt x by rewrite logE; lra.
have root := ler_wsqrtr logB.
have e : 4 * Num.sqrt x = (2 * Num.sqrt (Num.sqrt x)) ^+ 2.
  by rewrite exprMn sqr_sqrtr ?sqrtr_ge0 //; ring.
have rhs0 : 0 <= 2 * Num.sqrt (Num.sqrt x) by rewrite mulr_ge0 ?ler0n ?sqrtr_ge0.
by rewrite e sqrtr_sqr ger0_norm in root.
Qed.

Lemma reserve_eventually_ge (x : R) :
  exists d0 : nat, forall d, (d0 <= d)%N -> x <= d%:R.
Proof.
exists (Num.truncn x).+1 => d hd.
apply: ltW; apply: lt_le_trans (truncnS_gt x) _.
by rewrite ler_nat.
Qed.

Lemma reserve_log_rate_small (K delta : R) :
  0 <= K -> 0 < delta -> exists d0 : nat, forall d, (d0 <= d)%N ->
  [ /\ (0 < d)%N, K / Num.sqrt d%:R <= delta &
    K * (1 + Num.sqrt (ln (2 * d%:R))) <= delta * Num.sqrt d%:R ].
Proof.
move=> K0 delta0.
pose a := 1 + 3 * K / delta.
have a1 : 1 <= a by rewrite /a lerDl divr_ge0 ?mulr_ge0 ?ler0n ?(ltW delta0).
have a0 : 0 < a by lra.
have [n hn] := reserve_eventually_ge (a ^+ 4).
exists (maxn 1 n) => d; rewrite geq_max => /andP[d1 dn].
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
pose s := Num.sqrt (d%:R : R).
pose z := Num.sqrt s.
have s0 : 0 < s by rewrite /s sqrtr_gt0.
have z0 : 0 <= z := sqrtr_ge0 s.
have ss : s ^+ 2 = d%:R := sqr_sqrtr x00.
have zz : z ^+ 2 = s := sqr_sqrtr (ltW s0).
have z4 : z ^+ 4 = d%:R.
  have e : z ^+ 4 = (z ^+ 2) ^+ 2 by ring.
  by rewrite e zz ss.
have az4 : a ^+ 4 <= z ^+ 4 by rewrite z4; exact: hn.
have az : a <= z.
  by move: az4; rewrite ler_pXn2r ?nnegrE ?(ltW a0).
have za : 1 <= z by lra.
have ad : delta * a = delta + 3 * K.
  rewrite /a; field by rewrite ?gt_eqF.
have Kz : 3 * K <= delta * z.
  have h := ler_wpM2l (ltW delta0) az; nra.
have Ksmall : K <= delta * s.
  rewrite -zz; nra.
have logB := reserve_sqrt_log_bound x1.
rewrite -/s -/z in logB.
have bound : K * (1 + Num.sqrt (ln (2 * d%:R))) <= delta * s.
  have h := ler_wpM2l K0 (lerD (lexx (1 : R)) logB).
  rewrite -zz; nra.
split => //.
by rewrite ler_pdivrMr.
Qed.

End scalar_bounds.


Section sample_counts.
Context {R : realType}.

Lemma reserve_counts_of_limit (k : nat -> nat) (gamma : R) :
  0 < gamma ->
  (forall eps : R, 0 < eps -> exists n : nat, forall d, (n <= d)%N ->
    `| (k d)%:R / d%:R ^+ 2 - gamma | < eps) ->
  exists n : nat, forall d, (n <= d)%N ->
    gamma / 2 * d%:R ^+ 2 <= (k d)%:R <= (2 * gamma) * d%:R ^+ 2.
Proof.
move=> gamma0 limit.
have ep0 : 0 < gamma / 2 by rewrite divr_gt0 ?ltr0n.
have [n hn] := limit _ ep0.
exists (maxn 1 n) => d; rewrite geq_max => /andP[d1 dn].
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x20 : (0 : R) < d%:R ^+ 2 by rewrite exprn_gt0.
have hr := hn d dn; rewrite ltr_norml in hr; move/andP: hr => [lb ub].
apply/andP; split.
- rewrite -ler_pdivlMr //; lra.
- rewrite -ler_pdivrMr //; lra.
Qed.

End sample_counts.

Section asymptotic_reserve.
Context {R : realType}.
Variable k : nat -> nat.
Variable Q : forall d, probability 'M[R]_(k d,d) R.
Variable nu : forall d, probability 'cV[R]_d R.
Variables L M : R.
Hypotheses (L0 : 0 <= L) (M0 : 0 <= M).
Hypothesis signQ : forall d, reserve_sign_invariant (Q d).
Hypothesis intrinsic_probability : forall eps : R, 0 < eps ->
  exists d0 : nat, forall d, (d0 <= d)%N ->
    (Q d (~` reserve_intrinsic (L * d%:R) (M * d%:R)) <= eps%:E)%E.
Hypothesis covariance_tight : forall eps : R, 0 < eps ->
  exists A : R, 0 < A /\ exists d0 : nat, forall d, (d0 <= d)%N ->
    (Q d (~` reserve_covariance_event (A / Num.sqrt d%:R) (A * d%:R)
      (A / Num.sqrt d%:R) (A * d%:R * Num.sqrt d%:R)) <= eps%:E)%E.
Hypothesis rhs_tight : forall eps : R, 0 < eps ->
  exists B : R, 0 < B /\ exists d0 : nat, forall d, (d0 <= d)%N ->
    (nu d [set b | (B * Num.sqrt d%:R < frobenius b)%R] <= eps%:E)%E.

Lemma reserve_rate_from_counts (c C : R) :
  0 < c -> 0 <= C ->
  (exists n : nat, forall d, (n <= d)%N ->
    c * d%:R ^+ 2 <= (k d)%:R <= C * d%:R ^+ 2) ->
  forall eps : R, 0 < eps -> exists K : R, 0 < K /\
    exists d0 : nat, forall d, (d0 <= d)%N ->
    ((Q d \x nu d) (reserve_failure (K / Num.sqrt d%:R)
      (K * (1 + Num.sqrt (ln (2 * d%:R))))) <= eps%:E)%E.
Proof.
move=> c0 C0 [nc hcount] eps eps0.
have ep0 : 0 < eps / 4 by rewrite divr_gt0 ?ltr0n.
have [ne he] := intrinsic_probability ep0.
have [A [A0 [ng hg]]] := covariance_tight ep0.
have [B [B0 [nb hb]]] := rhs_tight ep0.
have A00 := ltW A0.
have B00 := ltW B0.
pose Kt := reserve_tail_scale L M c C B.
have Kt0 : 0 <= Kt := reserve_tail_scale_ge0 L M C (ltW c0) B00.
pose T := 1 + 4 * Kt / eps.
have T1 : 1 <= T.
  rewrite /T lerDl; apply: divr_ge0; last exact: ltW eps0.
  by apply: mulr_ge0; rewrite ?ler0n.
have T0 : 0 < T by lra.
pose Er := (2 * B / c) * (L + 1) * A ^+ 2.
have L10 : 0 <= L + 1 by apply: addr_ge0 => //; exact: ler01.
have Er0 : 0 <= Er.
  rewrite /Er; apply: mulr_ge0; last exact: sqr_ge0.
  apply: mulr_ge0 => //; apply: divr_ge0; last exact: ltW c0.
  by apply: mulr_ge0; rewrite ?ler0n.
pose Kr := B * Num.sqrt (2 / c).
have Kr0 : 0 <= Kr by rewrite /Kr mulr_ge0 ?sqrtr_ge0.
pose K := 1 + Kr + T + Er.
have K0 : 0 < K by rewrite /K; lra.
have KrK : Kr <= K by rewrite /K; lra.
have TK : T + Er <= K by rewrite /K; lra.
have [na ha] := reserve_eventually_ge ((2 * A) ^+ 2).
exists K; split => //.
exists (maxn 1 (maxn nc (maxn ne (maxn ng (maxn nb na))))) => d.
rewrite !geq_max => /andP[d1 /andP[dc /andP[de /andP[dg /andP[db da]]]]].
have d0 : (0 < d)%N by [].
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
have /andP[lo hi] := hcount d dc.
have kd0 : (0 < k d)%N.
  rewrite -(@ltr0n R); apply: lt_le_trans lo.
  by rewrite mulr_gt0 // exprn_gt0.
pose s := Num.sqrt (d%:R : R).
pose ell := 1 + Num.sqrt (ln (2 * d%:R) : R).
have s0 : 0 < s by rewrite /s sqrtr_gt0.
have s00 := ltW s0.
have ell1 : 1 <= ell by rewrite /ell lerDl sqrtr_ge0.
have ell0 : 0 < ell by lra.
have eta0 : 0 <= A / s by rewrite divr_ge0.
have eta2 : A / s <= 2^-1.
  have hs := ler_wsqrtr (ha d da).
  rewrite sqrtr_sqr ger0_norm ?mulr_ge0 ?ler0n // -/s in hs.
  rewrite ler_pdivrMr //; lra.
have Ad0 : 0 <= A * d%:R by rewrite mulr_ge0.
have Ads0 : 0 <= A * d%:R * s by rewrite mulr_ge0.
have Bs0 : 0 <= B * s by rewrite mulr_ge0.
have Ld0 : 0 <= L * d%:R by rewrite mulr_ge0.
have Md0 : 0 <= M * d%:R by rewrite mulr_ge0.
have t0 : 0 < T * ell by rewrite mulr_gt0.
have finite := @reserve_independent_correction_tail R (k d) d (Q d) (nu d)
  (L * d%:R) (M * d%:R) (A / s) (A * d%:R) (A / s) (A * d%:R * s)
  (B * s) (T * ell) kd0 d0 (@signQ d) Ld0 Md0 eta0 eta2 Ad0 eta0 Ads0 Bs0 t0.
have rawtail := @reserve_tail_scaling R (k d) d L M c C B d0 M0 c0 C0 B00 lo hi.
rewrite -/s -/Kt in rawtail.
have tailbd : (@reserve_tail_coefficient R (k d) d (L * d%:R) (M * d%:R) * (B * s) /
    (T * ell) <= eps / 4 :> R).
  have quot : @reserve_tail_coefficient R (k d) d (L * d%:R) (M * d%:R) * (B * s) /
      (T * ell) <= Kt / T.
    rewrite ler_pdivrMr //.
    have eqr : Kt / T * (T * ell) = Kt * ell by field by rewrite ?gt_eqF.
    rewrite eqr.
    apply: le_trans rawtail _; rewrite /ell mulrDr mulr1; lra.
  apply: le_trans quot _; rewrite ler_pdivrMr //.
  have e : eps / 4 * T = eps / 4 + Kt.
    by rewrite /T; field by rewrite ?gt_eqF.
  rewrite e; lra.
have probability_bound :
  ((Q d \x nu d) (reserve_failure (Num.sqrt (2 / (k d)%:R) * (B * s))
    (T * ell + (2 * (B * s) / (k d)%:R) *
      ((L * d%:R) * (A * d%:R) * (A / s) +
        (A / s) * (A * d%:R * s)))) <= eps%:E)%E.
  apply: le_trans finite _.
  have tailbdE : ((@reserve_tail_coefficient R (k d) d (L * d%:R) (M * d%:R) * (B * s) /
      (T * ell))%:E <= (eps / 4)%:E)%E by rewrite lee_fin.
  have sum := leeD (leeD (leeD (hb d db) (he d de)) (hg d dg)) tailbdE.
  apply: le_trans sum _.
  rewrite -!EFinD lee_fin; lra.
have rb := @reserve_correction_norm_scaling R (k d) d c B d0 c0 B00 lo.
rewrite -/s -/Kr in rb.
have rbound : Num.sqrt (2 / (k d)%:R) * (B * s) <= K / s.
  apply: le_trans rb _; apply: ler_wpM2r; first by rewrite invr_ge0.
  exact: KrK.
have eb := @reserve_correction_error_scaling R (k d) d c L A B
  d0 c0 L0 A00 B00 lo.
rewrite -/s -/Er in eb.
have ubound : T * ell + (2 * (B * s) / (k d)%:R) *
    ((L * d%:R) * (A * d%:R) * (A / s) +
      (A / s) * (A * d%:R * s)) <= K * ell.
  have := lerD (lexx (T * ell)) eb; nra.
have inclusion := @reserve_failure_antitone R (k d) d _ _ _ _ rbound ubound.
apply: le_trans (_ : ((Q d \x nu d) (reserve_failure
    (Num.sqrt (2 / (k d)%:R) * (B * s))
    (T * ell + (2 * (B * s) / (k d)%:R) *
      ((L * d%:R) * (A * d%:R) * (A / s) +
        (A / s) * (A * d%:R * s)))) <= eps%:E)%E) => //.
apply: le_measure; rewrite ?inE.
- exact: reserve_failure_measurable.
- exact: reserve_failure_measurable.
- exact: inclusion.
Qed.


Theorem reserve_rate (gamma : R) :
  0 < gamma ->
  (forall eps : R, 0 < eps -> exists n : nat, forall d, (n <= d)%N ->
    `| (k d)%:R / d%:R ^+ 2 - gamma | < eps) ->
  forall eps : R, 0 < eps -> exists K : R, 0 < K /\
    exists d0 : nat, forall d, (d0 <= d)%N ->
    ((Q d \x nu d) (reserve_failure (K / Num.sqrt d%:R)
      (K * (1 + Num.sqrt (ln (2 * d%:R))))) <= eps%:E)%E.
Proof.
move=> gamma0 limit.
apply: (@reserve_rate_from_counts (gamma / 2) (2 * gamma)).
- by rewrite divr_gt0 ?ltr0n.
- by rewrite mulr_ge0 ?ler0n ?(ltW gamma0).
- exact: reserve_counts_of_limit.
Qed.

Theorem reserve_correction_converges (gamma : R) :
  0 < gamma ->
  (forall eps : R, 0 < eps -> exists n : nat, forall d, (n <= d)%N ->
    `| (k d)%:R / d%:R ^+ 2 - gamma | < eps) ->
  forall eps delta : R, 0 < eps -> 0 < delta ->
  exists d0 : nat, forall d, (d0 <= d)%N ->
    ((Q d \x nu d) (reserve_failure delta (delta * Num.sqrt d%:R)) <= eps%:E)%E.
Proof.
move=> gamma0 limit eps delta eps0 delta0.
have [K [K0 [nr hr]]] := reserve_rate gamma0 limit eps0.
have [ns hs] := reserve_log_rate_small (ltW K0) delta0.
exists (maxn nr ns) => d; rewrite geq_max => /andP[dr ds].
have [d0 rb qb] := hs d ds.
apply: le_trans (_ : ((Q d \x nu d)
    (reserve_failure (K / Num.sqrt d%:R)
      (K * (1 + Num.sqrt (ln (2 * d%:R))))) <= eps%:E)%E); last exact: hr.
apply: le_measure; rewrite ?inE.
- exact: reserve_failure_measurable.
- exact: reserve_failure_measurable.
- exact: reserve_failure_antitone.
Qed.

End asymptotic_reserve.

Section example.
Variable R : realType.

(* A square number of observations, with unit-scale intrinsic bounds:
   the rescaled tail coefficient is at most 40 B sqrt(6) sqrt(ln(2d)). *)
Example square_reserve_tail_scale (d : nat) (B : R) :
  (0 < d)%N -> 0 <= B ->
  @reserve_tail_coefficient R (d * d) d d%:R d%:R *
      (B * Num.sqrt d%:R) <=
    40 * B * Num.sqrt 6 * Num.sqrt (ln (2 * d%:R)).
Proof.
move=> d0 B0.
have z1 : (0 : R) <= 1 := ler01.
have p1 : (0 : R) < 1 := ltr01.
have count : (1 : R) * d%:R ^+ 2 <= (d * d)%:R <= (1 : R) * d%:R ^+ 2.
  by rewrite !natrM !mul1r !expr2 !lexx.
have /andP[lo hi] := count.
have h := @reserve_tail_scaling R (d * d) d 1 1 1 1 B d0 z1 p1 z1 B0 lo hi.
have V : reserve_variance_scale 1 1 1 = (6 : R).
  rewrite /reserve_variance_scale !expr1n !mulr1 mul1r.
  have e : (2 + 2 : R) = 2 ^+ 2 by ring.
  by rewrite e sqrtr_sqr ger0_norm ?ler0n //; ring.
by rewrite !mul1r /reserve_tail_scale V divr1 in h.
Qed.

End example.
