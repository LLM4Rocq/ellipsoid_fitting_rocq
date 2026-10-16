From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix archimedean.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral probability measurable_realfun.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import image_projection.
From GaussianAnalysis.matrix Require Import euclidean opnorm random_opnorm centered_correction.
From GaussianAnalysis.matrix Require Import centered_quadratic_correction.
From GaussianAnalysis.probability Require Import lindeberg subgaussian subgaussian_matrix independent_row_signs.
From GaussianAnalysis.random_matrix Require Import restricted_isometry isotropic_rows.
From GaussianAnalysis.random_matrix Require Import gaussian_rows_bounds symmetric_reserve reserve_convergence.

(**md**************************************************************************)
(* # Reserve conditions from independent isotropic rows                     *)
(* Source: the reserve-sample argument in doc/shifted-gaussian.tex.           *)
(* Rows may have different laws and dependent coordinates. Directional      *)
(* subgaussianity, centering and isotropy use a common subgaussian constant. *)
(* This module verifies covariance tightness and the maximum-row event.     *)
(* It neither assumes nor proves the quadratic-adjoint bound or symmetry.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section row_events.
Context {R : realType} {k d : nat}.

Definition reserve_max_rows (M : R) : set 'M[R]_(k,d) :=
  [set H | forall i, frobenius (row i H) ^+ 2 <= M].

Lemma reserve_max_rows_sign M s H :
  reserve_max_rows M (reserve_row_sign s H) <-> reserve_max_rows M H.
Proof.
split=> h i; move: (h i); by rewrite reserve_row_sign_norm.
Qed.

Lemma reserve_max_rows_closed M : closed (reserve_max_rows M).
Proof.
have -> : reserve_max_rows M =
    \bigcap_(i in [set: 'I_k]) [set H | frobenius (row i H) ^+ 2 <= M].
  by apply/seteqP; split=> H h i; [move=> _; exact: h | exact: (h i I)].
apply: closed_bigI => i _.
have cc : continuous (fun H : 'M[R]_(k,d) => frobenius (row i H)).
  move=> H; apply: (continuous_comp (f := fun X : 'M[R]_(k,d) => row i X)
    (g := @frobenius R 1 d)).
  - exact: reserve_row_continuous.
  - exact: reserve_frobenius_continuous.
have cf : continuous (fun H : 'M[R]_(k,d) => frobenius (row i H) ^+ 2).
  under eq_fun do rewrite expr2.
  move=> H; apply: (continuousM (s := fun X : 'M[R]_(k,d) => frobenius (row i X))
    (t := fun X => frobenius (row i X))); exact: cc.
exact: (continuous_closedP _).1 cf _ (@closed_le R M).
Qed.

Lemma reserve_max_rows_measurable M : measurable (reserve_max_rows M).
Proof.
rewrite -[X in measurable X]setCK; apply: measurableC.
apply: open_measurable_mx; apply: closed_openC.
exact: reserve_max_rows_closed.
Qed.

Lemma reserve_raw_covariance_measurable :
  measurable_fun [set: 'M[R]_(k,d)]
    (fun H => opnorm (H^T *m H - k%:R *: 1%:M)).
Proof.
apply: measurable_opnorm; apply/measurable_fun_mxP.
apply: measurable_addmx; last exact: measurable_cst.
apply: measurable_mulmx; [exact: measurable_trmx | exact: measurable_id].
Qed.

Lemma reserve_mean_norm_measurable :
  measurable_fun [set: 'M[R]_(k,d)] (fun H => frobenius (reserve_mean H)).
Proof.
apply: measurable_frobenius_fun; rewrite /reserve_mean.
apply: measurable_scalemx; first exact: measurable_cst.
apply: measurable_mulmx; [exact: measurable_trmx | exact: measurable_cst].
Qed.

Lemma reserve_feature_sum (H : 'M[R]_(k,d)) :
  \sum_i reserve_feature H i = H^T *m H - k%:R *: 1%:M.
Proof.
rewrite /reserve_feature sumrB sumr_const card_ord -scaler_nat.
congr (_ - _); apply/matrixP => a b; rewrite mxE summxE.
by apply: eq_bigr => i _; rewrite !mxE big_ord1 !mxE.
Qed.

End row_events.

Section majorant_tail.
Context {R : realType} {e} {T : measurableType e}.
Variable P : probability T R.

Lemma reserve_majorant_tail (f N : T -> R) (B t : R) :
  measurable_fun setT f -> measurable_fun setT N ->
  (forall x, 0 <= f x) -> (forall x, f x <= N x) ->
  (\int[P]_x (N x)%:E <= B%:E)%E -> 0 < t ->
  (P [set x | (t < f x)%R] <= (B / t)%:E)%E.
Proof.
move=> mf mN f0 bN eN t0.
have m1 : measurable [set x | t < f x].
  have mt : measurable ([set true] : set bool) by [].
  have h := (measurable_fun_ltr (measurable_cst t) mf) measurableT _ mt.
  by rewrite setTI preimage_true in h.
have m2 : measurable [set x | t <= N x].
  have mt : measurable ([set true] : set bool) by [].
  have h := (measurable_fun_ler (measurable_cst t) mN) measurableT _ mt.
  by rewrite setTI preimage_true in h.
have sub : [set x | t < f x] `<=` [set x | t <= N x].
  by move=> x /= hx; exact: le_trans (ltW hx) (bN x).
apply: le_trans (le_measure P (mem_set m1) (mem_set m2) sub) _.
have N0 x : 0 <= N x := le_trans (f0 x) (bN x).
apply: le_trans (probability_markov_ge P t0 mN N0) _.
rewrite mulrC EFinM; apply: lee_wpmul2l; last exact: eN.
by rewrite lee_fin invr_ge0 ltW.
Qed.

End majorant_tail.

Section finite_rows.
Context {R : realType} (k d : nat).
Variable mu : nat -> probability 'rV[R]_d R.
Variable K : R.
Hypothesis K0 : 0 < K.
Hypothesis sub : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  subgaussian (mu i) (fun x => mxdot x y) K.
Hypothesis iso : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  \int[mu i]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
Hypothesis cen : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  \int[mu i]_x mxdot x y = 0.
Let Q := independent_row_matrix_law mu k.

Lemma reserve_raw_covariance_tail (t : R) : 0 < t ->
  (Q [set H | (t < opnorm (H^T *m H - k%:R *: 1%:M))%R] <=
    (isotropic_covariance_bound k d K / t)%:E)%E.
Proof.
move=> t0; rewrite /Q independent_row_matrix_lawE.
have [N [mN bN eN]] := isotropic_covariance_majorant K0 sub iso.
apply: (reserve_majorant_tail (P := tuple_prod mu k) _ mN _ bN eN t0).
- exact: measurableT_comp reserve_raw_covariance_measurable measurable_rows_matrix.
- by move=> x; exact: opnorm_ge0.
Qed.

Lemma reserve_rows_mean_tail (t : R) : (0 < k)%N -> 0 < t ->
  (Q [set H | (t < frobenius (reserve_mean H))%R] <=
    (d%:R / (k%:R * t ^+ 2))%:E)%E.
Proof.
move=> k0 t0; rewrite /Q independent_row_matrix_lawE.
have mm := measurableT_comp reserve_mean_norm_measurable
  (@measurable_rows_matrix R k d).
have m1 : measurable [set x : k.-tuple 'rV[R]_d |
    t < frobenius (reserve_mean (tuple_mx x))].
  have mt : measurable ([set true] : set bool) by [].
  have h := (measurable_fun_ltr (measurable_cst t) mm) measurableT _ mt.
  by rewrite setTI preimage_true in h.
have m2 : measurable [set x : k.-tuple 'rV[R]_d |
    t <= frobenius (reserve_mean (tuple_mx x))].
  have mt : measurable ([set true] : set bool) by [].
  have h := (measurable_fun_ler (measurable_cst t) mm) measurableT _ mt.
  by rewrite setTI preimage_true in h.
apply: le_trans _ (isotropic_mean_tail sub iso cen k0 t0).
apply: le_measure (mem_set m1) (mem_set m2) _ => x /=; exact: ltW.
Qed.

Lemma reserve_rows_max_tail (s : R) : (0 < k)%N -> 0 <= s ->
  (Q (~` reserve_max_rows
      (64 * K ^+ 2 * (7 + 6 * d%:R + ln k%:R + s))) <=
    (2 * expR (-s))%:E)%E.
Proof.
move=> k0 s0; rewrite /Q independent_row_matrix_lawE.
have [G [mG pG bG]] := isotropic_max_row_event K0 sub cen k0 s0.
apply: le_trans _ pG.
apply: le_measure; rewrite ?inE.
- have mE := measurableC (@reserve_max_rows_measurable R k d
    (64 * K ^+ 2 * (7 + 6 * d%:R + ln k%:R + s))).
  have h := (@measurable_rows_matrix R k d) measurableT _ mE.
  by rewrite setTI in h.
- exact: measurableC mG.
- move=> x hx gx; apply: hx => i.
  have h := bG x gx i.
  have -> : row i (tuple_mx x) = tnth x i.
    by apply/rowP => j; rewrite !mxE.
  exact: h.
Qed.

End finite_rows.

Section covariance_scaling.
Context {R : realType}.

Definition reserve_row_covariance_scale (K C : R) :=
  288 * K ^+ 2 * (Num.sqrt (2 * C) + 2).

Lemma reserve_row_covariance_scaling k d (K C : R) :
  (0 < d)%N -> 0 <= C -> (k%:R : R) <= C * d%:R ^+ 2 ->
  isotropic_covariance_bound k d K <=
    reserve_row_covariance_scale K C * d%:R * Num.sqrt d%:R.
Proof.
move=> d0 C0 ku.
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) <= d%:R by [].
have s1 : (1 : R) <= Num.sqrt d%:R by rewrite -{1}(@sqrtr1 R); exact: ler_wsqrtr x1.
have dx : (d.+1%:R : R) <= 2 * d%:R by rewrite -addn1 natrD /=; lra.
have prod : (k%:R : R) * d.+1%:R <= (2 * C) * d%:R ^+ 3.
  apply: le_trans (ler_pM (ler0n _ _) (ler0n _ _) ku dx) _.
  by nra.
have rt := ler_wsqrtr prod.
have er : Num.sqrt ((2 * C) * d%:R ^+ 3) =
    Num.sqrt (2 * C) * d%:R * Num.sqrt d%:R.
  have c20 : 0 <= 2 * C by rewrite mulr_ge0 ?ler0n.
  have e : (2 * C) * d%:R ^+ 3 =
      (Num.sqrt (2 * C) * d%:R * Num.sqrt d%:R) ^+ 2.
    rewrite !exprMn (sqr_sqrtr c20) (sqr_sqrtr x0); ring.
  rewrite e sqrtr_sqr ger0_norm //; by rewrite !mulr_ge0 ?sqrtr_ge0.
rewrite er in rt.
have ds : (d.+1%:R : R) <= 2 * d%:R * Num.sqrt d%:R.
  apply: le_trans dx _.
  have two0 : (0 : R) <= 2 * d%:R by rewrite mulr_ge0 ?ler0n.
  have := ler_wpM2l two0 s1.
  by rewrite mulr1.
rewrite /isotropic_covariance_bound /reserve_row_covariance_scale.
have fac0 : 0 <= 288 * K ^+ 2 by rewrite mulr_ge0 ?ler0n ?sqr_ge0.
have := ler_wpM2l fac0 (lerD rt ds).
by nra.
Qed.

Lemma reserve_covariance_event_mono k d (eta eta' A A' h h' S S' : R) :
  eta <= eta' -> A <= A' -> h <= h' -> S <= S' ->
  (@reserve_covariance_event R k d eta A h S) `<=`
    reserve_covariance_event eta' A' h' S'.
Proof.
move=> e a hh s H /and4P[he ha hm hs]; apply/and4P; split;
  [exact: le_trans he e | exact: le_trans ha a |
   exact: le_trans hm hh | exact: le_trans hs s].
Qed.

Lemma reserve_covariance_event_from_raw k d (H : 'M[R]_(k,d)) (r h : R) :
  (0 < k)%N -> 0 <= h ->
  opnorm (H^T *m H - k%:R *: 1%:M) <= r ->
  frobenius (reserve_mean H) <= h ->
  reserve_covariance_event (r / k%:R + h ^+ 2)
    (Num.sqrt (k%:R + r)) h r H.
Proof.
move=> k0 h0 hr hm; apply/and4P; split => //.
- apply: le_trans (centered_covariance_deviation H k0) _.
  rewrite mulrC; apply: lerD.
  + have ki0 : 0 <= (k%:R : R)^-1 by rewrite invr_ge0.
    by apply: ler_wpM2r.
  + by rewrite lerXn2r ?nnegrE ?frobenius_ge0.
- have hs := le_trans (opnorm_square_gram_deviation H) (lerD (lexx _) hr).
  have rr0 : 0 <= k%:R + r := le_trans (sqr_ge0 _) hs.
  rewrite -(@ger0_norm R (opnorm H)) ?opnorm_ge0 // -sqrtr_sqr.
  exact: ler_wsqrtr hs.
- by rewrite reserve_feature_sum.
Qed.

Definition reserve_row_event_scale (c C T U : R) :=
  1 + T + U + T / c + U ^+ 2 + Num.sqrt (C + T).

Lemma reserve_scaled_covariance_event k d (H : 'M[R]_(k,d)) (c C T U : R) :
  (0 < d)%N -> 0 < c -> 0 <= C -> 0 <= T -> 0 <= U ->
  c * d%:R ^+ 2 <= k%:R -> (k%:R : R) <= C * d%:R ^+ 2 ->
  opnorm (H^T *m H - k%:R *: 1%:M) <= T * d%:R * Num.sqrt d%:R ->
  frobenius (reserve_mean H) <= U / Num.sqrt d%:R ->
  let A := reserve_row_event_scale c C T U in
  reserve_covariance_event (A / Num.sqrt d%:R) (A * d%:R)
    (A / Num.sqrt d%:R) (A * d%:R * Num.sqrt d%:R) H.
Proof.
move=> d0 c0 C0 T0 U0 kl ku hr hm A.
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
pose s : R := Num.sqrt d%:R.
have s0 : 0 < s by rewrite /s sqrtr_gt0.
have s00 := ltW s0.
have s1 : 1 <= s by rewrite /s -{1}(@sqrtr1 R); exact: ler_wsqrtr x1.
have sx2 : s ^+ 2 = d%:R by rewrite /s sqr_sqrtr.
have sx : s <= d%:R by rewrite -sx2; nra.
have cx0 : 0 < c * d%:R ^+ 2 by rewrite mulr_gt0 ?exprn_gt0.
have kr0 := lt_le_trans cx0 kl.
have k0 : (0 < k)%N by move: kr0; rewrite ltr0n.
have r0 : 0 <= T * d%:R * s by rewrite !mulr_ge0.
have h0 : 0 <= U / s by rewrite divr_ge0.
have tc0 : 0 <= T / c by rewrite divr_ge0 ?(ltW c0).
have u20 := sqr_ge0 U.
have root0 := sqrtr_ge0 (C + T).
have TA : T <= A by rewrite /A /reserve_row_event_scale; lra.
have UA : U <= A by rewrite /A /reserve_row_event_scale; lra.
have CA : T / c + U ^+ 2 <= A by rewrite /A /reserve_row_event_scale; lra.
have RA : Num.sqrt (C + T) <= A by rewrite /A /reserve_row_event_scale; lra.
have A0 : 0 <= A by exact: le_trans T0 TA.
have rfrac : (T * d%:R * s) / k%:R <= (T / c) / s.
  have invb : (k%:R : R)^-1 <= (c * d%:R ^+ 2)^-1.
    by rewrite lef_pV2.
  apply: le_trans (ler_wpM2l r0 invb) _.
  have eq : (T * d%:R * s) / (c * d%:R ^+ 2) = (T / c) / s.
    rewrite -sx2; field by rewrite ?gt_eqF.
  by rewrite eq.
have meanb : (U / s) ^+ 2 <= U ^+ 2 / s.
  have si0 : 0 <= s^-1 by rewrite invr_ge0.
  have si1 : s^-1 <= 1 by rewrite invf_le1.
  have sii : s^-1 ^+ 2 <= s^-1 by nra.
  rewrite exprMn; by apply: ler_wpM2l.
have eb : (T * d%:R * s) / k%:R + (U / s) ^+ 2 <= A / s.
  apply: le_trans (lerD rfrac meanb) _.
  rewrite -mulrDl; apply: ler_wpM2r => //; by rewrite invr_ge0.
have rb : Num.sqrt (k%:R + T * d%:R * s) <= A * d%:R.
  have tr : T * d%:R * s <= T * d%:R ^+ 2.
    rewrite expr2 mulrA; apply: ler_wpM2l => //; exact: mulr_ge0.
  have sum : (k%:R : R) + T * d%:R * s <= (C + T) * d%:R ^+ 2.
    have := lerD ku tr; nra.
  have h := ler_wsqrtr sum.
  rewrite sqrtrM ?addr_ge0 // sqrtr_sqr ger0_norm // in h.
  apply: le_trans h _; by apply: ler_wpM2r.
have hb : U / s <= A / s.
  apply: ler_wpM2r => //; by rewrite invr_ge0.
have sb : T * d%:R * s <= A * d%:R * s.
  apply: ler_wpM2r => //; by apply: ler_wpM2r.
exact: (reserve_covariance_event_mono eb rb hb sb
  (reserve_covariance_event_from_raw k0 h0 hr hm)).
Qed.

Lemma reserve_rows_mean_scaling k d (c U : R) :
  (0 < d)%N -> 0 < c -> 0 < U -> c * d%:R ^+ 2 <= k%:R ->
  d%:R / (k%:R * (U / Num.sqrt d%:R) ^+ 2) <= 1 / (c * U ^+ 2).
Proof.
move=> d0 c0 U0 kl.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
pose s : R := Num.sqrt d%:R.
have s0 : 0 < s by rewrite /s sqrtr_gt0.
have sx2 : s ^+ 2 = d%:R by rewrite /s sqr_sqrtr.
have cx0 : 0 < c * d%:R ^+ 2 by rewrite mulr_gt0 ?exprn_gt0.
have kr0 := lt_le_trans cx0 kl.
have us0 : 0 < U / s by rewrite divr_gt0.
have den0 : 0 < c * d%:R ^+ 2 * (U / s) ^+ 2.
  by rewrite mulr_gt0 ?exprn_gt0.
have den : c * d%:R ^+ 2 * (U / s) ^+ 2 <= k%:R * (U / s) ^+ 2.
  apply: ler_wpM2r => //; exact: sqr_ge0.
have rhs0 := lt_le_trans den0 den.
have invb : (k%:R * (U / s) ^+ 2)^-1 <=
    (c * d%:R ^+ 2 * (U / s) ^+ 2)^-1 by rewrite lef_pV2.
apply: le_trans (ler_wpM2l x00 invb) _.
have eq : d%:R / (c * d%:R ^+ 2 * (U / s) ^+ 2) = 1 / (c * U ^+ 2).
  rewrite -sx2; field by rewrite ?gt_eqF.
by rewrite eq.
Qed.

End covariance_scaling.

Section maximum_scaling.
Context {R : realType}.

Definition reserve_row_max_scale (K gamma : R) :=
  64 * K ^+ 2 * (14 + 2 * Num.sqrt (2 * gamma)).

Lemma reserve_log_le_sqrt (x : R) : 0 < x -> ln x <= 2 * Num.sqrt x.
Proof.
move=> x0; have sx0 : 0 < Num.sqrt x by rewrite sqrtr_gt0.
have sx2 := sqr_sqrtr (ltW x0).
have logE : ln x = 2 * ln (Num.sqrt x).
  rewrite -{1}sx2 lnXn // mulr2n; ring.
have := ln_sublinear sx0; rewrite logE; lra.
Qed.

Lemma reserve_row_max_scaling k d (K gamma : R) :
  (0 < k)%N -> (0 < d)%N -> 0 < gamma ->
  (k%:R : R) <= (2 * gamma) * d%:R ^+ 2 ->
  64 * K ^+ 2 * (7 + 6 * d%:R + ln k%:R + d%:R) <=
    reserve_row_max_scale K gamma * d%:R.
Proof.
move=> k0 d0 gamma0 ku.
have x1 : (1 : R) <= d%:R by rewrite ler1n.
have x0 : (0 : R) <= d%:R by [].
have kr0 : (0 : R) < k%:R by rewrite ltr0n.
have l := reserve_log_le_sqrt kr0.
have r := ler_wsqrtr ku.
rewrite sqrtrM ?mulr_ge0 ?ler0n ?(ltW gamma0) // sqrtr_sqr ger0_norm // in r.
have b : 7 + 6 * d%:R + ln k%:R + d%:R <=
    (14 + 2 * Num.sqrt (2 * gamma)) * d%:R by nra.
have fac : 0 <= 64 * K ^+ 2 by rewrite mulr_ge0 ?ler0n ?sqr_ge0.
have h := ler_wpM2l fac b.
rewrite /reserve_row_max_scale; nra.
Qed.

Lemma reserve_exponential_failure (eps : R) : 0 < eps ->
  exists n : nat, forall d, (n <= d)%N ->
    2 * expR (-(d%:R : R)) <= eps.
Proof.
move=> eps0; have [n hn] := reserve_eventually_ge (2 / eps).
exists n => d dn.
have x0 : (0 : R) <= d%:R by [].
have e0 : (0 : R) < 1 + d%:R by lra.
have h := @expR_ge1Dx R d%:R.
have inv : (expR (d%:R : R))^-1 <= (1 + d%:R)^-1.
  by rewrite lef_pV2 ?posrE ?expR_gt0.
rewrite expRN; apply: le_trans (ler_wpM2l (ler0n R 2) inv) _.
rewrite ler_pdivrMr //.
have xd := hn d dn; rewrite ler_pdivrMr // in xd.
nra.
Qed.

End maximum_scaling.

Section row_sequences.
Context {R : realType}.
Variable k : nat -> nat.
Variable mu : forall d, nat -> probability 'rV[R]_d R.
Variables K gamma : R.
Hypotheses (K0 : 0 < K) (gamma0 : 0 < gamma).
Hypothesis sub : forall d i (y : 'rV[R]_d), (i < k d)%N -> frobenius y <= 1 ->
  subgaussian (mu d i) (fun x => mxdot x y) K.
Hypothesis iso : forall d i (y : 'rV[R]_d), (i < k d)%N -> frobenius y <= 1 ->
  \int[mu d i]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
Hypothesis cen : forall d i (y : 'rV[R]_d), (i < k d)%N -> frobenius y <= 1 ->
  \int[mu d i]_x mxdot x y = 0.
Hypothesis count_limit : forall eps : R, 0 < eps -> exists n : nat,
  forall d, (n <= d)%N -> `| (k d)%:R / d%:R ^+ 2 - gamma | < eps.
Let Q d := independent_row_matrix_law (mu d) (k d).

Theorem reserve_independent_rows_max :
  0 < reserve_row_max_scale K gamma /\
  forall eps : R, 0 < eps -> exists d0 : nat, forall d, (d0 <= d)%N ->
    (Q d (~` reserve_max_rows (reserve_row_max_scale K gamma * d%:R)) <= eps%:E)%E.
Proof.
split.
  rewrite /reserve_row_max_scale; apply: mulr_gt0.
  - by rewrite mulr_gt0 ?ltr0n ?exprn_gt0.
  - have h0 : 0 <= 2 * Num.sqrt (2 * gamma).
      by rewrite mulr_ge0 ?ler0n ?sqrtr_ge0.
    lra.
move=> eps eps0.
have [nc hc] := reserve_counts_of_limit gamma0 count_limit.
have [ne he] := reserve_exponential_failure eps0.
exists (maxn 1 (maxn nc ne)) => d.
rewrite !geq_max => /andP[d1 /andP[dc de]].
have d0 : (0 < d)%N by [].
have /andP[kl ku] := hc d dc.
have kd0 : (0 < k d)%N.
  rewrite -(@ltr0n R); apply: lt_le_trans _ kl.
  by rewrite mulr_gt0 ?divr_gt0 ?exprn_gt0 ?ltr0n.
have s0 : (0 : R) <= d%:R by [].
have tail := @reserve_rows_max_tail R (k d) d (mu d) K K0
  (@sub d) (@cen d) d%:R kd0 s0.
have b := reserve_row_max_scaling K kd0 d0 gamma0 ku.
have pe : ((2 * expR (- (d%:R : R)))%:E <= eps%:E)%E.
  rewrite lee_fin; exact: he.
apply: le_trans _ (le_trans tail pe).
apply: le_measure; rewrite ?inE; try exact: measurableC (reserve_max_rows_measurable _).
move=> H hn hs; apply: hn => i; exact: le_trans (hs i) b.
Qed.

Theorem reserve_independent_rows_covariance :
  forall eps : R, 0 < eps -> exists A : R, 0 < A /\
  exists d0 : nat, forall d, (d0 <= d)%N ->
    (Q d (~` reserve_covariance_event (A / Num.sqrt d%:R) (A * d%:R)
      (A / Num.sqrt d%:R) (A * d%:R * Num.sqrt d%:R)) <= eps%:E)%E.
Proof.
move=> eps eps0.
pose c := gamma / 2.
pose C := 2 * gamma.
have c0 : 0 < c by rewrite /c divr_gt0 ?ltr0n.
have C0 : 0 <= C by rewrite /C mulr_ge0 ?ler0n ?(ltW gamma0).
pose V := reserve_row_covariance_scale K C.
have V0 : 0 <= V.
  rewrite /V /reserve_row_covariance_scale; apply: mulr_ge0.
  - by rewrite mulr_ge0 ?sqr_ge0 ?ler0n.
  - apply: addr_ge0; [exact: sqrtr_ge0 | exact: ler0n].
pose T := 1 + 4 * V / eps.
pose U := 1 + 4 / (c * eps).
have tv0 : 0 <= 4 * V / eps.
  apply: divr_ge0; last exact: ltW eps0.
  apply: mulr_ge0; [exact: ler0n | exact: V0].
have uu0 : 0 <= 4 / (c * eps).
  apply: divr_ge0; first exact: ler0n.
  apply: mulr_ge0; [exact: ltW c0 | exact: ltW eps0].
have T0 : 0 < T by rewrite /T; lra.
have U0 : 0 < U by rewrite /U; lra.
have tc0 : 0 <= T / c by rewrite divr_ge0 ?(ltW T0) ?(ltW c0).
pose A := reserve_row_event_scale c C T U.
have A0 : 0 < A.
  rewrite /A /reserve_row_event_scale.
  have := sqr_ge0 U; have := sqrtr_ge0 (C + T); lra.
exists A; split => //.
have [nc hc] := reserve_counts_of_limit gamma0 count_limit.
exists (maxn 1 nc) => d; rewrite geq_max => /andP[d1 dc].
have d0 : (0 < d)%N by [].
have /andP[kl ku] := hc d dc.
have x0 : (0 : R) < d%:R by rewrite ltr0n.
have x00 := ltW x0.
pose sd : R := Num.sqrt d%:R.
have sd0 : 0 < sd by rewrite /sd sqrtr_gt0.
have kd0 : (0 < k d)%N.
  rewrite -(@ltr0n R); apply: lt_le_trans _ kl.
  by rewrite mulr_gt0 ?exprn_gt0.
pose r := T * d%:R * sd.
pose h := U / sd.
have r0 : 0 < r by rewrite /r !mulr_gt0.
have h0 : 0 < h by rewrite /h divr_gt0.
pose E := [set H : 'M[R]_(k d,d) | r < opnorm (H^T *m H - (k d)%:R *: 1%:M)].
pose F := [set H : 'M[R]_(k d,d) | h < frobenius (reserve_mean H)].
have mt : measurable ([set true] : set bool) by [].
have mE : measurable E.
  have m := (measurable_fun_ltr (measurable_cst r)
    (@reserve_raw_covariance_measurable R (k d) d)) measurableT _ mt.
  by rewrite setTI preimage_true in m.
have mF : measurable F.
  have m := (measurable_fun_ltr (measurable_cst h)
    (@reserve_mean_norm_measurable R (k d) d)) measurableT _ mt.
  by rewrite setTI preimage_true in m.
have pE : (Q d E <= (eps / 4)%:E)%E.
  have p := @reserve_raw_covariance_tail R (k d) d (mu d) K K0 (@sub d) (@iso d) r r0.
  apply: le_trans p _; rewrite lee_fin.
  have b := reserve_row_covariance_scaling K d0 C0 ku.
  have rb : isotropic_covariance_bound (k d) d K / r <= V / T.
    have ri0 : 0 <= r^-1 by rewrite invr_ge0 (ltW r0).
    apply: le_trans (ler_wpM2r ri0 b) _.
    have eq : V * d%:R * Num.sqrt d%:R / r = V / T.
      rewrite /r /sd; field by rewrite ?gt_eqF ?sqrtr_eq0 ?gt_eqF.
    by rewrite eq.
  apply: le_trans rb _.
  rewrite ler_pdivrMr // /T.
  have eq : (eps / 4) * (1 + 4 * V / eps) = eps / 4 + V.
    field by rewrite ?gt_eqF.
  rewrite eq; have ep0 : 0 <= eps / 4 by rewrite divr_ge0 ?ler0n ?(ltW eps0).
  lra.
have pF : (Q d F <= (eps / 4)%:E)%E.
  have p := @reserve_rows_mean_tail R (k d) d (mu d) K (@sub d) (@iso d) (@cen d)
    h kd0 h0.
  apply: le_trans p _; rewrite lee_fin.
  apply: le_trans (reserve_rows_mean_scaling d0 c0 U0 kl) _.
  have den0 : 0 < c * U ^+ 2 by rewrite mulr_gt0 ?exprn_gt0.
  have ce0 : 0 < c * eps by rewrite mulr_gt0.
  have u1 : 1 <= U by rewrite /U; lra.
  have z : 4 / (c * eps) <= U ^+ 2 by rewrite /U; nra.
  rewrite ler_pdivrMr // in z.
  rewrite ler_pdivrMr //; nra.
pose G : set 'M[R]_(k d,d) :=
  reserve_covariance_event (A / sd) (A * d%:R) (A / sd) (A * d%:R * sd).
have mG : measurable G := reserve_covariance_event_measurable _ _ _ _.
have inc : ~` G `<=` E `|` F.
  move=> H ng.
  have [hr|hr] := leP (opnorm (H^T *m H - (k d)%:R *: 1%:M)) r.
    have [hm|hm] := leP (frobenius (reserve_mean H)) h.
      exfalso; apply: ng.
      exact: reserve_scaled_covariance_event d0 c0 C0 (ltW T0) (ltW U0) kl ku hr hm.
    by right.
  by left.
apply: le_trans (le_measure (Q d) (mem_set (measurableC mG))
  (mem_set (measurableU _ _ mE mF)) inc) _.
apply: le_trans (measureU2 (Q d) mE mF) _.
apply: le_trans (leeD pE pF) _.
rewrite -EFinD lee_fin; lra.
Qed.

End row_sequences.

Section example.
Variable R : realType.

Example constant_scalar_rows_max k (a : R) :
  @reserve_max_rows R k 1 (a ^+ 2) (const_mx a).
Proof.
move=> i; by rewrite frobenius_sqr /mxdot !big_ord1 !mxE expr2.
Qed.

End example.
