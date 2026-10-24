(* The main-sample projection moment. Its weights depend on the sample,
   but only through the outer products. Independent row-sign averaging
   therefore gives a finite tail bound without a moment assumption on the
   sample law. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions cardinality reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.convex Require Import image_projection.
From GaussianAnalysis.probability Require Import symmetrization subgaussian symmetric_shift lindeberg.
From GaussianAnalysis.probability Require Import independent_row_signs.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve even_weights isotropic_rows.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Shifted Require Import GaussianRows ProjectionCertificate.
From EllipsoidUniversality.Shifted Require Import ConditionTranslation ReserveCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition matrix_sample n d (H : 'M[RR]_(n,d)) : paper_main_sample n d :=
  sample_of_row_tuple [tuple row i H | i < n].

Lemma matrix_sample_point n d (H : 'M[RR]_(n,d)) (i : 'I_n) :
  paper_main_point (matrix_sample H) i = (row i H)^T.
Proof. by rewrite /matrix_sample paper_main_point_of_row_tuple tnth_mktuple. Qed.

Lemma measurable_matrix_sample n d :
  measurable_fun [set: 'M[RR]_(n,d)] (@matrix_sample n d).
Proof.
apply: measurableT_comp (@measurable_sample_of_row_tuple n d) _.
apply/measurable_fun_tnthP => i; rewrite /comp /=.
under eq_fun do rewrite tnth_mktuple.
apply/measurable_fun_mxP => j k.
under eq_fun do rewrite mxE.
exact: measurable_mxentry.
Qed.

Definition main_max_rows n d (M : R) : set 'M[RR]_(n,d) :=
  [set H | forall i, frobenius (row i H)^+2 <= M].

Lemma measurable_main_max_rows n d M : measurable (@main_max_rows n d M).
Proof.
have -> : @main_max_rows n d M =
    \bigcap_(i in [set: 'I_n]) [set H | frobenius (row i H)^+2 <= M].
  by apply/seteqP; split=> H h i; [move=> _; exact: h|exact: (h i I)].
apply: fin_bigcap_measurable; first exact: finite_finset.
move=> i _.
have mf : measurable_fun [set: 'M[RR]_(n,d)]
    (fun H => frobenius (row i H)^+2).
  apply: measurable_funX; apply: measurable_frobenius_fun.
  apply/measurable_fun_mxP => a b; under eq_fun do rewrite mxE.
  exact: measurable_mxentry.
have mc : measurable_fun [set: 'M[RR]_(n,d)] (fun _ => (M : measurableTypeR RR)).
  exact: measurable_cst.
have mb := measurable_fun_ler mf mc.
have mt : measurable ([set true] : set bool) by [].
by have h := mb measurableT _ mt; rewrite setTI preimage_true in h.
Qed.

Lemma matrix_sample_matrixK n d (H : 'M[RR]_(n,d)) :
  sample_point_matrix (matrix_sample H) = H.
Proof.
by apply/matrixP => i j; rewrite sample_point_matrixE matrix_sample_point !mxE.
Qed.

Lemma sample_matrix_sampleK n d (x : paper_main_sample n d) :
  matrix_sample (sample_point_matrix x) = x.
Proof.
rewrite /matrix_sample -[RHS]sample_row_tupleK.
congr sample_of_row_tuple; apply: eq_from_tnth => i.
apply/rowP => j.
by rewrite tnth_mktuple /sample_point_matrix /gauss_matrix_law.tuple_mx
  /sample_row_tuple !mxE !tnth_mktuple !mxE.
Qed.

Lemma matrix_residual_direction_sign n d (H : 'M[RR]_(n,d)) (s : n.-tuple bool) :
  sample_residual_direction (matrix_sample (reserve_row_sign s H)) =
    sample_residual_direction (matrix_sample H).
Proof.
apply: (@sample_residual_direction_sign_eq n d _ _
  (fun i => rademacher (tnth s i))).
- by move=> i; exact: rademacher_sqr.
- by move=> i; rewrite !matrix_sample_point reserve_row_sign_row linearZ.
Qed.

Lemma matrix_residual_momentE n d (H : 'M[RR]_(n,d)) :
  sample_residual_moment (matrix_sample H) =
    weighted_row_moment H (sample_residual_direction (matrix_sample H)).
Proof.
apply/matrixP => j l; rewrite /sample_residual_moment summxE /weighted_row_moment mxE.
apply: eq_bigr => i _.
by rewrite matrix_sample_point !mxE ord1 mulrC.
Qed.

Lemma measurable_matrix_residual_moment n d : (0 < d)%N ->
  measurable_fun [set: 'M[RR]_(n,d)]
    (fun H => sample_residual_moment (matrix_sample H)).
Proof.
move=> d0; under eq_fun do rewrite matrix_residual_momentE.
apply: measurable_weighted_row_moment.
exact: measurableT_comp (@measurable_sample_residual_direction n d d0)
  (@measurable_matrix_sample n d).
Qed.

Lemma measurable_matrix_residual_moment_all n d :
  measurable_fun [set: 'M[RR]_(n,d)]
    (fun H => sample_residual_moment (matrix_sample H)).
Proof.
case: d => [|d]; last exact: measurable_matrix_residual_moment.
have z0 (v : 'cV[RR]_0) : v = 0.
  apply/matrixP => i j.
  by have := ltn_ord i; rewrite ltn0.
have -> : (fun H : 'M[RR]_(n,0) => sample_residual_moment (matrix_sample H)) =
    (fun _ => 0).
  by apply/funext => H; exact: z0.
exact: measurable_cst.
Qed.

Definition matrix_residual_moment_map n d :
    {mfun 'M[RR]_(n,d) >-> 'cV[RR]_d} :=
  HB.pack (fun H : 'M[RR]_(n,d) => sample_residual_moment (matrix_sample H))
    (isMeasurableFun.Build _ _ _ _ _ (@measurable_matrix_residual_moment_all n d)).

Definition main_moment_law n d (Q : probability 'M[RR]_(n,d) RR) :
    probability 'cV[RR]_d RR := distribution Q (matrix_residual_moment_map n d).

Lemma main_moment_lawE n d (Q : probability 'M[RR]_(n,d) RR) A :
  main_moment_law Q A =
    Q ((fun H => sample_residual_moment (matrix_sample H)) @^-1` A).
Proof. by []. Qed.

Theorem matrix_residual_moment_tail n d
    (Q : probability 'M[RR]_(n,d) RR) (E : set 'M[RR]_(n,d)) (M t : R) :
  (0 < d)%N -> reserve_sign_invariant Q -> measurable E -> 0 <= M -> 0 < t ->
  (forall H, E H -> forall i, frobenius (row i H)^+2 <= M) ->
  (Q [set H | (t < frobenius (sample_residual_moment (matrix_sample H))^+2)%R] <=
    Q (~` E) + (M/t)%:E)%E.
Proof.
move=> d0 symQ mE M0 t0 rows.
have mw : measurable_fun [set: 'M[RR]_(n,d)]
    (fun H => sample_residual_direction (matrix_sample H)).
  exact: measurableT_comp (@measurable_sample_residual_direction n d d0)
    (@measurable_matrix_sample n d).
have hs := @even_weights_moment_tail RR n d Q _ mw
  (fun s H => @matrix_residual_direction_sign n d H s)
  (fun H => sample_residual_norm_le1 (matrix_sample H)) E M t symQ mE M0 t0 rows.
have he : [set H : 'M[RR]_(n,d) |
    t < frobenius (sample_residual_moment (matrix_sample H))^+2] =
    [set H : 'M[RR]_(n,d) | t < frobenius (weighted_row_moment H
      (sample_residual_direction (matrix_sample H)))^+2].
  by apply/funext => H; rewrite /= matrix_residual_momentE.
by rewrite he.
Qed.

(* The only distributional inputs are symmetry, centering and a common
   directional subgaussian bound. In particular the row coordinates need
   not be independent, and no fourth moment enters this estimate. *)
Theorem independent_main_moment_tail n d
    (mu : nat -> probability 'rV[RR]_d RR) (K s t : R) :
  (0 < n)%N -> (0 < d)%N -> 0 < K -> 0 <= s -> 0 < t ->
  (forall i, (i < n)%N -> row_symmetric_law (mu i)) ->
  (forall i (y : 'rV[RR]_d), (i < n)%N -> frobenius y <= 1 ->
    subgaussian (mu i) (fun x => mxdot x y) K) ->
  (forall i (y : 'rV[RR]_d), (i < n)%N -> frobenius y <= 1 ->
    \int[mu i]_x mxdot x y = 0) ->
  (independent_row_matrix_law mu n
      [set H | (t < frobenius (sample_residual_moment (matrix_sample H))^+2)%R]
    <= (2 * expR (-s) +
      64 * K^+2 * (7 + 6*d%:R + ln n%:R + s) / t)%:E)%E.
Proof.
move=> n0 d0 K0 s0 t0 sym sub cen.
pose M := 64 * K^+2 * (7 + 6*d%:R + ln n%:R + s).
have M0 : 0 <= M.
  have ln0 : 0 <= ln (n%:R : RR) by apply: ln_ge0; rewrite ler1n.
  rewrite /M; apply: mulr_ge0; first by rewrite mulr_ge0 ?sqr_ge0.
  apply: addr_ge0 => //; apply: addr_ge0 => //.
have [G [mG pG bG]] :=
  @isotropic_max_row_event RR n d mu K K0 sub cen s n0 s0.
pose E : set 'M[RR]_(n,d) := main_max_rows M.
have mE : measurable E := @measurable_main_max_rows n d M.
have pE : (independent_row_matrix_law mu n (~` E) <=
    (2 * expR (-s))%:E)%E.
  rewrite independent_row_matrix_lawE.
  apply: le_trans (_ : (tuple_prod mu n (~` G) <= (2 * expR (-s))%:E)%E) => //.
  apply: le_measure; rewrite ?inE.
  - change (measurable ((@row_tuple_matrix RR d n) @^-1` (~` E))).
    exact (measurable_funPTI (@row_tuple_matrix RR d n) (measurableC mE)).
  - exact: measurableC mG.
  - move=> x bad gx; apply: bad => i.
    have rowE : row i (restricted_isometry.tuple_mx x) = tnth x i.
      by apply/rowP => j; rewrite /restricted_isometry.tuple_mx !mxE.
    rewrite rowE; exact (bG x gx i).
have h := @matrix_residual_moment_tail n d
  (independent_row_matrix_law mu n) E M t d0
  (independent_row_sign_invariant sym) mE M0 t0 (fun H h => h).
apply: le_trans h _.
by rewrite EFinD; apply: leeD; [exact: pE | exact: lexx].
Qed.

Lemma main_moment_truncation_choice (M eps : R) :
  0 <= M -> 0 < eps -> exists B : R, 0 < B /\ M / B^+2 <= eps / 2.
Proof.
move=> M0 e0.
pose B := 1 + 2*M/eps.
have B1 : 1 <= B by rewrite /B lerDl divr_ge0 ?mulr_ge0 ?(ltW e0).
have B0 : 0 < B by lra.
have eb : eps*B = eps+2*M by rewrite /B; field by rewrite ?gt_eqF.
exists B; split => //.
rewrite ler_pdivrMr ?exprn_gt0 //.
clearbody B.
have bb : B <= B^+2 by nra.
have he := ler_wpM2l (ltW e0) bb.
clear -eb he e0; nra.
Qed.

(* This is the right-hand-side tightness required by the independent
   reserve theorem. Its law remains the image of the main sample, whose
   projection weights may depend on every observation. *)
Theorem main_moment_tight_of_rows (N : nat -> nat)
    (Q : forall d, probability 'M[RR]_(N d,d) RR) (M : R) :
  0 <= M -> (forall d, reserve_sign_invariant (Q d)) ->
  (forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (Q d (~` main_max_rows (M*d%:R)) <= eps%:E)%E) ->
  forall eps : R, 0 < eps -> exists B : R, 0 < B /\
    exists D : nat, forall d, (D <= d)%N ->
      (main_moment_law (Q d) [set b | (B*Num.sqrt d%:R < frobenius b)%R]
        <= eps%:E)%E.
Proof.
move=> M0 sym rows eps e0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [B [B0 ratio]] := main_moment_truncation_choice M0 e0.
have [D hD] := rows _ e20.
exists B; split => //; exists (maxn 1 D) => d.
rewrite geq_max => /andP[d0 dD].
have dr0 : (0:RR) < d%:R by rewrite ltr0n.
have t0 : 0 < B^+2*d%:R by rewrite mulr_gt0 ?exprn_gt0.
have Md0 : 0 <= M*d%:R by rewrite mulr_ge0.
have h := @matrix_residual_moment_tail (N d) d (Q d)
  (main_max_rows (M*d%:R)) (M*d%:R) (B^+2*d%:R) d0 (sym d)
  (@measurable_main_max_rows (N d) d (M*d%:R)) Md0 t0 (fun H h => h).
have quotient : M*d%:R/(B^+2*d%:R) = M/B^+2.
  field by rewrite ?gt_eqF.
rewrite quotient in h.
have tail : (Q d [set H | (B^+2*d%:R <
    frobenius (sample_residual_moment (matrix_sample H))^+2)%R] <= eps%:E)%E.
  have ratioE : ((M/B^+2)%:E <= (eps/2)%:E)%E by rewrite lee_fin.
  apply: le_trans h _; apply: le_trans (leeD (hD d dD) ratioE) _.
  rewrite -EFinD lee_fin; clear -eps; lra.
rewrite main_moment_lawE.
have he : [set H : 'M[RR]_(N d,d) |
    B*Num.sqrt d%:R < frobenius (sample_residual_moment (matrix_sample H))] =
    [set H | B^+2*d%:R <
      frobenius (sample_residual_moment (matrix_sample H))^+2].
  apply/funext => H /=.
  have lhs0 : 0 <= B*Num.sqrt d%:R by rewrite mulr_ge0 ?(ltW B0) ?sqrtr_ge0.
  have ep : (B*Num.sqrt d%:R)^+2 = B^+2*d%:R.
    by rewrite exprMn sqr_sqrtr ?ler0n.
  by rewrite -ep ltr_pXn2r ?nnegrE ?frobenius_ge0.
change (Q d [set H : 'M[RR]_(N d,d) |
  (B*Num.sqrt d%:R < frobenius (sample_residual_moment (matrix_sample H)))%R]
  <= eps%:E)%E.
by rewrite he.
Qed.
