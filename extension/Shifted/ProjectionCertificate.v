(* The normalized centered quadratic design and its PSD certificate.
   The design acts on all d*d vector coordinates. Its projection on the
   image of the PSD trace-d slice has squared norm exactly equal to the
   frozen fitting error. The normalized image gives measurable weights
   determined only by the outer products, with their exact PSD margin.
   This module contains no reserve correction or probabilistic limit. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part psd_splitting psd_duality nuclear.
From GaussianAnalysis.matrix Require Import quadric_certificate centered_correction.
From GaussianAnalysis.convex Require Import image_projection psd_residual logdet_barrier.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From GaussianAnalysis.comparison Require Import gauss_matrix_law.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Gaussian Require Import Representation Limit.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Features Require Import Regular.
From EllipsoidUniversality.Sat Require Import Apriori.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sample_residual_coef {n d : nat} (x : paper_main_sample n d) :
    'M[R]_(d*d,n) :=
  (Num.sqrt n%:R)^-1 *:
    ((restricted_isometry.tuple_mx (unsat_features n d x))^T *m
      @centered_correction.centering_mx RR n).

Definition sample_residual_projection {n d : nat} (x : paper_main_sample n d) :=
  psd_residual_projection d%:R (sample_residual_coef x).
Definition sample_residual_direction {n d : nat} (x : paper_main_sample n d) :=
  psd_residual_direction d%:R (sample_residual_coef x).
Definition sample_residual_outer {n d : nat} (x : paper_main_sample n d) :=
  weighted_outer (fun i : 'I_n => sample_residual_direction x 0 i)
    (fun i => paper_main_point x i).
Definition sample_residual_moment {n d : nat} (x : paper_main_sample n d) :=
  \sum_(i < n) sample_residual_direction x 0 i *: paper_main_point x i.

Lemma measurable_sample_residual_coef n d :
  measurable_fun [set: paper_main_sample n d] (fun x => sample_residual_coef x : 'M[RR]_(d*d,n)).
Proof.
rewrite /sample_residual_coef.
apply: measurable_scalemx; first exact: measurable_cst.
apply: measurable_mulmx; last exact: measurable_cst.
apply: (measurableT_comp (g := fun x => restricted_isometry.tuple_mx
  (unsat_features n d x) : 'M[RR]_(n,d*d))).
  exact: measurable_trmx.
apply: (measurableT_comp (g := fun x => unsat_features n d x :
  n.-tuple 'rV[RR]_(d*d))); last exact: measurable_unsat_features.
change (measurable_fun [set: n.-tuple 'rV[RR]_(d*d)]
  (@gauss_matrix_law.tuple_mx RR n (d*d))).
exact: gauss_matrix_law.measurable_tuple_mx.
Qed.

Lemma measurable_sample_residual_projection n d : (0 < d)%N ->
  measurable_fun [set: paper_main_sample n d] (fun x => sample_residual_projection x : 'rV[RR]_n).
Proof.
move=> d0.
apply: (measurableT_comp (g := fun x => sample_residual_coef x :
  'M[RR]_(d*d,n))); last exact: measurable_sample_residual_coef.
exact: (@psd_residual_projection_measurable RR d n d%:R d0 (ler0n _ d)).
Qed.
Lemma measurable_sample_residual_direction n d : (0 < d)%N ->
  measurable_fun [set: paper_main_sample n d] (fun x => sample_residual_direction x : 'rV[RR]_n).
Proof.
move=> d0.
apply: (measurableT_comp (g := fun x => sample_residual_coef x :
  'M[RR]_(d*d,n))); last exact: measurable_sample_residual_coef.
exact: (@psd_residual_direction_measurable RR d n d%:R d0 (ler0n _ d)).
Qed.

Lemma sample_residual_coef_outer_eq n d (x x' : paper_main_sample n d) :
  (forall i : 'I_n, paper_main_point x i *m (paper_main_point x i)^T =
    paper_main_point x' i *m (paper_main_point x' i)^T) ->
  sample_residual_coef x = sample_residual_coef x'.
Proof.
move=> h.
have e : unsat_features n d x = unsat_features n d x'.
  apply: eq_from_tnth => i.
  by rewrite /unsat_features !tnth_mktuple /unsat_feature h.
by rewrite /sample_residual_coef e.
Qed.
Lemma sample_residual_projection_outer_eq n d (x x' : paper_main_sample n d) :
  (forall i : 'I_n, paper_main_point x i *m (paper_main_point x i)^T =
    paper_main_point x' i *m (paper_main_point x' i)^T) ->
  sample_residual_projection x = sample_residual_projection x'.
Proof. by move=> h; rewrite /sample_residual_projection (sample_residual_coef_outer_eq h). Qed.
Lemma sample_residual_direction_outer_eq n d (x x' : paper_main_sample n d) :
  (forall i : 'I_n, paper_main_point x i *m (paper_main_point x i)^T =
    paper_main_point x' i *m (paper_main_point x' i)^T) ->
  sample_residual_direction x = sample_residual_direction x'.
Proof. by move=> h; rewrite /sample_residual_direction (sample_residual_coef_outer_eq h). Qed.

Lemma sample_residual_direction_sign_eq n d (x x' : paper_main_sample n d)
    (s : 'I_n -> R) :
  (forall i, s i ^+ 2 = 1) ->
  (forall i : 'I_n, paper_main_point x' i = s i *: paper_main_point x i) ->
  sample_residual_direction x' = sample_residual_direction x.
Proof.
move=> s2 hx; apply: sample_residual_direction_outer_eq => i.
by rewrite hx linearZ /= -scalemxAl -scalemxAr scalerA -expr2 s2 scale1r.
Qed.

Lemma sample_map_feature_row n d (x : paper_main_sample n d) (S : 'M[R]_d) :
  sample_map x S = feature_row (unsat_features n d x) S.
Proof.
apply/rowP => i; rewrite /sample_map /coef_map /feature_row !mxE.
by rewrite -mxvec_sample_W mxdot_mxvec.
Qed.

Lemma sample_map_matrix_action n d (x : paper_main_sample n d) (S : 'M[R]_d) :
  mxvec S *m (restricted_isometry.tuple_mx (unsat_features n d x))^T =
  sample_map x S.
Proof.
apply/rowP => i; rewrite /sample_map /coef_map mxE mxE.
rewrite -[RHS]mxdot_mxvec mxvec_sample_W /mxdot big_ord1.
apply: eq_bigr => j _.
by rewrite /restricted_isometry.tuple_mx !mxE mulrC.
Qed.

Lemma sample_residual_coef_action n d (x : paper_main_sample n d) (S : 'M[R]_d) :
  mxvec S *m sample_residual_coef x =
  (Num.sqrt n%:R)^-1 *: (sample_map x S *m centered_correction.centering_mx n).
Proof.
by rewrite /sample_residual_coef -scalemxAr mulmxA sample_map_matrix_action.
Qed.

Lemma centered_rowE n (v : 'rV[R]_n) :
  v *m centered_correction.centering_mx n =
  \row_i (v 0 i - (\sum_j v 0 j) / n%:R).
Proof.
have vo : v *m centered_correction.centering_ones n =
    (\sum_j v 0 j)%:M :> 'M[R]_1.
  apply/matrixP => i j; rewrite !ord1 !mxE.
  under eq_bigr do rewrite /centered_correction.centering_ones mxE mulr1.
  by rewrite eqxx mulr1n.
rewrite /centered_correction.centering_mx mulmxBr mulmx1 -scalemxAr
  mulmxA vo mul_scalar_mx scalerA.
apply/rowP => i.
by rewrite /centered_correction.centering_ones !mxE mulr1 mulrC.
Qed.

Lemma frobenius_centered_sq n (v : 'rV[R]_n) :
  frobenius (v *m centered_correction.centering_mx n) ^+ 2 = centered_sq v.
Proof.
rewrite centered_rowE frobenius_sqr /mxdot big_ord1 /centered_sq.
by apply: eq_bigr => i _; rewrite !mxE expr2.
Qed.

(* The algebraic identity remains valid at zero dimensions because
   inversion is total. The minimum theorem below requires n,d > 0. *)
Lemma sample_residual_coef_sqr n d (x : paper_main_sample n d) (S : 'M[R]_d) :
  frobenius (mxvec S *m sample_residual_coef x) ^+ 2 =
  centered_sq (feature_row (unsat_features n d x) S) / n%:R.
Proof.
rewrite sample_residual_coef_action frobeniusZ exprMn.
rewrite real_normK ?num_real // exprVn sqr_sqrtr ?ler0n //.
by rewrite frobenius_centered_sq sample_map_feature_row mulrC.
Qed.

Lemma sample_residual_coef_mass n d (x : paper_main_sample n d) :
  (0 < n)%N ->
  sample_residual_coef x *m centered_correction.centering_ones n = 0.
Proof.
move=> n0.
have P1 : centered_correction.centering_mx n *m
    centered_correction.centering_ones n = 0 :> 'cV[R]_n.
  apply/trmx_inj; rewrite trmx_mul trmx0.
  rewrite (symmetricmxP _ (centered_correction.centering_symmetric _ n)).
  exact: centered_correction.centering_mass.
by rewrite /sample_residual_coef -scalemxAl -mulmxA P1 mulmx0 scaler0.
Qed.

Lemma sample_residual_coef_column_symmetric n d (x : paper_main_sample n d) i :
  (vec_mx ((col i (sample_residual_coef x))^T) : 'M[R]_d)
    \is symmetricmx.
Proof.
have Ws j : sample_W x j \is symmetricmx.
  apply/symmetricmxP; rewrite /sample_W linearZ /= linearB /=
    trmx_mul trmxK trmx1.
  done.
have colE : vec_mx ((col i (sample_residual_coef x))^T) =
    (Num.sqrt n%:R)^-1 *:
      \sum_j (centered_correction.centering_mx n) j i *: sample_W x j.
  rewrite tr_col /sample_residual_coef linearZ /= trmx_mul trmxK
    linearZ /= row_mul restricted_isometry.tuple_mxE linearZ /= linear_sum /=.
  congr (_ *: _); apply: eq_bigr => j _.
  by rewrite linearZ /= !mxE -mxvec_sample_W mxvecK.
apply/symmetricmxP; rewrite colE linearZ /= linear_sum /=.
congr (_ *: _); apply: eq_bigr => j _.
by rewrite linearZ /= (symmetricmxP _ (Ws j)).
Qed.

Theorem sample_residual_gamma n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N ->
  universality_fitting_error n d x =
    frobenius (sample_residual_projection x) ^+ 2.
Proof.
move=> n0 d0.
have nr0 : (0 : RR) < n%:R by rewrite ltr0n.
pose K := @psd_trace_vectors RR d d%:R.
pose A := sample_residual_coef x.
have Kcp : compact K by exact: psd_trace_vectors_compact.
have K0 : K !=set0.
  apply: psd_trace_vectors_nonempty d0 _; exact: ler0n.
have Kcvx : forall u v (t : RR), K u -> K v -> 0 <= t <= 1 ->
    K (u + t *: (v-u)).
  exact: psd_trace_vectors_convex.
have [[v Kv ev] _] := image_projectionP A Kcp K0 Kcvx.
pose S0 := vec_mx v.
have S0K : psd_trace_slice d S0.
  have [vp vt] := Kv; split.
  - exact/paper_psdP.
  - by rewrite paper_traceE.
have vecK (S : 'M[R]_d) : psd_trace_slice d S -> K (mxvec S).
  move=> [Sp St]; rewrite /K /psd_trace_vectors /= mxvecK; split.
  - exact/paper_psdP.
  - by rewrite -paper_traceE.
pose E (S : 'M[R]_d) := centered_sq (feature_row (unsat_features n d x) S).
pose V := [set E S | S in psd_trace_slice d].
have E0 : forall S, 0 <= E S.
  move=> S; rewrite /E /centered_sq.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have Vlb : has_lbound V.
  by exists 0 => _ [S _ <-]; exact: E0.
have ES0 : V (E S0) by exists S0.
have zE : frobenius (sample_residual_projection x) ^+ 2 = E S0 / n%:R.
  have h := @sample_residual_coef_sqr n d x S0.
  rewrite /S0 vec_mxK -/A ev in h.
  exact: h.
have Emin S : psd_trace_slice d S -> E S0 <= E S.
  move=> SK.
  have hn := @image_projection_min RR (d*d) n K A Kcp K0 Kcvx
    (mxvec S) (vecK S SK).
  have hs : frobenius (sample_residual_projection x) ^+ 2 <=
      frobenius (mxvec S *m A) ^+ 2.
    by rewrite ler_sqr ?nnegrE ?frobenius_ge0.
  rewrite zE /A (@sample_residual_coef_sqr n d x S) -/E in hs.
  by move: hs; rewrite ler_pM2r ?invr_gt0.
have infE : inf V = E S0.
  apply/le_anti; rewrite (ge_inf Vlb ES0) /=.
  apply: lb_le_inf; first by exists (E S0).
  by move=> _ [S SK <-]; exact: Emin S SK.
rewrite unsat_fitting_error // unsat_value_closed //.
change (n%:R^-1 * inf V = frobenius (sample_residual_projection x) ^+ 2).
by rewrite infE mulrC -zE.
Qed.

Lemma sample_residual_norm_le1 n d (x : paper_main_sample n d) :
  frobenius (sample_residual_direction x) <= 1.
Proof. exact: image_direction_norm_le1. Qed.

Lemma sample_residual_direction_projection0 n d (x : paper_main_sample n d) :
  sample_residual_projection x = 0 -> sample_residual_direction x = 0.
Proof. exact: image_direction_zero. Qed.

Lemma sample_residual_outer_direction0 n d (x : paper_main_sample n d) :
  sample_residual_direction x = 0 -> sample_residual_outer x = 0.
Proof.
move=> hz; rewrite /sample_residual_outer /weighted_outer hz.
by apply: big1 => i _; rewrite mxE scale0r.
Qed.

Lemma sample_residual_moment_direction0 n d (x : paper_main_sample n d) :
  sample_residual_direction x = 0 -> sample_residual_moment x = 0.
Proof.
move=> hz; rewrite /sample_residual_moment hz.
by apply: big1 => i _; rewrite mxE scale0r.
Qed.


Lemma sample_residual_projection_gamma0 n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> universality_fitting_error n d x = 0 ->
  sample_residual_projection x = 0.
Proof.
move=> n0 d0 g0.
have h := @sample_residual_gamma n d x n0 d0.
rewrite g0 in h.
have f0 : frobenius (sample_residual_projection x) = 0 by nra.
by apply/eqP; rewrite -frobenius_eq0 f0.
Qed.

Lemma sample_residual_direction_gamma0 n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> universality_fitting_error n d x = 0 ->
  sample_residual_direction x = 0.
Proof.
move=> n0 d0 g0; apply: sample_residual_direction_projection0.
exact: sample_residual_projection_gamma0 n0 d0 g0.
Qed.

Lemma sample_residual_outer_gamma0 n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> universality_fitting_error n d x = 0 ->
  sample_residual_outer x = 0.
Proof.
move=> n0 d0 g0; apply: sample_residual_outer_direction0.
exact: sample_residual_direction_gamma0 n0 d0 g0.
Qed.

Lemma sample_residual_moment_gamma0 n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> universality_fitting_error n d x = 0 ->
  sample_residual_moment x = 0.
Proof.
move=> n0 d0 g0; apply: sample_residual_moment_direction0.
exact: sample_residual_direction_gamma0 n0 d0 g0.
Qed.

Lemma sample_residual_norm n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N -> 0 < universality_fitting_error n d x ->
  frobenius (sample_residual_direction x) = 1.
Proof.
move=> n0 d0 g0; apply: image_direction_norm.
apply/negP => /eqP p0.
have h := @sample_residual_gamma n d x n0 d0.
have p0' : sample_residual_projection x = 0 := p0.
by rewrite p0' frobenius0 expr0n in h; rewrite h ltxx in g0.
Qed.

Lemma sample_residual_sum0 n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N ->
  \sum_(i < n) sample_residual_direction x 0 i = 0.
Proof.
move=> n0 d0; apply: psd_residual_sum0 => //.
  by rewrite ltr0n.
have oneE : (\col_(_ < n) (1 : R)) =
    centered_correction.centering_ones n.
  by apply/matrixP => i j; rewrite /centered_correction.centering_ones !mxE.
rewrite oneE; exact: sample_residual_coef_mass.
Qed.

Lemma sample_residual_adjoint_margin n d (x : paper_main_sample n d) :
  (0 < d)%N ->
  psdmx (psd_residual_adjoint (sample_residual_coef x)
    (sample_residual_direction x) -
    (frobenius (sample_residual_projection x) / d%:R)%:M).
Proof.
move=> d0; apply: psd_residual_psd => //.
  by rewrite ltr0n.
exact: sample_residual_coef_column_symmetric.
Qed.

Lemma sample_residual_margin_scale n d (g : R) : (0 < d)%N ->
  Num.sqrt n%:R * Num.sqrt d%:R * (g / d%:R) =
    Num.sqrt (n%:R / d%:R) * g.
Proof.
move=> d0.
have dr0 : (0 : RR) < d%:R by rewrite ltr0n.
have sd0 : Num.sqrt (d%:R : RR) != 0 by rewrite gt_eqF // sqrtr_gt0.
have dE : (d%:R : RR) = Num.sqrt d%:R ^+ 2 by rewrite sqr_sqrtr // ltW.
rewrite sqrtrM ?ler0n // sqrtrV ?ler0n //.
rewrite [in LHS]dE expr2 invfM.
rewrite -expr2 sqrtr_sqr ger0_norm ?sqrtr_ge0 //.
rewrite mulrA [Num.sqrt n%:R * Num.sqrt d%:R * g]mulrAC -!mulrA.
by rewrite [Num.sqrt d%:R * _]mulrA mulfV // mul1r [g * _]mulrC.
Qed.

(* Exact adjoint normalization for every zero-mass weight vector. *)
Lemma sample_residual_adjoint_sample_adj n d (x : paper_main_sample n d)
    (u : 'rV[R]_n) :
  \sum_i u 0 i = 0 ->
  psd_residual_adjoint (sample_residual_coef x) u =
  (Num.sqrt n%:R)^-1 *: sample_adj x u.
Proof.
move=> hu.
have uP : u *m centered_correction.centering_mx n = u.
  rewrite centered_rowE; apply/rowP => i.
  by rewrite mxE hu mul0r subr0.
rewrite /psd_residual_adjoint /sample_residual_coef linearZ /=
  trmx_mul trmxK -scalemxAr.
rewrite (symmetricmxP _ (centered_correction.centering_symmetric _ n))
  mulmxA uP linearZ /= -mxvec_sample_adj mxvecK.
done.
Qed.

Lemma sample_adj_zero_mass n d (x : paper_main_sample n d) (u : 'rV[R]_n) :
  \sum_i u 0 i = 0 ->
  sample_adj x u = (Num.sqrt d%:R)^-1 *:
    weighted_outer (fun i : 'I_n => u 0 i) (fun i => paper_main_point x i).
Proof.
move=> hu; rewrite /sample_adj /coef_adj.
under eq_bigr do rewrite /sample_W scalerA mulrC -scalerA scalerBr.
by rewrite -scaler_sumr sumrB -scaler_suml hu scale0r subr0 /weighted_outer.
Qed.

Lemma sample_residual_adjoint_outer n d (x : paper_main_sample n d)
    (u : 'rV[R]_n) :
  (0 < n)%N -> (0 < d)%N -> \sum_i u 0 i = 0 ->
  weighted_outer (fun i : 'I_n => u 0 i) (fun i => paper_main_point x i) =
  (Num.sqrt n%:R * Num.sqrt d%:R) *:
    psd_residual_adjoint (sample_residual_coef x) u.
Proof.
move=> n0 d0 hu.
have sn0 : (Num.sqrt n%:R : R) != 0 by rewrite sqrtr_eq0 -ltNge ltr0n.
have sd0 : (Num.sqrt d%:R : R) != 0 by rewrite sqrtr_eq0 -ltNge ltr0n.
rewrite (sample_residual_adjoint_sample_adj x hu) (sample_adj_zero_mass x hu).
by rewrite !scalerA -mulrA mulrACA !mulfV // mul1r scale1r.
Qed.

Theorem sample_residual_margin n d (x : paper_main_sample n d) :
  (0 < n)%N -> (0 < d)%N ->
  psdmx (sample_residual_outer x -
    (Num.sqrt (n%:R / d%:R) *
      Num.sqrt (universality_fitting_error n d x))%:M).
Proof.
move=> n0 d0.
have hy := sample_residual_sum0 x n0 d0.
have h := sample_residual_adjoint_margin x d0.
have hg : Num.sqrt (universality_fitting_error n d x) =
    frobenius (sample_residual_projection x).
  by rewrite (sample_residual_gamma x n0 d0) sqrtr_sqr ger0_norm ?frobenius_ge0.
rewrite /sample_residual_outer (sample_residual_adjoint_outer x n0 d0 hy) hg.
rewrite -(sample_residual_margin_scale n _ d0) -scale_scalar_mx -scalerBr.
apply: psdmxZ => //.
by rewrite mulr_ge0 ?sqrtr_ge0.
Qed.
