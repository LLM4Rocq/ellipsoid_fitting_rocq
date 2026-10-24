From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral random_opnorm.
From GaussianAnalysis.matrix Require Import centered_correction centered_quadratic_correction.
From GaussianAnalysis.probability Require Import lindeberg subgaussian efron_stein.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.

(**md**************************************************************************)
(* # Independent isotropic rows                                             *)
(*                                                                           *)
(* Finite-sample covariance and mean bounds for independent random rows.     *)
(* Coordinates within a row need not be independent. Covariance estimates   *)
(* use directional subgaussianity and isotropic second moments; centering   *)
(* is required only for the mean and centered covariance estimates.         *)
(*                                                                           *)
(* Write H for the matrix of k rows, hbar for their mean, and               *)
(* B = 288 K^2 (sqrt(k(d+1)) + d+1). The covariance majorant has mean <= B; *)
(* E ||hbar||^2 = d/k; the centered Gram deviation has a measurable majorant *)
(* of mean <= (B+d)/k. A measurable event with failure probability          *)
(* <= 2(B+d)/k gives ||H^T P H/k - I|| <= 1/2. For s >= 0, another event   *)
(* of failure probability <= 2 exp(-s) bounds all squared row norms by     *)
(* 64 K^2 (7 + 6d + log k + s). Constants are explicit, not optimized.     *)
(* The unnormalized covariance bound allows k=0; normalized results need  *)
(* k>0. Every result allows d=0. The general scalar second-moment lemma     *)
(* needs only integrable centered summands and integrable squares.         *)
(*                                                                           *)
(* Covariance concentration reuses opnorm_sum_subexponential; centering    *)
(* a squared subgaussian variable uses subexponential_center with factor 3. *)
(* The maximum-row bound is sparse_norm_subgaussian at sparsity one.       *)
(* Source: the reserve-sample argument in doc/shifted-gaussian.tex.          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section row_algebra.
Context {R : realType} {k d : nat}.

Lemma isotropic_row_form (x : 'rV[R]_d) (v : 'cV[R]_d) :
  mxdot v ((x^T *m x - 1%:M) *m v) =
    mxdot x v^T ^+ 2 - frobenius v ^+ 2.
Proof.
rewrite mulmxBl mxdotBr mul1mx frobenius_sqr; congr (_ - _).
rewrite -mulmxA [x *m v]mx11_scalar -[v]trmxK -mxdot_rowE trmxK.
rewrite mul_mx_scalar mxdotZr.
have -> : mxdot v x^T = mxdot x v^T.
  by rewrite -(mxdot_trmx v x^T) trmxK mxdotC.
by rewrite expr2.
Qed.

Lemma tuple_mx_gram (x : k.-tuple 'rV[R]_d) :
  (tuple_mx x)^T *m tuple_mx x = \sum_i (tnth x i)^T *m tnth x i.
Proof.
apply/matrixP => a b; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE big_ord1 !mxE.
Qed.

Lemma tuple_mx_centered_gram (x : k.-tuple 'rV[R]_d) :
  \sum_i ((tnth x i)^T *m tnth x i - 1%:M) =
    (tuple_mx x)^T *m tuple_mx x - k%:R *: 1%:M.
Proof. by rewrite sumrB -tuple_mx_gram sumr_const card_ord -scaler_nat. Qed.

Lemma measurable_rows_matrix :
  measurable_fun [set: k.-tuple 'rV[R]_d] (fun x => tuple_mx x).
Proof.
apply/measurable_fun_mxP => i j; under eq_fun do rewrite /tuple_mx mxE.
exact: measurableT_comp (measurable_mxentry 0 j) (measurable_tnth i).
Qed.

End row_algebra.

Section covariance.
Context {R : realType} (k d : nat).
Variable mu : nat -> probability 'rV[R]_d R.
Variable K : R.
Hypothesis K0 : 0 < K.
Hypothesis sub : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  subgaussian (mu i) (fun x => mxdot x y) K.
Hypothesis iso : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  \int[mu i]_x mxdot x y ^+ 2 = frobenius y ^+ 2.

Definition isotropic_covariance_bound :=
  288 * K ^+ 2 * (Num.sqrt (k%:R * d.+1%:R) + d.+1%:R).

Theorem isotropic_covariance_majorant :
  exists N : k.-tuple 'rV[R]_d -> R,
  [/\ measurable_fun setT N,
    (forall x, opnorm ((tuple_mx x)^T *m tuple_mx x - k%:R *: 1%:M) <= N x) &
    (\int[tuple_prod mu k]_x (N x)%:E <= isotropic_covariance_bound%:E)%E].
Proof.
pose Y (x : 'rV[R]_d) := x^T *m x - 1%:M.
have L0 : 0 < 3 * K ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have sY (v : 'cV[R]_d) i : frobenius v <= 1 -> (i < k)%N ->
    subexponential (mu i) (fun x => mxdot v (Y x *m v)) (3 * K ^+ 2).
  move=> v1 ik.
  have vt1 : frobenius v^T <= 1 by rewrite frobenius_trmx.
  have h := subexponential_center (subexponential_sqr (sub ik vt1)).
  rewrite (iso ik vt1) frobenius_trmx in h.
  have e : (fun x => mxdot v (Y x *m v)) =
      (fun x => mxdot x v^T ^+ 2 - frobenius v ^+ 2).
    by apply/funext => x; exact: isotropic_row_form.
  by rewrite e.
have cY (v : 'cV[R]_d) i : frobenius v <= 1 -> (i < k)%N ->
    \int[mu i]_x mxdot v (Y x *m v) = 0.
  move=> v1 ik.
  have vt1 : frobenius v^T <= 1 by rewrite frobenius_trmx.
  have i2 := integrable_subgaussian_exprn 2 (sub ik vt1).
  have ic := finite_measure_integrable_cst (mu i) (frobenius v ^+ 2) measurableT.
  under eq_Rintegral do rewrite /Y isotropic_row_form.
  rewrite (RintegralB measurableT i2 ic) (iso ik vt1) frobenius_trmx.
  rewrite Rintegral_cst; first exact: measurableT.
  change (frobenius v ^+ 2 - frobenius v ^+ 2 * fine (mu i [set: 'rV[R]_d]) = 0).
  by rewrite probability_setT /= mulr1 subrr.
have [N hn] := opnorm_sum_subexponential L0 sY cY.
have a1 i : (i < k)%N -> `|1 : R| <= 1 by rewrite normr1.
have [mN bN eN] := hn (fun=> 1) a1.
exists (N (fun=> 1)); split => //.
- move=> x; have h := bN x.
  have e : sym_part (\sum_(i < k) 1 *: Y (tnth x i)) =
      (tuple_mx x)^T *m tuple_mx x - k%:R *: 1%:M.
    under eq_bigr do rewrite scale1r.
    rewrite /Y tuple_mx_centered_gram /sym_part.
    have et : ((tuple_mx x)^T *m tuple_mx x - k%:R *: 1%:M)^T =
        (tuple_mx x)^T *m tuple_mx x - k%:R *: 1%:M.
      rewrite [(_ - _)^T]linearB /= trmx_mul trmxK.
      by rewrite [(_ *: _)^T]linearZ /= tr_scalar_mx.
    rewrite et scalerDr -scalerDl.
    by rewrite (_ : 2^-1 + 2^-1 = 1 :> R) ?scale1r //; field.
  by rewrite e in h.
- apply: le_trans eN _; rewrite lee_fin /isotropic_covariance_bound.
  by rewrite (_ : 96 * (3 * K ^+ 2) = 288 * K ^+ 2) //; ring.
Qed.

End covariance.

Section independent_second_moment.
Context {R : realType} {e} {T : measurableType e} {k : nat}.
Variable mu : nat -> probability T R.
Variable f : 'I_k -> T -> R.
Hypothesis fi : forall i : 'I_k, (mu i).-integrable setT (EFin \o f i).
Hypothesis f2i : forall i : 'I_k,
  (mu i).-integrable setT (fun t => (f i t ^+ 2)%:E).
Hypothesis fc : forall i : 'I_k, \int[mu i]_t f i t = 0.

Let P := tuple_prod mu k.

Lemma integrable_independent_coordinate i :
  P.-integrable setT (fun x => (f i (tnth x i))%:E).
Proof.
have /integrableP[mf hf] := fi i.
apply/integrableP; split.
  exact: measurableT_comp mf (measurable_tnth i).
under eq_integral do rewrite abse_EFin.
rewrite /P (ge0_integral_tuple_prod_coord mu i (f := fun t => (`|f i t|)%:E)) //.
by apply/measurable_EFinP; apply: measurableT_comp => //; exact/measurable_EFinP.
Qed.

Lemma independent_product_moment (i j : 'I_k) :
  P.-integrable setT (fun x => (f i (tnth x i) * f j (tnth x j))%:E) /\
  \int[P]_x (f i (tnth x i) * f j (tnth x j)) =
    if i == j then \int[mu i]_t f i t ^+ 2 else 0.
Proof.
have [->|ij] := eqVneq i j.
  have h2 := f2i j; have /integrableP[m2 b2] := h2.
  have hP : P.-integrable setT (fun x => (f j (tnth x j) ^+ 2)%:E).
    apply/integrableP; split.
      exact: measurableT_comp m2 (measurable_tnth j).
    under eq_integral do rewrite abse_EFin (ger0_norm (sqr_ge0 _)).
    rewrite /P (ge0_integral_tuple_prod_coord mu j (f := fun t => (f j t ^+ 2)%:E)) //.
    - by move=> t; rewrite lee_fin sqr_ge0.
    - have ea : (\int[mu j]_t `|(f j t ^+ 2)%:E|)%E =
          (\int[mu j]_t (f j t ^+ 2)%:E)%E.
        by apply: eq_integral => t _; rewrite abse_EFin (ger0_norm (sqr_ge0 _)).
      by rewrite ea in b2.
  split; first by under eq_fun do rewrite -expr2.
  rewrite /Rintegral.
  under eq_integral do rewrite -expr2.
  by rewrite /P (integral_tuple_prod_coord mu j m2).
have indep (x : k.-tuple T) t : f j (tnth (tuple_set x i t) j) = f j (tnth x j).
  by rewrite /tuple_set tnth_mktuple eq_sym (negbTE ij).
have [ip ep] := integral_tuple_prod_coordM (fi i)
  (integrable_independent_coordinate j) indep.
split=> //; rewrite /Rintegral ep.
have z : (\int[mu i]_t (f i t)%:E)%E = 0%E.
  rewrite -(fineK (integrable_fin_num measurableT (fi i))).
  by rewrite -/(\int[mu i]_t f i t) fc.
by rewrite z mul0e.
Qed.

Theorem independent_centered_sum_second_moment :
  P.-integrable setT (fun x => ((\sum_i f i (tnth x i)) ^+ 2)%:E) /\
  \int[P]_x (\sum_i f i (tnth x i)) ^+ 2 =
    \sum_(i < k) \int[mu i]_t f i t ^+ 2.
Proof.
have ex x : (\sum_i f i (tnth x i)) ^+ 2 =
    \sum_i \sum_j f i (tnth x i) * f j (tnth x j).
  by rewrite expr2 mulr_suml; apply: eq_bigr => i _; rewrite mulr_sumr.
have hI i : P.-integrable setT
    (fun x => (\sum_j f i (tnth x i) * f j (tnth x j))%:E).
  under eq_fun do rewrite -sumEFin.
  by apply: integrable_sum => // j _; exact: (independent_product_moment i j).1.
split.
- under eq_fun do rewrite ex -sumEFin.
  by apply: integrable_sum => // i _; exact: hI.
- under eq_Rintegral do rewrite ex.
  rewrite Rintegral_sum //; apply: eq_bigr => i _.
  rewrite Rintegral_sum //; first by move=> j; exact: (independent_product_moment i j).1.
  under eq_bigr do rewrite (independent_product_moment _ _).2.
  by rewrite (bigD1 i) //= eqxx big1 ?addr0 // => j /negbTE ji; rewrite eq_sym ji.
Qed.

End independent_second_moment.

Section row_mean_algebra.
Context {R : realType} {k d : nat}.

Lemma reserve_mean_entry (x : k.-tuple 'rV[R]_d) (j : 'I_d) :
  reserve_mean (tuple_mx x) j 0 = k%:R^-1 * \sum_i (tnth x i) 0 j.
Proof.
rewrite /reserve_mean !mxE; congr (_ * _); apply: eq_bigr => i _.
by rewrite /centering_ones !mxE mulr1.
Qed.

Lemma reserve_mean_square (x : k.-tuple 'rV[R]_d) :
  frobenius (reserve_mean (tuple_mx x)) ^+ 2 =
    (k%:R^-1) ^+ 2 * \sum_(j < d) (\sum_i (tnth x i) 0 j) ^+ 2.
Proof.
rewrite frobenius_sqr /mxdot mulr_sumr; apply: eq_bigr => j _.
by rewrite big_ord1 -expr2 reserve_mean_entry exprMn.
Qed.

End row_mean_algebra.

Section mean_second_moment.
Context {R : realType} (k d : nat).
Variable mu : nat -> probability 'rV[R]_d R.
Variable K : R.
Hypothesis sub : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  subgaussian (mu i) (fun x => mxdot x y) K.
Hypothesis iso : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  \int[mu i]_x mxdot x y ^+ 2 = frobenius y ^+ 2.
Hypothesis cen : forall i (y : 'rV[R]_d), (i < k)%N -> frobenius y <= 1 ->
  \int[mu i]_x mxdot x y = 0.

Let delta_unit (j : 'I_d) : frobenius (delta_mx 0 j : 'rV[R]_d) = 1.
Proof. by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1. Qed.

Let coordinate_sub (i : 'I_k) (j : 'I_d) :
  subgaussian (mu i) (fun x : 'rV[R]_d => x 0 j) K.
Proof.
have h := sub (ltn_ord i) (y := delta_mx 0 j).
have e : (fun x : 'rV[R]_d => mxdot x (delta_mx 0 j)) = (fun x => x 0 j).
  by apply/funext => x; rewrite mxdot_delta.
by rewrite e delta_unit in h; exact: h.
Qed.

Let coordinate_centered (i : 'I_k) (j : 'I_d) :
  \int[mu i]_x x 0 j = 0.
Proof.
have h := cen (ltn_ord i) (y := delta_mx 0 j).
rewrite delta_unit in h; have := h (lexx 1).
by under eq_Rintegral do rewrite mxdot_delta.
Qed.

Let coordinate_isotropic (i : 'I_k) (j : 'I_d) :
  \int[mu i]_x x 0 j ^+ 2 = 1.
Proof.
have h := iso (ltn_ord i) (y := delta_mx 0 j).
rewrite delta_unit expr1n in h; have := h (lexx 1).
by under eq_Rintegral do rewrite mxdot_delta.
Qed.

Theorem isotropic_mean_second_moment : (0 < k)%N ->
  (tuple_prod mu k).-integrable setT
    (fun x => (frobenius (reserve_mean (tuple_mx x)) ^+ 2)%:E) /\
  \int[tuple_prod mu k]_x frobenius (reserve_mean (tuple_mx x)) ^+ 2 = d%:R / k%:R.
Proof.
move=> k0.
have sums j :
    (tuple_prod mu k).-integrable setT
      (fun x => ((\sum_i (tnth x i) 0 j) ^+ 2)%:E) /\
    \int[tuple_prod mu k]_x (\sum_i (tnth x i) 0 j) ^+ 2 = k%:R.
  have i1 (i : 'I_k) : (mu i).-integrable setT (EFin \o (fun x : 'rV[R]_d => x 0 j)).
    have h := integrable_subgaussian_exprn 1 (coordinate_sub i j).
    by apply: eq_integrable h => // x _; rewrite /= expr1.
  have i2 (i : 'I_k) := integrable_subgaussian_exprn 2 (coordinate_sub i j).
  have [ip ep] := independent_centered_sum_second_moment i1 i2
    (fun i => coordinate_centered i j).
  split => //; rewrite ep.
  under eq_bigr do rewrite coordinate_isotropic.
  by rewrite sumr_const card_ord.
have isum : (tuple_prod mu k).-integrable setT
    (fun x => (\sum_(j < d) (\sum_i (tnth x i) 0 j) ^+ 2)%:E).
  under eq_fun do rewrite -sumEFin.
  by apply: integrable_sum => // j _; exact: (sums j).1.
split.
- under eq_fun do rewrite reserve_mean_square EFinM.
  exact: integrableZl.
- under eq_Rintegral do rewrite reserve_mean_square.
  rewrite (RintegralZl _ measurableT isum) Rintegral_sum //;
    first by move=> j; exact: (sums j).1.
  under eq_bigr do rewrite (sums _).2.
  rewrite sumr_const card_ord -mulr_natl.
  have kn : k%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
  by field.
Qed.

End mean_second_moment.

Section centered_gram_algebra.
Context {R : realType} {k d : nat}.

Lemma centered_covariance_mean (H : 'M[R]_(k,d)) : (0 < k)%N ->
  centered_covariance H = H^T *m H -
    k%:R *: (reserve_mean H *m (reserve_mean H)^T).
Proof.
move=> k0; have kn : k%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite /centered_covariance /centering_mx mulmxBr mulmxBl mulmx1.
rewrite -scalemxAr -scalemxAl mulmxA.
rewrite /reserve_mean [(_ *: _)^T]linearZ /=.
rewrite -scalemxAl -scalemxAr !scalerA.
rewrite trmx_mul trmxK -mulmxA.
have -> : (k%:R * k%:R^-1) * k%:R^-1 = k%:R^-1 :> R by field.
by rewrite !mulmxA.
Qed.

Lemma centered_covariance_normalized (H : 'M[R]_(k,d)) : (0 < k)%N ->
  k%:R^-1 *: centered_covariance H - 1%:M =
    k%:R^-1 *: (H^T *m H - k%:R *: 1%:M) -
    reserve_mean H *m (reserve_mean H)^T.
Proof.
move=> k0; have kn : k%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite centered_covariance_mean // !scalerBr !scalerA mulVf // !scale1r.
by rewrite addrAC.
Qed.

Lemma opnorm_column_outer (v : 'cV[R]_d) :
  opnorm (v *m v^T) <= frobenius v ^+ 2.
Proof.
apply: le_trans (opnorm_le_frobenius _) _.
apply: le_trans (frobenius_mulmx _ _) _.
by rewrite frobenius_trmx expr2.
Qed.

Lemma centered_covariance_deviation (H : 'M[R]_(k,d)) : (0 < k)%N ->
  opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <=
    k%:R^-1 * opnorm (H^T *m H - k%:R *: 1%:M) +
    frobenius (reserve_mean H) ^+ 2.
Proof.
move=> k0; rewrite centered_covariance_normalized //.
apply: le_trans (opnormD _ _) _.
rewrite opnormN opnormZ ger0_norm ?invr_ge0 ?ler0n //.
by apply: lerD => //; exact: opnorm_column_outer.
Qed.

End centered_gram_algebra.

Section markov_wrapper.
Context {R : realType} {e} {T : measurableType e}.
Variable P : probability T R.

Lemma probability_markov_ge (f : T -> R) (t : R) : 0 < t ->
  measurable_fun setT f -> (forall x, 0 <= f x) ->
  (P [set x | (t <= f x)%R] <= (t^-1)%:E * \int[P]_x (f x)%:E)%E.
Proof.
move=> t0 mf f0.
have mt : measurable [set x | t <= f x].
  have := mf measurableT _ (measurable_itv `[t, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => x /=; rewrite in_itv /= andbT.
rewrite -(setIT [set x | t <= f x]) -integral_indic //.
apply: le_trans (_ : (\int[P]_x (t^-1 * f x)%:E <= _)%E).
  apply: ge0_le_integral => //.
  - by apply/measurable_EFinP; exact: measurable_indic.
  - by apply/measurable_EFinP; apply: measurable_funM.
  move=> x _; rewrite lee_fin indicE.
  have [/set_mem /= tx|_] := boolP (x \in [set x0 | t <= f x0]).
    rewrite -[true%:R]/(1 : R) -(mulVf (lt0r_neq0 t0)).
    by apply: ler_wpM2l => //; rewrite invr_ge0 ltW.
  by rewrite -[false%:R]/(0 : R) mulr_ge0 // invr_ge0 ltW.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP.
- by rewrite invr_ge0 ltW.
Qed.

End markov_wrapper.

Section centered_covariance_probability.
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

Theorem isotropic_centered_covariance_majorant : (0 < k)%N ->
  exists M : k.-tuple 'rV[R]_d -> R,
  [/\ measurable_fun setT M,
    (forall x, opnorm (k%:R^-1 *: centered_covariance (tuple_mx x) - 1%:M) <= M x) &
    (\int[tuple_prod mu k]_x (M x)%:E <=
      ((isotropic_covariance_bound k d K + d%:R) / k%:R)%:E)%E].
Proof.
move=> k0.
have [N [mN bN eN]] := isotropic_covariance_majorant K0 sub iso.
have [im em] := isotropic_mean_second_moment sub iso cen k0.
have mm : measurable_fun setT
    (fun x : k.-tuple 'rV[R]_d => frobenius (reserve_mean (tuple_mx x)) ^+ 2).
  by apply/measurable_EFinP; exact: measurable_int im.
have n0 x : 0 <= N x := le_trans (opnorm_ge0 _) (bN x).
have eM : (\int[tuple_prod mu k]_x
    (frobenius (reserve_mean (tuple_mx x)) ^+ 2)%:E)%E = (d%:R / k%:R)%:E.
  rewrite -(fineK (integrable_fin_num measurableT im)).
  by rewrite -/(\int[tuple_prod mu k]_x frobenius (reserve_mean (tuple_mx x)) ^+ 2) em.
exists (fun x => k%:R^-1 * N x + frobenius (reserve_mean (tuple_mx x)) ^+ 2).
split.
- by apply: measurable_funD => //; apply: measurable_funM.
- move=> x; apply: le_trans (centered_covariance_deviation _ k0) _.
  by rewrite lerD2r ler_wpM2l ?invr_ge0 ?ler0n.
- under eq_integral do rewrite EFinD EFinM.
  rewrite ge0_integralD //.
  - by move=> x _; rewrite mule_ge0 ?lee_fin ?invr_ge0.
  - by apply: emeasurable_funM; [exact: measurable_cst|exact/measurable_EFinP].
  - by move=> x _; rewrite lee_fin sqr_ge0.
  - exact/measurable_EFinP.
  - rewrite ge0_integralZl_EFin //.
    + by move=> x _; rewrite lee_fin.
    + exact/measurable_EFinP.
    + rewrite eM.
      have ki0 : (0 <= (k%:R^-1)%:E :> \bar R)%E by rewrite lee_fin invr_ge0.
      apply: le_trans (leeD (lee_wpmul2l ki0 eN) (lexx _)) _.
      rewrite -EFinM -EFinD lee_fin.
      by rewrite mulrC -mulrDl.
Qed.

Theorem isotropic_mean_tail (t : R) : (0 < k)%N -> 0 < t ->
  (tuple_prod mu k [set x | (t <= frobenius (reserve_mean (tuple_mx x)))%R] <=
    (d%:R / (k%:R * t ^+ 2))%:E)%E.
Proof.
move=> k0 t0.
have [im em] := isotropic_mean_second_moment sub iso cen k0.
have mm : measurable_fun setT
    (fun x : k.-tuple 'rV[R]_d => frobenius (reserve_mean (tuple_mx x)) ^+ 2).
  by apply/measurable_EFinP; exact: measurable_int im.
have h := probability_markov_ge (tuple_prod mu k) (exprn_gt0 2 t0) mm
  (fun x => sqr_ge0 (frobenius (reserve_mean (tuple_mx x)))).
have e (x : k.-tuple 'rV[R]_d) : (t <= frobenius (reserve_mean (tuple_mx x))) =
    (t ^+ 2 <= frobenius (reserve_mean (tuple_mx x)) ^+ 2).
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0 //; exact: ltW t0.
have es : [set x : k.-tuple 'rV[R]_d | (t <= frobenius (reserve_mean (tuple_mx x)))%R] =
    [set x : k.-tuple 'rV[R]_d | (t ^+ 2 <= frobenius (reserve_mean (tuple_mx x)) ^+ 2)%R].
  by apply/seteqP; split=> x /=; rewrite e.
rewrite es; apply: le_trans h _.
rewrite -(fineK (integrable_fin_num measurableT im)) -/(\int[tuple_prod mu k]_x
  frobenius (reserve_mean (tuple_mx x)) ^+ 2) em -EFinM lee_fin.
by rewrite [(k%:R * t ^+ 2)^-1]invfM; nra.
Qed.

Theorem isotropic_centered_covariance_event : (0 < k)%N ->
  exists G : set (k.-tuple 'rV[R]_d),
  [/\ measurable G,
    (tuple_prod mu k (~` G) <=
      (2 * (isotropic_covariance_bound k d K + d%:R) / k%:R)%:E)%E &
    forall x, G x ->
      opnorm (k%:R^-1 *: centered_covariance (tuple_mx x) - 1%:M) <= 2^-1].
Proof.
move=> k0.
have [M [mM bM eM]] := isotropic_centered_covariance_majorant k0.
have m0 x : 0 <= M x := le_trans (opnorm_ge0 _) (bM x).
pose G := [set x | M x < 2^-1].
have mG : measurable G.
  have := mM measurableT _ (measurable_itv `]-oo, 2^-1[).
  rewrite setTI; congr measurable; apply/seteqP.
have eG : ~` G = [set x | 2^-1 <= M x].
  apply/seteqP; split=> x /= hx.
  - rewrite leNgt; apply/negP; exact: hx.
  - move=> hlt; move: hx; by rewrite leNgt hlt.
exists G; split => //.
- rewrite eG.
  have t0 : 0 < 2^-1 :> R by rewrite invr_gt0.
  apply: le_trans (probability_markov_ge (tuple_prod mu k) t0 mM m0) _.
  apply: le_trans (lee_wpmul2l _ eM) _.
    by rewrite lee_fin invrK.
  by rewrite invrK -EFinM lee_fin mulrA.
- move=> x gx; exact: le_trans (bM x) (ltW gx).
Qed.

Theorem isotropic_max_row_event (s : R) : (0 < k)%N -> 0 <= s ->
  exists G : set (k.-tuple 'rV[R]_d),
  [/\ measurable G,
    (tuple_prod mu k (~` G) <= (2 * expR (-s))%:E)%E &
    forall x, G x -> forall i : 'I_k,
      frobenius (tnth x i) ^+ 2 <=
        64 * K ^+ 2 * (7 + 6 * d%:R + ln k%:R + s)].
Proof.
move=> k0 s0.
have sub1 i (y : 'rV[R]_d) : (i < k)%N -> mxdot y y = 1 ->
    subgaussian (mu i) (fun x => mxdot x y) K.
  move=> ik y1; apply: sub => //.
  by rewrite /frobenius y1 sqrtr1.
have cen1 i (y : 'rV[R]_d) : (i < k)%N -> mxdot y y = 1 ->
    \int[mu i]_x mxdot x y = 0.
  move=> ik y1; apply: cen => //.
  by rewrite /frobenius y1 sqrtr1.
have [G [mG pG bG]] := sparse_norm_subgaussian K0 sub1 cen1
  (isT : (0 < 1)%N) k0 s0.
exists G; split => // x gx i.
have supp1 : supp (delta_mx 0 i : 'rV[R]_k) = finset.set1 i.
  apply/setP => j; rewrite /supp !inE mxE eqxx /=.
  by rewrite pnatr_eq0 eq_sym; case: (j == i).
have ns : (#|supp (delta_mx ord0 i : 'rV[R]_k)| <= 1)%N by rewrite supp1 cards1.
have h := bG x gx (delta_mx 0 i) ns.
have dm : delta_mx 0 i *m tuple_mx x = tnth x i :> 'rV[R]_d.
  apply/rowP => j; rewrite mxE (bigD1 i) //= !mxE !eqxx mul1r.
  rewrite big1 ?addr0 // => l li.
  by rewrite mxE eqxx /= (negbTE li) mul0r.
have du : frobenius (delta_mx 0 i : 'rV[R]_k) = 1.
  by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
rewrite dm du mulr1 /sparse_norm_bound /= divr1 mul1r natrD /= in h.
have a0 : 0 <= 7 + 6 * d%:R + ln k%:R + s.
  have lk : 0 <= ln k%:R :> R by rewrite ln_ge0 // ler1n.
  have dd : 0 <= d%:R :> R by [].
  lra.
have he : 1 + ln k%:R + 6 * (1 + d%:R) + s =
    7 + 6 * d%:R + ln k%:R + s :> R by ring.
rewrite he in h.
have hs : frobenius (tnth x i) ^+ 2 <=
    (8 * K * Num.sqrt (7 + 6 * d%:R + ln k%:R + s)) ^+ 2.
  by rewrite lerXn2r ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?sqrtr_ge0 ?(ltW K0) //; exact: h.
apply: le_trans hs _.
by rewrite !exprMn sqr_sqrtr //; nra.
Qed.

End centered_covariance_probability.

Section example.
Variable R : realType.

(* Two noncentered scalar observations, 2 and 4: centering subtracts 18
   from their raw Gram value 20. This is independent of any fitting model. *)
Example two_observations_centered_gram :
  let H : 'M[R]_(2,1) := \col_i (if i == 0 then 2 else 4) in
  centered_covariance H = 2%:M.
Proof.
move=> H; rewrite centered_covariance_mean //.
apply/matrixP => i j; rewrite !ord1 /H /reserve_mean /centering_ones.
do 2 rewrite !mxE !big_ord_recr !big_ord0 /=.
rewrite !mxE /=.
by field.
Qed.

End example.
