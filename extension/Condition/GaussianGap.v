(* The Gaussian gap above the threshold alpha_C, at Stdlib's R: item Q4 of
   phase 8 (notes/three-extensions-plan.md, section 2, G4).

   Setting as in Condition/GaussianWitness: for C > 1, K and B are the cone
   of condition number C and its slice of trace d, as sets of column vectors
   of the mxvec coordinates; cond_support C (vec_mx h) / d tends to
   sqrt (condition_alpha C) in probability (item Q2, a hypothesis here).

   1. Centering (the centering law of unsat_value_gaussian_features of
      Gaussian/FittingError, for any set of symmetric matrices). For k + 1
      features Z, center_mx Z = Q^T Z, with Q = centering_mx k the
      orthonormal basis of the orthogonal of 1. sum_sq_ge_center:
      sum_i (b - <Z_i, v>)^2 >= |Q^T Z v^T|^2 for every b
      (centered_sq_le, centered_sq_centering). For the Gaussian features of
      the rows of a (k + 1) x d^2 Gaussian matrix A, Q^T Z v^T =
      sqrt (2 / d) Q^T A v^T for v in the slice (center_features_mul), and
      Q^T A is a k x d^2 Gaussian matrix (centering_linE,
      centering_lin_orth, gauss_orthogonal_law), so that
      inf_(x in B) |Q^T Z x| >= sqrt (2 / d) inf_(x in B) |Q^T A x|
      (escape_center_ge).
   2. The mean of the auxiliary value. For n d / d^2 -> alpha >
      condition_alpha C and l = sqrt alpha - sqrt (condition_alpha C),
      (|g| - sigma_K(h)) / d -> l in probability, for z = (g, h) of law
      gauss ((n d - 1) + d * d), so E (|g| - sigma_K(h))_+ >= l d / 4 for
      every large d (gap_mean), since E f >= c P(f >= c) for f >= 0
      (Rintegral_ge_indic).
   3. The gap. cone_escape_lower_tail with r = sqrt d, rho = sqrt (C d) and
      u = l d sqrt d / 16 gives inf_(x in B) |Q^T A x| >= l d sqrt d / 8
      outside an event of probability at most 2 exp (- l^2 d^2 / (512 C)),
      so sum_i (b - <Z_i, mxvec S>)^2 >= (2 / d) (l d sqrt d / 8)^2 =
      l^2 d^2 / 32 >= g n for every S of the slice and every b, with
      g = l^2 / (64 alpha) and n <= 2 alpha d^2 (gaussian_gap_n).
      gaussian_gap states this in the form that the unsatisfiable half
      takes as its hypothesis. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From GaussianAnalysis Require Import euclidean measurable_matrix gauss.
From GaussianAnalysis Require Import gauss_law gauss_smoothing escape cgmt.
From GaussianAnalysis Require Import gauss_concentration.
From GaussianAnalysis Require Import cone_escape moreau condition_cone.
From GaussianAnalysis Require Import gauss_matrix_law lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Gaussian Require Import Cones Representation.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidUniversality.Gaussian Require Import Subcritical.
From EllipsoidUniversality.Condition Require Import GaussianWitness.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. Centering. *)

(* Q^T Z, for the k + 1 features Z. *)
Definition center_mx (k m : nat) (Z : k.+1.-tuple 'rV[RR]_m) : 'M[RR]_(k, m) :=
  (centering_mx k)^T *m tuple_mx Z.
Arguments center_mx {k m} Z.

Lemma sum_sq_ge_center (k m : nat) (Z : k.+1.-tuple 'rV[RR]_m)
    (v : 'rV[RR]_m) (b : R) :
  frobenius (center_mx Z *m v^T) ^+ 2 <=
  \sum_(i < k.+1) (b - mxdot (tnth Z i) v) ^+ 2.
Proof.
pose w : 'rV[RR]_k.+1 := \row_i mxdot (tnth Z i) v.
have wT : w^T = tuple_mx Z *m v^T.
  apply/matrixP => i j; rewrite ord1.
  by rewrite mulmx_trE row_tuple_mx !mxE.
have := centered_sq_le k.+1 w b (ltn0Sn k).
rewrite centered_sq_centering -frobenius_trmx trmx_mul wT mulmxA.
by under eq_bigr do rewrite mxE.
Qed.

Section centering_gap.
Variables (C : R) (k d : nat).
Hypothesis C1 : 1 < C.

Local Notation B := (tr_set (@cond_slice_vec RR d C)).

(* Q^T Z v^T = sqrt (2 / d) Q^T A v^T for the Gaussian features Z of the rows
   of A = vec_mx a. *)
Lemma center_features_mul (a : 'rV[RR]_(k.+1 * (d * d)))
    (x : 'cV[RR]_(d * d)) : B x ->
  center_mx (gaussian_features 3%:R k.+1 d a) *m x =
  Num.sqrt (2%:R / d%:R) *:
    ((vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d)) *m x).
Proof.
move=> Bx; rewrite /center_mx -mulmxA (features_mul C k.+1 d a x Bx).
by rewrite -scalemxAr centering_linE mxvecK mulmxA.
Qed.

Lemma escape_center_ge (a : 'rV[RR]_(k.+1 * (d * d))) : (0 < d)%N ->
  Num.sqrt (2%:R / d%:R) *
    escape_inf B (vec_mx (a *m centering_lin k (d * d)) : 'M[RR]_(k, d * d)) <=
  escape_inf B (center_mx (gaussian_features 3%:R k.+1 d a)).
Proof.
move=> d0; have B0 := cond_B_neq0 C d C1 d0.
apply: escape_inf_ge => // x Bx.
rewrite center_features_mul // frobeniusZ ger0_norm ?sqrtr_ge0 //.
by apply: ler_wpM2l; [exact: sqrtr_ge0 | exact: escape_inf_le].
Qed.

Lemma measurable_escape_center : (0 < d)%N ->
  measurable_fun setT
    (fun Z : k.+1.-tuple 'rV[RR]_(d * d) => escape_inf B (center_mx Z) : RR).
Proof.
move=> d0.
have m2 := measurable_escape_inf (N := k) (cond_B_neq0 C d C1 d0)
  (cond_B_le C d C1).
have -> : (fun Z : k.+1.-tuple 'rV[RR]_(d * d) => escape_inf B (center_mx Z)) =
    (fun Z => escape_inf B
       (vec_mx (mxvec (center_mx Z)) : 'M[RR]_(k, d * d))).
  by apply/funext => Z; rewrite mxvecK.
apply: measurableT_comp m2 _.
apply: measurableT_comp (@measurable_mxvec _ _ _) _.
exact: measurableT_comp (measurable_mulmx_l _ _ _ (centering_mx k)^T)
  (@measurable_tuple_mx _ _ _).
Qed.

End centering_gap.

(* 2. The mean of the auxiliary value. *)

(* E f >= c P(A) when f >= c on A and f >= 0. *)
Lemma Rintegral_ge_indic d' (T : measurableType d') (P : probability T RR)
    (f : T -> RR) (A : set T) (c : RR) :
  measurable A -> 0 <= c -> (forall x, 0 <= f x) ->
  (forall x, A x -> c <= f x) -> P.-integrable setT (EFin \o f) ->
  c * fine (P A) <= \int[P]_x f x.
Proof.
move=> mA c0 f0 fA fi.
have iA := integrable_indic P mA.
have ii : P.-integrable setT (EFin \o (fun x => c * \1_A x)).
  apply: (eq_integrable measurableT _ _ _ (integrableZl measurableT c iA)).
  by move=> x _ /=; rewrite EFinM.
have -> : c * fine (P A) = \int[P]_x (c * \1_A x).
  by rewrite RintegralZl // /Rintegral integral_indic // setIT.
apply: le_Rintegral => // x _; rewrite indicE.
have [xA|xA] := boolP (x \in A).
  by rewrite mulr1; apply: fA; rewrite inE in xA.
by rewrite mulr0.
Qed.

(* x |-> max (0, x) is 1-Lipschitz. *)
Lemma max0_lipschitz (a b : RR) : `|Num.max 0 a - Num.max 0 b| <= `|a - b|.
Proof.
have k (u v : RR) : Num.max 0 u <= Num.max 0 v + `|u - v|.
  by apply: max0_leD => //; have := ler_norm (u - v); lra.
rewrite ler_norml; apply/andP; split.
  by have := k b a; rewrite distrC; lra.
by have := k a b; lra.
Qed.

Definition gap_l (C alpha : R) : R :=
  Num.sqrt alpha - Num.sqrt (condition_alpha C).

Section gap_mean.
Variables (C alpha : R) (n : nat -> nat).
Hypotheses (C1 : 1 < C) (a0 : 0 < alpha) (aC : condition_alpha C < alpha).
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_alpha C)).

Local Notation P := (fun d => @gauss RR ((n d).-1 + d * d)).

Lemma gap_l_gt0 : 0 < gap_l C alpha.
Proof.
rewrite /gap_l subr_gt0.
have [h|h] := leP (condition_alpha C) 0.
  by rewrite ler0_sqrtr // sqrtr_gt0.
by rewrite ltr_sqrt.
Qed.

(* (|g| - cond_support C (vec_mx h)) / d -> l in probability. *)
Lemma gap_ratio_cvg : cvg_prob P
  (fun d z => (frobenius (lsubmx z) -
     cond_support C (vec_mx (rsubmx z) : 'M[RR]_d)) / d%:R)
  (gap_l C alpha).
Proof.
have h1 := gnorm_cvg alpha n hn.
have h2 := @cvg_prob_gauss_rsubmx (fun d => d * d) (fun d => (n d).-1) _ _
  hQ2.
apply: cvg_prob_eq (cvg_probB h1 h2); exists 0%N => d _ z /=.
by rewrite mulrBl.
Qed.

Lemma gap_mean : exists D : nat, forall d, (D <= d)%N ->
  gap_l C alpha * d%:R / 4%:R <=
  \int[P d]_z Num.max 0 (frobenius (lsubmx z) -
    cone_sup (tr_set (@cond_cone_vec RR d C)) (rsubmx z)).
Proof.
have l0 : 0 < gap_l C alpha := gap_l_gt0.
have l2 : 0 < gap_l C alpha / 2%:R by rewrite divr_gt0.
have e2 : (0 : RR) < 2^-1 by rewrite invr_gt0 ltr0n.
have [D hD] := gap_ratio_cvg (gap_l C alpha / 2%:R) l2 _ e2.
exists (maxn D 1) => d; rewrite geq_max => /andP[dD d1].
have [A [mA PA EA]] := hD d dD.
have K0 : tr_set (@cond_cone_vec RR d C) 0 := cond_K0 C d.
(* the positive part of |g| - sigma_K(h) is 2-Lipschitz, hence integrable *)
have fL (z z' : 'rV[RR]_((n d).-1 + d * d)) :
    `|Num.max 0 (frobenius (lsubmx z) -
        cone_sup (tr_set (@cond_cone_vec RR d C)) (rsubmx z)) -
      Num.max 0 (frobenius (lsubmx z') -
        cone_sup (tr_set (@cond_cone_vec RR d C)) (rsubmx z'))| <=
    2%:R * frobenius (z - z').
  apply: le_trans (max0_lipschitz _ _) _.
  have h1 := cone_sup_lipschitz K0 (rsubmx z) (rsubmx z').
  have h2 := ler_frobeniusB (lsubmx z) (lsubmx z').
  have h3 := frobenius_rsubmx_le (z - z').
  have h4 := frobenius_lsubmx_le (z - z').
  rewrite !linearB /= in h3 h4.
  set c1 := cone_sup _ (rsubmx z); set c2 := cone_sup _ (rsubmx z').
  have -> : frobenius (lsubmx z) - c1 - (frobenius (lsubmx z') - c2) =
      (frobenius (lsubmx z) - frobenius (lsubmx z')) - (c1 - c2) by ring.
  apply: le_trans (ler_normB _ _) _.
  apply: le_trans (lerD (le_trans h2 h4) (le_trans h1 h3)) _.
  by rewrite mulr_natl mulr2n.
have fi := integrable_gauss_lipschitz fL.
have dR : (0 : RR) < d%:R by rewrite ltr0n.
have c0 : (0 : RR) <= gap_l C alpha * d%:R / 2%:R.
  by rewrite divr_ge0 // mulr_ge0 // ltW.
have f0 (z : 'rV[RR]_((n d).-1 + d * d)) : 0 <= Num.max 0
    (frobenius (lsubmx z) -
     cone_sup (tr_set (@cond_cone_vec RR d C)) (rsubmx z)).
  by rewrite le_max lexx.
(* outside A, (|g| - sigma_K(h)) / d > l / 2 *)
have fA (z : 'rV[RR]_((n d).-1 + d * d)) : (~` A) z ->
    gap_l C alpha * d%:R / 2%:R <= Num.max 0 (frobenius (lsubmx z) -
      cone_sup (tr_set (@cond_cone_vec RR d C)) (rsubmx z)).
  move=> nz.
  have hlt : `|(frobenius (lsubmx z) -
      cond_support C (vec_mx (rsubmx z) : 'M[RR]_d)) / d%:R -
      gap_l C alpha| < gap_l C alpha / 2%:R.
    by rewrite ltNge; apply/negP => h; apply: nz; exact: EA.
  rewrite (cond_cone_supE C d C1) le_max; apply/orP; right.
  move: hlt; rewrite ltr_norml => /andP[h _].
  have hX : gap_l C alpha / 2%:R < (frobenius (lsubmx z) -
      cond_support C (vec_mx (rsubmx z) : 'M[RR]_d)) / d%:R by lra.
  have e : gap_l C alpha * d%:R / 2%:R = gap_l C alpha / 2%:R * d%:R.
    by rewrite mulrAC.
  by rewrite e -ler_pdivlMr // ltW.
have hf := Rintegral_ge_indic _ _ (gauss ((n d).-1 + d * d)) _ (~` A) _
  (measurableC mA) c0 f0 fA fi.
apply: le_trans hf.
have fA' : gauss ((n d).-1 + d * d) A \is a fin_num := fin_num_measure _ A mA.
have pa : fine (gauss ((n d).-1 + d * d) A) <= 2^-1.
  by rewrite -lee_fin fineK.
rewrite probability_setC // -(fineK fA') -EFinB /=.
have e4 : gap_l C alpha * d%:R / 4%:R =
    gap_l C alpha * d%:R / 2%:R * 2^-1 by field.
rewrite e4; apply: ler_wpM2l => //.
rewrite lerBrDl -lerBrDr; apply: le_trans pa _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

End gap_mean.

(* 3. The gap. *)

Lemma gap_near_gt0 (x a : RR) : `|x - a| < a -> 0 < x.
Proof. by rewrite ltr_norml => /andP[h _]; lra. Qed.

Lemma gap_near_lt2 (x a : RR) : `|x - a| < a -> x < 2 * a.
Proof. by rewrite ltr_norml => /andP[_ h]; lra. Qed.

Lemma gap_thr_ge (A m rho r : RR) : r * (4%:R * A) <= r * m ->
  rho <= A * r -> 2%:R * A * r <= r * m - rho - A * r.
Proof. by move=> h1 h2; lra. Qed.

Lemma gap_tail_exp (L D r rho C : RR) : r ^+ 2 = D -> rho ^+ 2 = C * D ->
  C != 0 -> D != 0 -> L != 0 ->
  (L * D * r) ^+ 2 / (2 * rho ^+ 2) = D / (2 * C / L ^+ 2) * D.
Proof. by move=> r2 rho2 Cn Dn Ln; rewrite !exprMn r2 rho2; field. Qed.

Lemma gap_sq (s A r D : RR) : s ^+ 2 = 2%:R / D -> r ^+ 2 = D -> D != 0 ->
  (s * (2%:R * A * r)) ^+ 2 = 8%:R * A ^+ 2.
Proof. by move=> s2 r2 Dn; rewrite !exprMn s2 r2; field. Qed.

Lemma gap_const (L a D : RR) : a != 0 ->
  L ^+ 2 / (64%:R * a) * (2 * a * D ^+ 2) = 8%:R * (L / 16%:R * D) ^+ 2.
Proof. by move=> an; field. Qed.

Section gap.
Variables (C alpha : R) (n : nat -> nat).
Hypotheses (C1 : 1 < C) (a0 : 0 < alpha) (aC : condition_alpha C < alpha).
Hypothesis hn : universality_density_tends_to n alpha.
Hypothesis hQ2 : cvg_prob (fun d => @gauss RR (d * d))
  (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
  (Num.sqrt (condition_alpha C)).

(* For one sequence n: outside an event of Gaussian probability at most
   eps, sum_i (b - <Z_i, mxvec S>)^2 >= g n for every S of the slice and
   every b, with g = l^2 / (64 alpha). *)
Lemma gaussian_gap_n (eps : R) : 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      gap_l C alpha ^+ 2 / (64%:R * alpha) * (n d)%:R <=
      \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2].
Proof.
move=> e0.
pose l : RR := gap_l C alpha.
have l0 : 0 < l := gap_l_gt0 C alpha a0 aC.
pose l' : RR := (l / 16%:R)%R.
have l'0 : 0 < l' by rewrite divr_gt0 // ltr0n.
have C0 : 0 < C := lt_trans ltr01 C1.
have C0' : 0 <= C := ltW C0.
pose c : RR := (2 * C / l' ^+ 2)%R.
have c0 : 0 < c by rewrite divr_gt0 ?mulr_gt0 ?exprn_gt0.
have [D1 hD1] := gap_mean C alpha n C1 a0 aC hn hQ2.
have [D2 hD2] := sample_density_cvg alpha n hn alpha a0.
have [D3 hD3] := hn alpha a0.
have [D4 hD4] := expR_lin_small c eps c0 e0.
pose D5 := (archimedean.Num.truncn (Num.sqrt C / l')).+1.
exists (maxn (maxn (maxn D1 D2) (maxn D3 D4)) (maxn D5 1)) => d.
rewrite !geq_max => /andP[/andP[/andP[dD1 dD2] /andP[dD3 dD4]] /andP[dD5 d1]].
have dR : (0 : RR) < d%:R by rewrite ltr0n.
have dn : (d%:R : RR) != 0 := lt0r_neq0 dR.
have d2R : (0 : RR) < d%:R ^+ 2 := exprn_gt0 2 dR.
have d2n : (d%:R ^+ 2 : RR) != 0 := lt0r_neq0 d2R.
have hm := hD1 d dD1.
(* k + 1 = n d points, k > 0 and k + 1 < 2 alpha d^2 *)
have hk : (0 < (n d).-1)%N.
  have := mulr_gt0 (gap_near_gt0 _ _ (hD2 d dD2)) d2R.
  by rewrite (divfK d2n) ltr0n.
set k := (n d).-1 in hm hk.
have N0 : (0 < n d)%N := leq_trans hk (leq_pred (n d)).
have e : n d = k.+1 by rewrite /k prednK.
have hkn : k.+1%:R < 2 * alpha * d%:R ^+ 2.
  have := gap_near_lt2 _ _ (hD3 d dD3).
  by rewrite /paper_main_density RdivE e (ltr_pdivrMr _ _ d2R).
have hkn' : k.+1%:R <= 2 * alpha * d%:R ^+ 2 := ltW hkn.
(* the CGMT on the cone *)
pose K := tr_set (@cond_cone_vec RR d C).
pose B := tr_set (@cond_slice_vec RR d C).
pose rho : RR := Num.sqrt (C * d%:R).
pose r : RR := Num.sqrt d%:R.
pose A : RR := (l' * d%:R)%R.
pose u : RR := (A * r)%R.
have r0 : 0 < r by rewrite /r sqrtr_gt0.
have r0' : 0 <= r := ltW r0.
have A0 : 0 < A by rewrite /A mulr_gt0.
have u0 : 0 <= u by rewrite /u mulr_ge0 // ltW.
have K0 : K 0 := cond_K0 C d.
have B0 : B !=set0 := cond_B_neq0 C d C1 d1.
have Bb : forall x, B x -> frobenius x <= rho := cond_B_le C d C1.
have Kcone := cond_K_cone C d.
have BK : forall x, B x -> K x := cond_B_sub C d.
have Br : forall x, B x -> r <= frobenius x := cond_B_ge C d C1.
have tail := cone_escape_lower_tail K0 B0 Bb hk Kcone BK Br u0.
pose mean : RR := \int[gauss (k + d * d)]_z
  Num.max 0 (frobenius (lsubmx z) - cone_sup K (rsubmx z)).
pose thr : RR := (r * mean - rho - u)%R.
(* thr >= 2 A r, for 16 sqrt C <= l d *)
have hthr : 2%:R * A * r <= thr.
  have e4 : 4%:R * A = gap_l C alpha * d%:R / 4%:R by rewrite /A /l' /l; field.
  have hm' : r * (4%:R * A) <= r * mean.
    by rewrite e4; apply: (ler_wpM2l r0'); exact: hm.
  have hrho : rho <= A * r.
    rewrite /rho (sqrtrM _ C0'); apply: (ler_wpM2r r0').
    have h : Num.sqrt C / l' < d%:R.
      apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
      by rewrite ler_nat.
    by rewrite /A mulrC; apply: ltW; rewrite -(ltr_pdivrMr _ _ l'0).
  exact: (gap_thr_ge _ _ _ _ hm' hrho).
pose s2 : RR := Num.sqrt (2%:R / d%:R).
have s20 : 0 < s2 by rewrite /s2 sqrtr_gt0 divr_gt0 // ltr0n.
have s20' : 0 <= s2 := ltW s20.
have r2 : r ^+ 2 = d%:R by rewrite /r sqr_sqrtr ?ler0n.
have rho2 : rho ^+ 2 = C * d%:R by rewrite /rho sqr_sqrtr // mulr_ge0 ?ler0n.
rewrite e.
pose E := [set Z : k.+1.-tuple 'rV[RR]_(d * d) |
  escape_inf B (center_mx Z) <= s2 * thr].
have mE : measurable E :=
  measurable_le_set _ (s2 * thr) (measurable_escape_center C k d C1 d1).
exists E; split => //.
  (* the probability of the event *)
  rewrite gaussian_features_law //.
  pose T := [set b : 'rV[RR]_(k * (d * d)) |
    escape_inf B (vec_mx b : 'M[RR]_(k, d * d)) <= thr].
  have mT : measurable T :=
    measurable_le_set _ thr (measurable_escape_inf (N := k) B0 Bb).
  have mlin : measurable_fun setT
      (fun a : 'rV[RR]_(k.+1 * (d * d)) => a *m centering_lin k (d * d)).
    by apply: measurable_mulmx => //; exact: measurable_cst.
  have mTA : measurable
      [set a : 'rV[RR]_(k.+1 * (d * d)) | T (a *m centering_lin k (d * d))].
    by have := mlin measurableT _ mT; rewrite setTI.
  apply: (@le_trans _ _ (gauss (k.+1 * (d * d))
    [set a | T (a *m centering_lin k (d * d))])).
    apply: le_measure; rewrite ?inE.
    - have := measurable_gaussian_features 3%:R k.+1 d measurableT _ mE.
      by rewrite setTI.
    - exact: mTA.
    - move=> a ha.
      have ha' : escape_inf B (center_mx (gaussian_features 3%:R k.+1 d a)) <=
        s2 * thr := ha.
      have h := escape_center_ge C k d C1 a d1.
      have := le_trans h ha'.
      by rewrite (ler_pM2l s20) => h'; exact: h'.
  rewrite (gauss_orthogonal_law (centering_lin_orth k (d * d)) mT).
  apply: (le_trans tail).
  rewrite lee_fin; apply: (le_trans _ (hD4 d dD4)).
  have two0 : (0 : RR) < 2 by rewrite ltr0n.
  have Cn : C != 0 := lt0r_neq0 C0.
  have ln : l' != 0 := lt0r_neq0 l'0.
  have eu : u ^+ 2 / (2 * rho ^+ 2) = d%:R / c * d%:R :=
    gap_tail_exp _ _ _ _ _ r2 rho2 Cn dn ln.
  have dc0 : 0 < d%:R / c by rewrite divr_gt0.
  rewrite (ler_pM2l two0) ler_expR mulNr lerN2 eu (ler_pMr _ dc0) ler1n.
  exact: d1.
(* outside the event, the gap *)
move=> Z nE S hS b.
have hlt : s2 * thr < escape_inf B (center_mx Z) by rewrite ltNge; apply/negP.
have Bx : B (mxvec S)^T.
  by exists (mxvec S) => //; rewrite /cond_slice_vec /= mxvecK.
have hle : escape_inf B (center_mx Z) <=
    frobenius (center_mx Z *m (mxvec S)^T).
  by apply: escape_inf_le; exact: Bx.
have hsum := sum_sq_ge_center k (d * d) Z (mxvec S) b.
apply: (le_trans _ hsum).
have hA : 0 <= s2 * (2%:R * A * r) by rewrite !mulr_ge0 ?ler0n // ltW.
have h1 : s2 * (2%:R * A * r) <= frobenius (center_mx Z *m (mxvec S)^T).
  apply: (le_trans _ hle); apply: ltW; apply: (le_lt_trans _ hlt).
  exact: (ler_wpM2l s20').
have h2 : (s2 * (2%:R * A * r)) ^+ 2 <=
    frobenius (center_mx Z *m (mxvec S)^T) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0.
apply: (le_trans _ h2).
have s22 : s2 ^+ 2 = 2%:R / d%:R by rewrite /s2 sqr_sqrtr // divr_ge0 ?ler0n.
have eA : (s2 * (2%:R * A * r)) ^+ 2 = 8%:R * A ^+ 2 :=
  gap_sq _ _ _ _ s22 r2 dn.
rewrite eA.
have an : alpha != 0 := lt0r_neq0 a0.
have g0 : 0 <= gap_l C alpha ^+ 2 / (64%:R * alpha).
  by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 ?ler0n // ltW.
apply: (le_trans (ler_wpM2l g0 hkn')).
by rewrite (gap_const _ _ _ an).
Qed.

End gap.

(* Item Q4, in the form that the unsatisfiable half takes as its
   hypothesis: above alpha_C, with g = l^2 / (64 alpha) and
   l = sqrt alpha - sqrt (condition_alpha C). The hypothesis on
   cond_support is the limit of item Q2. *)
Theorem gaussian_gap (C alpha : R) :
  1 < C -> 0 < alpha -> condition_alpha C < alpha ->
  cvg_prob (fun d => @gauss RR (d * d))
    (fun d a => cond_support C (vec_mx a : 'M[RR]_d) / d%:R)
    (Num.sqrt (condition_alpha C)) ->
  exists g : R, 0 < g /\
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law 3%:R d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> forall S : 'M[R]_d, cond_slice C S -> forall b : R,
      g * (n d)%:R <= \sum_(i < n d) (b - mxdot (tnth Z i) (mxvec S)) ^+ 2].
Proof.
move=> C1 a0 aC hQ2; exists (gap_l C alpha ^+ 2 / (64%:R * alpha)); split.
  by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0 ?ltr0n // (gap_l_gt0 C alpha a0 aC).
move=> n hn eps e0.
exact: (gaussian_gap_n C alpha n C1 a0 aC hn hQ2 eps e0).
Qed.
