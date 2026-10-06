From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import partial_diff gauss_smoothing.

(**md**************************************************************************)
(* # The Sudakov-Fernique and Slepian inequalities                            *)
(*                                                                            *)
(* Let x have law gauss n and y have law gauss m. For A : 'M[R]_(n, k.+1),    *)
(* x *m A is a centered Gaussian vector of covariance A^T *m A, and every     *)
(* centered Gaussian vector of 'rV[R]_k.+1 has this form. If every increment  *)
(* of x *m A has a variance at most that of the same increment of y *m B,     *)
(* that is incr_var A j l <= incr_var B j l for all j and l, then             *)
(* E[rmax (x *m A)] <= E[rmax (y *m B)], where rmax z is the largest          *)
(* coordinate of z (sudakov_fernique). Equal variances and larger covariances *)
(* imply the hypothesis (slepian).                                            *)
(*                                                                            *)
(* The proof applies Kahane's comparison inequality (gauss_comparison) to the *)
(* log-sum-exp function lse b. For every square matrix M, the pairing of M    *)
(* with the Hessian of lse b at z is                                          *)
(* b / 2 * \sum_(j, l) p_j p_l (M j j + M l l - 2 M j l), with                *)
(* p = softmax b z (lse_hessian). For M = A^T *m A - B^T *m B it is           *)
(* nonpositive. Since rmax z <= lse b z <= rmax z + ln (k + 1) / b, letting b *)
(* grow concludes.                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*           rmax z == the largest coordinate of the row vector z             *)
(*          lse b z == b^-1 * ln (\sum_j expR (b * z 0 j))                    *)
(*    softmax b z j == expR (b * z 0 j) / \sum_i expR (b * z 0 i)             *)
(*   incr_var A j l == (A^T *m A) j j + (A^T *m A) l l - 2 * (A^T *m A) j l,  *)
(*                     the variance of (x *m A) 0 j - (x *m A) 0 l            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section rmax.
Context {R : realType} {k : nat}.
Implicit Types z : 'rV[R]_k.+1.

(* The largest coordinate of a row vector. *)
Definition rmax z : R := \big[Num.max/z 0 ord0]_j z 0 j.

Lemma le_rmax z j : z 0 j <= rmax z.
Proof. exact: le_bigmax. Qed.

Lemma rmax_le z c : (forall j, z 0 j <= c) -> rmax z <= c.
Proof. by move=> zc; apply/bigmax_leP; split. Qed.

Lemma rmax_eq z : exists j, rmax z = z 0 j.
Proof.
rewrite /rmax; elim/big_ind: _ => [|x y [i ->] [j ->]|i _]; first by exists ord0.
  by rewrite /maxr; case: ifP => _; [exists j|exists i].
by exists i.
Qed.

Lemma rmax_lipschitz z z' : `|rmax z - rmax z'| <= `|z - z'|.
Proof.
have h (u v : 'rV[R]_k.+1) : rmax u - rmax v <= `|u - v|.
  have [j ->] := rmax_eq u.
  apply: (@le_trans _ _ (u 0 j - v 0 j)); first by rewrite lerB// le_rmax.
  have -> : u 0 j - v 0 j = (u - v) 0 j by rewrite !mxE.
  exact: le_trans (ler_norm _) (mx_norm_entry_le _ _ _).
rewrite ler_norml h andbT lerNl opprB.
by rewrite (le_trans (h z' z))// distrC.
Qed.

Lemma continuous_rmax : continuous rmax.
Proof.
move=> z A /nbhs_ballP [d d0 dA]; apply/nbhs_ballP; exists d => // z'.
rewrite /= -ball_normE /= => zz; apply: dA; rewrite -ball_normE /=.
exact: le_lt_trans (rmax_lipschitz _ _) zz.
Qed.

Lemma rmax_norm z : `|rmax z| <= `|z|.
Proof.
have := rmax_lipschitz z 0; rewrite !subr0.
have [j ->] := rmax_eq (0 : 'rV[R]_k.+1).
by rewrite mxE subr0.
Qed.


End rmax.

Section lse.
Context {R : realType} {k : nat}.
Variable b : R.
Hypothesis b0 : 0 < b.
Implicit Types z : 'rV[R]_k.+1.

(* The log-sum-exp function, a smooth approximation of rmax, and its
   gradient, the softmax weights. *)
Definition lse z : R := b^-1 * ln (\sum_j expR (b * z 0 j)).

Definition softmax z (j : 'I_k.+1) : R := expR (b * z 0 j) / \sum_i expR (b * z 0 i).

Lemma lse_sum_gt0 z : 0 < \sum_j expR (b * z 0 j).
Proof.
by rewrite (bigD1 ord0)//= ltr_pwDl ?expR_gt0// sumr_ge0// => i _; exact: expR_ge0.
Qed.

Lemma rmax_le_lse z : rmax z <= lse z.
Proof.
have [j ->] := rmax_eq z.
rewrite /lse ler_pdivlMl// -ler_expR lnK ?posrE ?lse_sum_gt0//.
by rewrite (bigD1 j)//= lerDl sumr_ge0.
Qed.

Lemma lse_le_rmax z : lse z <= rmax z + ln k.+1%:R / b.
Proof.
have hS : \sum_j expR (b * z 0 j) <= k.+1%:R * expR (b * rmax z).
  apply: (@le_trans _ _ (\sum_(j < k.+1) expR (b * rmax z))).
    apply: ler_sum => j _; rewrite ler_expR.
    by apply: ler_wpM2l; [exact: ltW|exact: le_rmax].
  by rewrite sumr_const card_ord -[X in X <= _]mulr_natl.
have hl : ln (\sum_j expR (b * z 0 j)) <= b * rmax z + ln k.+1%:R.
  rewrite -ler_expR lnK ?posrE ?lse_sum_gt0// expRD lnK ?posrE ?ltr0n//.
  by rewrite mulrC.
have bi : 0 <= b^-1 by rewrite invr_ge0 ltW.
rewrite /lse (le_trans (ler_wpM2l bi hl))//.
by rewrite mulrDr mulrA mulVf ?gt_eqF// mul1r mulrC.
Qed.

Lemma delta_shiftE z j i (h : R) :
  (h *: delta_mx 0 j + z) 0 i = z 0 i + h * (i == j)%:R.
Proof. by rewrite !mxE eqxx /= addrC. Qed.

(* A real affine function of h has derivative its slope. *)
Lemma is_derive_affine (c d h : R) : is_derive h 1 (fun h : R => c + d * h) d.
Proof.
have hd := is_deriveD (is_derive_cst c h 1) (is_deriveZ d (is_derive_id h 1)).
have -> : (fun h : R => c + d * h) = cst c + d \*: id.
  by apply/funext => x; rewrite !fctE /GRing.scale.
by apply: (is_derive_eq hd); rewrite /GRing.scale /= add0r mulr1.
Qed.

Lemma is_derive_expR_coord z i j :
  is_derive z (delta_mx 0 j) (fun z => expR (b * z 0 i))
    (b * (i == j)%:R * expR (b * z 0 i)).
Proof.
apply: (is_derive_transfer
  (G := fun h : R => expR (b * z 0 i + b * (i == j)%:R * h)) (b := 0) (w := 1)).
  move=> h; rewrite delta_shiftE.
  by rewrite addr0 -[h%:A]/(h * 1) mulr1; congr expR; ring.
have := @is_derive1_comp R expR (fun h => b * z 0 i + b * (i == j)%:R * h) 0 _ _
  (is_derive_expR _) (is_derive_affine _ _ _).
by move=> h; apply: (is_derive_eq h); rewrite mulr0 addr0 mulrC.
Qed.

(* The chain rule for a real function of a function of 'rV[R]_k.+1. *)
Lemma is_derive_lift (F : 'rV[R]_k.+1 -> R) (g : R -> R) z (v : 'rV[R]_k.+1)
    (d dg : R) :
  is_derive z v F d -> is_derive (F z) 1 g dg -> is_derive z v (g \o F) (dg * d).
Proof.
move=> Fd gd.
have phid : is_derive (0 : R) 1 (fun h : R => F (h *: v + z)) d.
  apply: (is_derive_transfer (G := F) (b := z) (w := v)) => // h.
  by rewrite addr0 -[h%:A]/(h * 1) mulr1.
apply: (is_derive_transfer (G := g \o (fun h : R => F (h *: v + z))) (b := 0) (w := 1)).
  by move=> h /=; rewrite addr0 -[h%:A]/(h * 1) mulr1.
have e : F (0 *: v + z) = F z by rewrite scale0r add0r.
by apply: is_derive1_comp; rewrite /= e.
Qed.

Lemma is_derive_lse_sum z j :
  is_derive z (delta_mx 0 j) (fun z => \sum_i expR (b * z 0 i)) (b * expR (b * z 0 j)).
Proof.
have h := is_derive_sum (fun i => is_derive_expR_coord z i j).
have -> : (fun z => \sum_i expR (b * z 0 i)) = \sum_i (fun z => expR (b * z 0 i)).
  by apply/funext => w; rewrite fct_sumE.
apply: (is_derive_eq h); rewrite (bigD1 j)//= eqxx mulr1 big1 ?addr0// => i /negPf ->.
by rewrite mulr0 mul0r.
Qed.

Lemma is_derive_lse z j : is_derive z (delta_mx 0 j) lse (softmax z j).
Proof.
have h := is_derive_lift (is_derive_lse_sum z j)
  (is_deriveZ b^-1 (is_derive1_ln (lse_sum_gt0 z))).
apply: (is_derive_eq h); rewrite /softmax /GRing.scale /=.
have b1 : b != 0 by rewrite gt_eqF.
have s1 : \sum_i expR (b * z 0 i) != 0 by rewrite gt_eqF// lse_sum_gt0.
by field.
Qed.

Lemma is_derive_softmax z j l :
  is_derive z (delta_mx 0 l) (softmax ^~ j)
    (b * (softmax z j * (j == l)%:R - softmax z j * softmax z l)).
Proof.
have s1 : \sum_i expR (b * z 0 i) != 0 by rewrite gt_eqF// lse_sum_gt0.
have hid : is_derive (\sum_i expR (b * z 0 i)) 1 (@id R) 1 := is_derive_id _ _.
have hinv := is_derive_lift (is_derive_lse_sum z l) (is_deriveV s1 hid).
have h := is_deriveM (is_derive_expR_coord z j l) hinv.
apply: (is_derive_eq h); rewrite /softmax /GRing.scale /= mulr1.
by field.
Qed.

Lemma continuous_expR_coord i : continuous (fun z : 'rV[R]_k.+1 => expR (b * z 0 i)).
Proof.
move=> z; apply: continuous_comp; last exact: continuous_expR.
apply: (cvgM (cvg_cst _)); [apply: nbhs_filter|apply: nbhs_filter|].
exact: coord_continuous.
Qed.

Lemma continuous_softmax j : continuous (softmax ^~ j).
Proof.
move=> z.
have cS : {for z, continuous (fun z : 'rV[R]_k.+1 => \sum_i expR (b * z 0 i))}.
  by apply: continuous_sum => i; exact: continuous_expR_coord.
have s1 : \sum_i expR (b * z 0 i) != 0 by rewrite gt_eqF// lse_sum_gt0.
rewrite /softmax; apply: (@cvgM _ _ _ _ (fun x : 'rV[R]_k.+1 => expR (b * x 0 j))
  (fun x : 'rV[R]_k.+1 => (\sum_i expR (b * x 0 i))^-1)).
- apply: nbhs_filter.
- exact: continuous_expR_coord.
- exact: (cvgV s1 cS).
Qed.

Lemma softmax_ge0 z j : 0 <= softmax z j.
Proof. by rewrite /softmax divr_ge0 ?expR_ge0// ltW// lse_sum_gt0. Qed.

Lemma softmax_sum z : \sum_j softmax z j = 1.
Proof.
rewrite /softmax -mulr_suml mulfV// gt_eqF//; exact: lse_sum_gt0.
Qed.

Lemma softmax_le1 z j : softmax z j <= 1.
Proof.
rewrite -(softmax_sum z) (bigD1 j)//= lerDl sumr_ge0// => i _.
exact: softmax_ge0.
Qed.

End lse.

Section lse_smooth.
Context {R : realType} {k : nat}.
Variable b : R.
Hypothesis b0 : 0 < b.

(* The second partial derivatives of lse b. *)
Definition lse_D2 (j l : 'I_k.+1) (z : 'rV[R]_k.+1) : R :=
  b * (softmax b z j * (j == l)%:R - softmax b z j * softmax b z l).

Lemma lse_differentiable z : differentiable (lse b : 'rV[R]_k.+1 -> R^o) z.
Proof.
apply: (@partial_differentiable R k.+1 (lse b) (fun j z => softmax b z j)).
  by move=> j w; exact: is_derive_lse.
by move=> j; exact: continuous_softmax.
Qed.

Lemma lse_DE j : 'D_(delta_mx 0 j) (lse b) = softmax b ^~ j :> ('rV[R]_k.+1 -> R).
Proof. by apply/funext => z; have h := is_derive_lse b0 z j; rewrite derive_val. Qed.

Lemma continuous_lse_D2 j l : continuous (lse_D2 j l).
Proof.
move=> z; rewrite /lse_D2.
apply: (cvgM (cvg_cst _)); [apply: nbhs_filter|apply: nbhs_filter|].
apply: cvgB; first apply: nbhs_filter.
  apply: (@cvgM _ _ _ _ (softmax b ^~ j) (cst ((j == l)%:R))).
  - apply: nbhs_filter.
  - exact: continuous_softmax.
  - by apply: cvg_cst; apply: nbhs_filter.
apply: (@cvgM _ _ _ _ (softmax b ^~ j) (softmax b ^~ l)).
- apply: nbhs_filter.
- exact: continuous_softmax.
- exact: continuous_softmax.
Qed.

Lemma softmax_differentiable j z :
  differentiable (softmax b ^~ j : 'rV[R]_k.+1 -> R^o) z.
Proof.
apply: (@partial_differentiable R k.+1 (softmax b ^~ j) (lse_D2 j)).
  by move=> l w; exact: is_derive_softmax.
by move=> l; exact: continuous_lse_D2.
Qed.

Lemma lse_D2E j l :
  'D_(delta_mx 0 l) ('D_(delta_mx 0 j) (lse b)) = lse_D2 j l :> ('rV[R]_k.+1 -> R).
Proof.
rewrite lse_DE; apply/funext => z.
by have h := is_derive_softmax b z j l; rewrite derive_val.
Qed.

Lemma lse_hessian (M : 'M[R]_k.+1) z :
  \sum_j \sum_l M j l * lse_D2 j l z =
  b / 2 * \sum_j \sum_l softmax b z j * softmax b z l * (M j j + M l l - 2 * M j l).
Proof.
set p := softmax b z.
have sp : \sum_l p l = 1 := softmax_sum b z.
have A : \sum_j \sum_l M j l * lse_D2 j l z =
    b * (\sum_j M j j * p j - \sum_j \sum_l M j l * (p j * p l)).
  rewrite -sumrB mulr_sumr; apply: eq_bigr => j _.
  rewrite (bigD1 j)//= [in RHS](bigD1 j)//= /lse_D2 -/p eqxx mulr1.
  rewrite opprD addrA mulrBr mulrDr !mulrBr; congr (_ + _).
    by rewrite /p; ring.
  rewrite mulr_sumr -sumrN; apply: eq_bigr => l /negPf jl.
  by rewrite eq_sym jl mulr0 sub0r; ring.
have e1 : \sum_j \sum_l p j * p l * M j j = \sum_j M j j * p j.
  apply: eq_bigr => j _; rewrite -[RHS]mulr1 -sp mulr_sumr.
  by apply: eq_bigr => l _; ring.
have e2 : \sum_j \sum_l p j * p l * M l l = \sum_j M j j * p j.
  rewrite exchange_big /=; apply: eq_bigr => l _; rewrite -[RHS]mulr1 -sp mulr_sumr.
  by apply: eq_bigr => j _; ring.
have B : \sum_j \sum_l p j * p l * (M j j + M l l - 2 * M j l) =
    2 * (\sum_j M j j * p j - \sum_j \sum_l M j l * (p j * p l)).
  have -> : \sum_j \sum_l p j * p l * (M j j + M l l - 2 * M j l) =
      \sum_j \sum_l p j * p l * M j j + \sum_j \sum_l p j * p l * M l l -
      2 * \sum_j \sum_l M j l * (p j * p l).
    rewrite mulr_sumr -big_split -sumrB /=; apply: eq_bigr => j _.
    rewrite mulr_sumr -big_split -sumrB /=; apply: eq_bigr => l _.
    by ring.
  by rewrite e1 e2; ring.
by rewrite A B; field.
Qed.

End lse_smooth.

Section sudakov_fernique.
Context {R : realType}.

(* For x of law gauss n, the variance of (x *m A)_j - (x *m A)_l. *)
Definition incr_var n k (A : 'M[R]_(n, k)) (j l : 'I_k) : R :=
  (A^T *m A) j j + (A^T *m A) l l - 2 * (A^T *m A) j l.

Lemma integrable_gauss_rmax n k (A : 'M[R]_(n, k.+1)) :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun x => rmax (x *m A))).
Proof.
have cA : continuous (fun x : 'rV[R]_n => rmax (x *m A)).
  move=> x; apply: continuous_comp; last exact: continuous_rmax.
  exact: continuous_mulmxr.
apply: (integrable_gauss_poly (continuous_measurable_mx cA)
  (C := n%:R * `|A| + 1) (k := 1)) => x.
rewrite (le_trans (rmax_norm _))// (le_trans (mx_norm_mulmx_le _ _))// expr1.
have h0 := normr_ge0 x; have h1 := normr_ge0 A; have h2 : (0 : R) <= n%:R by [].
nra.
Qed.

Lemma lse_norm k (b : R) (z : 'rV[R]_k.+1) : 0 < b ->
  `|lse b z| <= `|z| + ln k.+1%:R / b.
Proof.
move=> b0; have c0 : 0 <= ln k.+1%:R / b by rewrite divr_ge0 ?ln_ge0 ?ler1n// ltW.
have l1 := rmax_le_lse b0 z; have l2 := lse_le_rmax b0 z.
have r1 := rmax_norm z.
have r2 : - `|z| <= rmax z by rewrite lerNl (le_trans _ r1)// -normrN ler_norm.
have r3 : rmax z <= `|z| by rewrite (le_trans (ler_norm _)).
rewrite ler_norml; apply/andP; split; lra.
Qed.

Lemma integrable_gauss_lse n k (b : R) (A : 'M[R]_(n, k.+1)) : 0 < b ->
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun x => lse b (x *m A))).
Proof.
move=> b0.
have cA : continuous (fun x : 'rV[R]_n => lse b (x *m A)).
  move=> x; apply: (continuous_comp (f := fun y : 'rV[R]_n => y *m A) (g := lse b)).
    exact: continuous_mulmxr.
  exact: differentiable_continuous (lse_differentiable b0 _).
apply: (integrable_gauss_poly (continuous_measurable_mx cA)
  (C := n%:R * `|A| + 1 + ln k.+1%:R / b) (k := 1)) => x.
rewrite (le_trans (lse_norm _ b0))// expr1.
have := mx_norm_mulmx_le x A.
have h0 := normr_ge0 x; have h1 := normr_ge0 A; have h2 : (0 : R) <= n%:R by [].
have c0 : 0 <= ln k.+1%:R / b by rewrite divr_ge0 ?ln_ge0 ?ler1n// ltW.
nra.
Qed.

Theorem sudakov_fernique n m k (A : 'M[R]_(n, k.+1)) (B : 'M[R]_(m, k.+1)) :
  (forall j l, incr_var A j l <= incr_var B j l) ->
  (\int[gauss n]_x (rmax (x *m A))%:E <= \int[gauss m]_y (rmax (y *m B))%:E)%E.
Proof.
move=> AB.
have iA := integrable_gauss_rmax A; have iB := integrable_gauss_rmax B.
rewrite -(fineK (integrable_fin_num measurableT iA)).
rewrite -(fineK (integrable_fin_num measurableT iB)) lee_fin.
apply/ler_addgt0Pr => e e0.
pose c : R := ln k.+1%:R.
have c0 : 0 <= c by rewrite /c ln_ge0// ler1n.
pose b := (c + 1) / e.
have b0 : 0 < b by rewrite divr_gt0// ltr_wpDl.
have cb : c / b <= e.
  rewrite /b invf_div mulrA ler_pdivrMr ?ltr_wpDl// mulrC ler_wpM2l ?ltW//.
  by rewrite ltrDl.
pose C : R := 1 + c / b + 2 * b.
have cb0 : 0 <= c / b by rewrite divr_ge0// ltW.
have C1 : 1 <= C by rewrite /C; have := ltW b0; lra.
(* Compare the smooth maxima lse b (x *m A) and lse b (y *m B). *)
have h2 : (\int[gauss n]_x (lse b (x *m A))%:E <=
           \int[gauss m]_y (lse b (y *m B))%:E)%E.
  apply: (@gauss_comparison R k.+1 (lse b) _ _ _ C 1).
  - by move=> z; exact: lse_differentiable.
  - by move=> j z; rewrite lse_DE//; exact: softmax_differentiable.
  - by move=> j l; rewrite lse_D2E//; exact: continuous_lse_D2.
  - move=> z; rewrite (le_trans (lse_norm _ b0))// expr1.
    by have := normr_ge0 z; have := ltW b0; rewrite /C -/c; nra.
  - move=> j z; have h := is_derive_lse b0 z j.
    rewrite derive_val ger0_norm ?softmax_ge0//.
    rewrite (le_trans (softmax_le1 _ _ _))// -[1]mulr1 ler_pM ?ler01//.
    by rewrite mul1r lerDl expr1.
  - move=> j l z.
    have -> : 'D_(delta_mx 0 l) ('D_(delta_mx 0 j) (lse b)) z = lse_D2 b j l z.
      exact: (congr1 (fun f => f z) (lse_D2E b0 j l)).
    rewrite /lse_D2 normrM (ger0_norm (ltW b0)).
    set pj := softmax b z j; set pl := softmax b z l.
    have p1 : 0 <= pj := softmax_ge0 b z j.
    have p2 : 0 <= pl := softmax_ge0 b z l.
    have q1 : pj <= 1 := softmax_le1 b z j.
    have q2 : pl <= 1 := softmax_le1 b z l.
    have e1 : `|pj * (j == l)%:R - pj * pl| <= 2.
      clearbody pj pl; rewrite (le_trans (ler_normB _ _))//.
      rewrite !normrM normr_nat (ger0_norm p1) (ger0_norm p2).
      by case: (j == l) => /=; nra.
    by have := normr_ge0 z; have := ltW b0; rewrite /C -/c; nra.
  - move=> z.
    have -> : \sum_j \sum_l (A^T *m A - B^T *m B) j l *
        'D_(delta_mx 0 l) ('D_(delta_mx 0 j) (lse b)) z =
        \sum_j \sum_l (A^T *m A - B^T *m B) j l * lse_D2 b j l z.
      apply: eq_bigr => j _; apply: eq_bigr => l _.
      by rewrite (congr1 (fun f => f z) (lse_D2E b0 j l)).
    rewrite lse_hessian.
    have b20 : 0 <= b / 2 by rewrite divr_ge0// ltW.
    apply: mulr_ge0_le0 => //.
    rewrite sumr_le0// => j _; rewrite sumr_le0// => l _.
    apply: mulr_ge0_le0; first by rewrite mulr_ge0 ?softmax_ge0.
    by have := AB j l; rewrite /incr_var !mxE; lra.
(* rmax <= lse b <= rmax + c / b, and c / b <= e. *)
have iLA := integrable_gauss_lse A b0; have iLB := integrable_gauss_lse B b0.
have h1 : \int[gauss n]_x rmax (x *m A) <= \int[gauss n]_x lse b (x *m A).
  by apply: le_Rintegral => // x _; exact: rmax_le_lse.
have h2' : \int[gauss n]_x lse b (x *m A) <= \int[gauss m]_y lse b (y *m B).
  apply: fine_le; [exact: integrable_fin_num|exact: integrable_fin_num|].
  exact: h2.
have iC : (gauss m).-integrable setT (EFin \o cst (c / b)).
  exact: finite_measure_integrable_cst.
have iD : (gauss m).-integrable setT
    (EFin \o (fun y => rmax (y *m B) + c / b)).
  rewrite (_ : EFin \o _ =
    (EFin \o (fun y => rmax (y *m B))) \+ (EFin \o cst (c / b)))//.
  exact: integrableD.
have h3 : \int[gauss m]_y lse b (y *m B) <=
          \int[gauss m]_y (rmax (y *m B) + c / b).
  by apply: le_Rintegral => // y _; exact: lse_le_rmax.
rewrite RintegralD// Rintegral_cst// [X in fine X]probability_setT mulr1 in h3.
apply: (le_trans h1); apply: (le_trans h2'); apply: (le_trans h3).
by apply: lerD; [exact: lexx|exact: cb].
Qed.

(* Slepian's inequality for expected maxima: equal variances and larger
   covariances give a smaller expected maximum. *)
Corollary slepian n m k (A : 'M[R]_(n, k.+1)) (B : 'M[R]_(m, k.+1)) :
  (forall j, (A^T *m A) j j = (B^T *m B) j j) ->
  (forall j l, (B^T *m B) j l <= (A^T *m A) j l) ->
  (\int[gauss n]_x (rmax (x *m A))%:E <= \int[gauss m]_y (rmax (y *m B))%:E)%E.
Proof.
move=> var_eq cov_le; apply: sudakov_fernique => j l.
by rewrite /incr_var !var_eq; have := cov_le j l; lra.
Qed.

End sudakov_fernique.
