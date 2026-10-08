(* The well-conditioned exact fit of the Gaussian model below the threshold:
   Lemma 5.17 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372, lines 6111-6190 of
   arxiv_v1.tex), which is Proposition 1.4 (i). Item G9 of stage 2 of
   phase 5 (lane B), at Stdlib's R.

   Main result. gaussian_fit_below_threshold: let 1 < kappa and
   0 < alpha < alpha*(kappa). There are 0 < m <= M such that for every
   sequence n of density alpha (universality_density_tends_to), every
   eps > 0 and every large d, some measurable set E of samples has
   probability at most eps under tuple_prod of gaussian_feature_law kappa d,
   and for every sample Z outside E some symmetric S has
   m |v|^2 <= v S v^T <= M |v|^2, tr S = d and <Z_i, mxvec S> = 0 for
   every i. So all the values <Z_i, S> are equal (to 0), which is the fit
   A_{G,kappa} S = 0 of the Gaussian model, with intercept 0. This is the
   form in which the approximate fit of the satisfiable phase (S1) uses the
   lemma.

   Route. The paper shows that Phi = inf_K |A T_kappa S| tends to 0 in
   probability, for an i.i.d. Gaussian matrix A and K the slice of the
   matrices with m I <= S <= M I and tr S = d; that alone does not give an
   exact fit. Here the approximate fit is corrected.
   1. The model. For S symmetric, <Z(a), mxvec S> is
      <a, mxvec (sqrt (2/d) T_kappa S)> (gaussian_feature_vec_dot of
      Gaussian/Representation): feature_rows. The features of n
      independent Gaussian rows have the law of the sample
      (tuple_prod_map), and the rows form a Gaussian matrix
      (gauss_tuple_mx).
   2. The approximate fit. The auxiliary value of the CGMT (cgmt_aux of
      library/comparison/cgmt.v) for cone_rows, the set of the
      mxvec (T_kappa S) with S in the slice fit_slice, vanishes with
      probability more than 1/2 for every large d (aux_zero_eventually).
      The witness is wit_mx: psd_part (W - w I) + c I for the GOE matrix W
      of the auxiliary vector h, normalized to trace d, with w and c chosen
      from alpha < alpha*(kappa) (witness_scalar, from the semicircle
      integrals of Gaussian/Threshold); its spectral statistics come from
      Wigner's law (wigner), the diagonal of W and |g|^2 from chi-square
      tails, the diagonal of the witness from Lemma 5.13
      (goe_diag_var_tail), and the inequality |g| |x| <= <h, x> from
      witness_numeric. Then cgmt_zero_tail bounds Phi by
      C sqrt (d ln (4 / eps)) (approx_tail).
   3. The margin. The map l |-> goe_part (vec_mx (l A)) has smallest
      singular value sym_margin at least c d with probability at least
      1 - exp (- c^2 d^2 / 2) (margin_tail, from gauss_proj_singular_tail
      for the projection sym_proj on the symmetric matrices, whose trace
      is d (d + 1) / 2, and gauss_trmx); c > 0 because
      alpha*(kappa) < 1/2. For the features, sym_margin_feature and
      approx_feature carry both bounds over with a factor sqrt (2/d).
   4. The correction (subcritical_correction, deterministic, used at
      kappa = 3 for the matrix of the features in exact_fit_of_margin).
      Given an approximate fit S_0 in the slice and the margin, the range
      duality (range_duality_sym of library/matrix/nuclear.v) gives D
      symmetric with A mxvec D = - A mxvec (T_kappa S_0) and opnorm D
      small; then S_0 + T_kappa^-1 D, rescaled to trace d, is an exact fit
      in a slightly larger slice.

   Other results.
   - sym_proj, mul_sym_proj, sym_proj_sym, sym_proj_idem, sym_proj_trace:
     the orthogonal projection of 'rV_(d * d) on the symmetric matrices in
     mxvec coordinates, v sym_proj = mxvec ((V + V^T) / 2) for
     V = vec_mx v, of trace d (d + 1) / 2;
   - opnorm_diag_part, opnorm_cone_map: the operator norm of the diagonal
     part, and of T_kappa D, at most (1 + |sqrt ((kappa - 1)/2) - 1|)
     opnorm D;
   - cone_rows_closed, cone_rows_convex, cone_rows_bounded: T_kappa of the
     slice is a compact convex set of radius cone_slice_radius;
   - mxdot_cmap, mxdot_cone_map_sqr: <W, T_kappa X> and |T_kappa X|^2 in
     terms of the diagonal of X. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval archimedean.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import measure lebesgue_measure probability.
From mathcomp Require Import measurable_realfun numfun.
From mathcomp Require Import ereal lebesgue_integral derive realfun ftc.
From mathcomp Require Import sequences exp trigo.
From GaussianAnalysis Require Import semicircle_law variational.
From GaussianAnalysis Require Import measurable_matrix euclidean real_spectral.
From GaussianAnalysis Require Import opnorm nuclear psd_part von_neumann.
From GaussianAnalysis Require Import gauss nets escape cgmt gauss_matrix_law.
From GaussianAnalysis Require Import lindeberg tuple_rows.
From GaussianAnalysis Require Import goe wigner goe_rotation.
From GaussianAnalysis Require Import chi_square feature_moments logdet_barrier.
From GaussianAnalysis Require Import gauss_smoothing.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.Gaussian Require Import Representation.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

Section sym_proj.
Variable d : nat.

(* The orthogonal projection on the symmetric matrices, acting on the
   mxvec coordinates. *)
Definition sym_proj : 'M[R]_(d * d) :=
  (2%:R)^-1 *: (1%:M + lin_mx (@trmx R d d)).

Lemma mul_sym_proj (v : 'rV[R]_(d * d)) :
  v *m sym_proj = mxvec (goe_part (vec_mx v)).
Proof.
rewrite /sym_proj -scalemxAr mulmxDr mulmx1 mul_rV_lin /goe_part.
apply/rowP => k; case/mxvec_indexP: k => i j.
by rewrite !mxE !mxvecE !mxE.
Qed.

Lemma lin_trmx_sym : (lin_mx (@trmx R d d))^T = lin_mx (@trmx R d d).
Proof.
apply/matrixP => p q; rewrite mxE /lin_mx !mxE /=.
case/mxvec_indexP: p => i j; case/mxvec_indexP: q => k l.
rewrite !vec_mx_delta !mxvecE !mxE.
by rewrite andbC [i == l]eq_sym [j == k]eq_sym.
Qed.

Lemma sym_proj_sym : sym_proj^T = sym_proj.
Proof. by rewrite /sym_proj linearZ /= linearD /= trmx1 lin_trmx_sym. Qed.

Lemma goe_part_idem (A : 'M[R]_d) : goe_part (goe_part A) = goe_part A.
Proof.
apply/matrixP => i j; rewrite /goe_part !mxE.
by field.
Qed.

Lemma sym_proj_idem : sym_proj *m sym_proj = sym_proj.
Proof.
apply/row_matrixP => p; rewrite !rowE mulmxA !mul_sym_proj mxvecK.
by rewrite goe_part_idem.
Qed.

Lemma sym_proj_trace : \tr sym_proj = (d * d.+1)%:R / 2%:R.
Proof.
rewrite /sym_proj mxtraceZ mxtraceD mxtrace1.
have -> : \tr (lin_mx (@trmx R d d)) = d%:R.
  rewrite /mxtrace (reindex _ (curry_mxvec_bij d d)) /=.
  have e (p : 'I_d * 'I_d) :
      lin_mx (@trmx R d d) (uncurry (@mxvec_index d d) p)
        (uncurry (@mxvec_index d d) p) = (p.1 == p.2)%:R.
    case: p => i j /=; rewrite /lin_mx !mxE /= vec_mx_delta mxvecE !mxE.
    by rewrite [j == i]eq_sym andbb.
  under eq_bigr => p _ do rewrite e.
  rewrite -(pair_bigA _ (fun i j : 'I_d => ((i == j)%:R : R))) /=.
  have inner (i : 'I_d) : \sum_(j < d) ((i == j)%:R : R) = 1.
    rewrite (bigD1 i) //= eqxx.
    have -> : \sum_(j < d | j != i) ((i == j)%:R : R) = 0.
      by apply: big1 => j /negPf ji; rewrite eq_sym ji.
    by rewrite addr0.
  under eq_bigr => i _ do rewrite inner.
  by rewrite sumr_const card_ord.
by rewrite mulrC -natrD -mulnSr mulnC.
Qed.

End sym_proj.

Section correction.

Lemma diag_part_mul d (D : 'M[R]_d) (x : 'cV[R]_d) i :
  (diag_part D *m x) i 0 = D i i * x i 0.
Proof.
rewrite mxE (bigD1 i) //= /diag_part mxE eqxx.
have -> : \sum_(j < d | j != i) (\matrix_(i0, j0)
    (if i0 == j0 then D i0 j0 else 0)) i j * x j 0 = 0.
  by apply: big1 => j ji; rewrite mxE eq_sym (negPf ji) mul0r.
by rewrite addr0.
Qed.

Lemma opnorm_diag_part d (D : 'M[R]_d) : opnorm (diag_part D) <= opnorm D.
Proof.
apply: opnorm_le => x x1.
have hD i : `|D i i| <= opnorm D :=
  le_trans (mx_norm_entry_le D i i) (mx_norm_le_opnorm D).
have o0 := opnorm_ge0 D.
have hs : mxdot (diag_part D *m x) (diag_part D *m x) <=
    opnorm D ^+ 2 * mxdot x x.
  rewrite /mxdot mulr_sumr; apply: ler_sum => i _.
  rewrite !big_ord1 diag_part_mul.
  have : D i i ^+ 2 <= opnorm D ^+ 2.
    by rewrite -real_normK ?num_real // lerXn2r ?nnegrE ?normr_ge0.
  by have := sqr_ge0 (x i 0); nra.
have hx : mxdot x x <= 1.
  by rewrite -frobenius_sqr; have := frobenius_ge0 x; nra.
rewrite /frobenius -(ger0_norm o0) -sqrtr_sqr; apply: ler_wsqrtr.
apply: le_trans hs _; have := sqr_ge0 (opnorm D); nra.
Qed.

(* The operator norm of T_kappa D. *)
Lemma opnorm_cone_map d (kappa : R) (D : 'M[R]_d) :
  opnorm (cone_map kappa D) <=
  (1 + `|Num.sqrt ((kappa - 1) / 2%:R) - 1|) * opnorm D.
Proof.
have -> : cone_map kappa D =
    D + (Num.sqrt ((kappa - 1) / 2%:R) - 1) *: diag_part D.
  by apply/matrixP => i j; rewrite /cone_map !mxE; ring.
apply: le_trans (opnormD _ _) _; rewrite opnormZ.
have := @opnorm_diag_part d D; have := opnorm_ge0 (diag_part D).
by have := normr_ge0 (Num.sqrt ((kappa - 1) / 2%:R) - 1); nra.
Qed.

Lemma symmetric_paper d (S : 'M[R]_d) :
  S \is symmetricmx -> paper_main_symmetric S.
Proof. by move=> /symmetricmxP Ss i j; rewrite -[in LHS]Ss mxE. Qed.

Lemma paper_symmetric d (S : 'M[R]_d) :
  paper_main_symmetric S -> S \is symmetricmx.
Proof. by move=> Ss; apply/symmetricmxP/matrixP => i j; rewrite mxE Ss. Qed.

Lemma goe_part_symmetric d (A : 'M[R]_d) : goe_part A \is symmetricmx.
Proof.
by apply/symmetricmxP; rewrite /goe_part linearZ /= linearD /= trmxK addrC.
Qed.

Lemma mxdot_goe_part_symr d (A D : 'M[R]_d) : D \is symmetricmx ->
  mxdot (goe_part A) D = mxdot A D.
Proof.
move=> /symmetricmxP Ds; rewrite /goe_part mxdotZl mxdotDl.
rewrite -[X in mxdot _^T X]Ds mxdot_trmx.
by field.
Qed.

Lemma tr_le_opnorm d (D : 'M[R]_d) : `|\tr D| <= d%:R * opnorm D.
Proof.
rewrite /mxtrace (le_trans (ler_norm_sum _ _ _)) //.
apply: le_trans (_ : \sum_(i < d) opnorm D <= _).
  apply: ler_sum => i _.
  exact: le_trans (mx_norm_entry_le D i i) (mx_norm_le_opnorm D).
by rewrite sumr_const card_ord mulr_natl.
Qed.

(* Step 4: an approximate fit S0 in the slice m I <= S <= M I, tr S = d,
   and a margin sig of the map S |-> A mxvec S on the symmetric matrices
   give an exact fit in a slightly larger slice, when the residual is at
   most sig min (m / 2, 1 / 2) / cK, cK bounding the operator norm of
   T_kappa^-1. *)
Theorem subcritical_correction (kappa : R) n d (A : 'M[R]_(n, d * d))
    (S0 : 'M[R]_d) (m M sig : R) :
  1 < kappa -> (0 < d)%N -> 0 < m -> 0 < sig -> S0 \is symmetricmx ->
  (forall v : 'cV[R]_d, m * mxdot v v <= mxdot v (S0 *m v)) ->
  (forall v : 'cV[R]_d, mxdot v (S0 *m v) <= M * mxdot v v) ->
  \tr S0 = d%:R ->
  (forall l : 'rV[R]_n,
     sig * frobenius l <= frobenius (goe_part (vec_mx (l *m A)))) ->
  (1 + `|Num.sqrt ((kappa_dual kappa - 1) / 2%:R) - 1|) *
    frobenius (A *m (mxvec (cone_map kappa S0))^T) <=
    sig * Num.min (m / 2%:R) (2%:R^-1) ->
  exists2 S : 'M[R]_d, S \is symmetricmx &
    [/\ forall v : 'cV[R]_d, m / 3%:R * mxdot v v <= mxdot v (S *m v),
        forall v : 'cV[R]_d, mxdot v (S *m v) <= (2%:R * M + m) * mxdot v v,
        \tr S = d%:R &
        A *m (mxvec (cone_map kappa S))^T = 0].
Proof.
move=> k1 d0 m0 sig0 S0s hm hM tr0 hsig hsmall.
set r := A *m (mxvec (cone_map kappa S0))^T.
set cK := 1 + `|Num.sqrt ((kappa_dual kappa - 1) / 2%:R) - 1|.
have cK1 : 1 <= cK by rewrite /cK lerDl.
pose W (i : 'I_n) : 'M[R]_d := goe_part (vec_mx (row i A)).
have Ws i : W i \is symmetricmx := goe_part_symmetric _ _.
have adjE (l : 'rV[R]_n) : coef_adj W l = goe_part (vec_mx (l *m A)).
  apply/matrixP => i j; rewrite /coef_adj /W summxE /goe_part !mxE.
  under eq_bigr do rewrite !mxE.
  rewrite -big_split mulr_sumr /=; apply: eq_bigr => k _; ring.
pose y : 'rV[R]_n := - r^T.
have yr : frobenius y = frobenius r by rewrite /y frobeniusN frobenius_trmx.
have hdual (l : 'rV[R]_n) :
    `|mxdot l y| <= frobenius y / sig * nuclear (coef_adj W l).
  apply: le_trans (mxdot_le _ _) _; rewrite mulrC -mulrA ler_wpM2l //.
    exact: frobenius_ge0.
  rewrite ler_pdivlMl // adjE; apply: le_trans (hsig l) _.
  exact: frobenius_le_nuclear.
have y0 : 0 <= frobenius y / sig.
  by apply: divr_ge0; [exact: frobenius_ge0 | exact: ltW].
have [D Ds [hD hDy]] := range_duality_sym y0 Ws hdual.
(* A mxvec D = - r *)
have hAD : A *m (mxvec D)^T = - r.
  apply/colP => i.
  have e1 : mxdot (W i) D = - r i 0.
    have := congr1 (fun v : 'rV[R]_n => v 0 i) hDy.
    by rewrite /coef_map /y !mxE.
  rewrite [in RHS]mxE -e1 /W mxdot_goe_part_symr //.
  rewrite mxdotC mxdot_vec_mxr mxdotC /mxdot big_ord1 mxE.
  by apply: eq_bigr => k _; rewrite !mxE.
pose Del := cone_map (kappa_dual kappa) D.
have cDel : cone_map kappa Del = D by rewrite /Del cone_mapVK.
have Dels : Del \is symmetricmx.
  by apply: paper_symmetric; apply: cone_map_sym; exact: symmetric_paper.
have cK0 : 0 <= cK by apply: le_trans cK1.
have oDel : opnorm Del <= Num.min (m / 2%:R) (2%:R^-1).
  apply: le_trans (opnorm_cone_map _ _ _) _; rewrite -/cK.
  apply: le_trans (ler_wpM2l cK0 hD) _; rewrite yr mulrA ler_pdivrMr //.
  by rewrite [X in _ <= X]mulrC; exact: hsmall.
have oDm : opnorm Del <= m / 2%:R.
  by apply: le_trans oDel _; rewrite ge_min lexx.
have oD2 : opnorm Del <= 2%:R^-1.
  by apply: le_trans oDel _; rewrite ge_min lexx orbT.
have qDel (v : 'cV[R]_d) : `|mxdot v (Del *m v)| <= opnorm Del * mxdot v v.
  apply: le_trans (mxdot_opnorm _ _ _) _.
  by rewrite -mulrA -expr2 frobenius_sqr.
pose S1 := S0 + Del.
have S1s : S1 \is symmetricmx.
  have /symmetricmxP S0t := S0s; have /symmetricmxP Dt := Dels.
  by apply/symmetricmxP; rewrite /S1 linearD /= S0t Dt.
have fit1 : A *m (mxvec (cone_map kappa S1))^T = 0.
  by rewrite /S1 cone_mapD cDel linearD /= linearD /= mulmxDr hAD -/r subrr.
have lo1 (v : 'cV[R]_d) : m / 2%:R * mxdot v v <= mxdot v (S1 *m v).
  rewrite /S1 mulmxDl mxdotDr; have := hm v; have := qDel v.
  rewrite ler_norml => /andP [h1 _] h2.
  have := mxdot_ge0 v; have := opnorm_ge0 Del; nra.
have up1 (v : 'cV[R]_d) : mxdot v (S1 *m v) <= (M + m / 2%:R) * mxdot v v.
  rewrite /S1 mulmxDl mxdotDr; have := hM v; have := qDel v.
  rewrite ler_norml => /andP [_ h1] h2.
  have := mxdot_ge0 v; have := opnorm_ge0 Del; nra.
have trD : `|\tr Del| <= d%:R / 2%:R.
  have := tr_le_opnorm _ Del; have := ler0n R d; nra.
have tr1 : \tr S1 = d%:R + \tr Del by rewrite /S1 mxtraceD tr0.
have dpos : 0 < d%:R :> R by rewrite ltr0n.
have trS1 : d%:R / 2%:R <= \tr S1 <= 3%:R * d%:R / 2%:R.
  by move: trD; rewrite tr1 ler_norml => /andP [h1 h2]; apply/andP; split; lra.
pose c := d%:R / \tr S1.
have tS1 : 0 < \tr S1 by move: trS1 => /andP [h _]; apply: lt_le_trans h; lra.
have c23 : 2%:R / 3%:R <= c <= 2%:R.
  have e : c * \tr S1 = d%:R by rewrite /c mulfVK // gt_eqF.
  by move: trS1 => /andP [h1 h2]; apply/andP; split; nra.
exists (c *: S1).
  have /symmetricmxP S1t := S1s.
  by apply/symmetricmxP; rewrite linearZ /= S1t.
have q0 (v : 'cV[R]_d) : 0 <= mxdot v (S1 *m v).
  apply: le_trans (lo1 v); apply: mulr_ge0; last exact: mxdot_ge0.
  by have := m0; lra.
split.
- move=> v; rewrite -scalemxAl mxdotZr; have := lo1 v; have := mxdot_ge0 v.
  by have := q0 v; move: c23 => /andP [h1 h2]; nra.
- move=> v; rewrite -scalemxAl mxdotZr; have := up1 v; have := mxdot_ge0 v.
  by have := q0 v; move: c23 => /andP [h1 h2]; nra.
- by rewrite mxtraceZ /c mulfVK // gt_eqF.
- by rewrite cone_mapZ linearZ /= linearZ /= -scalemxAr fit1 scaler0.
Qed.

End correction.

Section semicircle_scale.
Context {RT : realType}.
Local Notation mu := (@lebesgue_measure RT).

(* The semicircle law of radius 2 is the image of that of radius sqrt 2
   under y |-> sqrt 2 y: Wigner's law (radius 2) and the threshold law
   (radius sqrt 2) are related by this change of variables. *)
Lemma semicircle_scale (f : RT -> RT) : continuous f ->
  \int[semicircle_prob (2%:R : RT)]_x f x =
  \int[semicircle_prob (Num.sqrt 2%:R : RT)]_y f (Num.sqrt 2%:R * y).
Proof.
move=> cf.
set s := Num.sqrt (2%:R : RT).
have s0 : 0 < s by rewrite sqrtr_gt0.
have ss : s * s = 2%:R by rewrite -expr2 sqr_sqrtr.
have r20 : (2%:R : RT) != 0 by rewrite pnatr_eq0.
have rs0 : s != 0 by rewrite gt_eqF.
have cfs : continuous (fun y => f (s * y)).
  move=> y; apply: continuous_comp; last exact: cf.
  by apply: continuousM; [exact: cvg_cst | exact: cvg_id].
rewrite (Rintegral_semicircle r20 (integrable_semicircle_continuous r20 cf)).
rewrite (Rintegral_semicircle rs0 (integrable_semicircle_continuous rs0 cfs)).
rewrite (ger0_norm (ler0n _ 2)) (ger0_norm (ltW s0)).
pose F (y : RT) := s * y.
pose G (x : RT) := f x * semicircle_pdf 2%:R x.
have dF (y : RT) : is_derive y 1 F s.
  apply: (is_derive_eq (is_deriveZ s (is_derive_id y 1))).
  by rewrite /GRing.scale /= mulr1.
have F'E : F^`() = (fun _ => s).
  by apply/funext => y; rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF y)).
have cF : continuous F.
  move=> y; apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (dF y)).
have cG : continuous G.
  rewrite /G => x; apply: (@continuousM _ _ f (semicircle_pdf 2%:R) x).
    exact: cf.
  exact: continuous_semicircle_pdf.
have := @integration_by_substitution_increasing RT F G (- s) s.
rewrite F'E.
have -> : F (- s) = - 2%:R by rewrite /F mulrN ss.
have -> : F s = 2%:R by rewrite /F ss.
move=> /(_ _ _ _ _ _ _ _) h.
have ab : - s <= s by have := s0; lra.
have incr : {in `[- s, s]%R &, {homo F : x y / x < y}}.
  by move=> x y _ _ xy; rewrite /F ltr_pM2l.
have cvgl : cvg ((fun _ : RT => s) x @[x --> (- s)^'+]) by exact: is_cvg_cst.
have cvgr : cvg ((fun _ : RT => s) x @[x --> s^'-]) by exact: is_cvg_cst.
have dLR : derivable_oo_LRcontinuous F (- s) s.
  split.
  - by move=> x _; exact: (@ex_derive _ _ _ _ _ _ _ (dF x)).
  - by apply: cvg_at_right_filter; exact: cF.
  - by apply: cvg_at_left_filter; exact: cF.
have := h ab incr (fun x _ => cvg_cst s) cvgl cvgr dLR
  (continuous_subspaceT cG).
move=> E; rewrite /Rintegral.
rewrite [X in fine X](_ : _ =
  (\int[mu]_(x in `[(- 2%:R)%R, 2%:R]) (G x)%:E)%E) //.
rewrite E; congr fine; apply: eq_integral => y yI.
rewrite /= /G /F !fctE; congr EFin.
rewrite !semicircle_pdfE //.
have s2 : s ^+ 2 = 2%:R by rewrite sqr_sqrtr.
have e2 : 2%:R ^+ 2 - (s * y) ^+ 2 = 2%:R * (2%:R - y ^+ 2) :> RT.
  by rewrite exprMn s2; ring.
rewrite e2 sqrtrM ?ler0n // -/s s2.
set t := Num.sqrt (2%:R - y ^+ 2).
have pi0 : pi != 0 :> RT by rewrite gt_eqF // pi_gt0.
have -> : f (s * y) * (2%:R / (pi * 2%:R ^+ 2) * (s * t)) * s =
    f (s * y) * (2%:R / (pi * 2%:R ^+ 2) * t) * (s * s) by ring.
rewrite ss; have two0 : (2%:R : RT) != 0 by rewrite pnatr_eq0.
have p2 : pi * 2%:R != 0 :> RT by rewrite mulf_neq0.
have p4 : pi * 2%:R ^+ 2 != 0 :> RT by rewrite mulf_neq0 // expf_neq0.
have key (p u : RT) : p != 0 ->
    2%:R / (p * 2%:R ^+ 2) * u * 2%:R = 2%:R / (p * 2%:R) * u.
  by move=> p0; field.
by rewrite -mulrA key.
Qed.

End semicircle_scale.

Section ppart.
Context {RT : realType}.

(* (x - w)_+, the positive part of the paper. *)
Definition ppart (w x : RT) : RT := Num.max (x - w) 0.

Lemma ppart_ge0 w x : 0 <= ppart w x.
Proof. by rewrite /ppart le_max lexx orbT. Qed.

Lemma ppart_scale (a w x : RT) : 0 < a ->
  ppart (a * w) (a * x) = a * ppart w x.
Proof.
move=> a0; rewrite /ppart -mulrBr.
have [h|h] := leP (x - w) 0.
  by rewrite !max_r ?mulr0 // pmulr_rle0.
by rewrite !max_l ?pmulr_rge0 // ltW.
Qed.

(* (x - w) (x - w)_+ = (x - w)_+^2. *)
Lemma ppart_sqr w x : (x - w) * ppart w x = ppart w x ^+ 2.
Proof.
rewrite /ppart expr2; have [h|h] := leP (x - w) 0; first by rewrite !mulr0.
by [].
Qed.

(* Continuity of pointwise operations. They are stated over a realType:
   at Stdlib's R, cvgD and cvgM do not find the normed structure of a
   function R -> R. *)
Lemma continuous_add (f g : RT -> RT) : continuous f -> continuous g ->
  continuous (fun y => f y + g y).
Proof. by move=> cf cg y; apply: cvgD; [exact: cf | exact: cg]. Qed.

Lemma continuous_mul (f g : RT -> RT) : continuous f -> continuous g ->
  continuous (fun y => f y * g y).
Proof. by move=> cf cg y; apply: cvgM; [exact: cf | exact: cg]. Qed.

Lemma continuous_cstf (k : RT) : continuous (fun _ : RT => k).
Proof. by move=> y; exact: cvg_cst. Qed.

Lemma continuous_idf : continuous (fun y : RT => y).
Proof. by move=> y; exact: cvg_id. Qed.

Lemma continuous_cstM (k : RT) (f : RT -> RT) : continuous f ->
  continuous (fun y => k * f y).
Proof. by move=> cf; apply: continuous_mul => //; exact: continuous_cstf. Qed.

Lemma continuous_sqr (f : RT -> RT) : continuous f ->
  continuous (fun y => f y ^+ 2).
Proof. by move=> cf; under eq_fun do rewrite expr2; exact: continuous_mul. Qed.

(* The last step of the scalar choice below. *)
Lemma margin_arith (A Y Z a : RT) : 0 < a -> a < A -> Y <= Z ->
  Z * (2%:R * a) <= A * (A - a) ->
  2%:R * a * (2%:R * (A + Y)) < (2%:R * A) ^+ 2.
Proof.
move=> a0 aA YZ hZ.
have A0 : 0 < A by lra.
have p1 : a * Y <= a * Z := ler_wpM2l (ltW a0) YZ.
have p2 : a * A < A * A by rewrite ltr_pM2r.
nra.
Qed.

End ppart.

Section witness_scalar.
Local Notation nu := threshold_law.
Local Notation sig2 := (@semicircle_prob R 2%:R).

Lemma continuous_ppart w : continuous (@ppart R w).
Proof.
move=> x; have := continuous_upper_part w 1 x.
by apply: cvg_trans; apply: near_eq_cvg; near=> y; rewrite expr1.
Unshelve. all: by end_near.
Qed.

Lemma nu_integrable (f : R -> R) : continuous f ->
  nu.-integrable [set: R] (EFin \o f).
Proof. exact: threshold_integrable_continuous. Qed.

Lemma nu_intD (f g : R -> R) : continuous f -> continuous g ->
  \int[nu]_x (f x + g x) = \int[nu]_x f x + \int[nu]_x g x.
Proof. by move=> cf cg; rewrite RintegralD // ?nu_integrable. Qed.

Lemma nu_intZ (a : R) (f : R -> R) : continuous f ->
  \int[nu]_x (a * f x) = a * \int[nu]_x f x.
Proof. by move=> cf; rewrite RintegralZl // nu_integrable. Qed.

Lemma nu_int_cst (c : R) : \int[nu]_x c = c.
Proof. exact: Rintegral_prob_cst. Qed.

(* The choice of the witness: w and c > 0 such that the profile
   x |-> (x - w)_+ + c, against the semicircle law of radius 2, satisfies
   2 alpha (int f^2 + c_kappa (int f)^2) < (int x f)^2. With
   f (sqrt 2 y) = sqrt 2 ((y - omega)_+ + l) for omega the cutoff of
   Gaussian/Threshold, the integrals are those of the paper's p + l,
   and the inequality reads alpha (s + 2 l m + l^2 + c_kappa (m + l)^2) <
   (s + omega m)^2 = alpha*^2; it holds for l small since
   s + c_kappa m^2 = alpha* and omega = c_kappa m. *)
Lemma witness_scalar (kappa alpha : R) : 1 < kappa -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists w c : R, [/\ 0 < c,
    0 < \int[sig2]_x (ppart w x + c),
    0 < \int[sig2]_x (x * (ppart w x + c)) &
    2%:R * alpha * (\int[sig2]_x ((ppart w x + c) ^+ 2) +
      cone_shift kappa * (\int[sig2]_x (ppart w x + c)) ^+ 2) <
    (\int[sig2]_x (x * (ppart w x + c))) ^+ 2].
Proof.
move=> k1 a0 aast.
set om := universality_cutoff kappa.
set m := universality_m om.
set sv := universality_s om.
set ast := universality_alpha_star kappa.
set ck := cone_shift kappa.
have [_ omE _] := universality_cutoff_spec _ k1.
rewrite -/om -/m in omE.
have astE : ast = sv + ck * m ^+ 2.
  by rewrite /ast /universality_alpha_star /universality_energy -/om -/m -/sv
    /ck cone_shiftE.
have cp := continuous_ppart om.
have cp2 : continuous (fun y => ppart om y ^+ 2) := continuous_upper_part om 2.
have mE : m = \int[nu]_y ppart om y.
  rewrite /m /universality_m threshold_integralE //.
  exact: nu_integrable cp.
have sE : sv = \int[nu]_y (ppart om y ^+ 2).
  rewrite /sv /universality_s threshold_integralE //.
  exact: nu_integrable cp2.
have m0 : 0 <= m.
  by rewrite mE; apply: Rintegral_ge0 => // y _; exact: ppart_ge0.
have ast0 : 0 < ast := universality_alpha_star_gt0 _ k1.
have aast' : alpha < ast by [].
have ck1 : 0 < 1 + ck by rewrite /ck cone_shiftD1; apply: divr_gt0 => //; lra.
have den0 : 0 < 2%:R * alpha * (1 + ck) * (2%:R * m + 1).
  by apply: mulr_gt0; [apply: mulr_gt0; [lra|exact: ck1]|lra].
pose l := Num.min 1 (ast * (ast - alpha) / (2%:R * alpha * (1 + ck) *
  (2%:R * m + 1))).
have l0 : 0 < l.
  rewrite /l lt_min ltr01 /=; apply: divr_gt0 => //.
  by apply: mulr_gt0 => //; lra.
have l1 : l <= 1 by rewrite /l ge_min lexx.
have lb : l * (1 + ck) * (2%:R * m + 1) <= ast * (ast - alpha) / (2%:R * alpha).
  have h : l <= ast * (ast - alpha) / (2%:R * alpha * (1 + ck) *
      (2%:R * m + 1)) by rewrite /l ge_min lexx orbT.
  move: h; rewrite ler_pdivlMr // => h.
  rewrite ler_pdivlMr; last lra.
  by move: h; rewrite !mulrA; lra.
set s2 := Num.sqrt (2%:R : R).
have s20 : 0 < s2 by rewrite sqrtr_gt0.
have s2s : s2 * s2 = 2%:R by rewrite -expr2 sqr_sqrtr.
have cpl : continuous (fun y => ppart om y + l).
  by move=> y; apply: cvgD; [exact: cp | exact: cvg_cst].
have cs2 : continuous (fun y : R => s2 * y).
  by move=> y; apply: cvgM; [exact: cvg_cst | exact: cvg_id].
have cf : continuous (fun x => ppart (s2 * om) x + s2 * l).
  move=> x; apply: cvgD; [exact: continuous_ppart | exact: cvg_cst].
exists (s2 * om), (s2 * l).
have I1 : \int[sig2]_x (ppart (s2 * om) x + s2 * l) = s2 * (m + l).
  rewrite semicircle_scale //.
  transitivity (\int[nu]_y (s2 * (ppart om y + l))).
    by apply: eq_Rintegral => y _; rewrite ppart_scale // mulrDr.
  by rewrite nu_intZ // nu_intD ?nu_int_cst -?mE // => y; exact: cvg_cst.
have cid : continuous (fun y : R => y) by exact: continuous_idf.
have c0 : continuous (fun y => 2%:R * ppart om y ^+ 2).
  by apply: continuous_cstM; exact: cp2.
have omE' : om = ck * m by rewrite omE /ck cone_shiftE.
have I2 : \int[sig2]_x ((ppart (s2 * om) x + s2 * l) ^+ 2) =
    2%:R * (sv + 2%:R * l * m + l ^+ 2).
  have cf2 : continuous (fun x => (ppart (s2 * om) x + s2 * l) ^+ 2).
    by apply: continuous_sqr; exact: cf.
  rewrite semicircle_scale //.
  transitivity (\int[nu]_y (2%:R * ppart om y ^+ 2 +
      ((4%:R * l) * ppart om y + 2%:R * l ^+ 2))).
    apply: eq_Rintegral => y _; rewrite ppart_scale // -mulrDr exprMn.
    by rewrite [s2 ^+ 2]expr2 s2s; ring.
  have c1 : continuous (fun y => 4%:R * l * ppart om y).
    by apply: continuous_cstM; exact: cp.
  have c2 : continuous (fun y => 4%:R * l * ppart om y + 2%:R * l ^+ 2).
    by apply: continuous_add => //; exact: continuous_cstf.
  have c3 : continuous (fun _ : R => 2%:R * l ^+ 2) by exact: continuous_cstf.
  rewrite nu_intD // nu_intD // nu_int_cst !nu_intZ // -mE -sE; ring.
have I3 : \int[sig2]_x (x * (ppart (s2 * om) x + s2 * l)) =
    2%:R * (sv + om * m).
  have cf3 : continuous (fun x : R => x * (ppart (s2 * om) x + s2 * l)).
    by apply: continuous_mul; [exact: continuous_idf | exact: cf].
  rewrite semicircle_scale //.
  transitivity (\int[nu]_y (2%:R * ppart om y ^+ 2 +
      (2%:R * om * ppart om y + (2%:R * l) * y))).
    apply: eq_Rintegral => y _; rewrite ppart_scale // -/s2 -mulrDr.
    rewrite mulrACA s2s.
    have e : y * ppart om y = ppart om y ^+ 2 + om * ppart om y.
      by rewrite -ppart_sqr; ring.
    by rewrite mulrDr e; ring.
  have c1 : continuous (fun y => 2%:R * om * ppart om y).
    by apply: continuous_cstM; exact: cp.
  have c2 : continuous (fun y : R => 2%:R * l * y).
    by apply: continuous_cstM; exact: continuous_idf.
  have c3 : continuous (fun y => 2%:R * om * ppart om y + 2%:R * l * y).
    exact: continuous_add.
  rewrite nu_intD // nu_intD // !nu_intZ // -mE -sE.
  have -> : \int[nu]_y (y : R) = 0.
    by apply: semicircle_moment1; exact: (lt0r_neq0 s20).
  by rewrite mulr0 addr0; ring.
have e3 : sv + om * m = ast by rewrite astE omE' expr2 mulrA.
have e1 : (s2 * (m + l)) ^+ 2 = 2%:R * (m + l) ^+ 2.
  by rewrite exprMn [s2 ^+ 2]expr2 s2s.
have e4 : 2%:R * (sv + 2%:R * l * m + l ^+ 2) + ck * (2%:R * (m + l) ^+ 2) =
    2%:R * (ast + l * (1 + ck) * (2%:R * m + l)) by rewrite astE; ring.
have h : 2%:R * m + l <= 2%:R * m + 1 by rewrite lerD2l.
have a2 : 0 < 2%:R * alpha := mulr_gt0 (ltr0Sn _ 1) a0.
have lb' := lb; rewrite ler_pdivlMr // in lb'.
rewrite I1 I2 I3 e3; split.
- exact: mulr_gt0.
- exact: mulr_gt0 s20 (ltr_wpDl m0 l0).
- exact: mulr_gt0 (ltr0Sn _ 1) ast0.
- rewrite e1 e4; apply: (@margin_arith _ ast _ _ alpha a0 aast' _ lb').
  exact: (ler_wpM2l (ltW (mulr_gt0 l0 ck1)) h).
Qed.

End witness_scalar.


Section mxvec_scale.
Context {RT : realType}.

Lemma mxvec_scale m k (c : RT) (A : 'M[RT]_(m, k)) :
  mxvec (c *: A) = c *: mxvec A.
Proof.
by apply/rowP => p; case/mxvec_indexP: p => i j; rewrite mxE !mxvecE mxE.
Qed.

End mxvec_scale.

Section feature_matrix.
Variables (kappa : R) (n d : nat).

Local Notation sk := (Num.sqrt ((kappa - 1) / 2%:R)).

(* The Gaussian features of the rows a_i. *)
Definition feature_tuple (a : n.-tuple 'rV[R]_(d * d)) :
    n.-tuple 'rV[R]_(d * d) :=
  tuple_map (fun=> gaussian_feature_vec kappa d) a.

Lemma row_tuple_mx m k (t : m.-tuple 'rV[R]_k) i :
  row i (tuple_mx t) = tnth t i.
Proof. by apply/rowP => j; rewrite !mxE. Qed.

Lemma mulmx_trE m k (Z : 'M[R]_(m, k)) (v : 'rV[R]_k) i :
  (Z *m v^T) i 0 = mxdot (row i Z) v.
Proof. by rewrite mxdot_rowE -row_mul [RHS]mxE. Qed.

Lemma tuple_mx_feature (a : n.-tuple 'rV[R]_(d * d)) :
  tuple_mx (feature_tuple a) = tuple_mx a *m gaussian_feature_mx kappa d.
Proof.
apply/row_matrixP => i; rewrite row_mul !row_tuple_mx.
by rewrite /feature_tuple /tuple_map tnth_mktuple.
Qed.


(* <Z_i, mxvec S> = sqrt (2 / d) <a_i, mxvec (T_kappa S)>. *)
Lemma feature_rows (a : n.-tuple 'rV[R]_(d * d)) (S : 'M[R]_d) :
  S \is symmetricmx ->
  tuple_mx (feature_tuple a) *m (mxvec S)^T =
  Num.sqrt (2%:R / d%:R) *: (tuple_mx a *m (mxvec (cone_map kappa S))^T).
Proof.
move=> Ss; apply/matrixP => i j; rewrite ord1 [RHS]mxE !mulmx_trE.
rewrite !row_tuple_mx /feature_tuple /tuple_map tnth_mktuple.
rewrite (gaussian_feature_vec_dot _ _ _ _ (symmetric_paper _ _ Ss)).
by rewrite mxvec_scale mxdotZr.
Qed.

Lemma symmetric_scale (c : R) m (A : 'M[R]_m) :
  A \is symmetricmx -> c *: A \is symmetricmx.
Proof.
by move=> /symmetricmxP As; apply/symmetricmxP; rewrite linearZ /= As.
Qed.

Lemma goe_part_symK m (A : 'M[R]_m) : A \is symmetricmx -> goe_part A = A.
Proof.
move=> /symmetricmxP As; rewrite /goe_part As -mulr2n -scaler_nat scalerA.
by rewrite mulVf ?scale1r // pnatr_eq0.
Qed.

Lemma cone_map_symmetric m (A : 'M[R]_m) :
  A \is symmetricmx -> cone_map kappa A \is symmetricmx.
Proof.
by move=> As; apply: paper_symmetric; apply: cone_map_sym;
  exact: symmetric_paper As.
Qed.

(* The symmetric part of l Z is sqrt (2 / d) T_kappa of that of l A. *)
Lemma feature_goe_part (a : n.-tuple 'rV[R]_(d * d)) (l : 'rV[R]_n) :
  goe_part (vec_mx (l *m tuple_mx (feature_tuple a))) =
  Num.sqrt (2%:R / d%:R) *:
    cone_map kappa (goe_part (vec_mx (l *m tuple_mx a))).
Proof.
rewrite tuple_mx_feature mulmxA gaussian_feature_mxE mxvecK /gaussian_feature.
apply: goe_part_symK; apply: symmetric_scale; apply: cone_map_symmetric.
exact: goe_part_symmetric.
Qed.

Lemma frobenius_cone_map_lb (X : 'M[R]_d) :
  Num.min 1 sk * frobenius X <= frobenius (cone_map kappa X).
Proof.
set s := sk; have s0 : 0 <= s := sqrtr_ge0 _.
set mn := Num.min 1 s.
have mn0 : 0 <= mn by rewrite le_min ler01 s0.
have mn1 : mn <= 1 by rewrite ge_min lexx.
have mns : mn <= s by rewrite ge_min lexx orbT.
have h2 : mn ^+ 2 <= s ^+ 2 by rewrite !expr2; apply: ler_pM.
have h1 : mn ^+ 2 <= 1 by rewrite expr2 -[1]mulr1; apply: ler_pM.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?mulr_ge0 ?frobenius_ge0 //.
rewrite exprMn !frobenius_sqr /mxdot mulr_sumr; apply: ler_sum => i _.
rewrite mulr_sumr; apply: ler_sum => j _; rewrite !cone_mapE.
have x0 : 0 <= X i j * X i j by rewrite -expr2 sqr_ge0.
move: x0; case: eqP => [<-|_] x0.
  have -> : s * X i i * (s * X i i) = s ^+ 2 * (X i i * X i i) by ring.
  exact: (ler_wpM2r x0 h2).
exact: (ler_piMl x0 h1).
Qed.

Lemma frobenius_cone_map_ub (X : 'M[R]_d) :
  frobenius (cone_map kappa X) <= Num.max 1 sk * frobenius X.
Proof.
set s := sk; have s0 : 0 <= s := sqrtr_ge0 _.
set mx := Num.max 1 s.
have mx0 : 0 <= mx by rewrite le_max ler01.
have mx1 : 1 <= mx by rewrite le_max lexx.
have mxs : s <= mx by rewrite le_max lexx orbT.
have h2 : s ^+ 2 <= mx ^+ 2 by rewrite !expr2; apply: ler_pM.
have h1 : 1 <= mx ^+ 2 by rewrite expr2 -[1]mulr1; apply: ler_pM.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?mulr_ge0 ?frobenius_ge0 //.
rewrite exprMn !frobenius_sqr /mxdot mulr_sumr; apply: ler_sum => i _.
rewrite mulr_sumr; apply: ler_sum => j _; rewrite !cone_mapE.
have x0 : 0 <= X i j * X i j by rewrite -expr2 sqr_ge0.
move: x0; case: eqP => [<-|_] x0.
  have -> : s * X i i * (s * X i i) = s ^+ 2 * (X i i * X i i) by ring.
  exact: (ler_wpM2r x0 h2).
exact: (ler_peMl x0 h1).
Qed.

End feature_matrix.

Arguments feature_tuple kappa {n d}.

Section continuity_helpers.
Context {RT : realType} {T : topologicalType}.

Lemma continuous_scale_fun (c : RT) (f : T -> RT) : continuous f ->
  continuous (fun x => c * f x).
Proof. by move=> cf x; apply: cvgM; [exact: cvg_cst | exact: cf]. Qed.

End continuity_helpers.

Section slice.
Variable d : nat.

(* The slice of the paper: the symmetric S with m I <= S <= M I and
   tr S = d, the quadratic forms written mxdot v (S *m v). *)
Definition fit_slice (m M : R) : set 'M[R]_d :=
  [set S | [/\ S \is symmetricmx,
     forall v : 'cV[R]_d, m * mxdot v v <= mxdot v (S *m v),
     forall v : 'cV[R]_d, mxdot v (S *m v) <= M * mxdot v v &
     \tr S = d%:R]].

(* T_kappa of the slice, in the mxvec coordinates. *)
Definition cone_rows (kappa m M : R) : set 'rV[R]_(d * d) :=
  [set mxvec (cone_map kappa S) | S in fit_slice m M].

Lemma fit_slice1 (m M : R) : m <= 1 -> 1 <= M -> fit_slice m M 1%:M.
Proof.
move=> m1 M1; split.
- by apply/symmetricmxP; rewrite trmx1.
- by move=> v; rewrite mul1mx; apply: ler_piMl => //; exact: mxdot_ge0.
- by move=> v; rewrite mul1mx; apply: ler_peMl => //; exact: mxdot_ge0.
- exact: mxtrace1.
Qed.

Lemma fit_slice_spec (m M : R) (S : 'M[R]_d) : fit_slice m M S ->
  forall i, m <= spec S 0 i <= M.
Proof.
move=> [Ss Sm SM _] i; have [P Po SE] := spec_decomposition Ss.
rewrite ((spectral_form_ge m Po SE).1 Sm i).
by rewrite ((spectral_form_le M Po SE).1 SM i).
Qed.

Lemma fit_slice_frobenius (m M : R) (S : 'M[R]_d) : 0 <= m ->
  fit_slice m M S -> frobenius S ^+ 2 <= M * d%:R.
Proof.
move=> m0 hS; have [Ss _ _ Str] := hS.
have [P Po SE] := spec_decomposition Ss.
rewrite frobenius_sqr (spectral_mxdot Po SE) -Str (spectral_trace Po SE).
rewrite mulr_sumr; apply: ler_sum => i _.
have /andP[h1 h2] := fit_slice_spec _ _ _ hS i.
by rewrite expr2; exact: (ler_wpM2r (le_trans m0 h1) h2).
Qed.

Lemma fit_slice_convex (m M : R) S1 S2 (t : R) :
  fit_slice m M S1 -> fit_slice m M S2 -> 0 <= t <= 1 ->
  fit_slice m M (S1 + t *: (S2 - S1)).
Proof.
move=> [s1 m1 M1 tr1] [s2 m2 M2 tr2] /andP[t0 t1]; split.
- have /symmetricmxP e1 := s1; have /symmetricmxP e2 := s2.
  by apply/symmetricmxP; rewrite linearD /= linearZ /= linearB /= e1 e2.
- move=> v; rewrite mulmxDl -scalemxAl mulmxBl mxdotDr mxdotZr mxdotBr.
  by have := m1 v; have := m2 v; nra.
- move=> v; rewrite mulmxDl -scalemxAl mulmxBl mxdotDr mxdotZr mxdotBr.
  by have := M1 v; have := M2 v; nra.
- by rewrite mxtraceD mxtraceZ linearB /= tr1 tr2 subrr mulr0 addr0.
Qed.

Lemma mxdot_quad_outer (Y : 'M[R]_d) (v : 'cV[R]_d) :
  mxdot Y (v *m v^T) = mxdot v (Y *m v).
Proof. by rewrite -mxdot_mulmxr mxdotC. Qed.

Lemma mxdot_one (Y : 'M[R]_d) : mxdot Y 1%:M = \tr Y.
Proof. by rewrite mxdot_trace trmx1 mulmx1. Qed.

Lemma fit_slice_closed (m M : R) : closed (fit_slice m M).
Proof.
pose hs (W : 'M[R]_d) c := [set Y : 'M[R]_d | c <= mxdot Y W].
have chs W c : closed (hs W c).
  exact: (continuous_closedP _).1 (continuous_pairing _ W) _ (@closed_ge _ c).
pose E (ij : 'I_d * 'I_d) : 'M[R]_d := delta_mx ij.1 ij.2 - delta_mx ij.2 ij.1.
have pE Y ij : mxdot Y (E ij) = Y ij.1 ij.2 - Y ij.2 ij.1.
  by rewrite mxdotBr !mxdot_delta.
have -> : fit_slice m M =
    (\bigcap_(ij in [set: 'I_d * 'I_d]) (hs (E ij) 0 `&` hs (- E ij) 0)) `&`
    (\bigcap_(v in [set: 'cV[R]_d])
       (hs (v *m v^T) (m * mxdot v v) `&`
        hs (- (v *m v^T)) (- (M * mxdot v v)))) `&`
    (hs 1%:M d%:R `&` hs (- 1%:M) (- d%:R)).
  apply/seteqP; split => Y.
    move=> [Ys Ym YM Ytr]; split; first split.
    - move=> ij _; rewrite /hs /= mxdotNr pE.
      have /symmetricmxP Ye := Ys.
      have := congr1 (fun A : 'M[R]_d => A ij.2 ij.1) Ye.
      by rewrite mxE => ->; rewrite subrr oppr0 lexx.
    - move=> v _; rewrite /hs /= mxdotNr mxdot_quad_outer lerN2; split => //.
    - by rewrite /hs /= mxdotNr mxdot_one Ytr lexx.
  move=> [[HE Hv] [Ht1 Ht2]]; split.
  - apply/symmetricmxP/matrixP => i j; rewrite mxE.
    have [h1 h2] := HE (j, i) I; move: h1 h2; rewrite /hs /= mxdotNr pE /=.
    rewrite oppr_ge0 subr_ge0 subr_le0 => h1 h2.
    by apply/eqP; rewrite eq_le h1 h2.
  - by move=> v; have [h _] := Hv v I; move: h; rewrite /hs /= mxdot_quad_outer.
  - move=> v; have [_ h] := Hv v I; move: h.
    rewrite /hs /= mxdotNr mxdot_quad_outer.
    by rewrite lerN2.
  - move: Ht1 Ht2; rewrite /hs /= mxdotNr mxdot_one lerN2 => h1 h2.
    by apply/eqP; rewrite eq_le h1 h2.
apply: closedI; first apply: closedI.
- by apply: closed_bigI => ij _; apply: closedI; exact: chs.
- by apply: closed_bigI => v _; apply: closedI; exact: chs.
- by apply: closedI; exact: chs.
Qed.

Lemma cone_rows_neq0 (kappa m M : R) : m <= 1 -> 1 <= M ->
  cone_rows kappa m M !=set0.
Proof.
move=> m1 M1; exists (mxvec (cone_map kappa 1%:M)), 1%:M => //.
exact: fit_slice1.
Qed.

Lemma cone_rows_bounded (kappa m M : R) : 0 <= m -> forall x,
  cone_rows kappa m M x ->
  frobenius x <=
    Num.max 1 (Num.sqrt ((kappa - 1) / 2%:R)) * Num.sqrt (M * d%:R).
Proof.
move=> m0 _ [S hS <-]; rewrite frobenius_mxvec.
apply: le_trans (frobenius_cone_map_ub _ _ _) _.
apply: ler_wpM2l; first by rewrite le_max ler01.
have -> : frobenius S = Num.sqrt (frobenius S ^+ 2).
  by rewrite sqrtr_sqr ger0_norm ?frobenius_ge0.
by apply: ler_wsqrtr; exact: fit_slice_frobenius _ _ _ m0 hS.
Qed.

Lemma cone_rows_convex (kappa m M : R) x y (t : R) :
  cone_rows kappa m M x -> cone_rows kappa m M y -> 0 <= t <= 1 ->
  cone_rows kappa m M (x + t *: (y - x)).
Proof.
move=> [S1 h1 <-] [S2 h2 <-] t01.
exists (S1 + t *: (S2 - S1)); first exact: fit_slice_convex.
apply/rowP => k; case/mxvec_indexP: k => i j.
rewrite !(mxE, mxvecE, cone_mapE); case: eqP => [<-|_]; rewrite ?mxE;
  by move: (Num.sqrt _) => s; ring.
Qed.

Lemma cone_rows_closed (kappa m M : R) : 1 < kappa ->
  closed (cone_rows kappa m M).
Proof.
move=> k1.
have -> : cone_rows kappa m M =
    (fun x => cone_map (kappa_dual kappa) (vec_mx x)) @^-1` fit_slice m M.
  apply/seteqP; split => [_ [S hS <-]|x hx] /=.
    by rewrite mxvecK cone_mapK.
  exists (cone_map (kappa_dual kappa) (vec_mx x)) => //.
  by rewrite cone_mapVK // vec_mxK.
apply: (continuous_closedP _).1 _ _ (fit_slice_closed m M).
apply: continuous_mxP => i j.
have -> : (fun x : 'rV[R]_(d * d) =>
      cone_map (kappa_dual kappa) (vec_mx x) i j) =
    (fun x => (if i == j then Num.sqrt ((kappa_dual kappa - 1) / 2%:R) else 1) *
       x 0 (mxvec_index i j)).
  apply/funext => x; rewrite cone_mapE !mxE.
  by case: eqP => [->|_]; rewrite ?mul1r.
by apply: continuous_scale_fun; exact: coord_continuous.
Qed.

End slice.

Section scale_generic.
Context {RT : realType}.

Lemma vec_mx_scale m k (c : RT) (v : 'rV[RT]_(m * k)) :
  vec_mx (c *: v) = c *: vec_mx v.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

End scale_generic.

Lemma goe_part_scale m (c : R) (A : 'M[R]_m) :
  goe_part (c *: A) = c *: goe_part A.
Proof. by rewrite /goe_part linearZ /= -scalerDr !scalerA mulrC. Qed.

Section measurable_generic.
Context {RT : realType}.

Lemma measurable_mulmx_tr p q m (P : 'M[RT]_(p, q)) :
  measurable_fun setT (fun X : 'M[RT]_(m, q) => P *m X^T).
Proof.
apply/measurable_fun_mxP => i j.
have -> : (fun X : 'M[RT]_(m, q) => (P *m X^T) i j) =
    (fun X => \sum_k P i k * X j k).
  by apply/funext => X; rewrite mxE; apply: eq_bigr => k _; rewrite mxE.
apply: measurable_sum => k.
by apply: measurable_funM; [exact: measurable_cst | exact: measurable_mxentry].
Qed.

Lemma measurable_mulmx_l p q m (P : 'M[RT]_(p, q)) :
  measurable_fun setT (fun B : 'M[RT]_(q, m) => P *m B).
Proof.
apply/measurable_fun_mxP => i j.
have -> : (fun B : 'M[RT]_(q, m) => (P *m B) i j) =
    (fun B => \sum_k P i k * B k j).
  by apply/funext => B; rewrite mxE.
apply: measurable_sum => k.
by apply: measurable_funM; [exact: measurable_cst | exact: measurable_mxentry].
Qed.

End measurable_generic.

Section margin.
Variables (n d : nat).

(* The smallest singular value of l |-> goe_part (vec_mx (l X)), as an
   infimum over the unit sphere of 'cV_n. *)
Definition sym_margin (X : 'M[R]_(n, d * d)) : R :=
  escape_inf (@unit_sphere R n) (sym_proj d *m X^T).

Lemma frobenius_sym_proj_col (X : 'M[R]_(n, d * d)) (x : 'cV[R]_n) :
  frobenius (sym_proj d *m X^T *m x) = frobenius (goe_part (vec_mx (x^T *m X))).
Proof.
rewrite -frobenius_trmx !trmx_mul trmxK sym_proj_sym mulmxA mul_sym_proj.
exact: frobenius_mxvec.
Qed.

Lemma unit_sphere_neq0 : (0 < n)%N -> @unit_sphere R n !=set0.
Proof.
move=> n0; exists (delta_mx (Ordinal n0) 0).
by rewrite /unit_sphere /= /frobenius mxdot_delta mxE !eqxx sqrtr1.
Qed.

Lemma sym_margin_le (X : 'M[R]_(n, d * d)) (l : 'rV[R]_n) :
  sym_margin X * frobenius l <= frobenius (goe_part (vec_mx (l *m X))).
Proof.
have [->|l0] := eqVneq l 0.
  by rewrite frobenius0 mulr0 frobenius_ge0.
have fl : 0 < frobenius l by rewrite frobenius_gt0.
have il : 0 <= (frobenius l)^-1 by rewrite invr_ge0 ltW.
pose x := (frobenius l)^-1 *: l^T.
have ux : @unit_sphere R n x.
  rewrite /unit_sphere /= /x frobeniusZ frobenius_trmx (ger0_norm il).
  exact: mulVf (lt0r_neq0 fl).
have := escape_inf_le (sym_proj d *m X^T) ux.
rewrite -/(sym_margin X) frobenius_sym_proj_col /x linearZ /= trmxK.
rewrite -scalemxAl vec_mx_scale goe_part_scale frobeniusZ (ger0_norm il) => h.
by rewrite -ler_pdivlMr // mulrC.
Qed.

Lemma sym_margin_feature (kappa : R) (a : n.-tuple 'rV[R]_(d * d)) :
  (0 < n)%N ->
  Num.sqrt (2%:R / d%:R) * Num.min 1 (Num.sqrt ((kappa - 1) / 2%:R)) *
    sym_margin (tuple_mx a) <= sym_margin (tuple_mx (feature_tuple kappa a)).
Proof.
move=> n0; apply: (escape_inf_ge (unit_sphere_neq0 n0)) => x ux.
rewrite frobenius_sym_proj_col feature_goe_part frobeniusZ.
rewrite ger0_norm ?sqrtr_ge0 // -mulrA.
apply: (ler_wpM2l (sqrtr_ge0 _)).
apply: le_trans (frobenius_cone_map_lb _ _ _).
apply: (ler_wpM2l _); first by rewrite le_min ler01 sqrtr_ge0.
rewrite -frobenius_sym_proj_col; exact: escape_inf_le.
Qed.

Lemma measurable_sym_margin : (0 < n)%N ->
  measurable_fun setT
    (fun Z : n.-tuple 'rV[RR]_(d * d) => sym_margin (tuple_mx Z) : RR).
Proof.
move=> n0.
have Kb : forall x, @unit_sphere R n x -> frobenius x <= 1.
  by move=> x /= ->.
have m1 := measurable_escape_inf (N := d * d) (unit_sphere_neq0 n0) Kb.
have -> : (fun Z : n.-tuple 'rV[RR]_(d * d) => sym_margin (tuple_mx Z) : RR) =
    (fun b : 'rV[RR]_(d * d * n) =>
       escape_inf (@unit_sphere RR n) (vec_mx b : 'M[RR]_(d * d, n))) \o
    (fun Z => mxvec (sym_proj d *m (tuple_mx Z)^T)).
  by apply/funext => Z /=; rewrite mxvecK.
apply: measurableT_comp m1 _.
apply: measurableT_comp (@measurable_mxvec _ _ _) _.
have := measurableT_comp (measurable_mulmx_tr _ _ n (sym_proj d))
  (@measurable_tuple_mx RR n (d * d)).
exact.
Qed.

Lemma measurable_approx (kappa m M : R) : 0 <= m -> m <= 1 -> 1 <= M ->
  measurable_fun setT (fun Z : n.-tuple 'rV[RR]_(d * d) =>
    escape_inf (tr_set (cone_rows d kappa m M)) (tuple_mx Z) : RR).
Proof.
move=> m0 m1 M1.
have K0 := tr_set_neq0 (cone_rows_neq0 d kappa m M m1 M1).
have Kb := tr_set_bounded (cone_rows_bounded d kappa m M m0).
have m2 := measurable_escape_inf (N := n) K0 Kb.
have -> : (fun Z : n.-tuple 'rV[RR]_(d * d) =>
      escape_inf (tr_set (cone_rows d kappa m M)) (tuple_mx Z) : RR) =
    (fun a : 'rV[RR]_(n * (d * d)) =>
       escape_inf (tr_set (cone_rows d kappa m M))
         (vec_mx a : 'M[RR]_(n, d * d))) \o (fun Z => mxvec (tuple_mx Z)).
  by apply/funext => Z /=; rewrite mxvecK.
apply: measurableT_comp m2 _.
exact: measurableT_comp (@measurable_mxvec _ _ _) (@measurable_tuple_mx _ _ _).
Qed.

End margin.

Arguments sym_margin {n d}.

Section exact_fit.
Variables (n d : nat).

(* On the event where the margin is at least sig and some S_0 of the
   slice has |Z mxvec S_0| < r <= sig min (m/2, 1/2), the features have an
   exact fit in a slightly larger slice (subcritical_correction at
   kappa = 3, where T_3 is the identity). *)
Lemma exact_fit_of_margin (Z : n.-tuple 'rV[R]_(d * d)) (m M sig r : R) :
  (0 < d)%N -> 0 < m -> m <= 1 -> 1 <= M -> 0 < sig ->
  r <= sig * Num.min (m / 2%:R) 2^-1 ->
  sig <= sym_margin (tuple_mx Z) ->
  escape_inf (tr_set (cone_rows d 3%:R m M)) (tuple_mx Z) < r ->
  exists2 S : 'M[R]_d, S \is symmetricmx &
    [/\ forall v : 'cV[R]_d, m / 3%:R * mxdot v v <= mxdot v (S *m v),
        forall v : 'cV[R]_d, mxdot v (S *m v) <= (2%:R * M + m) * mxdot v v,
        \tr S = d%:R &
        forall i, mxdot (tnth Z i) (mxvec S) = 0].
Proof.
move=> d0 m0 m1 M1 sig0 hr hsig happ.
rewrite escape_inf_tr_set in happ.
have K0 : [set frobenius (tuple_mx Z *m x^T) | x in cone_rows d 3%:R m M]
    !=set0.
  have [x Kx] := cone_rows_neq0 d 3%:R m M m1 M1.
  by exists (frobenius (tuple_mx Z *m x^T)), x.
have [_ [x [S0 hS0 <-] <-] hlt] := inf_lt K0 happ.
have [S0s S0m S0M S0tr] := hS0.
have marg (l : 'rV[R]_n) :
    sig * frobenius l <= frobenius (goe_part (vec_mx (l *m tuple_mx Z))).
  apply: le_trans (sym_margin_le _ _ (tuple_mx Z) l).
  exact: (ler_wpM2r (frobenius_ge0 l) hsig).
have k3 : (1 : R) < 3%:R by rewrite ltr1n.
have hres : (1 + `|Num.sqrt ((kappa_dual 3%:R - 1) / 2%:R) - 1|) *
    frobenius (tuple_mx Z *m (mxvec (cone_map 3%:R S0))^T) <=
    sig * Num.min (m / 2%:R) 2^-1.
  rewrite kappa_dual3.
  have -> : ((3%:R : R) - 1) / 2%:R = 1 by field.
  rewrite sqrtr1 subrr normr0 addr0 mul1r; exact: ltW (lt_le_trans hlt hr).
have [S Ss [Sm SM Str SA]] :=
  subcritical_correction _ _ _ (tuple_mx Z) S0 _ _ _ k3 d0 m0 sig0 S0s S0m S0M
    S0tr marg hres.
exists S => //; split => // i.
have := congr1 (fun A : 'M[R]_(n, 1) => A i 0) SA.
by rewrite cone_map3 mulmx_trE row_tuple_mx mxE.
Qed.

End exact_fit.

Section approx_transfer.
Variables (kappa : R) (n d : nat).

(* The approximation value of the features is sqrt (2 / d) times that of
   the Gaussian rows over T_kappa of the slice. *)
Lemma approx_feature (a : n.-tuple 'rV[R]_(d * d)) (m M r : R) :
  (0 < d)%N -> m <= 1 -> 1 <= M ->
  escape_inf (tr_set (cone_rows d kappa m M)) (tuple_mx a) < r ->
  escape_inf (tr_set (cone_rows d 3%:R m M))
    (tuple_mx (feature_tuple kappa a)) <
    Num.sqrt (2%:R / d%:R) * r.
Proof.
move=> d0 m1 M1 happ; rewrite escape_inf_tr_set in happ.
have K0 : [set frobenius (tuple_mx a *m x^T) | x in cone_rows d kappa m M]
    !=set0.
  have [x Kx] := cone_rows_neq0 d kappa m M m1 M1.
  by exists (frobenius (tuple_mx a *m x^T)), x.
have [_ [x [S hS <-] <-] hlt] := inf_lt K0 happ.
have [Ss _ _ _] := hS.
rewrite escape_inf_tr_set.
apply: le_lt_trans (_ : _ <= Num.sqrt (2%:R / d%:R) *
    frobenius (tuple_mx a *m (mxvec (cone_map kappa S))^T)) _.
  apply: ge_inf; first by exists 0 => _ [y _ <-]; exact: frobenius_ge0.
  exists (mxvec (cone_map 3%:R S)); first by exists S.
  by rewrite cone_map3 (feature_rows _ _ _ _ _ Ss) frobeniusZ
    (ger0_norm (sqrtr_ge0 _)).
have s0 : 0 < Num.sqrt (2%:R / d%:R) :> R.
  by rewrite sqrtr_gt0 divr_gt0 // ltr0n.
by rewrite ltr_pM2l.
Qed.

End approx_transfer.

Section level_sets.
Context {RT : realType} {dT : measure_display} {T : measurableType dT}.

Lemma measurable_le_set (f : T -> RT) (c : RT) : measurable_fun setT f ->
  measurable [set x | f x <= c].
Proof.
move=> mf; have := mf measurableT _ (measurable_itv `]-oo, c]%R).
by rewrite setTI; congr measurable; apply/seteqP; split => x /=;
  rewrite in_itv /=.
Qed.

Lemma measurable_ge_set (f : T -> RT) (c : RT) : measurable_fun setT f ->
  measurable [set x | c <= f x].
Proof.
move=> mf; have := mf measurableT _ (measurable_itv `[c, +oo[%R).
by rewrite setTI; congr measurable; apply/seteqP; split => x /=;
  rewrite in_itv /= andbT.
Qed.

Lemma measurable_lt_set (f : T -> RT) (c : RT) : measurable_fun setT f ->
  measurable [set x | f x < c].
Proof.
move=> mf; have := mf measurableT _ (measurable_itv `]-oo, c[%R).
by rewrite setTI; congr measurable; apply/seteqP; split => x /=;
  rewrite in_itv /=.
Qed.

Lemma measurable_gt_set (f : T -> RT) (c : RT) : measurable_fun setT f ->
  measurable [set x | c < f x].
Proof.
move=> mf; have := mf measurableT _ (measurable_itv `]c, +oo[%R).
by rewrite setTI; congr measurable; apply/seteqP; split => x /=;
  rewrite in_itv /= andbT.
Qed.

Lemma measurable_eq_set (f : T -> RT) (c : RT) : measurable_fun setT f ->
  measurable [set x | f x = c].
Proof.
move=> mf; have := mf measurableT _ (measurable_set1 c).
by rewrite setTI.
Qed.

End level_sets.

Section row_tails.
Variables (n d : nat).

Lemma measurable_sym_margin_mx : (0 < n)%N ->
  measurable_fun setT (fun A : 'M[RR]_(n, d * d) => sym_margin A : RR).
Proof.
move=> n0.
have Kb : forall x, @unit_sphere R n x -> frobenius x <= 1.
  by move=> x /= ->.
have m1 := measurable_escape_inf (N := d * d) (unit_sphere_neq0 _ n0) Kb.
have -> : (fun A : 'M[RR]_(n, d * d) => sym_margin A : RR) =
    (fun b : 'rV[RR]_(d * d * n) =>
       escape_inf (@unit_sphere RR n) (vec_mx b : 'M[RR]_(d * d, n))) \o
    (fun A => mxvec (sym_proj d *m A^T)).
  by apply/funext => A /=; rewrite mxvecK.
apply: measurableT_comp m1 _.
apply: measurableT_comp (@measurable_mxvec _ _ _) _.
exact: (measurable_mulmx_tr _ _ n (sym_proj d)).
Qed.

(* The margin of n independent Gaussian rows, from the escape bound of the
   projection on the symmetric matrices. *)
Lemma margin_tail (u : R) : (0 < n)%N -> (0 < d)%N -> 0 <= u ->
  (tuple_prod (fun=> gauss (d * d)) n
    [set a : n.-tuple 'rV[RR]_(d * d) | (sym_margin (tuple_mx a) <=
      Num.sqrt ((d * d.+1)%:R / 2%:R - 1) - Num.sqrt n%:R - u)%R] <=
   (expR (- u ^+ 2 / 2%:R))%:E)%E.
Proof.
move=> n0 d0 u0.
set c := Num.sqrt _ - _ - _.
have mX : measurable [set A : 'M[RR]_(n, d * d) | sym_margin A <= c].
  exact: measurable_le_set (measurable_sym_margin_mx n0).
have mX' : measurable [set B : 'M[RR]_(d * d, n) |
    escape_inf (@unit_sphere RR n) (sym_proj d *m B) <= c].
  apply: measurable_le_set.
  have Kb : forall x, @unit_sphere R n x -> frobenius x <= 1.
    by move=> x /= ->.
  have m1 := measurable_escape_inf (N := d * d) (unit_sphere_neq0 _ n0) Kb.
  have -> : (fun B : 'M[RR]_(d * d, n) =>
      escape_inf (@unit_sphere RR n) (sym_proj d *m B) : RR) =
    (fun b : 'rV[RR]_(d * d * n) =>
       escape_inf (@unit_sphere RR n) (vec_mx b : 'M[RR]_(d * d, n))) \o
    (fun B => mxvec (sym_proj d *m B)).
    by apply/funext => B /=; rewrite mxvecK.
  apply: measurableT_comp m1 _.
  apply: measurableT_comp (@measurable_mxvec _ _ _) _.
  exact: (measurable_mulmx_l _ _ n (sym_proj d)).
change (tuple_prod (fun=> gauss (d * d)) n
  (@tuple_mx RR n (d * d) @^-1` [set A | (sym_margin A <= c)%R]) <=
  (expR (- u ^+ 2 / 2%:R))%:E)%E.
rewrite (gauss_tuple_mx mX).
rewrite (_ : [set a | _] = [set a : 'rV[RR]_(n * (d * d)) |
    [set B : 'M[RR]_(d * d, n) |
      (escape_inf (@unit_sphere RR n) (sym_proj d *m B) <= c)%R]
      (vec_mx a)^T]) //.
rewrite (gauss_trmx mX').
have P0 : sym_proj d != 0.
  apply/eqP => P0; have := sym_proj_trace d; rewrite P0 mxtrace0.
  move/esym/eqP; apply/negP; apply: lt0r_neq0.
  by apply: divr_gt0; rewrite ltr0n // muln_gt0 d0.
apply: le_trans (gauss_proj_singular_tail (sym_proj_sym d) (sym_proj_idem d)
  P0 n0 u0).
by rewrite sym_proj_trace.
Qed.

End row_tails.

(* The radius of T_kappa of the slice, in the Frobenius norm. *)
Definition cone_slice_radius (kappa M : R) (d : nat) : R :=
  Num.max 1 (Num.sqrt ((kappa - 1) / 2%:R)) * Num.sqrt (M * d%:R).

Section approx_tail.
Variables (n d : nat).

Lemma approx_tail (kappa m M u : R) : 1 < kappa -> (0 < n)%N -> (0 < d)%N ->
  0 <= m -> m <= 1 -> 1 <= M -> 0 <= u ->
  ((2^-1)%:E < gauss (n + d * d)
     [set z | cgmt_aux (tr_set (cone_rows d kappa m M)) (lsubmx z) (rsubmx z)
       = 0%R])%E ->
  (tuple_prod (fun=> gauss (d * d)) n
    [set a : n.-tuple 'rV[RR]_(d * d) |
      (cone_slice_radius kappa M d * (1 + 2 * Num.sqrt (ln 4)) + u <=
       escape_inf (tr_set (cone_rows d kappa m M)) (tuple_mx a))%R] <=
   (2 * expR (- u ^+ 2 / (2 * cone_slice_radius kappa M d ^+ 2)))%:E)%E.
Proof.
move=> k1 n0 d0 m0 m1 M1 u0 h.
set K := tr_set (cone_rows d kappa m M).
set c := (_ + u)%R.
have K0 : K !=set0 := tr_set_neq0 (cone_rows_neq0 d kappa m M m1 M1).
have Kb := tr_set_bounded (cone_rows_bounded d kappa m M m0).
have rho0 : 0 < cone_slice_radius kappa M d.
  apply: mulr_gt0; first by rewrite lt_max ltr01.
  by rewrite sqrtr_gt0 mulr_gt0 // ?ltr0n // (lt_le_trans ltr01).
have Kc : closed K := closed_tr_set (cone_rows_closed d kappa m M k1).
have Kcvx := convex_tr_set (cone_rows_convex d kappa m M).
have mX : measurable [set A : 'M[RR]_(n, d * d) | (c <= escape_inf K A)%R].
  have m2 := measurable_escape_inf (N := n) K0 Kb.
  have -> : [set A : 'M[RR]_(n, d * d) | (c <= escape_inf K A)%R] =
      [set A : 'M[RR]_(n, d * d) |
        (c <= escape_inf K (vec_mx (mxvec A) : 'M[RR]_(n, d * d)))%R].
    by apply/seteqP; split => A /=; rewrite mxvecK.
  apply: measurable_ge_set.
  exact: measurableT_comp m2 (@measurable_mxvec _ _ _).
change (tuple_prod (fun=> gauss (d * d)) n
  (@tuple_mx RR n (d * d) @^-1` [set A | (c <= escape_inf K A)%R]) <=
  (2 * expR (- u ^+ 2 / (2 * cone_slice_radius kappa M d ^+ 2)))%:E)%E.
rewrite (gauss_tuple_mx mX).
exact: (cgmt_zero_tail K0 Kb n0 rho0 Kc Kcvx u0 h).
Qed.

End approx_tail.

Section cone_map_identities.
Variables (kappa : R) (d : nat).

(* cone_map with the diagonal factor as a variable. *)
Definition cmap (s : R) (X : 'M[R]_d) : 'M[R]_d :=
  X - diag_part X + s *: diag_part X.

Lemma cone_map_cmap (X : 'M[R]_d) :
  cone_map kappa X = cmap (Num.sqrt ((kappa - 1) / 2%:R)) X.
Proof. by []. Qed.

Lemma cmapE (s : R) (X : 'M[R]_d) i j :
  cmap s X i j = if i == j then s * X i i else X i j.
Proof. by rewrite !mxE; case: eqP => [->|_]; ring. Qed.

Lemma mxdot_cmap (s : R) (W X : 'M[R]_d) :
  mxdot W (cmap s X) = mxdot W X + (s - 1) * \sum_j W j j * X j j.
Proof.
rewrite /mxdot mulr_sumr -big_split /=; apply: eq_bigr => i _.
rewrite (bigD1 i) //= [in RHS](bigD1 i) //= cmapE eqxx.
have -> : \sum_(j < d | j != i) W i j * cmap s X i j =
    \sum_(j < d | j != i) W i j * X i j.
  by apply: eq_bigr => j ji; rewrite cmapE eq_sym (negPf ji).
ring.
Qed.

Lemma mxdot_cmap_sqr (s : R) (X : 'M[R]_d) :
  mxdot (cmap s X) (cmap s X) = mxdot X X + (s ^+ 2 - 1) * \sum_j X j j ^+ 2.
Proof.
rewrite /mxdot mulr_sumr -big_split /=; apply: eq_bigr => i _.
rewrite (bigD1 i) //= [in RHS](bigD1 i) //= cmapE eqxx.
have -> : \sum_(j < d | j != i) cmap s X i j * cmap s X i j =
    \sum_(j < d | j != i) X i j * X i j.
  by apply: eq_bigr => j ji; rewrite cmapE eq_sym (negPf ji).
ring.
Qed.

Lemma mxdot_cone_map_sqr (X : 'M[R]_d) : 1 <= kappa ->
  mxdot (cone_map kappa X) (cone_map kappa X) =
  mxdot X X + cone_shift kappa * \sum_j X j j ^+ 2.
Proof.
move=> k1; have ka : 0 <= (kappa - 1) / 2%:R :> R.
  by rewrite divr_ge0 // subr_ge0.
rewrite cone_map_cmap mxdot_cmap_sqr (sqr_sqrtr ka) cone_shiftE.
by congr (_ + _ * _); field.
Qed.

End cone_map_identities.

Section witness_matrix.
Variables (d : nat) (w c : R).

(* The witness of Lemma 5.17 before normalization: the spectral function
   x |-> (x - w)_+ + c of W. *)
Definition wit_mx (W : 'M[R]_d) : 'M[R]_d := psd_part (W - w%:M) + c%:M.

Definition wit_fun (x : R) : R := ppart w x + c.

Lemma wit_spectral (W : 'M[R]_d) : W \is symmetricmx ->
  exists2 P : 'M[R]_d, P \is orthogonalmx &
    W = P^T *m diag_mx (spec W) *m P /\
    wit_mx W = P^T *m diag_mx (\row_i wit_fun (spec W 0 i)) *m P.
Proof.
move=> Ws; have [P Po E] := spec_shift_decomposition w Ws.
have PP := orthogonalmxT Po.
have cst (a : R) : a%:M = P^T *m diag_mx (const_mx a) *m P :> 'M[R]_d.
  by rewrite diag_const_mx mul_mx_scalar -scalemxAl PP scalemx1.
exists P => //; split.
  rewrite -{1}[W](subrK w%:M) E (cst w) -mulmxDl -mulmxDr -linearD /=.
  by rewrite subrK.
rewrite /wit_mx (psd_partE Po E) (cst c) -mulmxDl -mulmxDr -linearD /=.
by congr (_ *m diag_mx _ *m _); apply/rowP => i; rewrite !mxE.
Qed.

Lemma wit_sym (W : 'M[R]_d) : W \is symmetricmx -> wit_mx W \is symmetricmx.
Proof.
move=> Ws; have [P Po [_ ->]] := wit_spectral _ Ws.
apply/symmetricmxP; rewrite !trmx_mul trmxK tr_diag_mx mulmxA.
by [].
Qed.

Lemma wit_trace (W : 'M[R]_d) : W \is symmetricmx ->
  \tr (wit_mx W) = \sum_i wit_fun (spec W 0 i).
Proof.
move=> Ws; have [P Po [_ E]] := wit_spectral _ Ws.
by rewrite (spectral_trace Po E); apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma wit_frobenius (W : 'M[R]_d) : W \is symmetricmx ->
  mxdot (wit_mx W) (wit_mx W) = \sum_i wit_fun (spec W 0 i) ^+ 2.
Proof.
move=> Ws; have [P Po [_ E]] := wit_spectral _ Ws.
by rewrite (spectral_mxdot Po E); apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma wit_dot (W : 'M[R]_d) : W \is symmetricmx ->
  mxdot W (wit_mx W) = \sum_i spec W 0 i * wit_fun (spec W 0 i).
Proof.
move=> Ws; have [P Po [EW E]] := wit_spectral _ Ws.
have PTo : P^T \is orthogonalmx by rewrite trmx_orthogonal.
rewrite {1}EW E mxdot_orthogonalmxr // mxdot_orthogonalmxl //.
by rewrite mxdot_diag; apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma wit_form_ge (W : 'M[R]_d) (b : R) : W \is symmetricmx ->
  (forall i, b <= wit_fun (spec W 0 i)) ->
  forall v : 'cV[R]_d, b * mxdot v v <= mxdot v (wit_mx W *m v).
Proof.
move=> Ws hb; have [P Po [_ E]] := wit_spectral _ Ws.
by apply/(spectral_form_ge b Po E) => i; rewrite mxE.
Qed.

Lemma wit_form_le (W : 'M[R]_d) (b : R) : W \is symmetricmx ->
  (forall i, wit_fun (spec W 0 i) <= b) ->
  forall v : 'cV[R]_d, mxdot v (wit_mx W *m v) <= b * mxdot v v.
Proof.
move=> Ws hb; have [P Po [_ E]] := wit_spectral _ Ws.
by apply/(spectral_form_le b Po E) => i; rewrite mxE.
Qed.

End witness_matrix.

Arguments wit_mx {d}.

Section sum_mxvec.
Context {RT : realType}.

(* A sum over the indices mxvec_index i j is a double sum. *)
Lemma sum_mxvec n m (F : 'I_(n * m) -> RT) :
  \sum_(k < n * m) F k = \sum_(i < n) \sum_(j < m) F (mxvec_index i j).
Proof.
rewrite (reindex _ (curry_mxvec_bij n m)) /= [RHS]pair_big /=.
by apply: eq_bigr => -[i j] _.
Qed.

End sum_mxvec.

Section goe_side.
Variable d : nat.
Hypothesis d0 : (0 < d)%N.

(* <h, mxvec X> = (sqrt (2 d) / 2) <W, X> for X symmetric and W = goe_mx h. *)
Lemma mxdot_goe (h : 'rV[R]_(d * d)) (X : 'M[R]_d) : X \is symmetricmx ->
  mxdot h (mxvec X) = Num.sqrt (2%:R * d%:R) / 2%:R * mxdot (goe_mx h) X.
Proof.
move=> Xs; rewrite -[h in LHS]vec_mxK mxdot_mxvec.
rewrite -(mxdot_goe_part_symr _ _ _ Xs) -mxdotZl; congr mxdot.
have s0 : Num.sqrt (2%:R * d%:R) != 0 :> R.
  by rewrite sqrtr_eq0 -ltNge mulr_gt0 // ltr0n.
rewrite /goe_part /goe_mx scalerA; congr (_ *: _).
by rewrite mulrAC mulfV // mul1r.
Qed.

Lemma goe_diag_sqr (h : 'rV[R]_(d * d)) :
  \sum_j goe_mx h j j ^+ 2 =
  2%:R / d%:R * \sum_j h 0 (mxvec_index j j) ^+ 2.
Proof.
have d0' : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have s2 : Num.sqrt (2%:R * d%:R) ^+ 2 = 2%:R * d%:R :> R.
  by rewrite sqr_sqrtr // mulr_ge0 // ler0n.
rewrite mulr_sumr; apply: eq_bigr => j _; rewrite goe_mxE exprMn exprVn s2.
by field.
Qed.

(* The sum of the squared diagonal entries of vec_mx h minus d is the
   centered chi-square statistic with weights mxvec 1. *)
Lemma centered_chi2_diag (h : 'rV[R]_(d * d)) :
  centered_chi2 (mxvec (1%:M : 'M[R]_d)) h =
  \sum_j h 0 (mxvec_index j j) ^+ 2 - d%:R.
Proof.
rewrite /centered_chi2 sum_mxvec.
transitivity (\sum_(i < d) (h 0 (mxvec_index i i) ^+ 2 - 1)).
  apply: eq_bigr => i _; rewrite (bigD1 i) //=.
  have -> : \sum_(j < d | j != i) mxvec (1%:M : 'M[R]_d) 0 (mxvec_index i j) *
      (h 0 (mxvec_index i j) ^+ 2 - 1) = 0.
    by apply: big1 => j ji; rewrite mxvecE mxE eq_sym (negPf ji) mul0r.
  by rewrite addr0 mxvecE mxE eqxx mul1r.
by rewrite sumrB sumr_const card_ord.
Qed.

End goe_side.

Lemma centered_chi2_const1 n (g : 'rV[R]_n) :
  centered_chi2 (const_mx 1) g = mxdot g g - n%:R.
Proof.
rewrite /centered_chi2 /mxdot big_ord1.
transitivity (\sum_(i < n) (g 0 i * g 0 i - 1)).
  by apply: eq_bigr => i _; rewrite mxE mul1r expr2.
by rewrite sumrB sumr_const card_ord.
Qed.

Section witness_numeric.
Context {RT : realType}.

(* A slack dl in the strict inequality 2 al P < A3^2 of the scalar
   choice. *)
Lemma choose_delta (al P c1 A1 A3 : RT) : 0 < al -> 0 <= c1 -> 0 < A1 ->
  0 < A3 -> 2 * al * P < A3 ^+ 2 ->
  exists dl : RT, [/\ 0 < dl, dl <= 1, dl <= A1 / 2, 0 <= A3 - 2 * dl &
    2 * (al + 2 * dl) * (P + dl * c1) <= (A3 - 2 * dl) ^+ 2].
Proof.
move=> al0 c10 A10 A30 hP.
set eta := A3 ^+ 2 - 2 * al * P.
have eta0 : 0 < eta by rewrite /eta subr_gt0.
set K := 2 * al * c1 + 4 * `|P| + 4 * c1 + 4 * A3 + 1.
have K0 : 0 < K.
  have := normr_ge0 P; rewrite /K.
  have : 0 <= al * c1 by rewrite mulr_ge0 // ltW.
  by lra.
pose dl := Num.min 1 (Num.min (A1 / 2) (Num.min (A3 / 4) (eta / K))).
have dl0 : 0 < dl.
  by rewrite /dl !lt_min ltr01 !divr_gt0.
have dl1 : dl <= 1 by rewrite /dl ge_min lexx.
have dlA1 : dl <= A1 / 2 by rewrite /dl !ge_min lexx orbT.
have dlA3 : dl <= A3 / 4 by rewrite /dl !ge_min lexx !orbT.
have dlK : dl * K <= eta.
  have : dl <= eta / K by rewrite /dl !ge_min lexx !orbT.
  by rewrite ler_pdivlMr.
exists dl; split => //; first by lra.
have Pa : P <= `|P| := ler_norm P.
have Pb : - `|P| <= P by rewrite lerNl -normrN ler_norm.
have d2 : dl ^+ 2 <= dl by rewrite expr2 ler_piMl // ltW.
have e1 : 2 * (al + 2 * dl) * (P + dl * c1) <=
    2 * al * P + dl * (2 * al * c1 + 4 * `|P| + 4 * c1).
  have h1 : 2 * (al + 2 * dl) * (P + dl * c1) =
      2 * al * P + dl * (2 * al * c1 + 4 * P) + 4 * c1 * dl ^+ 2 by ring.
  rewrite h1.
  have h2 : dl * (4 * P) <= dl * (4 * `|P|).
    by apply: ler_wpM2l; [exact: ltW | lra].
  have h3 : 4 * c1 * dl ^+ 2 <= 4 * c1 * dl.
    by apply: ler_wpM2l => //; rewrite mulr_ge0.
  by nra.
have e2 : A3 ^+ 2 - 4 * dl * A3 <= (A3 - 2 * dl) ^+ 2.
  by have := sqr_ge0 dl; nra.
have e3 : dl * (2 * al * c1 + 4 * `|P| + 4 * c1) + 4 * dl * A3 <= eta.
  apply: le_trans dlK; rewrite /K.
  by have := ltW dl0; nra.
apply: le_trans e1 _; apply: le_trans _ e2.
by rewrite /eta in e3; lra.
Qed.

(* The inequality of the witness, divided by the right powers of d. *)
Lemma witness_numeric (al dl P c1 A3 Gn dd T2 B : RT) :
  0 < dd -> 0 <= Gn -> Gn <= (al + 2 * dl) * dd ^+ 2 -> 0 <= al + 2 * dl ->
  0 <= T2 -> T2 <= dd * (P + dl * c1) ->
  dd * (A3 - 2 * dl) <= B -> 0 <= A3 - 2 * dl ->
  2 * (al + 2 * dl) * (P + dl * c1) <= (A3 - 2 * dl) ^+ 2 ->
  0 <= B /\ Gn * T2 <= dd / 2 * B ^+ 2.
Proof.
move=> dd0 G0 hG a0 T0 hT hB A0 hP.
have B0 : 0 <= B by apply: le_trans hB; rewrite mulr_ge0 // ltW.
split => //.
have PT : 0 <= P + dl * c1.
  by have := le_trans T0 hT; rewrite pmulr_rge0.
have s1 : Gn * T2 <= (al + 2 * dl) * dd ^+ 2 * (dd * (P + dl * c1)).
  by apply: ler_pM.
have s2 : (al + 2 * dl) * dd ^+ 2 * (dd * (P + dl * c1)) <=
    dd ^+ 3 / 2 * (A3 - 2 * dl) ^+ 2.
  have -> : (al + 2 * dl) * dd ^+ 2 * (dd * (P + dl * c1)) =
      dd ^+ 3 / 2 * (2 * (al + 2 * dl) * (P + dl * c1)) by field.
  apply: ler_wpM2l => //; rewrite divr_ge0 // exprn_ge0 // ltW //.
have s3 : dd ^+ 3 / 2 * (A3 - 2 * dl) ^+ 2 <= dd / 2 * B ^+ 2.
  have -> : dd ^+ 3 / 2 * (A3 - 2 * dl) ^+ 2 =
      dd / 2 * (dd * (A3 - 2 * dl)) ^+ 2 by field.
  apply: ler_wpM2l; first by rewrite divr_ge0 // ltW.
  by rewrite ler_sqr ?nnegrE // mulr_ge0 // ltW.
exact: le_trans s1 (le_trans s2 s3).
Qed.

(* The bound on |T_kappa Q|^2 / d from the statistics of the spectrum and
   the variance dv of the diagonal. *)
Lemma frob_bound (ck A1 A2 x1 x2 dv dl : RT) : 0 < A1 -> 0 <= dv ->
  dv <= dl -> dl <= 1 -> 0 <= A1 - dl -> x2 <= A2 + dl ->
  A1 - dl <= x1 -> x1 <= A1 + dl ->
  x2 + ck * (dv + x1 ^+ 2) <=
  A2 + ck * A1 ^+ 2 + dl * (1 + `|ck| * (2 * A1 + 2)).
Proof.
move=> A10 dv0 dvl dl1 A1l x2u x1l x1u.
have dl0 : 0 <= dl by apply: le_trans dvl.
have [ck0|ck0] := leP 0 ck.
  rewrite ger0_norm //.
  have s1 : x1 ^+ 2 <= A1 ^+ 2 + dl * (2 * A1 + 1).
    have h1 : x1 ^+ 2 <= (A1 + dl) ^+ 2 by rewrite ler_sqr ?nnegrE //; lra.
    have h2 : dl ^+ 2 <= dl by rewrite expr2; exact: ler_piMl dl0 dl1.
    nra.
  have s2 : ck * (dv + x1 ^+ 2) <= ck * (A1 ^+ 2 + dl * (2 * A1 + 2)).
    by apply: ler_wpM2l => //; lra.
  by nra.
rewrite ltr0_norm //.
have s1 : (A1 - dl) ^+ 2 <= x1 ^+ 2 by rewrite ler_sqr ?nnegrE //; lra.
have s2 : ck * (dv + x1 ^+ 2) <= ck * (A1 - dl) ^+ 2.
  by rewrite ler_nM2l //; have := sqr_ge0 x1; lra.
by nra.
Qed.

End witness_numeric.

Section witness_zero.
Variables (kappa : R) (n d : nat) (w c A1 A2 A3 al dl : R).

Local Notation sk := (Num.sqrt ((kappa - 1) / 2%:R)).
Local Notation F1 := (wit_fun w c).

(* The slice of the witness: m I <= S <= M I for these m and M. *)
Definition wit_lo : R := Num.min 1 (c / (2%:R * A1)).
Definition wit_hi : R := Num.max 1 (2%:R * (Num.max (3%:R - w) 0 + c) / A1).

Lemma goe_stat_sum (f : R -> R) (h : 'rV[R]_(d * d)) : (0 < d)%N ->
  \sum_i f (spec (goe_mx h) 0 i) = d%:R * goe_stat f h.
Proof.
by move=> d0; rewrite /goe_stat mulrC divfK // pnatr_eq0 -lt0n.
Qed.

Lemma diag_dot_le (W Q : 'M[R]_d) :
  `|\sum_j W j j * Q j j| <=
  Num.sqrt (\sum_j W j j ^+ 2) * Num.sqrt (\sum_j Q j j ^+ 2).
Proof.
pose a : 'rV[R]_d := \row_j W j j; pose b : 'rV[R]_d := \row_j Q j j.
have e (A : 'M[R]_d) : mxdot (\row_j A j j) (\row_j A j j) = \sum_j A j j ^+ 2.
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE expr2.
have := mxdot_le a b; rewrite /frobenius /a /b !e.
suff -> : mxdot (\row_j W j j) (\row_j Q j j) = \sum_j W j j * Q j j by [].
by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE.
Qed.

Lemma witness_aux_zero (g : 'rV[R]_n) (h : 'rV[R]_(d * d)) :
  1 < kappa -> (0 < d)%N -> 0 < c -> 0 < A1 ->
  opnorm (goe_mx h) < 3%:R ->
  `|goe_stat F1 h - A1| < dl ->
  `|goe_stat (fun x => F1 x ^+ 2) h - A2| < dl ->
  `|goe_stat (fun x => x * F1 x) h - A3| < dl ->
  \sum_j h 0 (mxvec_index j j) ^+ 2 <= 2%:R * d%:R ->
  diag_var (wit_mx w c (goe_mx h)) < dl ->
  mxdot g g <= (al + 2%:R * dl) * d%:R ^+ 2 ->
  0 < dl -> dl <= 1 -> dl <= A1 / 2%:R -> 0 <= A3 - 2%:R * dl ->
  0 <= al + 2%:R * dl ->
  2%:R * (al + 2%:R * dl) *
    (A2 + cone_shift kappa * A1 ^+ 2 +
     dl * (1 + `|cone_shift kappa| * (2%:R * A1 + 2%:R))) <=
    (A3 - 2%:R * dl) ^+ 2 ->
  4%:R * `|sk - 1| ^+ 2 * (A2 + 1) <= dl ^+ 2 * d%:R ->
  cgmt_aux (tr_set (cone_rows d kappa wit_lo wit_hi)) g h = 0.
Proof.
move=> k1 d0 c0 A10 hop h1 h2 h3 hdiag hdv hg dl0 dl1 dlA1 A3dl a0 hP hD.
set W := goe_mx h.
have Ws : W \is symmetricmx := goe_mx_symmetric h.
set Q := wit_mx w c W.
have Qs : Q \is symmetricmx := wit_sym _ _ _ _ Ws.
have dd0 : 0 < d%:R :> R by rewrite ltr0n.
set x1 := goe_stat F1 h; set x2 := goe_stat (fun x => F1 x ^+ 2) h.
set x3 := goe_stat (fun x => x * F1 x) h.
have trQ : \tr Q = d%:R * x1 by rewrite /Q /W wit_trace // goe_stat_sum.
have QQ : mxdot Q Q = d%:R * x2.
  by rewrite /Q /W wit_frobenius // (goe_stat_sum (fun x => F1 x ^+ 2)).
have WQ : mxdot W Q = d%:R * x3.
  by rewrite /Q /W wit_dot // (goe_stat_sum (fun x => x * F1 x)).
have /andP[x1l x1u] : A1 - dl < x1 < A1 + dl by rewrite -ltr_distl.
have /andP[_ x2u] : A2 - dl < x2 < A2 + dl by rewrite -ltr_distl.
have /andP[x3l _] : A3 - dl < x3 < A3 + dl by rewrite -ltr_distl.
have x10 : 0 < x1 by lra.
have x1lo : A1 / 2%:R <= x1 by lra.
have x1hi : x1 <= 2%:R * A1 by lra.
have x20 : 0 <= x2.
  by have := mxdot_ge0 Q; rewrite QQ pmulr_rge0.
(* the normalized witness S = Q / x1, of trace d *)
set S := x1^-1 *: Q.
have Ss : S \is symmetricmx := symmetric_scale _ _ _ Qs.
have F1ge i : c <= F1 (spec W 0 i) by rewrite /wit_fun lerDr ppart_ge0.
set Fm := Num.max (3%:R - w) 0 + c.
have F1le i : F1 (spec W 0 i) <= Fm.
  have si : spec W 0 i <= 3%:R.
    apply: le_trans (ler_norm _) _; apply: le_trans (spec_le_opnorm i Ws) _.
    exact: ltW.
  rewrite /wit_fun /Fm lerD2r /ppart ge_max; apply/andP; split; rewrite le_max.
    by rewrite lerD2r si.
  by rewrite lexx orbT.
have SQ v : mxdot v (S *m v) = x1^-1 * mxdot v (Q *m v).
  by rewrite /S -scalemxAl mxdotZr.
have ix0 : 0 < x1^-1 by rewrite invr_gt0.
have hS : fit_slice d wit_lo wit_hi S.
  split => //.
  - move=> v; rewrite SQ.
    have hv := wit_form_ge _ _ _ _ c Ws F1ge v.
    apply: le_trans (_ : _ <= x1^-1 * (c * mxdot v v)) _; last first.
      exact: (ler_wpM2l (ltW ix0) hv).
    rewrite mulrA; apply: (ler_wpM2r (mxdot_ge0 v)).
    apply: le_trans (_ : _ <= c / (2%:R * A1)) _.
      by rewrite ge_min lexx orbT.
    rewrite [x1^-1 * c]mulrC; apply: (ler_wpM2l (ltW c0)).
    by rewrite lef_pV2 ?posrE // mulr_gt0.
  - move=> v; rewrite SQ.
    have hv := wit_form_le _ _ _ _ Fm Ws F1le v.
    apply: le_trans (ler_wpM2l (ltW ix0) hv) _.
    rewrite mulrA; apply: (ler_wpM2r (mxdot_ge0 v)).
    apply: le_trans _ (_ : 2%:R * Fm / A1 <= _); last first.
      by rewrite le_max lexx orbT.
    have Fm0 : 0 <= Fm by rewrite /Fm addr_ge0 ?le_max ?lexx ?orbT // ltW.
    rewrite mulrAC; apply: (ler_wpM2r Fm0).
    have hA : 0 < A1 / 2%:R by rewrite divr_gt0 // ltr0n.
    by rewrite -[2%:R / A1]invf_div lef_pV2 ?posrE.
  - by rewrite /S mxtraceZ trQ mulrCA mulVf ?mulr1 // gt_eqF.
(* the point x = mxvec (T_kappa S) of the CGMT set *)
set x := mxvec (cone_map kappa S).
have hx : cone_rows d kappa wit_lo wit_hi x by exists S.
have TQs : cone_map kappa Q \is symmetricmx := cone_map_symmetric _ _ _ Qs.
have TS : cone_map kappa S = x1^-1 *: cone_map kappa Q by rewrite /S cone_mapZ.
have fx : frobenius x = x1^-1 * frobenius (cone_map kappa Q).
  by rewrite /x frobenius_mxvec TS frobeniusZ ger0_norm // ltW.
have hxh : mxdot h x = x1^-1 *
    (Num.sqrt (2%:R * d%:R) / 2%:R * mxdot W (cone_map kappa Q)).
  by rewrite /x TS mxvec_scale mxdotZr (mxdot_goe _ d0 h _ TQs).
(* |T_kappa Q|^2 <= d (P + dl c1) *)
set ck := cone_shift kappa.
have dn : d%:R != 0 :> R by rewrite gt_eqF.
have eQ : \sum_j Q j j ^+ 2 = d%:R * (diag_var Q + x1 ^+ 2).
  by rewrite diag_varE trQ [d%:R * x1]mulrC (mulfK dn) subrK (mulVKf dn).
have T2E : mxdot (cone_map kappa Q) (cone_map kappa Q) =
    d%:R * (x2 + ck * (diag_var Q + x1 ^+ 2)).
  by rewrite (mxdot_cone_map_sqr _ _ _ (ltW k1)) QQ eQ -/ck; ring.
have dv0 := diag_var_ge0 Q.
have hA1 : 0 <= A1 - dl by lra.
have T2le : mxdot (cone_map kappa Q) (cone_map kappa Q) <=
    d%:R * (A2 + ck * A1 ^+ 2 + dl * (1 + `|ck| * (2%:R * A1 + 2%:R))).
  rewrite T2E; apply: (ler_wpM2l (ltW dd0)).
  exact: (frob_bound ck A1 A2 x1 x2 (diag_var Q) dl A10 dv0 (ltW hdv) dl1 hA1
    (ltW x2u) (ltW x1l) (ltW x1u)).
(* <W, T_kappa Q> >= d (A3 - 2 dl) *)
have BE : mxdot W (cone_map kappa Q) =
    d%:R * x3 + (sk - 1) * \sum_j W j j * Q j j.
  by rewrite cone_map_cmap mxdot_cmap WQ.
have sW : Num.sqrt (\sum_j W j j ^+ 2) <= 2%:R.
  rewrite /W (goe_diag_sqr _ d0 h).
  rewrite -[X in _ <= X](@ger0_norm _ 2%:R) // -sqrtr_sqr; apply: ler_wsqrtr.
  apply: le_trans (ler_wpM2l _ hdiag) _; first by rewrite divr_ge0.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have sQ : Num.sqrt (\sum_j Q j j ^+ 2) <= Num.sqrt (d%:R * x2).
  by apply: ler_wsqrtr; rewrite -QQ; exact: diag_sqr_le.
have cr : `|(sk - 1) * \sum_j W j j * Q j j| <= dl * d%:R.
  rewrite normrM; apply: le_trans (ler_wpM2l (normr_ge0 _) (diag_dot_le W Q)) _.
  apply: le_trans (_ : _ <= `|sk - 1| * (2%:R * Num.sqrt (d%:R * x2))) _.
    apply: (ler_wpM2l (normr_ge0 _)); apply: ler_pM => //; exact: sqrtr_ge0.
  have h0 : 0 <= `|sk - 1| * (2%:R * Num.sqrt (d%:R * x2)).
    by rewrite mulr_ge0 // mulr_ge0 // sqrtr_ge0.
  have r0 : 0 <= dl * d%:R by rewrite mulr_ge0 // ltW.
  rewrite -(@ler_pXn2r _ 2) ?nnegrE //.
  have x2d : 0 <= d%:R * x2 by rewrite mulr_ge0 // ltW.
  rewrite !exprMn (sqr_sqrtr x2d).
  have hx2 : x2 <= A2 + 1 by lra.
  have e1 : `|sk - 1| ^+ 2 * (2%:R ^+ 2 * (d%:R * x2)) <=
      d%:R * (4%:R * `|sk - 1| ^+ 2 * (A2 + 1)).
    have -> : `|sk - 1| ^+ 2 * (2%:R ^+ 2 * (d%:R * x2)) =
        d%:R * (4%:R * `|sk - 1| ^+ 2 * x2) by ring.
    apply: (ler_wpM2l (ltW dd0)); apply: (ler_wpM2l _ hx2).
    by rewrite mulr_ge0 // sqr_ge0.
  apply: le_trans e1 _.
  have -> : dl ^+ 2 * d%:R ^+ 2 = d%:R * (dl ^+ 2 * d%:R) by ring.
  exact: (ler_wpM2l (ltW dd0) hD).
have hB : d%:R * (A3 - 2%:R * dl) <= mxdot W (cone_map kappa Q).
  rewrite BE.
  have ht : - (dl * d%:R) <= (sk - 1) * \sum_j W j j * Q j j.
    rewrite lerNl; apply: le_trans (ler_norm _) _; rewrite normrN; exact: cr.
  have hx3 : d%:R * (A3 - dl) <= d%:R * x3.
    by apply: (ler_wpM2l (ltW dd0)); lra.
  have -> : d%:R * (A3 - 2%:R * dl) = d%:R * (A3 - dl) - dl * d%:R by ring.
  exact: lerD hx3 ht.
have [B0 key] := witness_numeric al dl (A2 + ck * A1 ^+ 2)
  (1 + `|ck| * (2%:R * A1 + 2%:R)) A3 (mxdot g g) d%:R
  (mxdot (cone_map kappa Q) (cone_map kappa Q)) (mxdot W (cone_map kappa Q))
  dd0 (mxdot_ge0 g) hg a0 (mxdot_ge0 (cone_map kappa Q)) T2le hB A3dl hP.
(* |g| |x| <= <h, x> *)
have main : frobenius g * frobenius x <= mxdot h x.
  rewrite fx hxh mulrCA; apply: (ler_wpM2l (ltW ix0)).
  have s2d : (Num.sqrt (2%:R * d%:R) / 2%:R) ^+ 2 = d%:R / 2%:R :> R.
    by rewrite expr_div_n sqr_sqrtr ?mulr_ge0 ?ler0n //; field.
  have lhs0 : 0 <= frobenius g * frobenius (cone_map kappa Q).
    by rewrite mulr_ge0 ?frobenius_ge0.
  have rhs0 : 0 <= Num.sqrt (2%:R * d%:R) / 2%:R * mxdot W (cone_map kappa Q).
    by rewrite mulr_ge0 ?divr_ge0 ?sqrtr_ge0.
  rewrite -(@ler_pXn2r _ 2) ?nnegrE // exprMn !frobenius_sqr exprMn s2d.
  exact: key.
rewrite cgmt_aux_tr_set; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_inf.
    by exists 0 => _ [y _ <-]; rewrite le_max lexx.
  exists x => //; apply: max_l; rewrite subr_le0; exact: main.
apply: lb_le_inf.
  by exists (Num.max 0 (frobenius g * frobenius x - mxdot h x)), x.
by move=> _ [y _ <-]; rewrite le_max lexx.
Qed.

End witness_zero.

Section ppart_lipschitz.
Context {RT : realType}.

Lemma ppart_lipschitz (w x y : RT) : `|ppart w x - ppart w y| <= `|x - y|.
Proof.
rewrite /ppart; have [hx|hx] := leP (x - w) 0; have [hy|hy] := leP (y - w) 0.
- by rewrite subrr normr0.
- rewrite sub0r normrN (ger0_norm (ltW hy)) distrC.
  by apply: le_trans _ (ler_norm _); lra.
- rewrite subr0 (ger0_norm (ltW hx)).
  by apply: le_trans _ (ler_norm _); lra.
- have -> : x - w - (y - w) = x - y by ring.
  exact: lexx.
Qed.

End ppart_lipschitz.

Section wigner_inputs.
Variables (w c : R).
Hypothesis c0 : 0 <= c.

Local Notation F1 := (wit_fun w c).
Let Fm := Num.max (3%:R - w) 0 + c.

Lemma continuous_wit : continuous F1.
Proof.
apply: continuous_add; first exact: continuous_ppart.
exact: continuous_cstf.
Qed.

Lemma continuous_wit_sqr : continuous (fun x => F1 x ^+ 2).
Proof. by apply: continuous_sqr; exact: continuous_wit. Qed.

Lemma continuous_wit_id : continuous (fun x : R => x * F1 x).
Proof.
by apply: continuous_mul; [exact: continuous_idf | exact: continuous_wit].
Qed.

Lemma wit_lipschitz x y : `|F1 x - F1 y| <= 1 * `|x - y|.
Proof.
rewrite mul1r /wit_fun.
have -> : ppart w x + c - (ppart w y + c) = ppart w x - ppart w y by ring.
exact: ppart_lipschitz.
Qed.

Lemma wit_ge0 x : 0 <= F1 x.
Proof. by rewrite /wit_fun addr_ge0 // ppart_ge0. Qed.

Lemma wit_le x : x <= 3%:R -> F1 x <= Fm.
Proof.
move=> x3; rewrite /wit_fun /Fm lerD2r /ppart ge_max; apply/andP; split.
  by rewrite le_max lerD2r x3.
by rewrite le_max lexx orbT.
Qed.

Lemma wit_sqr_lipschitz x y : -3%:R <= x <= 3%:R -> -3%:R <= y <= 3%:R ->
  `|F1 x ^+ 2 - F1 y ^+ 2| <= (2%:R * Fm) * `|x - y|.
Proof.
move=> /andP[_ x3] /andP[_ y3].
rewrite subr_sqr normrM [X in _ <= X]mulrC.
apply: ler_pM; [exact: normr_ge0 | exact: normr_ge0 | | ].
  by have := wit_lipschitz x y; rewrite mul1r.
rewrite (ger0_norm (addr_ge0 (wit_ge0 x) (wit_ge0 y))) mulr_natl mulr2n.
by apply: lerD; exact: wit_le.
Qed.

Lemma wit_id_lipschitz x y : -3%:R <= x <= 3%:R -> -3%:R <= y <= 3%:R ->
  `|x * F1 x - y * F1 y| <= (3%:R + Fm) * `|x - y|.
Proof.
move=> /andP[x3l x3u] /andP[_ y3].
have -> : x * F1 x - y * F1 y = x * (F1 x - F1 y) + (x - y) * F1 y by ring.
apply: le_trans (ler_normD _ _) _.
rewrite !normrM (ger0_norm (wit_ge0 y)) mulrDl.
apply: lerD.
  apply: ler_pM; [exact: normr_ge0 | exact: normr_ge0 | | ].
    by rewrite ler_norml; apply/andP; split.
  by have := wit_lipschitz x y; rewrite mul1r.
rewrite mulrC; apply: (ler_wpM2r (normr_ge0 _)); exact: wit_le.
Qed.

End wigner_inputs.

Section witness_measurable.
Variables (d : nat) (w c : R).

Lemma wit_conj : conj_equivariant (@wit_mx d w c).
Proof.
move=> Q W Qo Ws; rewrite /wit_mx.
have QQ : Q *m Q^T = 1%:M by apply/orthogonalmxP.
have cs (a : R) : Q *m a%:M *m Q^T = a%:M.
  by rewrite mul_mx_scalar -scalemxAl QQ scalemx1.
have Ws' : W - w%:M \is symmetricmx.
  have /symmetricmxP We := Ws.
  by apply/symmetricmxP; rewrite linearB /= tr_scalar_mx We.
rewrite -[w%:M in LHS](cs w) -mulmxBl -mulmxBr (psd_part_conj Ws' Qo).
by rewrite -[c%:M in LHS](cs c) -mulmxDl -mulmxDr.
Qed.

Lemma measurable_wit_goe : measurable_fun setT
  (fun a : 'rV[RR]_(d * d) => (wit_mx w c (goe_mx a) : 'M[RR]_d)).
Proof.
apply/measurable_fun_mxP => i j.
apply: continuous_measurable_mx.
apply: (@lipschitz_frobenius_continuous _ _ _ (Num.sqrt (2%:R / d%:R))) => a b.
have Wa := goe_mx_symmetric a; have Wb := goe_mx_symmetric b.
have sym (W : 'M[R]_d) : W \is symmetricmx -> W - w%:M \is symmetricmx.
  move=> /symmetricmxP We.
  by apply/symmetricmxP; rewrite linearB /= tr_scalar_mx We.
have e : wit_mx w c (goe_mx a) i j - wit_mx w c (goe_mx b) i j =
    (psd_part (goe_mx a - w%:M) - psd_part (goe_mx b - w%:M)) i j.
  by rewrite /wit_mx !mxE; ring.
rewrite e; apply: le_trans (entry_le_mx_norm _ i j) _.
apply: le_trans (mx_norm_le_frobenius _) _.
apply: le_trans (psd_part_nonexpansive (sym _ Wa) (sym _ Wb)) _.
have -> : goe_mx a - w%:M - (goe_mx b - w%:M) = goe_mx (a - b).
  by rewrite goe_mxB opprB addrA subrK.
exact: frobenius_goe_mx.
Qed.

End witness_measurable.

Section prob_helpers.
Context {RT : realType} {dT : measure_display} {T : measurableType dT}.
Variable P : probability T RT.

Lemma prob_union_le (A B : set T) (a b : RT) : measurable A -> measurable B ->
  (P A <= a%:E)%E -> (P B <= b%:E)%E -> (P (A `|` B) <= (a + b)%:E)%E.
Proof.
move=> mA mB hA hB; apply: le_trans (measureU2 P mA mB) _.
by rewrite EFinD; exact: leeD.
Qed.

Lemma prob_compl_ge (U E : set T) (e : RT) : measurable U -> measurable E ->
  ~` U `<=` E -> (P U <= e%:E)%E -> ((1 - e)%:E <= P E)%E.
Proof.
move=> mU mE UE hU.
have [u uE] : exists u : RT, P U = u%:E.
  exists (fine (P U)); rewrite fineK // ge0_fin_numE ?measure_ge0 //.
  by apply: le_lt_trans (probability_le1 P mU) _; rewrite ltry.
apply: (@le_trans _ _ (P (~` U))).
  rewrite probability_setC // uE -EFinB lee_fin lerD2l lerN2.
  by move: hU; rewrite uE lee_fin.
by apply: le_measure => //; rewrite inE //; exact: measurableC.
Qed.

End prob_helpers.

Section eventually.

Lemma exp_small (K : R) : 0 < K ->
  exists D : nat, forall d : nat, (D <= d)%N -> expR (- (K * d%:R)) <= 32%:R^-1.
Proof.
move=> K0; exists (truncn (32%:R / K)).+1 => d hd.
have hdK : 32%:R / K < d%:R.
  apply: lt_le_trans (truncnS_gt _) _; rewrite ler_nat; exact: hd.
have x0 : 0 < K * d%:R.
  by rewrite mulr_gt0 //; apply: le_lt_trans hdK; rewrite divr_ge0 // ltW.
rewrite expRN lef_pV2 ?posrE ?expR_gt0 //.
apply: le_trans (_ : 1 + K * d%:R <= _); last exact: expR_ge1Dx.
have : 32%:R < K * d%:R by rewrite mulrC -ltr_pdivrMr.
by lra.
Qed.

End eventually.

Section chi2_exponent.
Context {RT : realType}.

(* The exponent of the chi-square tail of |g|^2 - n at u = dl d^2. *)
Lemma chi2_exponent (al dl n d : RT) : 0 < dl -> 0 <= al -> 1 <= d ->
  0 <= n -> n <= (al + dl) * d ^+ 2 ->
  dl ^+ 2 / (4 * (al + 2 * dl)) * d <=
  (dl * d ^+ 2) ^+ 2 / (4 * (n + 1 * (dl * d ^+ 2))).
Proof.
move=> dl0 al0 d1 n0 hn.
have d0 : 0 < d by apply: lt_le_trans d1; exact: ltr01.
have u0 : 0 < dl * d ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have nu0 : 0 < 4 * (n + 1 * (dl * d ^+ 2)).
  by rewrite mulr_gt0 // mul1r ltr_wpDl.
have a20 : 0 < al + 2 * dl by lra.
set K := dl ^+ 2 / (4 * (al + 2 * dl)).
have K0 : 0 <= K by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
have KE : K * (4 * (al + 2 * dl)) = dl ^+ 2.
  by rewrite /K mulfVK // mulf_neq0 // gt_eqF.
rewrite ler_pdivlMr //.
have hnu : n + 1 * (dl * d ^+ 2) <= (al + 2 * dl) * d ^+ 2.
  by rewrite mul1r; nra.
have dd : d ^+ 3 <= d ^+ 4.
  by rewrite (exprS d 3) ler_peMl // exprn_ge0 // ltW.
have s1 : K * d * (4 * (n + 1 * (dl * d ^+ 2))) <=
    K * d * (4 * ((al + 2 * dl) * d ^+ 2)).
  apply: ler_wpM2l; first by rewrite mulr_ge0 // ltW.
  by apply: ler_wpM2l => //.
apply: le_trans s1 _.
have -> : K * d * (4 * ((al + 2 * dl) * d ^+ 2)) =
    (K * (4 * (al + 2 * dl))) * d ^+ 3 by ring.
rewrite KE.
have -> : (dl * d ^+ 2) ^+ 2 = dl ^+ 2 * d ^+ 4 by ring.
by apply: ler_wpM2l => //; exact: sqr_ge0.
Qed.

Lemma chi2_diag_exponent (x : RT) : 0 < x ->
  - x ^+ 2 / (4 * (x + 1 * x)) = - (8^-1 * x).
Proof.
move=> x0; have xn : x != 0 by rewrite gt_eqF.
have xx : x + x != 0 by rewrite gt_eqF // addr_gt0.
by field.
Qed.

End chi2_exponent.

Section goe_events.
Context {RT : realType}.

Lemma measurable_goe_dev d (f : RT -> RT) (I eps : RT) : continuous f ->
  measurable [set h : 'rV[RT]_(d * d) | eps <= `|goe_stat f h - I|].
Proof.
move=> cf; apply: measurable_ge_set.
apply: continuous_measurable_mx => a.
apply: (continuous_comp (continuousB (@continuous_goe_stat _ d _ cf a)
  (@cst_continuous _ _ I a))).
exact: norm_continuous.
Qed.

Lemma measurable_goe_opnorm d (b : RT) :
  measurable [set h : 'rV[RT]_(d * d) | b <= opnorm (goe_mx h)].
Proof.
apply: measurable_ge_set; apply: continuous_measurable_mx.
exact: (lipschitz_frobenius_continuous (@goe_opnorm_lipschitz RT d)).
Qed.

Lemma measurable_diag_var n : measurable_fun setT (@diag_var RT n).
Proof.
apply: measurable_funM; first exact: measurable_cst.
apply: measurable_sum => j; apply: measurable_funX.
apply: measurable_funB; first exact: measurable_mxentry.
apply: measurable_funM; last exact: measurable_cst.
by apply: measurable_sum => i; exact: measurable_mxentry.
Qed.

Lemma mxdot_const1 n : mxdot (const_mx 1 : 'rV[RT]_n) (const_mx 1) = n%:R.
Proof.
rewrite /mxdot big_ord1.
have -> : \sum_(i < n)
    (const_mx 1 : 'rV[RT]_n) 0 i * (const_mx 1 : 'rV[RT]_n) 0 i
    = \sum_(i < n) (1 : RT) by apply: eq_bigr => i _; rewrite !mxE mulr1.
by rewrite sumr_const card_ord.
Qed.

Lemma mxdot_mxvec1 d : mxdot (mxvec (1%:M : 'M[RT]_d)) (mxvec 1%:M) = d%:R.
Proof.
rewrite /mxdot big_ord1 sum_mxvec.
have -> : \sum_(i < d) \sum_(j < d)
    mxvec (1%:M : 'M[RT]_d) 0 (mxvec_index i j) *
    mxvec (1%:M : 'M[RT]_d) 0 (mxvec_index i j) = \sum_(i < d) (1 : RT).
  apply: eq_bigr => i _; rewrite (bigD1 i) //=.
  have -> : \sum_(j < d | j != i) mxvec (1%:M : 'M[RT]_d) 0 (mxvec_index i j) *
      mxvec (1%:M : 'M[RT]_d) 0 (mxvec_index i j) = 0.
    by apply: big1 => j ji; rewrite !mxvecE !mxE eq_sym (negPf ji) mulr0.
  by rewrite addr0 !mxvecE !mxE eqxx mulr1.
by rewrite sumr_const card_ord.
Qed.

End goe_events.

Section aux_zero.

Theorem aux_zero_eventually (kappa alpha : R) : 1 < kappa -> 0 < alpha ->
  alpha < universality_alpha_star kappa ->
  exists m0 M0 dl : R, [/\ 0 < m0, m0 <= 1, 1 <= M0, 0 < dl &
    exists D : nat, forall d n : nat, (D <= d)%N ->
      n%:R <= (alpha + dl) * d%:R ^+ 2 ->
      ((2^-1)%:E < gauss (n + d * d)
        [set z | cgmt_aux (tr_set (cone_rows d kappa m0 M0)) (lsubmx z)
          (rsubmx z) = 0%R])%E].
Proof.
move=> k1 a0 aast.
have [w [c [c0 A10 A30 hsc]]] := witness_scalar _ _ k1 a0 aast.
set sig2 := @semicircle_prob R 2%:R in A10 A30 hsc.
set A1 := \int[sig2]_x (ppart w x + c) in A10 hsc.
set A2 := \int[sig2]_x ((ppart w x + c) ^+ 2) in hsc.
set A3 := \int[sig2]_x (x * (ppart w x + c)) in A30 hsc.
set ck := cone_shift kappa in hsc.
set c1 := 1 + `|ck| * (2%:R * A1 + 2%:R).
have c10 : 0 <= c1.
  by rewrite addr_ge0 // mulr_ge0 // addr_ge0 // mulr_ge0 // ltW.
have [dl [dl0 dl1 dlA1 A3dl hP]] :=
  choose_delta alpha (A2 + ck * A1 ^+ 2) c1 A1 A3 a0 c10 A10 A30 hsc.
exists (wit_lo c A1), (wit_hi w c A1), dl; split => //.
- by rewrite /wit_lo lt_min ltr01 divr_gt0 // mulr_gt0.
- by rewrite /wit_lo ge_min lexx.
- by rewrite /wit_hi le_max lexx.
set eps := Num.min dl 32%:R^-1.
have eps0 : 0 < eps by rewrite lt_min dl0 invr_gt0 ltr0n.
have epsd : eps <= dl by rewrite ge_min lexx.
have eps32 : eps <= 32%:R^-1 by rewrite ge_min lexx orbT.
have [D1 hw1] := wigner (continuous_wit w c)
  (fun x y _ _ => wit_lipschitz w c x y) eps0.
have [D2 hw2] := wigner (continuous_wit_sqr w c)
  (wit_sqr_lipschitz w c (ltW c0)) eps0.
have [D3 hw3] := wigner (continuous_wit_id w c)
  (wit_id_lipschitz w c (ltW c0)) eps0.
have s3 : 2 * Num.sqrt 2 < 3%:R :> R.
  have h : Num.sqrt 2 < 3%:R / 2%:R :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 //.
    by rewrite sqr_sqrtr // expr_div_n; lra.
  by lra.
have i32 : 0 < 32%:R^-1 :> R by rewrite invr_gt0 ltr0n.
have [D4 hop] := goe_opnorm_tail_small s3 i32.
set Kg := dl ^+ 2 / (4%:R * (alpha + 2%:R * dl)).
have Kg0 : 0 < Kg by rewrite divr_gt0 ?exprn_gt0 // mulr_gt0 //; lra.
have [D5 hKg] := exp_small _ Kg0.
have i8 : 0 < 8%:R^-1 :> R by rewrite invr_gt0 ltr0n.
have [D6 hK8] := exp_small _ i8.
set sk := Num.sqrt ((kappa - 1) / 2%:R).
set X := Num.max (64%:R * (`|A2| + 1) / dl)
  (4%:R * `|sk - 1| ^+ 2 * (A2 + 1) / dl ^+ 2).
exists (maxn (maxn D1 D2)
  (maxn (maxn D3 D4) (maxn (maxn D5 D6) (truncn X).+1))).
move=> d n; rewrite !geq_max.
move=> /andP[/andP[d1 d2] /andP[/andP[d3 d4] /andP[/andP[d5 d6] d7]]] hn.
have dX : X < d%:R.
  by apply: lt_le_trans (truncnS_gt X) _; rewrite ler_nat.
have d0 : (0 < d)%N by apply: leq_trans d7.
have dd0 : 0 < d%:R :> R by rewrite ltr0n.
have d1R : 1 <= d%:R :> R by rewrite ler1n.
(* the event of g *)
pose Sg := [set g : 'rV[RR]_n |
  (dl * d%:R ^+ 2 <= centered_chi2 (const_mx 1) g)%R].
have mSg : measurable Sg := measurable_ge_set _ _ (measurable_centered_chi2 _).
have PSg : (gauss n Sg <= (32%:R^-1)%:E)%E.
  have u0 : 0 < dl * d%:R ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
  have a1 : forall i : 'I_n, `|(const_mx 1 : 'rV[RR]_n) 0 i| <= 1.
    by move=> i; rewrite mxE normr1.
  have nu : 0 < mxdot (const_mx 1 : 'rV[RR]_n) (const_mx 1) +
      1 * (dl * d%:R ^+ 2).
    by rewrite mxdot_const1 mul1r ltr_wpDl // ler0n.
  apply: le_trans (gauss_centered_chi2_upper_tail ler01 a1 u0 nu) _.
  rewrite lee_fin mxdot_const1; apply: le_trans (hKg d d5).
  rewrite ler_expR mulNr lerN2.
  exact: (chi2_exponent alpha dl n%:R d%:R dl0 (ltW a0) d1R (ler0n _ n) hn).
(* the events of h *)
pose Sop := [set h : 'rV[RR]_(d * d) | (3%:R <= opnorm (goe_mx h))%R].
have mSop : measurable Sop := measurable_goe_opnorm _ _.
have PSop : (gauss (d * d) Sop <= (32%:R^-1)%:E)%E := hop d d4.
pose S1 := [set h : 'rV[RR]_(d * d) |
  (eps <= `|goe_stat (wit_fun w c) h - A1|)%R].
have mS1 : measurable S1 := measurable_goe_dev _ _ _ _ (continuous_wit w c).
have PS1 : (gauss (d * d) S1 <= (32%:R^-1)%:E)%E.
  by apply: le_trans (hw1 d d1) _; rewrite lee_fin.
pose S2 := [set h : 'rV[RR]_(d * d) |
  (eps <= `|goe_stat (fun x => wit_fun w c x ^+ 2) h - A2|)%R].
have mS2 : measurable S2 := measurable_goe_dev _ _ _ _ (continuous_wit_sqr w c).
have PS2 : (gauss (d * d) S2 <= (32%:R^-1)%:E)%E.
  by apply: le_trans (hw2 d d2) _; rewrite lee_fin.
pose S3 := [set h : 'rV[RR]_(d * d) |
  (eps <= `|goe_stat (fun x => x * wit_fun w c x) h - A3|)%R].
have mS3 : measurable S3 := measurable_goe_dev _ _ _ _ (continuous_wit_id w c).
have PS3 : (gauss (d * d) S3 <= (32%:R^-1)%:E)%E.
  by apply: le_trans (hw3 d d3) _; rewrite lee_fin.
pose Sd := [set h : 'rV[RR]_(d * d) |
  (d%:R <= centered_chi2 (mxvec (1%:M : 'M[R]_d)) h)%R].
have mSd : measurable Sd := measurable_ge_set _ _ (measurable_centered_chi2 _).
have PSd : (gauss (d * d) Sd <= (32%:R^-1)%:E)%E.
  have a1 : forall k : 'I_(d * d),
      `|(mxvec (1%:M : 'M[RR]_d)) 0 k| <= 1.
    move=> k; case/mxvec_indexP: k => i j; rewrite mxvecE mxE.
    by case: eqP; rewrite ?normr1 ?normr0 // ler01.
  have nu : 0 < mxdot (mxvec (1%:M : 'M[RR]_d)) (mxvec 1%:M) + 1 * d%:R.
    by rewrite mxdot_mxvec1 mul1r addr_gt0.
  apply: le_trans (gauss_centered_chi2_upper_tail ler01 a1 dd0 nu) _.
  rewrite lee_fin mxdot_mxvec1; apply: le_trans (hK8 d d6).
  by rewrite (chi2_diag_exponent _ dd0).
pose Sv := [set h : 'rV[RR]_(d * d) |
  (dl <= diag_var (wit_mx w c (goe_mx h)))%R].
have mF := measurable_wit_goe d w c.
have mSv : measurable Sv.
  exact: measurable_ge_set _ _ (measurableT_comp (measurable_diag_var _) mF).
have PSv : (gauss (d * d) Sv <= (32%:R^-1 + 32%:R^-1)%:E)%E.
  set C := `|A2| + 1.
  have C0 : 0 <= C by rewrite addr_ge0.
  have := goe_diag_var_tail (wit_conj d w c) (wit_sym d w c) mF C0 dl0.
  move/le_trans; apply; rewrite EFinD; apply: leeD.
    have hX1 : 64%:R * C / dl < d%:R.
      by apply: le_lt_trans dX; rewrite le_max lexx.
    have h64 : 64%:R * C < d%:R * dl by rewrite -ltr_pdivrMr.
    rewrite lee_fin ler_pdivrMr ?mulr_gt0 ?addr_gt0 //.
    by nra.
  have mN : measurable_fun setT (fun a : 'rV[RR]_(d * d) =>
      mxdot (wit_mx w c (goe_mx a)) (wit_mx w c (goe_mx a)) : RR).
    rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
    by apply: measurable_funM; exact: ((measurable_fun_mxP _).1 mF i j).
  apply: le_trans _ PS2; apply: le_measure; rewrite ?inE //.
    exact: measurable_gt_set _ _ mN.
  move=> a /= hC.
  have Wa := goe_mx_symmetric a.
  have e : mxdot (wit_mx w c (goe_mx a)) (wit_mx w c (goe_mx a)) =
      d%:R * goe_stat (fun x => wit_fun w c x ^+ 2) a.
    rewrite (wit_frobenius _ _ _ _ Wa).
    by rewrite (goe_stat_sum d (fun x => wit_fun w c x ^+ 2)).
  rewrite e mulrC ltr_pM2l // in hC.
  apply: le_trans (_ : 1 <= _).
    have h32 : (0 : R) < 32%:R by rewrite ltr0n.
    by apply: le_trans eps32 _; rewrite (invf_le1 h32) ler1n.
  apply: le_trans (ler_norm _); rewrite /C in hC.
  by have := ler_norm A2; lra.
(* the events of z *)
pose Lr (S : set 'rV[RR]_(d * d)) := @rsubmx RR 1 n (d * d) @^-1` S.
have mLr (S : set 'rV[RR]_(d * d)) : measurable S -> measurable (Lr S).
  by move=> mS; rewrite -[X in measurable X]setTI; exact: measurable_rsubmx.
have PLr (S : set 'rV[RR]_(d * d)) (b : R) : measurable S ->
    (gauss (d * d) S <= b%:E)%E -> (gauss (n + d * d) (Lr S) <= b%:E)%E.
  by move=> mS hS; rewrite /Lr (gauss_rsubmx n mS).
pose Lg := @lsubmx RR 1 n (d * d) @^-1` Sg.
have mLg : measurable Lg.
  by rewrite -[X in measurable X]setTI; exact: measurable_lsubmx.
have PLg : (gauss (n + d * d) Lg <= (32%:R^-1)%:E)%E.
  by rewrite /Lg (gauss_lsubmx (d * d) mSg).
set e := 32%:R^-1 : R.
pose U := Lg `|` (Lr Sop `|` (Lr S1 `|` (Lr S2 `|` (Lr S3 `|`
  (Lr Sd `|` Lr Sv))))).
have m6 := measurableU _ _ (mLr _ mSd) (mLr _ mSv).
have m5 := measurableU _ _ (mLr _ mS3) m6.
have m4 := measurableU _ _ (mLr _ mS2) m5.
have m3 := measurableU _ _ (mLr _ mS1) m4.
have m2 := measurableU _ _ (mLr _ mSop) m3.
have mU : measurable U := measurableU _ _ mLg m2.
have PU : (gauss (n + d * d) U <=
    (e + (e + (e + (e + (e + (e + (e + e)))))))%:E)%E.
  apply: (prob_union_le _ _ _ _ _ mLg m2 PLg).
  apply: (prob_union_le _ _ _ _ _ (mLr _ mSop) m3 (PLr _ _ mSop PSop)).
  apply: (prob_union_le _ _ _ _ _ (mLr _ mS1) m4 (PLr _ _ mS1 PS1)).
  apply: (prob_union_le _ _ _ _ _ (mLr _ mS2) m5 (PLr _ _ mS2 PS2)).
  apply: (prob_union_le _ _ _ _ _ (mLr _ mS3) m6 (PLr _ _ mS3 PS3)).
  apply: (prob_union_le _ _ _ _ _ (mLr _ mSd) (mLr _ mSv) (PLr _ _ mSd PSd)).
  exact: (PLr _ _ mSv PSv).
set K := tr_set (cone_rows d kappa (wit_lo c A1) (wit_hi w c A1)).
have wl0 : 0 <= wit_lo c A1.
  by rewrite /wit_lo le_min ler01 divr_ge0 // ?mulr_ge0 // ltW.
have wl1 : wit_lo c A1 <= 1 by rewrite /wit_lo ge_min lexx.
have wh1 : 1 <= wit_hi w c A1 by rewrite /wit_hi le_max lexx.
have K0 : K !=set0 := tr_set_neq0 (cone_rows_neq0 d kappa _ _ wl1 wh1).
have Kb := tr_set_bounded
  (cone_rows_bounded d kappa (wit_lo c A1) (wit_hi w c A1) wl0).
have mE : measurable [set z : 'rV[RR]_(n + d * d) |
    cgmt_aux K (lsubmx z) (rsubmx z) = 0%R].
  exact: measurable_eq_set _ _ (measurable_cgmt_aux (N := n) K0 Kb).
have UE : ~` U `<=` [set z : 'rV[RR]_(n + d * d) |
    cgmt_aux K (lsubmx z) (rsubmx z) = 0%R].
  move=> z /= hz.
  have ng : ~ Sg (lsubmx z) by move=> h; apply: hz; left.
  have nop : ~ Sop (rsubmx z) by move=> h; apply: hz; right; left.
  have n1 : ~ S1 (rsubmx z) by move=> h; apply: hz; right; right; left.
  have n2 : ~ S2 (rsubmx z) by move=> h; apply: hz; do 3 right; left.
  have n3 : ~ S3 (rsubmx z) by move=> h; apply: hz; do 4 right; left.
  have nd : ~ Sd (rsubmx z) by move=> h; apply: hz; do 5 right; left.
  have nv : ~ Sv (rsubmx z) by move=> h; apply: hz; do 6 right.
  have lt_of (a b : R) : ~ (a <= b) -> b < a.
    by move=> h; rewrite ltNge; apply/negP.
  set g := lsubmx z; set h := rsubmx z.
  have hop' : opnorm (goe_mx h) < 3%:R := lt_of _ _ nop.
  have h1' : `|goe_stat (wit_fun w c) h - A1| < dl.
    exact: lt_le_trans (lt_of _ _ n1) epsd.
  have h2' : `|goe_stat (fun x => wit_fun w c x ^+ 2) h - A2| < dl.
    exact: lt_le_trans (lt_of _ _ n2) epsd.
  have h3' : `|goe_stat (fun x => x * wit_fun w c x) h - A3| < dl.
    exact: lt_le_trans (lt_of _ _ n3) epsd.
  have hdiag : \sum_j h 0 (mxvec_index j j) ^+ 2 <= 2%:R * d%:R.
    by have := lt_of _ _ nd; rewrite centered_chi2_diag => hh; lra.
  have hdv : diag_var (wit_mx w c (goe_mx h)) < dl := lt_of _ _ nv.
  have hg : mxdot g g <= (alpha + 2%:R * dl) * d%:R ^+ 2.
    by have := lt_of _ _ ng; rewrite centered_chi2_const1 => hh; lra.
  have a2 : 0 <= alpha + 2%:R * dl by lra.
  have hD : 4%:R * `|sk - 1| ^+ 2 * (A2 + 1) <= dl ^+ 2 * d%:R.
    have hX2 : 4%:R * `|sk - 1| ^+ 2 * (A2 + 1) / dl ^+ 2 < d%:R.
      by apply: le_lt_trans dX; rewrite le_max lexx orbT.
    have dl2 : 0 < dl ^+ 2 by exact: exprn_gt0.
    by rewrite [dl ^+ 2 * _]mulrC; apply: ltW; rewrite -ltr_pdivrMr.
  exact: (witness_aux_zero kappa n d w c A1 A2 A3 alpha dl g h k1 d0 c0 A10
    hop' h1' h2' h3' hdiag hdv hg dl0 dl1 dlA1 A3dl a2 hP hD).
apply: lt_le_trans (prob_compl_ge _ _ _ _ mU mE UE PU).
rewrite lte_fin /e; lra.
Qed.

End aux_zero.

Section final_helpers.

Lemma exp_small_eps (K e : R) : 0 < K -> 0 < e ->
  exists D : nat, forall d : nat, (D <= d)%N -> expR (- (K * d%:R)) <= e.
Proof.
move=> K0 e0; exists (truncn (e^-1 / K)).+1 => d hd.
have hdK : e^-1 / K < d%:R.
  apply: lt_le_trans (truncnS_gt _) _; rewrite ler_nat; exact: hd.
have x0 : 0 < K * d%:R.
  rewrite mulr_gt0 //; apply: le_lt_trans hdK.
  by rewrite divr_ge0 // ?invr_ge0 ltW.
rewrite expRN -[e]invrK lef_pV2 ?posrE ?invr_gt0 ?expR_gt0 //.
apply: le_trans (_ : 1 + K * d%:R <= _); last exact: expR_ge1Dx.
have : e^-1 < K * d%:R by rewrite mulrC -ltr_pdivrMr.
by lra.
Qed.

(* sqrt (d (d + 1) / 2 - 1) >= sqrt (1/2) d for d >= 2. *)
Lemma sqrt_trace_ge (d : nat) : (2 <= d)%N ->
  Num.sqrt 2%:R^-1 * d%:R <= Num.sqrt ((d * d.+1)%:R / 2%:R - 1) :> R.
Proof.
move=> d2; have d2R : 2%:R <= d%:R :> R by rewrite ler_nat.
have dsq : d%:R = Num.sqrt (d%:R ^+ 2) :> R.
  by rewrite sqrtr_sqr ger0_norm ?ler0n.
have i2 : 0 <= 2%:R^-1 :> R by rewrite invr_ge0 ler0n.
rewrite [X in _ * X <= _]dsq -(sqrtrM _ i2).
apply: ler_wsqrtr; rewrite natrM -[d.+1%:R]natr1.
have -> : d%:R * (d%:R + 1) / 2%:R - 1 = 2%:R^-1 * d%:R ^+ 2 +
    (d%:R / 2%:R - 1) :> R by field.
rewrite lerDl subr_ge0 ler_pdivlMr //; lra.
Qed.

Section final_arith.
Context {RT : realType}.

Lemma half_gap (al t : RT) : al < 2^-1 -> t <= (2^-1 - al) / 2 ->
  al + t < 2^-1.
Proof. by move=> h1 h2; lra. Qed.

(* sqrt T - sqrt n - c d >= c d when sqrt T >= s d, sqrt n <= r d and
   s - r = 2 c. *)
Lemma margin_lower (sT sn s r c d : RT) : s * d <= sT -> sn <= r * d ->
  2 * c = s - r -> c * d <= sT - sn - c * d.
Proof.
move=> h1 h2 h3.
have h4 : 2 * c * d = s * d - r * d by rewrite h3 mulrBl.
lra.
Qed.

(* the density gives n <= a d^2 and n > 0 *)
Lemma density_bounds (nd d2 al tol t : RT) : 0 < d2 -> 0 < al ->
  tol <= t -> tol <= al / 2 -> `|nd / d2 - al| < tol ->
  nd <= (al + t) * d2 /\ 0 < nd.
Proof.
move=> d20 a0 tt ta; rewrite ltr_distl => /andP[h1 h2]; split.
  have h3 : nd / d2 < al + t by lra.
  by move: h3; rewrite ltr_pdivrMr // => /ltW.
have h3 : 0 < nd / d2 by lra.
by move: h3; rewrite pmulr_lgt0 // invr_gt0.
Qed.

Lemma exp_margin_le (c d : RT) : 1 <= d ->
  - (c * d) ^+ 2 / 2 <= - (c ^+ 2 / 2 * d).
Proof.
move=> d1; have dd : d <= d ^+ 2.
  by rewrite expr2 ler_peMl // (le_trans ler01 d1).
have c2 := sqr_ge0 c.
by rewrite mulNr lerN2 exprMn; nra.
Qed.

Lemma radius_le (x M K cp d : RT) : 0 < cp -> 0 < d ->
  x ^+ 2 * M * K ^+ 2 / cp ^+ 2 < d ->
  x ^+ 2 * (M * d) * K ^+ 2 <= cp ^+ 2 * d ^+ 2.
Proof.
move=> cp0 d0; rewrite ltr_pdivrMr ?exprn_gt0 // => h.
have e1 : x ^+ 2 * (M * d) * K ^+ 2 = x ^+ 2 * M * K ^+ 2 * d by ring.
have e2 : cp ^+ 2 * d ^+ 2 = d * cp ^+ 2 * d by ring.
by rewrite e1 e2; exact: (ler_wpM2r (ltW d0) (ltW h)).
Qed.

End final_arith.

End final_helpers.

Section final.

Lemma row_form d (S : 'M[R]_d) (v : 'rV[R]_d) : S \is symmetricmx ->
  mxdot v (v *m S) = mxdot v^T (S *m v^T).
Proof. by move=> /symmetricmxP Ss; rewrite -mxdot_trmx trmx_mul Ss. Qed.

(* Lemma 5.17 (Proposition 1.4 (i)), in the form of the Gaussian
   hypothesis of the approximate fit of the satisfiable phase: a bad event
   of probability at most eps outside of which an exact fit with
   m0 I <= S <= M0 I and trace d exists. *)
Theorem gaussian_fit_below_threshold (kappa alpha : R) : 1 < kappa ->
  0 < alpha -> alpha < universality_alpha_star kappa ->
  exists m0 M0 : R, [/\ 0 < m0, m0 <= M0 &
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d : nat, (D <= d)%N ->
  exists E : set ((n d).-tuple 'rV[RR]_(d * d)), [/\ measurable E,
    (tuple_prod (fun=> gaussian_feature_law kappa d) (n d) E <= eps%:E)%E &
    forall Z, ~ E Z -> exists S : 'M[R]_d, [/\ S \is symmetricmx,
      forall v : 'rV[R]_d,
        m0 * mxdot v v <= mxdot v (v *m S) <= M0 * mxdot v v,
      \tr S = d%:R &
      forall i, mxdot (tnth Z i) (mxvec S) = 0]]].
Proof.
move=> k1 a0 aast.
have [m1 [M1 [dl [m10 m11 M11 dl0 [D0 haux]]]]] :=
  aux_zero_eventually _ _ k1 a0 aast.
exists (m1 / 3%:R), (2%:R * M1 + m1); split.
- by rewrite divr_gt0 // ltr0n.
- by lra.
move=> n hn eps eps0.
set e : R := (Num.min eps 1)%R.
have e0 : 0 < e by rewrite lt_min eps0 ltr01.
have e1 : e <= 1 by rewrite ge_min lexx orbT.
have ee : e <= eps by rewrite ge_min lexx.
have ahalf : alpha < 2%:R^-1.
  have /andP[_ h] := universality_alpha_star_lt _ k1.
  exact: lt_trans aast h.
set dlp : R := (Num.min dl ((2%:R^-1 - alpha) / 2%:R))%R.
have dlp0 : 0 < dlp by rewrite lt_min dl0 divr_gt0 // subr_gt0.
have dlpdl : dlp <= dl by rewrite ge_min lexx.
have dlph : dlp <= (2%:R^-1 - alpha) / 2%:R by rewrite ge_min lexx orbT.
set tol : R := (Num.min dlp (alpha / 2%:R))%R.
have tol0 : 0 < tol by rewrite lt_min dlp0 divr_gt0.
have toldl : tol <= dlp by rewrite ge_min lexx.
have tola : tol <= alpha / 2%:R by rewrite ge_min lexx orbT.
have [Dn hdn] := hn tol tol0.
set a : R := (alpha + dlp)%R.
have a_lt : a < 2%:R^-1 by exact: half_gap ahalf dlph.
have a_ge : 0 <= a by rewrite /a addr_ge0 // ltW.
set c : R := ((Num.sqrt 2%:R^-1 - Num.sqrt a) / 2%:R)%R.
have h2 : 0 < 2%:R^-1 :> R by rewrite invr_gt0 ltr0n.
have c0 : 0 < c by rewrite /c divr_gt0 // subr_gt0 (ltr_sqrt _ h2).
set sk : R := (Num.sqrt ((kappa - 1) / 2%:R))%R.
have sk0 : 0 < sk by rewrite sqrtr_gt0 divr_gt0 // subr_gt0.
set mk : R := (Num.min 1 sk)%R.
have mk0 : 0 < mk by rewrite lt_min ltr01 sk0.
set mm : R := (Num.min (m1 / 2%:R) 2%:R^-1)%R.
have mm0 : 0 < mm by rewrite lt_min divr_gt0 // invr_gt0 ltr0n.
set Ke : R := (1 + 2 * Num.sqrt (ln 4) + Num.sqrt (2%:R * ln (4%:R / e)))%R.
have Ke0 : 0 <= Ke.
  have s1 : 0 <= 2 * Num.sqrt (ln 4 : R).
    by apply: mulr_ge0; [exact: ler0n | exact: sqrtr_ge0].
  have s2 := sqrtr_ge0 (2%:R * ln (4%:R / e)).
  by rewrite /Ke; apply: addr_ge0 => //; apply: addr_ge0 => //; exact: ler01.
set cp : R := (mk * c * mm)%R.
have cp0 : 0 < cp by rewrite /cp; apply: mulr_gt0 => //; exact: mulr_gt0.
have ck0 : 0 < c ^+ 2 / 2%:R.
  by apply: divr_gt0; [exact: exprn_gt0 | exact: ltr0Sn].
have e20 : 0 < e / 2%:R by apply: divr_gt0 => //; exact: ltr0Sn.
have [Dm hm] := exp_small_eps (c ^+ 2 / 2%:R) (e / 2%:R) ck0 e20.
set B1 : R := (Num.max 1 sk ^+ 2 * M1 * Ke ^+ 2 / cp ^+ 2)%R.
exists (maxn (maxn D0 Dn) (maxn (maxn Dm 2) (truncn B1).+1)).
move=> d; rewrite !geq_max.
move=> /andP[/andP[hd0 hdn'] /andP[/andP[hdm hd2] hdr]].
have d0 : (0 < d)%N by apply: leq_trans hd2.
have dR : 0 < d%:R :> R by rewrite ltr0n.
have d1R : 1 <= d%:R :> R by rewrite ler1n.
have d2R : 0 < d%:R ^+ 2 :> R by rewrite exprn_gt0.
have [hnu hnpos] := density_bounds (n d)%:R (d%:R ^+ 2) alpha tol dlp d2R a0
  toldl tola (hdn d hdn').
have hn0 : (0 < n d)%N by move: hnpos; rewrite ltr0n.
have hn_aux : (n d)%:R <= (alpha + dl) * d%:R ^+ 2.
  apply: le_trans hnu _; apply: (ler_wpM2r (ltW d2R)).
  by rewrite lerD2l.
have hP := haux d (n d) hd0 hn_aux.
(* the margin *)
set u : R := (c * d%:R)%R.
have u0 : 0 <= u by rewrite /u mulr_ge0 // ltW.
have sigA_ge : c * d%:R <=
    Num.sqrt ((d * d.+1)%:R / 2%:R - 1) - Num.sqrt (n d)%:R - u.
  have g1 := sqrt_trace_ge _ hd2.
  have g2 : Num.sqrt (n d)%:R <= Num.sqrt a * d%:R.
    have e2 : Num.sqrt a * d%:R = Num.sqrt (a * d%:R ^+ 2).
      by rewrite (sqrtrM _ a_ge) sqrtr_sqr (ger0_norm (ler0n _ d)).
    by rewrite e2; exact: ler_wsqrtr hnu.
  have e2c : 2 * c = Num.sqrt 2%:R^-1 - Num.sqrt a.
    by rewrite /c mulrC divfK // pnatr_eq0.
  exact: (margin_lower _ _ _ _ _ _ g1 g2 e2c).
(* the CGMT *)
set rho : R := (cone_slice_radius kappa M1 d)%R.
have M10 : 0 < M1 by apply: lt_le_trans M11; exact: ltr01.
have rho0 : 0 < rho.
  rewrite /rho /cone_slice_radius; apply: mulr_gt0.
    by rewrite lt_max ltr01.
  by rewrite sqrtr_gt0 mulr_gt0.
set u' : R := (rho * Num.sqrt (2%:R * ln (4%:R / e)))%R.
have lne : 0 <= ln (4%:R / e) :> R.
  apply: ln_ge0; rewrite ler_pdivlMr // mul1r; apply: le_trans e1 _.
  by rewrite ler1n.
have u'0 : 0 <= u' by rewrite /u' mulr_ge0 ?sqrtr_ge0 // ltW.
set rA : R := (rho * (1 + 2 * Num.sqrt (ln 4)) + u')%R.
set sZ : R := (Num.sqrt (2%:R / d%:R))%R.
have sZ0 : 0 < sZ by rewrite /sZ sqrtr_gt0 divr_gt0 // ltr0n.
set sigZ : R := (sZ * mk * (c * d%:R))%R.
have sigZ0 : 0 < sigZ.
  by rewrite /sigZ; apply: mulr_gt0; [exact: mulr_gt0 | exact: mulr_gt0].
set rZ : R := (sZ * rA)%R.
have hB1 : B1 < d%:R.
  by apply: lt_le_trans (truncnS_gt _) _; rewrite ler_nat.
have hrA : rA <= cp * d%:R.
  have rAE : rA = rho * Ke by rewrite /Ke mulrDr.
  have l0 : 0 <= rho * Ke by rewrite mulr_ge0 // ltW.
  have r0 : 0 <= cp * d%:R by rewrite mulr_ge0 // ltW.
  have Md : 0 <= M1 * d%:R by rewrite mulr_ge0 // ltW.
  rewrite rAE -(@ler_pXn2r _ 2) ?nnegrE // [(rho * Ke) ^+ 2]exprMn.
  rewrite [(cp * _) ^+ 2]exprMn /rho /cone_slice_radius.
  rewrite [(Num.max _ _ * _) ^+ 2]exprMn (sqr_sqrtr Md).
  exact: (radius_le _ _ _ _ _ cp0 dR hB1).
(* the two bad events of the Gaussian rows *)
pose Bm := [set a : (n d).-tuple 'rV[RR]_(d * d) | (sym_margin (tuple_mx a) <=
  Num.sqrt ((d * d.+1)%:R / 2%:R - 1) - Num.sqrt (n d)%:R - u)%R].
pose Ba := [set a : (n d).-tuple 'rV[RR]_(d * d) |
  (cone_slice_radius kappa M1 d * (1 + 2 * Num.sqrt (ln 4)) + u' <=
   escape_inf (tr_set (cone_rows d kappa m1 M1)) (tuple_mx a))%R].
have mBm : measurable Bm.
  exact: measurable_le_set _ _ (measurable_sym_margin _ _ hn0).
have mBa : measurable Ba.
  exact: measurable_ge_set _ _ (measurable_approx _ _ _ _ _ (ltW m10) m11 M11).
have PBm : (tuple_prod (fun=> gauss (d * d)) (n d) Bm <= (e / 2%:R)%:E)%E.
  apply: le_trans (margin_tail _ _ _ hn0 d0 u0) _.
  rewrite lee_fin; apply: le_trans (hm d hdm).
  by rewrite ler_expR /u; exact: exp_margin_le.
have PBa : (tuple_prod (fun=> gauss (d * d)) (n d) Ba <= (e / 2%:R)%:E)%E.
  apply: le_trans
    (approx_tail _ _ _ _ _ _ k1 hn0 d0 (ltW m10) m11 M11 u'0 hP) _.
  have rn : rho != 0 by rewrite gt_eqF.
  have eu : u' ^+ 2 / (2 * cone_slice_radius kappa M1 d ^+ 2) = ln (4%:R / e).
    rewrite -/rho /u' exprMn sqr_sqrtr ?mulr_ge0 ?ler0n //.
    by field.
  have e4 : (0 : R) < 4%:R / e by rewrite divr_gt0 // ltr0n.
  rewrite lee_fin mulNr eu expRN (lnK e4).
  have en : e != 0 by rewrite gt_eqF.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have PU : (tuple_prod (fun=> gauss (d * d)) (n d) (Bm `|` Ba) <= eps%:E)%E.
  apply: le_trans (prob_union_le _ _ _ _ _ mBm mBa PBm PBa) _.
  have ee2 : e / 2%:R + e / 2%:R = e by field.
  by rewrite lee_fin ee2.
(* the good event of the features *)
pose Eg1 := [set Z : (n d).-tuple 'rV[RR]_(d * d) |
  sigZ <= sym_margin (tuple_mx Z)].
pose Eg2 := [set Z : (n d).-tuple 'rV[RR]_(d * d) |
  escape_inf (tr_set (cone_rows d 3%:R m1 M1)) (tuple_mx Z) < rZ].
pose Eg := Eg1 `&` Eg2.
have mg1 : measurable Eg1.
  exact: measurable_ge_set _ _ (measurable_sym_margin _ _ hn0).
have mg2 : measurable Eg2.
  exact: measurable_lt_set _ _
    (measurable_approx _ _ 3%:R m1 M1 (ltW m10) m11 M11).
have mEg : measurable Eg := measurableI _ _ mg1 mg2.
have lt_of (x y : R) : ~ (x <= y) -> y < x.
  by move=> h; rewrite ltNge; apply/negP.
exists (~` Eg); split.
- exact: measurableC.
- have mug : forall (i : nat) (B : set 'rV[RR]_(d * d)), measurable B ->
      gaussian_feature_law kappa d B =
      gauss (d * d) (gaussian_feature_vec kappa d @^-1` B) by [].
  rewrite (tuple_prod_map (fun=> measurable_gaussian_feature_vec kappa d) mug
    (measurableC mEg)).
  apply: le_trans PU; apply: le_measure; rewrite ?inE.
  + rewrite -[X in measurable X]setTI.
    exact: (measurable_tuple_map (fun=> measurable_gaussian_feature_vec kappa d)
      measurableT (measurableC mEg)).
  + exact: measurableU.
  move=> t /= hnt; apply: contrapT => hU; apply: hnt.
  have nBm : ~ Bm t by move=> h; apply: hU; left.
  have nBa : ~ Ba t by move=> h; apply: hU; right.
  split.
    apply: le_trans (sym_margin_feature _ _ kappa t hn0).
    apply: (ler_wpM2l (mulr_ge0 (ltW sZ0) (ltW mk0))).
    exact: le_trans sigA_ge (ltW (lt_of _ _ nBm)).
  exact: (approx_feature _ _ _ t m1 M1 rA d0 m11 M11 (lt_of _ _ nBa)).
move=> Z hZ; have hE : Eg Z by apply: contrapT.
case: hE => z1 z2.
have hr : rZ <= sigZ * mm.
  have -> : sigZ * mm = sZ * (cp * d%:R).
    rewrite /sigZ /cp; move: (sZ) (mk) (c) (mm) (d%:R) => x1 x2 x3 x4 x5.
    ring.
  exact: (ler_wpM2l (ltW sZ0) hrA).
have [S Ss [Sm SM Str SZ]] :=
  exact_fit_of_margin _ _ Z m1 M1 sigZ rZ d0 m10 m11 M11 sigZ0 hr z1 z2.
exists S; split => // v.
rewrite (row_form _ _ _ Ss) -(mxdot_trmx v v).
by apply/andP; split; [exact: Sm | exact: SM].
Qed.

End final.
