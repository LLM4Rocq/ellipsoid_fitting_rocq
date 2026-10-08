(* The well-conditioned exact fit of the Gaussian model below the threshold:
   Lemma 5.17 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372, lines 6111-6190 of
   arxiv_v1.tex), which is Proposition 1.4 (i). Item G9 of stage 2 of
   phase 5 (lane B), at Stdlib's R.

   Statement. Let 1 < kappa and 0 < alpha < alpha*(kappa), and let n / d^2
   tend to alpha. There are 0 < m <= M, depending only on alpha and kappa,
   such that with probability tending to one, for Z of law
   tuple_prod (fun=> gaussian_feature_law kappa d) n, some symmetric S has
   m I <= S <= M I, tr S = d and <Z_i, mxvec S> = 0 for every i; then the
   values <Z_i, S> are all equal, which is the fit A_{G,kappa} S = 0 of the
   Gaussian model.

   Route. The paper shows that Phi = inf_K |A T_kappa S| tends to 0 in
   probability, for an i.i.d. Gaussian matrix A and K the slice of the
   matrices with m I <= S <= M I and tr S = d; that alone does not give an
   exact fit. Here the approximate fit is corrected.
   1. The model. For S symmetric, <Z(a), mxvec S> is
      <a, mxvec (sqrt (2/d) T_kappa S)> (gaussian_feature_vec_dot,
      Gaussian/Representation), and n independent rows a_i of law
      gauss (d * d) form a Gaussian matrix A (gauss_tuple_mx of
      library/comparison/gauss_matrix_law.v).
   2. The approximate fit. The auxiliary value of the CGMT for
      K = {mxvec (T_kappa S) | S in the slice} vanishes with probability
      tending to one: the witness is S_q, proportional to
      psd_part (W - w I) + c I for the GOE matrix W of the auxiliary vector
      h (psd_part of library/matrix/psd_part.v), with w and c chosen from
      alpha < alpha*(kappa) (Gaussian/Threshold); Wigner's law
      (random_matrix/wigner.v) gives its spectral statistics, Lemma 5.13
      (goe_diag_var_tail of random_matrix/goe_rotation.v) its diagonal when
      kappa > 3, and |g| / d tends to sqrt alpha. Then cgmt_zero_tail
      (library/comparison/cgmt.v) bounds Phi by C sqrt (d ln d) with
      probability tending to one.
   3. The margin. The map S |-> A mxvec S on the symmetric matrices has
      smallest singular value at least c d with probability tending to
      one: gauss_proj_singular_tail of library/comparison/escape.v for the
      projection sym_proj on the symmetric matrices, whose trace is
      d (d + 1) / 2, and gauss_trmx; c > 0 because alpha*(kappa) < 1/2.
   4. The correction (subcritical_correction, deterministic). Given an
      approximate fit S_0 in the slice and the margin, the range duality
      (range_duality_sym of library/matrix/nuclear.v) gives D symmetric
      with A mxvec D = - A mxvec (T_kappa S_0) and opnorm D small; then
      S_0 + T_kappa^-1 D, rescaled to trace d, is an exact fit in a
      slightly larger slice.

   Proved so far:
   - sym_proj, mul_sym_proj, sym_proj_sym, sym_proj_idem, sym_proj_trace:
     the orthogonal projection of 'rV_(d * d) on the symmetric matrices in
     mxvec coordinates, v sym_proj = mxvec ((V + V^T) / 2) for
     V = vec_mx v, of trace d (d + 1) / 2;
   - opnorm_diag_part, opnorm_cone_map: the operator norm of the diagonal
     part, and of T_kappa D, at most (1 + |sqrt ((kappa - 1)/2) - 1|)
     opnorm D;
   - subcritical_correction, step 4. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import measure lebesgue_measure probability.
From GaussianAnalysis Require Import measurable_matrix euclidean real_spectral.
From GaussianAnalysis Require Import opnorm nuclear.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

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

Lemma goe_part_sym d (A : 'M[R]_d) : goe_part A \is symmetricmx.
Proof.
by apply/symmetricmxP; rewrite /goe_part linearZ /= linearD /= trmxK addrC.
Qed.

Lemma mxdot_goe_part d (A D : 'M[R]_d) : D \is symmetricmx ->
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
have Ws i : W i \is symmetricmx := goe_part_sym _ _.
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
  rewrite [in RHS]mxE -e1 /W mxdot_goe_part //.
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
