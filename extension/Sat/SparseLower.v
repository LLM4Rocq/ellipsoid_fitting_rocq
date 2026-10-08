(* The sparse lower bound: Proposition 3.3 of Koehler and Sohn (arXiv
   2608.27372, lines 2303-2418 of arxiv_v1.tex), at Stdlib's R. Item S4 of
   stage 3 of phase 5 (lane C).

   For a sample x of n points of R^d, W_i = (x_i x_i^T - I) / sqrt d and
   L_X^* u = sample_adj x u = sum_i u_i W_i (Sat/Apriori). The statements
   are deterministic, on the event of the sparse a priori estimates
   (Sat/AprioriSparse): for every m-sparse u,
     (hQ) | |L_X^* u|_F^2 / d - |u|^2 | <= delta |u|^2, with delta <= 1/2,
     (hX) |sum_i u_i x_i| <= L |u|.

   Proved here.
   - sample_adj_delta, sample_adj_sym, sample_adj_form: L_X^* e_j = W_j,
     L_X^* u is symmetric, and
     <v, (L_X^* u) v> = sum_i u_i (<x_i, v>^2 - |v|^2) / sqrt d.
   - sparse_points_sqr: sum_(i in I) <x_i, v>^2 <= L^2 |v|^2 for a set I
     of size at most m (hX at u = (<x_i, v>)_(i in I)).
   - gram_form u v = <L_X^* u, L_X^* v> / d, the form of the Gram matrices
     Q_I; gram_defect (polarization): for u and v supported in a set I of
     size at most m, |gram_form u v - <u, v>| <= delta |u| |v|.
   - sparse_certificate: for I of size at most m and e supported in I,
     there is y supported in I with gram_form y e_j = e_j for every j in I
     (y = e Q_I^(-1), Q_I being invertible), so that
     (1 - delta) |y|^2 <= <e, y>.
   - sparse_lower (Proposition 3.3): for every lambda with at most m
     nonzero coordinates,
     |lambda|_1 d sqrt d <= (L^2 (1 + 2 delta sqrt m) + 2 m)
       nuclear (L_X^* lambda),
     by the certificate A = (1/d) L_X^* y for e = sign lambda:
     <L_X^* lambda, A> = |lambda|_1, |y| <= 2 sqrt m,
     |y_j| <= 1 + 2 delta sqrt m (gram_defect), |sum_i y_i| <= 2 m, hence
     opnorm A <= d^(-3/2) (L^2 (1 + 2 delta sqrt m) + 2 m) (opnorm_symP
     and sparse_points_sqr), and the duality mxdot_le_nuclear of
     matrix/nuclear.v. With delta = C (ln d)^(3/2) / sqrt d,
     L = C sqrt d ln d and m = C0 d ln d this is the paper's
     nuclear (L_X^* lambda) >= c sqrt d / (ln d)^4 |lambda|_1. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import sesquilinear boolp classical_sets reals Rstruct.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.matrix Require Import nuclear.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori AprioriSparse.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section sample_adj_linear.
Variables (n d : nat) (x : paper_main_sample n d).

Lemma sample_adjD (u v : 'rV[R]_n) :
  sample_adj x (u + v) = sample_adj x u + sample_adj x v.
Proof.
rewrite /sample_adj /coef_adj -big_split /=; apply: eq_bigr => i _.
by rewrite mxE scalerDl.
Qed.

Lemma sample_adjZ (a : R) (u : 'rV[R]_n) :
  sample_adj x (a *: u) = a *: sample_adj x u.
Proof.
rewrite /sample_adj /coef_adj scaler_sumr; apply: eq_bigr => i _.
by rewrite [(a *: u) 0 i]mxE [RHS]scalerA.
Qed.

Lemma sample_adjN (u : 'rV[R]_n) : sample_adj x (- u) = - sample_adj x u.
Proof. by rewrite -scaleN1r sample_adjZ scaleN1r. Qed.

Lemma sample_adj_sum (I : Type) (r : seq I) (P : pred I)
    (F : I -> 'rV[R]_n) :
  sample_adj x (\sum_(k <- r | P k) F k) =
  \sum_(k <- r | P k) sample_adj x (F k).
Proof.
elim/big_rec2: _ => [|k y1 y2 _ <-]; last by rewrite sample_adjD.
rewrite /sample_adj /coef_adj big1 // => i _.
by rewrite mxE scale0r.
Qed.

Lemma sample_adj_delta (j : 'I_n) : sample_adj x (delta_mx 0 j) = sample_W x j.
Proof.
rewrite /sample_adj /coef_adj (bigD1 j) //= [delta_mx 0 j 0 j]mxE !eqxx.
rewrite scale1r big1 ?addr0 // => i ij.
by rewrite mxE eqxx (negPf ij) scale0r.
Qed.

Lemma sample_adj_sym (u : 'rV[R]_n) : sample_adj x u \is symmetricmx.
Proof.
apply/symmetricmxP; rewrite /sample_adj /coef_adj linear_sum /=.
apply: eq_bigr => i _; rewrite linearZ /= /sample_W linearZ /= linearB /=.
by rewrite trmx_mul trmxK trmx1.
Qed.

(* The quadratic form of L_X^* u: <v, (L_X^* u) v> =
   sum_i u_i (<x_i, v>^2 - |v|^2) / sqrt d. *)
Lemma sample_adj_form (u : 'rV[R]_n) (v : 'cV[R]_d) :
  mxdot v (sample_adj x u *m v) = (Num.sqrt d%:R)^-1 *
    \sum_i u 0 i * (mxdot (paper_main_point x i) v ^+ 2 - mxdot v v).
Proof.
have -> : mxdot v (sample_adj x u *m v) = mxdot (sample_adj x u) (v *m v^T).
  by rewrite mxdot_outer mxdot_colE mulmxA.
rewrite /sample_adj /coef_adj mxdot_suml mulr_sumr; apply: eq_bigr => i _.
rewrite mxdotZl /sample_W mxdotZl mxdotBl mxdot_outer2 mxdot_outer mulmx1.
by rewrite -mxdot_colE expr2 mulrCA.
Qed.

End sample_adj_linear.

Section sparse_lower.
Variables (n d : nat) (x : paper_main_sample n d).
Hypothesis d0 : (0 < d)%N.
Variables (m : nat) (delta L : R).
Hypotheses (delta0 : (0 <= delta)%R) (delta12 : (delta <= 1 / 2)%R).
Hypothesis hQ : forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
  (`|frobenius (sample_adj x u) ^+ 2 / d%:R - mxdot u u| <=
   delta * mxdot u u)%R.
Hypothesis hX : forall u : 'rV[R]_n, (#|supp u| <= m)%N ->
  (frobenius (sample_comb x u) <= L * frobenius u)%R.

(* The points of a set I of size at most m:
   sum_(i in I) <x_i, v>^2 <= L^2 |v|^2. *)
Lemma sparse_points_sqr (I : {set 'I_n}) (v : 'cV[R]_d) : (#|I| <= m)%N ->
  (\sum_(i in I) mxdot (paper_main_point x i) v ^+ 2 <= L ^+ 2 * mxdot v v)%R.
Proof.
move=> Im.
(* u = (<x_i, v>)_(i in I) has |u|^2 = <sum_i u_i x_i, v> <= L |u| |v| *)
pose u : 'rV[R]_n :=
  \row_i (if i \in I then mxdot (paper_main_point x i) v else 0)%R.
have uI : supported I u by move=> i iI; rewrite mxE (negPf iI).
have uu : (mxdot u u =
    \sum_(i in I) mxdot (paper_main_point x i) v ^+ 2)%R.
  rewrite [LHS]/mxdot big_ord1 [RHS]big_mkcond /=; apply: eq_bigr => i _.
  by rewrite !mxE; case: ifP => _; rewrite ?mul0r // expr2.
have uc : (mxdot (sample_comb x u) v = mxdot u u)%R.
  rewrite /sample_comb mxdot_suml [RHS]/mxdot big_ord1.
  apply: eq_bigr => i _.
  by rewrite mxdotZl !mxE; case: ifP => _; rewrite ?mul0r.
have h : (frobenius u ^+ 2 <= L * frobenius u * frobenius v)%R.
  rewrite frobenius_sqr -uc.
  apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_le _ _) _.
  apply: ler_wpM2r; first exact: frobenius_ge0.
  exact: hX (supported_card uI Im).
rewrite -uu -!frobenius_sqr.
have [u0|u0] := eqVneq (frobenius u) 0.
  by rewrite u0 expr0n /= mulr_ge0 ?sqr_ge0.
have up : (0 < frobenius u)%R by rewrite lt_def u0 frobenius_ge0.
have h1 : (frobenius u <= L * frobenius v)%R.
  by rewrite -(ler_pM2r up) -expr2 mulrAC.
by rewrite -exprMn !expr2; apply: ler_pM; rewrite ?frobenius_ge0.
Qed.

(* The form of the Gram matrices Q_I. *)
Definition gram_form (u v : 'rV[R]_n) : R :=
  (mxdot (sample_adj x u) (sample_adj x v) / d%:R)%R.

(* Polarization: the defect of the Gram form on vectors supported in a set
   of size at most m. *)
Lemma gram_defect (I : {set 'I_n}) (u v : 'rV[R]_n) : (#|I| <= m)%N ->
  supported I u -> supported I v ->
  (`|gram_form u v - mxdot u v| <= delta * frobenius u * frobenius v)%R.
Proof.
move=> Im hu hv.
have hD w : supported I w ->
    `|gram_form w w - mxdot w w| <= delta * mxdot w w.
  move=> hw; have := hQ w (supported_card hw Im).
  by rewrite frobenius_sqr.
(* polarization *)
have gfDB a b : (gram_form (a + b) (a + b) - gram_form (a - b) (a - b) =
    4 * gram_form a b)%R.
  rewrite /gram_form sample_adjD sample_adjD sample_adjN.
  rewrite !mxdotDl !mxdotDr !mxdotNl !mxdotNr.
  rewrite [mxdot (sample_adj x b) (sample_adj x a)]mxdotC.
  have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
  move: (mxdot (sample_adj x a) (sample_adj x a))
    (mxdot (sample_adj x a) (sample_adj x b))
    (mxdot (sample_adj x b) (sample_adj x b)) => p q r.
  by rewrite -mulrBl mulrA; congr (_ * _); ring.
have mdDB a b : (mxdot (a + b) (a + b) - mxdot (a - b) (a - b) =
    4 * mxdot a b :> R)%R.
  by rewrite !mxdotDl !mxdotDr !mxdotNl !mxdotNr [mxdot b a]mxdotC; ring.
have para (a b : 'rV[R]_n) : (mxdot (a + b) (a + b) +
    mxdot (a - b) (a - b) = 2 * mxdot a a + 2 * mxdot b b :> R)%R.
  by rewrite !mxdotDl !mxdotDr !mxdotNl !mxdotNr [mxdot b a]mxdotC; ring.
have supD a b : supported I a -> supported I b -> supported I (a + b).
  by move=> ha hb i iI; rewrite !mxE ha ?hb ?addr0.
have pol (a b : 'rV[R]_n) : supported I a -> supported I b ->
    (`|gram_form a b - mxdot a b| <= delta * (mxdot a a + mxdot b b) / 2)%R.
  move=> ha hb.
  have hp := hD (a + b) (supD _ a b ha hb).
  have hm := hD (a - b) (supportedB ha hb).
  have e : (gram_form a b - mxdot a b =
      ((gram_form (a + b) (a + b) - mxdot (a + b) (a + b)) -
       (gram_form (a - b) (a - b) - mxdot (a - b) (a - b))) / 4)%R.
    have h1 := gfDB a b; have h2 := mdDB _ _ a b.
    move: h1 h2; move: (gram_form (a + b) (a + b)) (gram_form (a - b) (a - b))
      (mxdot (a + b) (a + b)) (mxdot (a - b) (a - b)) => g1 g2 m1 m2 h1 h2.
    have e1 : (g1 - m1 - (g2 - m2) = (g1 - g2) - (m1 - m2))%R by ring.
    by rewrite e1 h1 h2 -mulrBr mulrC mulKf ?pnatr_eq0.
  rewrite e normrM (ger0_norm (_ : (0 <= 4^-1 :> R)%R)); last first.
  2: by rewrite invr_ge0 ler0n.
  apply: (@le_trans _ _ ((delta * mxdot (a + b) (a + b) +
      delta * mxdot (a - b) (a - b)) / 4)).
    rewrite ler_pM2r ?invr_gt0 ?ltr0n //.
    apply: le_trans (ler_normB _ _) _.
    exact: lerD hp hm.
  rewrite -mulrDr para.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  move: (mxdot a a) (mxdot b b) => A B.
  by field.
(* rescaling: (s u, v / s) with s^2 = |v| / |u| *)
have gfZ (s t : R) (a b : 'rV[R]_n) :
    (gram_form (s *: a) (t *: b) = s * t * gram_form a b)%R.
  by rewrite /gram_form !sample_adjZ mxdotZl mxdotZr !mulrA.
have supZ (s : R) a : supported I a -> supported I (s *: a).
  by move=> ha i iI; rewrite mxE ha ?mulr0.
have adj0 : sample_adj x 0 = 0.
  by rewrite -(scale0r (0 : 'rV[R]_n)) sample_adjZ scale0r.
have [u0|un0] := eqVneq (frobenius u) 0.
  have -> : u = 0 by apply/eqP; rewrite -frobenius_eq0 u0.
  rewrite /gram_form adj0 !mxdot0l frobenius0 mulr0 mul0r.
  by rewrite (_ : (0 / d%:R - 0 = 0 :> R)%R) ?normr0 // mul0r subrr.
have [v0|vn0] := eqVneq (frobenius v) 0.
  have -> : v = 0 by apply/eqP; rewrite -frobenius_eq0 v0.
  rewrite /gram_form adj0 !mxdot0r frobenius0 mulr0.
  by rewrite (_ : (0 / d%:R - 0 = 0 :> R)%R) ?normr0 // mul0r subrr.
have fu : (0 < frobenius u)%R by rewrite lt_def un0 frobenius_ge0.
have fv : (0 < frobenius v)%R by rewrite lt_def vn0 frobenius_ge0.
set s := Num.sqrt (frobenius v / frobenius u).
have s0 : (0 < s)%R by rewrite sqrtr_gt0 divr_gt0.
have sn : s != 0 by rewrite gt_eqF.
have ss : (s ^+ 2 = frobenius v / frobenius u)%R.
  by rewrite sqr_sqrtr // divr_ge0 // ltW.
have h := pol (s *: u) (s^-1 *: v) (supZ s u hu) (supZ s^-1 v hv).
rewrite gfZ mulfV // mul1r mxdotZl mxdotZr mulrA mulfV // mul1r in h.
apply: le_trans h _.
rewrite !mxdotZl !mxdotZr !mulrA -!expr2 ss exprVn ss invf_div.
rewrite -!frobenius_sqr.
have un : frobenius u != 0 := un0.
have vn : frobenius v != 0 := vn0.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
move: (frobenius u) (frobenius v) un vn => p q pn qn.
by field.
Qed.

(* The solution of the Gram system on I. *)
Lemma sparse_certificate (I : {set 'I_n}) (e : 'rV[R]_n) : (#|I| <= m)%N ->
  supported I e -> exists y : 'rV[R]_n, [/\ supported I y,
    forall j, j \in I -> gram_form y (delta_mx 0 j) = e 0 j &
    ((1 - delta) * mxdot y y <= mxdot e y)%R].
Proof.
move=> Im he.
set k := #|I|.
pose f (a : 'I_k) : 'I_n := enum_val a.
pose ev (a : 'I_k) : 'rV[R]_n := delta_mx 0 (f a).
pose G : 'M[R]_k := \matrix_(a, b) gram_form (ev a) (ev b).
(* the coordinates of I, and the vectors supported in I *)
pose emb (w : 'rV[R]_k) : 'rV[R]_n := sparse_emb (F := I) w^T.
have embE w : emb w = \sum_a w 0 a *: ev a.
  by rewrite /emb /sparse_emb; apply: eq_bigr => a _; rewrite mxE.
have emb_dot w w' : mxdot (emb w) (emb w') = mxdot w w'.
  by rewrite /emb sparse_emb_dot mxdot_trmx.
have supp_emb w : supported I (emb w).
  by move=> i iI; rewrite /emb sparse_emb_out.
have gfE (w w' : 'rV[R]_k) : (gram_form (emb w) (emb w') =
    \sum_a \sum_b w 0 a * w' 0 b * G a b)%R.
  rewrite /gram_form !embE sample_adj_sum [X in mxdot _ X]sample_adj_sum.
  rewrite mxdot_suml mulr_suml; apply: eq_bigr => a _.
  rewrite mxdot_sumr mulr_suml; apply: eq_bigr => b _.
  rewrite !sample_adjZ mxdotZl mxdotZr mxE /gram_form.
  by rewrite !mulrA.
have gfM (w w' : 'rV[R]_k) : (gram_form (emb w) (emb w') =
    \sum_b (w *m G) 0 b * w' 0 b)%R.
  rewrite gfE exchange_big /=; apply: eq_bigr => b _.
  rewrite mxE mulr_suml; apply: eq_bigr => a _.
  by rewrite mulrAC.
have gfD (w w' : 'rV[R]_k) :
    (gram_form (emb w) (emb w') = mxdot (w *m G) w')%R.
  by rewrite gfM /mxdot big_ord1.
have gram_low (u : 'rV[R]_n) : supported I u ->
    ((1 - delta) * mxdot u u <= gram_form u u)%R.
  move=> uI; have := hQ u (supported_card uI Im).
  rewrite /gram_form -frobenius_sqr ler_norml => /andP[h _].
  by rewrite -frobenius_sqr mulrBl mul1r -lerBrDl.
have d1 : (0 < 1 - delta)%R.
  by rewrite subr_gt0 (le_lt_trans delta12) // ltr_pdivrMr // mul1r ltr1n.
(* Q_I is invertible *)
have Gu : G \in unitmx.
  rewrite unitmxE unitfE; apply/negP => /det0P [w w0 wG].
  have := gram_low (emb w) (supp_emb w).
  rewrite gfM wG emb_dot.
  under eq_bigr do rewrite mxE mul0r; rewrite big1_eq.
  rewrite pmulr_rle0 // => h.
  have : mxdot w w == 0 by rewrite eq_le h mxdot_ge0.
  by rewrite mxdot_eq0 (negPf w0).
pose eh : 'rV[R]_k := \row_b e 0 (f b).
have eE : e = emb eh.
  have sI : supp e \subset I by apply/supportedP.
  rewrite /emb -[LHS](sparse_emb_proj sI).
  by congr sparse_emb; apply/colP => b; rewrite !mxE.
pose w := eh *m invmx G.
have wG : w *m G = eh by rewrite /w mulmxKV.
have evE b : emb (delta_mx 0 b) = ev b.
  rewrite embE (bigD1 b) //= [delta_mx 0 b 0 b]mxE !eqxx scale1r.
  rewrite big1 ?addr0 // => a ab.
  by rewrite mxE eqxx (negPf ab) scale0r.
exists (emb w); split; first exact: supp_emb.
  move=> j jI.
  have -> : delta_mx 0 j = ev (enum_rank_in jI j).
    by rewrite /ev /f /= enum_rankK_in.
  by rewrite -evE gfD wG mxdot_delta mxE /f /= enum_rankK_in.
apply: le_trans (gram_low _ (supp_emb w)) _.
by rewrite gfD wG eE emb_dot.
Qed.

(* Proposition 3.3. *)
Theorem sparse_lower (lam : 'rV[R]_n) : (#|supp lam| <= m)%N ->
  ((\sum_i `|lam 0 i|) * (d%:R * Num.sqrt d%:R) <=
   (L ^+ 2 * (1 + 2 * delta * Num.sqrt m%:R) + 2 * m%:R) *
   nuclear (sample_adj x lam))%R.
Proof.
move=> lm.
have d2 : (1 <= 2 * (1 - delta))%R.
  have h2 : (delta * 2 <= 1)%R by rewrite -ler_pdivlMr.
  rewrite mulrBr mulr1 [2 * delta]mulrC lerBrDr.
  have -> : (2 = 1 + 1 :> R)%R by [].
  by rewrite lerD2l.
have c0 : (0 <= 1 + 2 * delta * Num.sqrt m%:R)%R.
  by rewrite addr_ge0 // mulr_ge0 // ?sqrtr_ge0 // mulr_ge0.
(* the certificate for e = sign lambda *)
set I := supp lam.
pose e : 'rV[R]_n := \row_i Num.sg (lam 0 i).
have eI : supported I e.
  by move=> i; rewrite inE negbK mxE => /eqP ->; rewrite sgr0.
have [y [yI yG ye]] := sparse_certificate I e lm eI.
have ee : (mxdot e e <= m%:R)%R.
  have -> : mxdot e e = (\sum_(i in I) 1)%R.
    rewrite /mxdot big_ord1 [RHS]big_mkcond /=; apply: eq_bigr => i _.
    rewrite !mxE inE -expr2 sqr_sg.
    by case: (lam 0 i != 0).
  by rewrite sumr_const ler_nat.
have sm0 : (0 <= Num.sqrt m%:R :> R)%R := sqrtr_ge0 _.
(* |y| <= 2 sqrt m *)
have yn : (frobenius y <= 2 * Num.sqrt m%:R)%R.
  have en : (frobenius e <= Num.sqrt m%:R)%R by rewrite ler_sqrt ?ler0n.
  have h1 : ((1 - delta) * frobenius y ^+ 2 <=
      Num.sqrt m%:R * frobenius y)%R.
    rewrite frobenius_sqr; apply: le_trans ye _.
    apply: le_trans (ler_norm _) _; apply: le_trans (mxdot_le _ _) _.
    by apply: ler_wpM2r; [exact: frobenius_ge0 | exact: en].
  have [y0|y0] := eqVneq (frobenius y) 0.
    by rewrite y0 mulr_ge0.
  have yp : (0 < frobenius y)%R by rewrite lt_def y0 frobenius_ge0.
  have h2 : ((1 - delta) * frobenius y <= Num.sqrt m%:R)%R.
    by rewrite -(ler_pM2r yp) -mulrA -expr2.
  apply: le_trans (_ : 2 * ((1 - delta) * frobenius y) <= _)%R.
    rewrite mulrA -[X in (X <= _)%R]mul1r.
    by apply: ler_wpM2r; [exact: frobenius_ge0 | exact: d2].
  by rewrite ler_pM2l.
(* |y_j| <= 1 + 2 delta sqrt m, by gram_defect *)
set c := (1 + 2 * delta * Num.sqrt m%:R)%R.
have yinf j : (`|y 0 j| <= c)%R.
  have [jI|jI] := boolP (j \in I); last by rewrite yI // normr0.
  have dj : supported I (delta_mx 0 j : 'rV[R]_n).
    move=> i iI; rewrite mxE eqxx /=.
    have ij : i != j by apply: contraNneq iI => ->.
    by rewrite (negPf ij).
  have := gram_defect I y (delta_mx 0 j) lm yI dj.
  rewrite yG // mxdot_delta.
  have -> : frobenius (delta_mx 0 j : 'rV[R]_n) = 1%R.
    by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
  rewrite mulr1 => h.
  have -> : y 0 j = (e 0 j - (e 0 j - y 0 j))%R.
    by rewrite opprB addrC subrK.
  apply: le_trans (ler_normB _ _) _; rewrite /c; apply: lerD.
    by rewrite mxE normr_sg lern1 leq_b1.
  apply: le_trans h _.
  rewrite -mulrA [X in (_ <= X)%R]mulrC -mulrA ler_wpM2l //.
  by rewrite mulrC.
(* |sum_i y_i| <= 2 m *)
have ysum : (`|\sum_i y 0 i| <= 2 * m%:R)%R.
  pose o : 'rV[R]_n := \row_i ((i \in I)%:R)%R.
  have -> : (\sum_i y 0 i = mxdot y o)%R.
    rewrite /mxdot big_ord1; apply: eq_bigr => i _; rewrite mxE.
    by case: (boolP (i \in I)) => iI; rewrite ?mulr1 // mulr0 yI.
  have oo : (frobenius o <= Num.sqrt m%:R)%R.
    rewrite ler_sqrt ?ler0n //.
    have -> : mxdot o o = (\sum_(i in I) 1)%R.
      rewrite /mxdot big_ord1 [RHS]big_mkcond /=; apply: eq_bigr => i _.
      by rewrite mxE; case: (i \in I); rewrite ?mulr1 ?mul0r.
    by rewrite sumr_const ler_nat.
  apply: le_trans (mxdot_le _ _) _.
  have -> : (2 * m%:R = 2 * Num.sqrt m%:R * Num.sqrt m%:R :> R)%R.
    by rewrite -mulrA -expr2 sqr_sqrtr ?ler0n.
  by apply: ler_pM; rewrite ?frobenius_ge0.
(* the dual matrix B = L_X^* y / d and its operator norm *)
set B := sample_adj x ((d%:R)^-1 *: y).
have dp : (0 < d%:R :> R)%R by rewrite ltr0n.
have sdp : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0.
have b0 : (0 <= (L ^+ 2 * c + 2 * m%:R) / (d%:R * Num.sqrt d%:R))%R.
  rewrite divr_ge0 //; last by rewrite mulr_ge0 // ltW.
  by rewrite addr_ge0 // mulr_ge0 // sqr_ge0.
have Bop : (opnorm B <= (L ^+ 2 * c + 2 * m%:R) / (d%:R * Num.sqrt d%:R))%R.
  apply/(opnorm_symP (sample_adj_sym _ _ _ _) b0) => v.
  rewrite sample_adj_form.
  set s := mxdot v v.
  have s0 : (0 <= s)%R := mxdot_ge0 v.
  have -> : (\sum_i ((d%:R)^-1 *: y) 0 i *
        (mxdot (paper_main_point x i) v ^+ 2 - s) =
      (d%:R)^-1 * (\sum_i y 0 i * mxdot (paper_main_point x i) v ^+ 2 -
        (\sum_i y 0 i) * s))%R.
    rewrite mulr_suml -sumrB mulr_sumr; apply: eq_bigr => i _.
    by rewrite mxE !mulrBr !mulrA.
  have hY : (`|\sum_i y 0 i * mxdot (paper_main_point x i) v ^+ 2| <=
      c * (L ^+ 2 * s))%R.
    apply: le_trans (ler_norm_sum _ _ _) _.
    rewrite (bigID (mem I)) /= [X in (_ + X <= _)%R]big1 ?addr0.
      by move=> i iI; rewrite yI // mul0r normr0.
    apply: le_trans (_ : \sum_(i in I)
        c * mxdot (paper_main_point x i) v ^+ 2 <= _)%R.
      apply: ler_sum => i _; rewrite normrM (ger0_norm (sqr_ge0 _)).
      by apply: ler_wpM2r; [exact: sqr_ge0 | exact: yinf].
    by rewrite -mulr_sumr ler_wpM2l // sparse_points_sqr.
  have si : (0 <= (Num.sqrt d%:R)^-1 :> R)%R by rewrite invr_ge0 ltW.
  have di : (0 <= (d%:R)^-1 :> R)%R by rewrite invr_ge0 ltW.
  rewrite normrM (ger0_norm si) normrM (ger0_norm di).
  apply: le_trans (_ : (Num.sqrt d%:R)^-1 * ((d%:R)^-1 *
      (c * (L ^+ 2 * s) + 2 * m%:R * s)) <= _)%R.
    apply: ler_wpM2l => //; apply: ler_wpM2l => //.
    apply: le_trans (ler_normB _ _) _; apply: lerD => //.
    by rewrite normrM (ger0_norm s0); apply: ler_wpM2r.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite invfM; ring.
(* <L_X^* lambda, B> = |lambda|_1 *)
have Bdot : (mxdot (sample_adj x lam) B = \sum_i `|lam 0 i|)%R.
  rewrite {1}/sample_adj /coef_adj mxdot_suml; apply: eq_bigr => j _.
  have gfj : (mxdot (sample_W x j) B = gram_form y (delta_mx 0 j))%R.
    rewrite /B sample_adjZ mxdotZr /gram_form sample_adj_delta mxdotC.
    by rewrite mulrC.
  rewrite mxdotZl gfj.
  have [jI|jI] := boolP (j \in I).
    by rewrite yG // mxE mulrC -normrEsg.
  have -> : lam 0 j = 0%R by apply/eqP; move: jI; rewrite inE negbK.
  by rewrite mul0r normr0.
(* duality between the operator and the nuclear norms *)
have sl0 : (0 <= \sum_i `|lam 0 i|)%R.
  by apply: sumr_ge0 => i _; exact: normr_ge0.
have := mxdot_le_nuclear (sample_adj x lam) B.
rewrite Bdot (ger0_norm sl0) => h.
have ddp : (0 < d%:R * Num.sqrt d%:R :> R)%R by rewrite mulr_gt0.
rewrite -ler_pdivlMr //; apply: le_trans h _.
rewrite [X in (_ <= X)%R]mulrAC.
by apply: ler_wpM2r; [exact: nuclear_ge0 | exact: Bop].
Qed.

End sparse_lower.
