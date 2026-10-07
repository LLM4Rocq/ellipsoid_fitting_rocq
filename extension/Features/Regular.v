(* The regularity of the quadratic features: Proposition 2.6 of Koehler and
   Sohn, "Universality and sharp thresholds for ellipsoid fitting" (arXiv
   2608.27372, lines 1117-1134 of arxiv_v1.tex, proof lines 4233-4438), at
   Stdlib's R, for a point x with independent coordinates of laws nu 0, ...,
   nu (d - 1) as universality_coordinate_law kappa K asks: mean 0, variance
   1, fourth moment kappa and E exp (x^2 / K^2) <= 2. The feature of x is
   unsat_feature d x, the mxvec of W = (x x^T - I) / sqrt d
   (Unsat/LeastSquares), and its law is data_feature_law nu d
   (Features/Definitions). For a matrix A, <W, A> is
   mxdot (unsat_feature d x) (mxvec A). The coordinates are independent, so
   the paper's approximate tensorization of variance holds with constant 1:
   it is the Efron-Stein inequality (probability/efron_stein.v).

   Main results. Constants depend only on K (and kappa where stated).
   - Moments of the coordinates: coordinate_law_moment
     (E x^(2k) <= 2 k! K^(2k), probability/subgaussian.v) and, by
     Hoeffding's inequality, lin_form_moment8: E <c, x>^8 <=
     48 4^8 K^8 |c|^8.
   - The quadratic form Q_A (x) = x^T A x - tr A is quad_form A, equal to
     <A, quad_mx t>, and <W, A> = Q_A / sqrt d (data_feature_dot). Its
     moments: quad_form_mean (E Q_A = 0), quad_form_cov (E Q_A Q_B =
     <A, B> + <A, B^T> + (kappa - 3) sum_a A_aa B_aa) and
     quad_form_moment4 (E Q_A^4 <= 9 2^33 K^8 |A|_F^4), by the fourth
     moment bound of Efron-Stein: resampling the coordinate i changes Q_A
     by u (sum_b (A_ib + A_bi) x_b - A_ii u), u = x_i - s (quad_form_set),
     whose fourth moment is at most (2^16 K^4 r_i)^2, r_i the squared norm
     of the row and the column i of A (quad_form_resample4).
   - Covariance matching (eq:C-kappa-trace, line 271), for the law of the
     features: data_feature_mean (E <W, theta> = 0) and data_feature_cov
     (E <W, theta> <W, theta'> = theta C_kappa theta'^T, where unsat_covE
     says that unsat_cov kappa d is the matrix of the form unsat_cov_form);
     (F1) as data_feature_fourth: E <W, theta>^4 <= 9 2^33 K^8 |theta|^4 /
     d^2; unsat_cov_opnorm_ge: the operator norm of C_kappa is at least
     (kappa - 1) / d.
   - The same in the vocabulary of Gaussian/Cones, for Unsat/Ridge:
     unsat_cov_form_sym and data_feature_cov_sym (feature_cov kappa A B, B
     symmetric), feature_cov_ge (min (2, kappa - 1) |A|_F^2 / d <=
     feature_cov kappa A A for kappa > 1) and data_feature_fourth_cov
     (E <W, A>^4 <= 9 2^33 K^8 feature_cov kappa A A^2 /
     min (2, kappa - 1)^2).

   Planned (phase 5, stage 1):
   - (F2): Var (Z T Z^T) <= C |T|_F^2 / d for the features, by Efron-Stein:
     a resampled coordinate changes W only in one row and one column, and
     the fourth moments of the projected linear forms are bounded by (F1)
     (lines 4370-4436).
   - Proposition 2.6: for kappa > 1, data_feature_law nu d is a regular
     feature with covariance unsat_cov kappa d (regular_feature of
     convex/least_squares.v), with constants depending only on kappa and K
     and tau of order 1 / sqrt d.
   - The Gaussian feature: the covariance matrix of
     gaussian_feature_law kappa d is unsat_cov kappa d, so it is a regular
     feature with that covariance and constants 3^(1/4) and
     sqrt 2 opnorm (unsat_cov kappa d), by the Gaussian case of
     convex/barrier_lindeberg.v. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import sesquilinear.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.probability Require Import efron_stein.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.convex Require Import least_squares.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure. *)
Local Notation RR := (R : realType).

Section coordinate_moments.
Local Open Scope ereal_scope.
Variables (kappa K : R) (mu : probability (measurableTypeR R) R).
Hypothesis hmu : universality_coordinate_law kappa K mu.

Lemma coordinate_law_K : (0 < K)%R.
Proof. by case: hmu. Qed.

Lemma coordinate_law_subgaussian : subgaussian mu (fun x : R => x) K.
Proof.
case: hmu => K0 [_ [_ [_ h]]]; split => //.
by move: h; rewrite unlock /universality_subgaussian_test.
Qed.

Lemma coordinate_law_integrable k :
  mu.-integrable setT (fun x : measurableTypeR R => ((x : R) ^+ k)%:E).
Proof. exact: integrable_subgaussian_exprn coordinate_law_subgaussian. Qed.

Lemma coordinate_law_mean : \int[mu]_x ((x : R))%:E = 0.
Proof.
case: hmu => _ [h _]; move: h; rewrite unlock /universality_power.
by under eq_integral do rewrite expr1.
Qed.

Lemma coordinate_law_second : \int[mu]_x ((x : R) ^+ 2)%:E = 1.
Proof. by case: hmu => _ [_ [h _]]; move: h; rewrite unlock. Qed.

Lemma coordinate_law_fourth : \int[mu]_x ((x : R) ^+ 4)%:E = kappa%:E.
Proof. by case: hmu => _ [_ [_ [h _]]]; move: h; rewrite unlock. Qed.

Lemma coordinate_law_moment k :
  \int[mu]_x ((x : R) ^+ (2 * k))%:E <= (2 * k`!%:R * K ^+ (2 * k))%:E.
Proof. exact: subgaussian_moment coordinate_law_subgaussian. Qed.

End coordinate_moments.

Lemma tnth_tuple_set_eq (T : Type) n (t : n.-tuple T) (i : 'I_n) (s : T) :
  tnth (tuple_set t i s) i = s.
Proof. by rewrite /tuple_set tnth_mktuple eqxx. Qed.

Lemma tnth_tuple_set_neq (T : Type) n (t : n.-tuple T) (i k : 'I_n) (s : T) :
  k != i -> tnth (tuple_set t i s) k = tnth t k.
Proof. by move=> ki; rewrite /tuple_set tnth_mktuple (negbTE ki). Qed.

Lemma amgm4 (a b c e : R) :
  `|a * b * c * e| <= (a ^+ 4 + b ^+ 4 + c ^+ 4 + e ^+ 4) / 4.
Proof.
have h1 := sqr_ge0 (a ^+ 2 - b ^+ 2); have h2 := sqr_ge0 (c ^+ 2 - e ^+ 2).
have h3 := sqr_ge0 (a * b - c * e); have h4 := sqr_ge0 (a * b + c * e).
by rewrite ler_norml; apply/andP; split; nra.
Qed.

(* The quadratic form x^T A x - tr A of the coordinates of a point. For the
   feature W of the point, <W, A> = quad_form A t / sqrt d. *)
Definition quad_form {d} (A : 'M[R]_d) (t : d.-tuple (measurableTypeR R)) : R :=
  \sum_(a < d) \sum_(b < d) A a b * ((tnth t a : R) * tnth t b - (a == b)%:R).

Lemma sum_delta d (F : 'I_d -> R) (k : 'I_d) :
  \sum_(e < d) F e * (k == e)%:R = F k.
Proof.
rewrite (bigD1 k) //= eqxx mulr1 big1 ?addr0 // => e ek.
by rewrite eq_sym (negbTE ek) mulr0.
Qed.

Lemma sum_delta' d (F : 'I_d -> R) (k : 'I_d) :
  \sum_(e < d) F e * (e == k)%:R = F k.
Proof. by under eq_bigr do rewrite eq_sym; exact: sum_delta. Qed.

(* The fourth moments summed against B: E [x_a x_b x^T B x]. *)
Lemma moment4_sum d (kappa : R) (B : 'M[R]_d) (a b : 'I_d) :
  \sum_(c < d) \sum_(e < d) B c e *
    ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
     (a == e)%:R * (b == c)%:R +
     (kappa - 3) * (((a == b) && (a == c)) && (a == e))%:R) =
  (a == b)%:R * \tr B + B a b + B b a + (kappa - 3) * (a == b)%:R * B a a.
Proof.
have andR (b1 b2 : bool) : ((b1 && b2)%:R = b1%:R * b2%:R :> R).
  by case: b1; case: b2; rewrite /= ?mulr1 ?mulr0 ?mul0r.
transitivity (\sum_(c < d) (B c c * (a == b)%:R + B c b * (a == c)%:R +
  B c a * (b == c)%:R + ((kappa - 3) * (a == b)%:R * B c a) * (a == c)%:R)).
  apply: eq_bigr => c _.
  transitivity (\sum_(e < d) ((B c e * (a == b)%:R) * (c == e)%:R +
    (B c e * (a == c)%:R) * (b == e)%:R + (B c e * (b == c)%:R) * (a == e)%:R +
    ((kappa - 3) * ((a == b) && (a == c))%:R * B c e) * (a == e)%:R)).
    by apply: eq_bigr => e _; rewrite andR; ring.
  by rewrite !big_split /= !sum_delta andR; ring.
by rewrite !big_split /= !sum_delta -mulr_suml /mxtrace; ring.
Qed.

Definition quad_sum {d} (A : 'M[R]_d) (t : d.-tuple (measurableTypeR R)) : R :=
  \sum_(a < d) \sum_(b < d) A a b * ((tnth t a : R) * tnth t b).

Lemma quad_formE d (A : 'M[R]_d) t : quad_form A t = quad_sum A t - \tr A.
Proof.
rewrite /quad_form /quad_sum /mxtrace -sumrB; apply: eq_bigr => a _.
under eq_bigr do rewrite mulrBr.
rewrite sumrB; congr (_ - _).
rewrite (bigD1 a) //= eqxx mulr1 big1 ?addr0 // => b ba.
by rewrite eq_sym (negbTE ba) mulr0.
Qed.

Lemma mxdot_mxvec m n (A B : 'M[R]_(m, n)) :
  mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 pair_bigA /=.
rewrite (reindex (uncurry (@mxvec_index m n))) /=.
  exact: (curry_mxvec_bij m n).
by apply: eq_bigr => -[i j] _ /=; rewrite !mxvecE.
Qed.

Lemma data_feature_dot d (A : 'M[R]_d) (t : d.-tuple (measurableTypeR R)) :
  mxdot (data_feature_map d t) (mxvec A) = (Num.sqrt d%:R)^-1 * quad_form A t.
Proof.
rewrite /data_feature_map /unsat_feature mxdot_mxvec /mxdot /quad_form.
rewrite mulr_sumr; apply: eq_bigr => a _; rewrite mulr_sumr.
apply: eq_bigr => b _; rewrite !mxE big_ord1 !mxE.
by rewrite -mulrA [A a b * _]mulrC.
Qed.

Lemma measurable_quad_form d (A : 'M[R]_d) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun t => quad_form A t : RR).
Proof.
apply/measurable_EFinP.
rewrite (_ : EFin \o _ = fun t => \sum_(a < d) \sum_(b < d)
  (A a b * ((tnth t a : R) * tnth t b - (a == b)%:R))%:E).
  apply/boolp.funext => t /=; rewrite /quad_form -sumEFin.
  by apply: eq_bigr => a _; rewrite sumEFin.
apply: emeasurable_sum => a; apply: emeasurable_sum => b.
apply/measurable_EFinP; apply: measurable_funM => //.
apply: measurable_funB => //.
by apply: measurable_funM; exact: measurable_tnth.
Qed.

Lemma vec_mx_sum m n (th : 'rV[R]_(m * n)) :
  vec_mx th = \sum_(p < m * n) th 0 p *: vec_mx (delta_mx 0 p).
Proof.
rewrite {1}(matrix_sum_delta th) big_ord1 linear_sum.
by apply: eq_bigr => p _; rewrite linearZ /= (ord1 0).
Qed.

Lemma unsat_cov_formC (kappa : R) d (A B : 'M[R]_d) :
  unsat_cov_form kappa d A B = unsat_cov_form kappa d B A.
Proof.
rewrite /unsat_cov_form mxdotC; congr (_ * (_ + _ + _)).
  by rewrite -(mxdot_trmx A B^T) trmxK mxdotC.
by congr (_ * _); apply: eq_bigr => j _; rewrite mulrC.
Qed.

(* unsat_cov_form kappa d A B is the Frobenius product of A with a matrix
   that depends only on B. *)
Lemma unsat_cov_form_dot (kappa : R) d (A B : 'M[R]_d) :
  unsat_cov_form kappa d A B =
  mxdot A (d%:R^-1 *: (B + B^T + (kappa - 3%:R) *: diag_mx (\row_j B j j))).
Proof.
rewrite /unsat_cov_form !RmultE !RplusE ?RminusE mxdotZr !mxdotDr mxdotZr.
congr (_ * (_ + _ + _ * _)); apply: eq_bigr => i _.
rewrite (bigD1 i) //= big1 ?addr0.
  by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0n mulr0.
by rewrite !mxE eqxx mulr1n.
Qed.

Lemma unsat_cov_form_suml (kappa : R) d I (r : seq I) (c : I -> R)
    (M : I -> 'M[R]_d) (B : 'M[R]_d) :
  unsat_cov_form kappa d (\sum_(k <- r) c k *: M k) B =
  \sum_(k <- r) c k * unsat_cov_form kappa d (M k) B.
Proof.
rewrite unsat_cov_form_dot mxdot_suml; apply: eq_bigr => k _.
by rewrite mxdotZl unsat_cov_form_dot.
Qed.

(* The matrix unsat_cov kappa d represents the form unsat_cov_form. *)
Lemma unsat_covE (kappa : R) d (th th' : 'rV[R]_(d * d)) :
  mxdot (th *m unsat_cov kappa d) th' =
  unsat_cov_form kappa d (vec_mx th) (vec_mx th').
Proof.
rewrite (vec_mx_sum _ _ th) unsat_cov_form_suml /mxdot big_ord1.
under eq_bigr do rewrite mxE big_distrl /=.
rewrite exchange_big /=; apply: eq_bigr => p _.
rewrite unsat_cov_formC (vec_mx_sum _ _ th') unsat_cov_form_suml mulr_sumr.
by apply: eq_bigr => q _; rewrite unsat_cov_formC mxE; ring.
Qed.

(* The matrix x x^T - I of a point t, so that
   quad_form A t = <A, quad_mx t>. *)
Definition quad_mx {d} (t : d.-tuple (measurableTypeR R)) : 'M[R]_d :=
  \matrix_(a, b) ((tnth t a : R) * tnth t b - (a == b)%:R).

Lemma quad_form_mxdot d (A : 'M[R]_d) t :
  quad_form A t = mxdot A (quad_mx t).
Proof. by apply: eq_bigr => a _; apply: eq_bigr => b _; rewrite mxE. Qed.

Lemma exprn4_ge0 (r : R) : 0 <= r ^+ 4.
Proof. by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0. Qed.

Lemma exprn8_ge0 (r : R) : 0 <= r ^+ 8.
Proof. by rewrite (_ : 8 = 4 * 2)%N // exprM sqr_ge0. Qed.

Lemma coord_pow8_le d (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  (tnth t k : R) ^+ 8 <= \sum_(i < d) (tnth t i : R) ^+ 8.
Proof.
rewrite (bigD1 k) //= lerDl; apply: sumr_ge0 => i _; exact: exprn8_ge0.
Qed.

(* (sum_ij Y_ij)^2 <= m n sum_ij Y_ij^2. *)
Lemma sqr_sum_le m n (Y : 'I_m -> 'I_n -> R) :
  (\sum_i \sum_j Y i j) ^+ 2 <= (m * n)%:R * \sum_i \sum_j Y i j ^+ 2.
Proof.
have e1 : \sum_i \sum_j Y i j = mxdot (\matrix_(i, j) Y i j) (const_mx 1).
  by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite !mxE mulr1.
have e2 : \sum_i \sum_j Y i j ^+ 2 =
    mxdot (\matrix_(i, j) Y i j) (\matrix_(i, j) Y i j).
  by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite !mxE expr2.
have e3 : mxdot (const_mx 1 : 'M[R]_(m, n)) (const_mx 1) = (m * n)%:R.
  rewrite /mxdot; under eq_bigr do under eq_bigr do rewrite !mxE mulr1.
  under eq_bigr do rewrite sumr_const card_ord.
  by rewrite sumr_const card_ord natrM mulr_natl.
by rewrite e1 e2 mulrC -e3; exact: mxdot_cauchy_schwarz.
Qed.

Lemma pow4_add_le (u w : R) : (u + w) ^+ 4 <= 8 * (u ^+ 4 + w ^+ 4).
Proof.
have h1 := sqr_ge0 (u - w); have h2 := sqr_ge0 (u ^+ 2 - w ^+ 2).
have h3 : (u + w) ^+ 2 <= 2 * (u ^+ 2 + w ^+ 2) by nra.
have h4 : 0 <= (u + w) ^+ 2 := sqr_ge0 _.
rewrite (_ : 4 = 2 * 2)%N // !exprM; nra.
Qed.

Lemma pow4_sub_le (u w : R) : (u - w) ^+ 4 <= 8 * (u ^+ 4 + w ^+ 4).
Proof.
have h1 := sqr_ge0 (u + w); have h2 := sqr_ge0 (u ^+ 2 - w ^+ 2).
have h3 : (u - w) ^+ 2 <= 2 * (u ^+ 2 + w ^+ 2) by nra.
have h4 : 0 <= (u - w) ^+ 2 := sqr_ge0 _.
rewrite (_ : 4 = 2 * 2)%N // !exprM; nra.
Qed.

Lemma pow8_add_le (u w : R) : (u + w) ^+ 8 <= 2 ^+ 7 * (u ^+ 8 + w ^+ 8).
Proof.
have e (x : R) : x ^+ 8 = (x ^+ 2) ^+ 4 by rewrite -exprM.
have h : (u + w) ^+ 2 <= 2 * (u ^+ 2 + w ^+ 2).
  by have := sqr_ge0 (u - w); nra.
have h4 : ((u + w) ^+ 2) ^+ 4 <= (2 * (u ^+ 2 + w ^+ 2)) ^+ 4.
  rewrite ler_pXn2r // nnegrE ?sqr_ge0 //.
  by rewrite mulr_ge0 // addr_ge0 // sqr_ge0.
have h2 := pow4_add_le (u ^+ 2) (w ^+ 2).
rewrite !e; rewrite exprMn in h4; lra.
Qed.

Lemma pow8_sub_le (u w : R) : (u - w) ^+ 8 <= 2 ^+ 7 * (u ^+ 8 + w ^+ 8).
Proof.
have := pow8_add_le u (- w)%R.
by rewrite -[8%N]/(2 * 4)%N !exprM sqrrN.
Qed.

Lemma quad_mx_entry4_le d (t : d.-tuple (measurableTypeR R)) (a b : 'I_d) :
  quad_mx t a b ^+ 4 <= 8 * (1 + \sum_(k < d) (tnth t k : R) ^+ 8).
Proof.
rewrite mxE; set x := (tnth t a : R); set y := (tnth t b : R).
set v : R := (a == b)%:R; set S := \sum_(k < d) _.
have v4 : v ^+ 4 <= 1 by rewrite /v; case: (a == b); rewrite ?expr1n ?expr0n.
have u4 : (x * y) ^+ 4 <= S.
  have ha : x ^+ 8 <= S := coord_pow8_le _ t a.
  have hb : y ^+ 8 <= S := coord_pow8_le _ t b.
  have h := sqr_ge0 (x ^+ 4 - y ^+ 4).
  rewrite exprMn; rewrite (_ : 8 = 4 * 2)%N // !exprM in ha hb; nra.
have := pow4_sub_le (x * y)%R v; have := exprn4_ge0 v; lra.
Qed.

(* A crude bound, enough for integrability:
   (x^T A x - tr A)^4 <= 8 d^4 |A|_F^4 (1 + sum_k x_k^8). *)
Lemma quad_form_pow4_le d (A : 'M[R]_d) (t : d.-tuple (measurableTypeR R)) :
  quad_form A t ^+ 4 <=
  8 * (d * d)%:R ^+ 2 * mxdot A A ^+ 2 *
    (1 + \sum_(k < d) (tnth t k : R) ^+ 8).
Proof.
set S := 1 + _.
have S0 : 0 <= S by rewrite addr_ge0 // sumr_ge0 // => k _; exact: exprn8_ge0.
set G := quad_mx t.
have GG : mxdot G G ^+ 2 <= (d * d)%:R ^+ 2 * (8 * S).
  have e : mxdot G G = \sum_a \sum_b G a b ^+ 2.
    by apply: eq_bigr => a _; apply: eq_bigr => b _; rewrite expr2.
  rewrite e; apply: le_trans (sqr_sum_le _ _ (fun a b => G a b ^+ 2)) _.
  rewrite expr2 -mulrA ler_wpM2l //.
  apply: le_trans (_ : \sum_(a < d) \sum_(b < d) (8 * S) <= _).
    apply: ler_sum => a _; apply: ler_sum => b _; rewrite -exprM.
    exact: quad_mx_entry4_le.
  under eq_bigr do rewrite sumr_const card_ord.
  rewrite sumr_const card_ord -mulrnA [in X in _ <= X]mulr_natl.
  exact: lexx.
rewrite quad_form_mxdot -/G.
have cs := mxdot_cauchy_schwarz A G.
rewrite (_ : 4 = 2 * 2)%N // exprM.
apply: le_trans (_ : (mxdot A A * mxdot G G) ^+ 2 <= _).
  by rewrite ler_pXn2r ?nnegrE ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0.
rewrite exprMn; apply: le_trans (ler_wpM2l (sqr_ge0 _) GG) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma tnth_tuple_setE d (t : d.-tuple (measurableTypeR R)) (i a : 'I_d)
    (s : R) :
  (tnth (tuple_set t i s) a : R) = tnth t a + (s - tnth t i) * (a == i)%:R.
Proof.
rewrite /tuple_set tnth_mktuple; case: eqP => [->|_].
  by rewrite mulr1 addrC subrK.
by rewrite mulr0 addr0.
Qed.

(* Resampling the coordinate i: with u = x_i - s,
   Q_A (x) - Q_A (x^(i)) = u (sum_b (A_ib + A_bi) x_b - A_ii u). *)
Lemma quad_form_set d (A : 'M[R]_d) (t : d.-tuple (measurableTypeR R))
    (i : 'I_d) (s : R) :
  quad_form A t - quad_form A (tuple_set t i s) =
  (tnth t i - s) * (\sum_(b < d) (A i b + A b i) * tnth t b -
    A i i * (tnth t i - s)).
Proof.
rewrite !quad_formE opprB addrA subrK /quad_sum.
set x := fun b : 'I_d => (tnth t b : R); set D := s - tnth t i.
have e1 : \sum_(a < d) \sum_(b < d) (A a b * x b) * (a == i)%:R =
    \sum_(b < d) A i b * x b.
  by rewrite exchange_big /=; apply: eq_bigr => b _; rewrite sum_delta'.
have e2 : \sum_(a < d) \sum_(b < d) (A a b * x a) * (b == i)%:R =
    \sum_(b < d) A b i * x b.
  by apply: eq_bigr => a _; rewrite sum_delta'.
have e3 : \sum_(a < d) \sum_(b < d) (A a b * (a == i)%:R) * (b == i)%:R =
    A i i.
  by under eq_bigr do rewrite sum_delta'; rewrite sum_delta'.
transitivity (\sum_(a < d) \sum_(b < d)
    (- D * ((A a b * x b) * (a == i)%:R) -
     D * ((A a b * x a) * (b == i)%:R) -
     D ^+ 2 * ((A a b * (a == i)%:R) * (b == i)%:R))).
  rewrite -sumrB; apply: eq_bigr => a _; rewrite -sumrB.
  apply: eq_bigr => b _; rewrite !tnth_tuple_setE -/D /x; ring.
under eq_bigr do rewrite !sumrB -!mulr_sumr.
rewrite !sumrB -!mulr_sumr e1 e2 e3.
under [in RHS]eq_bigr do rewrite mulrDl.
by rewrite big_split /= /D /x; ring.
Qed.

(* The pointwise bound behind the fourth moment of a resampled quadratic
   form, for r > 0 with a^2 <= r. *)
Lemma resample4_le (r u l a : R) : 0 < r -> a ^+ 2 <= r ->
  (u * (l - a * u)) ^+ 4 <=
  (2 ^+ 6 + 2^-1) * (r ^+ 2 * u ^+ 8) + 2 ^+ 6 * (l ^+ 8 / r ^+ 2).
Proof.
move=> r0 ar.
have rn0 : r != 0 by rewrite gt_eqF.
have r2 : 0 < r ^+ 2 by rewrite exprn_gt0.
have V8 : (l - a * u) ^+ 8 <= 2 ^+ 7 * (l ^+ 8 + a ^+ 8 * u ^+ 8).
  by rewrite -exprMn; exact: pow8_sub_le.
move: (l - a * u) V8 => V V8.
have amgm : 2 * (u ^+ 4 * V ^+ 4) <= r ^+ 2 * u ^+ 8 + V ^+ 8 / r ^+ 2.
  have h := sqr_ge0 (r * u ^+ 4 - V ^+ 4 / r).
  have e : (r * u ^+ 4 - V ^+ 4 / r) ^+ 2 =
      r ^+ 2 * u ^+ 8 - 2 * (u ^+ 4 * V ^+ 4) + V ^+ 8 / r ^+ 2.
    by field.
  by rewrite e in h; lra.
have a8 : a ^+ 8 <= r ^+ 4.
  rewrite -[8%N]/(2 * 4)%N exprM ler_pXn2r // nnegrE ?sqr_ge0 //.
  exact: ltW.
have au : a ^+ 8 * u ^+ 8 / r ^+ 2 <= r ^+ 2 * u ^+ 8.
  rewrite ler_pdivrMr // (_ : r ^+ 2 * u ^+ 8 * r ^+ 2 = r ^+ 4 * u ^+ 8).
    by ring.
  by apply: ler_wpM2r => //; exact: exprn8_ge0.
have V8r : V ^+ 8 / r ^+ 2 <=
    2 ^+ 7 * (l ^+ 8 / r ^+ 2 + a ^+ 8 * u ^+ 8 / r ^+ 2).
  have ir : 0 <= (r ^+ 2)^-1 by rewrite invr_ge0 ltW.
  by have h := ler_wpM2r ir V8; lra.
rewrite exprMn; lra.
Qed.

(* A function on 'I_d as a function on nat, zero outside, for the lemmas of
   the library that index by nat. *)
Definition ord_fun {d} (f : 'I_d -> R) (j : nat) : R :=
  \sum_(k < d | (k : nat) == j) f k.

Lemma ord_funE d (f : 'I_d -> R) (k : 'I_d) : ord_fun f k = f k.
Proof. by rewrite /ord_fun (big_pred1 k). Qed.

Section resample_integrals.
Local Open Scope ereal_scope.
Variables (d : nat) (nu : nat -> probability (measurableTypeR R) R) (i : 'I_d).
Local Notation P := (tuple_prod nu d).
Local Notation T := (d.-tuple (measurableTypeR R)).

(* The mean over x and a resampled coordinate s is an integral against the
   product measure; its marginals are P, nu i and, for the resampled point,
   P again. *)
Lemma resample_prod (G : T * measurableTypeR R -> \bar R) :
  measurable_fun setT G -> (forall p, 0 <= G p) ->
  \int[P]_t \int[nu i]_s G (t, s) = \int[P \x nu i]_p G p.
Proof.
move=> mG G0; rewrite (fubini_tonelli1 (m1 := P) (m2 := nu i) _ mG G0).
by rewrite /fubini_F.
Qed.

Lemma resample_fst (f : T -> \bar R) :
  measurable_fun setT f -> (forall t, 0 <= f t) ->
  \int[P \x nu i]_p f p.1 = \int[P]_t f t.
Proof.
move=> mf f0; rewrite -resample_prod.
- exact: measurableT_comp mf measurable_fst.
- by move=> p; exact: f0.
apply: eq_integral => t _ /=.
rewrite (@integral_cst _ _ _ (nu i) _ measurableT (f t)).
by rewrite [X in _ * X]probability_setT mule1.
Qed.

Lemma resample_snd (g : measurableTypeR R -> \bar R) :
  measurable_fun setT g -> (forall s, 0 <= g s) ->
  \int[P \x nu i]_p g p.2 = \int[nu i]_s g s.
Proof.
move=> mg g0; rewrite -resample_prod.
- exact: measurableT_comp mg measurable_snd.
- by move=> p; exact: g0.
rewrite (@integral_cst _ _ _ P _ measurableT (\int[nu i]_s g s)).
by rewrite [X in _ * X]probability_setT mule1.
Qed.

Lemma resample_set (f : T -> \bar R) :
  measurable_fun setT f -> (forall t, 0 <= f t) ->
  \int[P \x nu i]_p f (tuple_set p.1 i p.2) = \int[P]_t f t.
Proof.
move=> mf f0; rewrite -resample_prod.
- exact: measurableT_comp mf (measurable_tuple_set_pair i).
- by move=> p; exact: f0.
by rewrite [RHS](ge0_integral_tuple_prod_set nu i mf f0).
Qed.

End resample_integrals.

Section product_moments.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).

Local Notation P := (tuple_prod nu d).

Lemma integrable_coord_pow (a : 'I_d) k :
  P.-integrable setT (fun t => ((tnth t a : R) ^+ k)%:E).
Proof.
have ia := @coordinate_law_integrable _ _ _ (hnu a (ltn_ord a)) k.
have mk : measurable_fun setT (fun s : measurableTypeR R => ((s : R) ^+ k)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
apply/integrableP; split.
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_tnth.
rewrite (ge0_integral_tuple_prod_coord nu a
  (f := fun s => `|((s : R) ^+ k)%:E|)) //.
- exact: measurableT_comp mk.
- by have /integrableP[] := ia.
Qed.

(* A function bounded by C (1 + sum_i x_i^p) is integrable. *)
Lemma integrable_poly p (f : d.-tuple (measurableTypeR R) -> RR) (C : R) :
  measurable_fun setT f ->
  (forall t, `|f t| <= C * (1 + \sum_(i < d) (tnth t i : R) ^+ p))%R ->
  P.-integrable setT (EFin \o f).
Proof.
move=> mf fC.
have ig : P.-integrable setT
    (fun t => (C * (1 + \sum_(i < d) (tnth t i : R) ^+ p))%:E).
  under eq_fun do rewrite EFinM.
  apply: integrableZl => //; under eq_fun do rewrite EFinD.
  apply: integrableD => //; first exact: finite_measure_integrable_cst.
  under eq_fun do rewrite -sumEFin.
  apply: integrable_sum; first exact: measurableT.
  by move=> i _; exact: integrable_coord_pow.
apply: le_integrable ig => //; first exact/measurable_EFinP.
move=> t _; change (`|(f t)%:E| <=
  `|(C * (1 + \sum_(i < d) tnth t i ^+ p))%:E|).
by rewrite !abse_EFin lee_fin; apply: le_trans (fC t) _; exact: ler_norm.
Qed.

Lemma coord_pow4_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  ((tnth t k : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
have e4 (r : R) : (0 <= r ^+ 4)%R by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
rewrite (bigD1 k) //=.
have s0 : (0 <= \sum_(i < d | i != k) (tnth t i : R) ^+ 4)%R.
  by rewrite sumr_ge0.
lra.
Qed.

(* A product of four factors, each a coordinate or 1. *)
Lemma prod4_le (t : d.-tuple (measurableTypeR R)) (y1 y2 y3 y4 : R) :
  (y1 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y2 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y3 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y4 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (`|y1 * y2 * y3 * y4| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
set S := (1 + _)%R => h1 h2 h3 h4.
by apply: le_trans (amgm4 y1 y2 y3 y4) _; lra.
Qed.

(* A power of the coordinate a and a function of the other coordinates. *)
Lemma coord_extract (a : 'I_d) k (H : d.-tuple (measurableTypeR R) -> RR) :
  measurable_fun setT H ->
  (forall t, `|H t| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (forall t s, H (tuple_set t a s) = H t) ->
  \int[P]_t (((tnth t a : R) ^+ k) * H t)%:E =
  \int[nu a]_s ((s : R) ^+ k)%:E * \int[P]_t (H t)%:E.
Proof.
move=> mH Hb Hind.
have iH : P.-integrable setT (EFin \o H).
  by apply: (integrable_poly 4 _ 1) => // t; rewrite mul1r.
have ik := @coordinate_law_integrable _ _ _ (hnu a (ltn_ord a)) k.
by have [_ ->] := integral_tuple_prod_coordM
  (f := fun s : measurableTypeR R => ((s : R) ^+ k)%R) ik iH Hind.
Qed.

Lemma one_pow4_le (t : d.-tuple (measurableTypeR R)) :
  ((1 : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
rewrite expr1n lerDl sumr_ge0 // => i _.
by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
Qed.

Lemma coord_abs_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  (`|(tnth t k : R)| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
have one4 := one_pow4_le t.
have := @prod4_le t (tnth t k) 1 1 1 (coord_pow4_le t k) one4 one4 one4.
by rewrite !mulr1.
Qed.

Lemma moment1 (a : 'I_d) : \int[P]_t ((tnth t a : R))%:E = 0.
Proof.
rewrite (integral_tuple_prod_coord nu a
  (f := fun s : measurableTypeR R => ((s : R))%:E)).
- by apply/measurable_EFinP.
- exact: (@coordinate_law_mean _ _ _ (hnu a (ltn_ord a))).
Qed.

Lemma moment2 (a b : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b)%:E = ((a == b)%:R)%:E.
Proof.
case: (eqVneq a b) => [<-|ab].
  under eq_integral do rewrite -expr2.
  rewrite (integral_tuple_prod_coord nu a
    (f := fun s : measurableTypeR R => ((s : R) ^+ 2)%:E)).
  - by apply/measurable_EFinP; exact: measurable_funX.
  - by rewrite (@coordinate_law_second _ _ _ (hnu a (ltn_ord a))).
rewrite -[RHS](mule0 (\int[P]_t (tnth t b : R)%:E)) muleC.
rewrite -(@coordinate_law_mean _ _ _ (hnu a (ltn_ord a))).
have Hind (t : d.-tuple (measurableTypeR R)) s :
    (tnth (tuple_set t a s) b : RR) = tnth t b.
  by rewrite tnth_tuple_set_neq // eq_sym.
have := coord_extract a 1 (fun t => (tnth t b : RR)) (measurable_tnth b)
  (fun t => coord_abs_le t b) Hind.
under eq_integral do rewrite expr1.
by under [X in _ = X * _]eq_integral do rewrite expr1.
Qed.

Lemma moment4 (a b c e : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E =
  ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
   (a == e)%:R * (b == c)%:R +
   (kappa - 3) * (((a == b) && (a == c)) && (a == e))%:R)%:E.
Proof.
have one4 := one_pow4_le; have c4 := coord_pow4_le.
have h2 := @coordinate_law_second _ _ _ (hnu a (ltn_ord a)).
have h4 := @coordinate_law_fourth _ _ _ (hnu a (ltn_ord a)).
have ind (k : 'I_d) (t : d.-tuple (measurableTypeR R)) s :
    k != a -> (tnth (tuple_set t a s) k : R) = tnth t k.
  by move=> ka; rewrite tnth_tuple_set_neq.
(* x_a^k times one, two or three coordinates other than a *)
have ext1 k (k1 : 'I_d) : k1 != a ->
    \int[P]_t (((tnth t a : R) ^+ k) * tnth t k1)%:E =
    \int[nu a]_s ((s : R) ^+ k)%:E * \int[P]_t ((tnth t k1 : R))%:E.
  move=> k1a.
  apply: (coord_extract a k (fun t => (tnth t k1 : RR))) => //.
  - exact: measurable_tnth.
  - by move=> t; exact: coord_abs_le.
  - by move=> t s /=; rewrite ind.
have ext2 k (k1 k2 : 'I_d) : k1 != a -> k2 != a ->
    \int[P]_t (((tnth t a : R) ^+ k) * (tnth t k1 * tnth t k2))%:E =
    \int[nu a]_s ((s : R) ^+ k)%:E *
      \int[P]_t ((tnth t k1 : R) * tnth t k2)%:E.
  move=> k1a k2a.
  refine (coord_extract a k
    (fun t => ((tnth t k1 : RR) * (tnth t k2 : RR))%R) _ _ _).
  - by apply: measurable_funM; exact: measurable_tnth.
  - move=> t; have := @prod4_le t _ _ _ _ (c4 t k1) (c4 t k2) (one4 t)
      (one4 t).
    by rewrite !mulr1.
  - by move=> t s /=; rewrite !ind.
have ext3 (k1 k2 k3 : 'I_d) : k1 != a -> k2 != a -> k3 != a ->
    \int[P]_t (((tnth t a : R) ^+ 1) *
      (tnth t k1 * tnth t k2 * tnth t k3))%:E =
    \int[nu a]_s ((s : R) ^+ 1)%:E *
      \int[P]_t ((tnth t k1 : R) * tnth t k2 * tnth t k3)%:E.
  move=> k1a k2a k3a.
  refine (coord_extract a 1 (fun t =>
    ((tnth t k1 : RR) * (tnth t k2 : RR) * (tnth t k3 : RR))%R) _ _ _).
  - apply: measurable_funM; last exact: measurable_tnth.
    by apply: measurable_funM; exact: measurable_tnth.
  - move=> t; have := @prod4_le t _ _ _ _ (c4 t k1) (c4 t k2) (c4 t k3)
      (one4 t).
    by rewrite !mulr1.
  - by move=> t s /=; rewrite !ind.
have m1 : \int[nu a]_s ((s : R) ^+ 1)%:E = 0.
  under eq_integral do rewrite expr1.
  exact: (@coordinate_law_mean _ _ _ (hnu a (ltn_ord a))).
have [<-|ab] := eqVneq a b; have [<-|ac] := eqVneq a c;
  have [<-|ae] := eqVneq a e; rewrite ?eqxx /=.
- (* a = b = c = e *)
  transitivity (\int[P]_t ((tnth t a : R) ^+ 4)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (integral_tuple_prod_coord nu a
    (f := fun s : measurableTypeR R => ((s : R) ^+ 4)%:E)).
  + by apply/measurable_EFinP; exact: measurable_funX.
  + by rewrite h4; congr EFin; ring.
- (* a = b = c, e <> a *)
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 3 * tnth t e)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  by rewrite (ext1 3%N e ea) moment1 mule0; congr EFin; ring.
- (* a = b = e, c <> a *)
  have ca : c != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 3 * tnth t c)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext1 3%N c ca) moment1 mule0 (negbTE ca).
  by rewrite /= !(mulr0, mul0r, addr0, mulr0n).
- (* a = b, c <> a, e <> a *)
  have ca : c != a by rewrite eq_sym.
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t c * tnth t e))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  by rewrite (ext2 2%N c e ca ea) h2 mul1e moment2; congr EFin; ring.
- (* a = c = e, b <> a *)
  have ba : b != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 3 * tnth t b)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext1 3%N b ba) moment1 mule0 (negbTE ba).
  by rewrite /= !(mulr0, mul0r, addr0, mulr0n).
- (* a = c, b <> a, e <> a *)
  have ba : b != a by rewrite eq_sym.
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t b * tnth t e))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext2 2%N b e ba ea) h2 mul1e moment2 (negbTE ba).
  by congr EFin; ring.
- (* a = e, b <> a, c <> a *)
  have ba : b != a by rewrite eq_sym.
  have ca : c != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t b * tnth t c))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  by rewrite (ext2 2%N b c ba ca) h2 mul1e moment2; congr EFin; ring.
- (* b, c, e <> a *)
  have ba : b != a by rewrite eq_sym.
  have ca : c != a by rewrite eq_sym.
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 1 *
    (tnth t b * tnth t c * tnth t e))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext3 b c e ba ca ea) m1 mul0e.
  by rewrite /= !(mulr0, mul0r, addr0, mulr0n).
Qed.

Lemma integral_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  \int[P]_t (\sum_(i < d) f i t)%:E = \sum_(i < d) \int[P]_t (f i t)%:E.
Proof.
move=> fi; under eq_integral do rewrite -sumEFin.
by rewrite integral_sum.
Qed.

Lemma integrable_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  P.-integrable setT (fun t => (\sum_(i < d) f i t)%:E).
Proof.
move=> fi; under eq_fun do rewrite -sumEFin.
by apply: integrable_sum => // i _.
Qed.

Lemma integrable_x2 (a b : 'I_d) :
  P.-integrable setT (fun t => ((tnth t a : R) * tnth t b)%:E).
Proof.
apply: (integrable_poly 4 (fun t => ((tnth t a : RR) * (tnth t b : RR))%R) 1).
  by apply: measurable_funM; exact: measurable_tnth.
move=> t; rewrite mul1r.
have := @prod4_le t _ _ _ _ (coord_pow4_le t a) (coord_pow4_le t b)
  (one_pow4_le t) (one_pow4_le t).
by rewrite !mulr1.
Qed.

Lemma integrable_x4 (a b c e : 'I_d) :
  P.-integrable setT
    (fun t => ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E).
Proof.
apply: (integrable_poly 4 (fun t =>
  ((tnth t a : RR) * (tnth t b : RR) * (tnth t c : RR) * (tnth t e : RR))%R) 1).
  apply: measurable_funM; last exact: measurable_tnth.
  apply: measurable_funM; last exact: measurable_tnth.
  by apply: measurable_funM; exact: measurable_tnth.
move=> t; rewrite mul1r.
exact: (@prod4_le t _ _ _ _ (coord_pow4_le t a) (coord_pow4_le t b)
  (coord_pow4_le t c) (coord_pow4_le t e)).
Qed.

Lemma integrable_quad_sum (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_sum A t)%:E).
Proof.
apply: integrable_sum_ord => a; apply: integrable_sum_ord => b.
under eq_fun do rewrite EFinM.
by apply: integrableZl => //; exact: integrable_x2.
Qed.

Lemma integrable_quad_sum2 (A B : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_sum A t * quad_sum B t)%:E).
Proof.
apply: (@eq_integrable _ _ _ P setT measurableT (fun t =>
  (\sum_(a < d) \sum_(b < d) \sum_(c < d) \sum_(e < d)
    (A a b * B c e) * ((tnth t a : R) * tnth t b * tnth t c * tnth t e))%:E)).
  move=> t _; congr EFin.
  rewrite /quad_sum mulr_suml; apply: eq_bigr => a _.
  rewrite mulr_suml; apply: eq_bigr => b _.
  rewrite mulr_sumr; apply: eq_bigr => c _.
  by rewrite mulr_sumr; apply: eq_bigr => e _; ring.
apply: integrable_sum_ord => a; apply: integrable_sum_ord => b.
apply: integrable_sum_ord => c; apply: integrable_sum_ord => e.
under eq_fun do rewrite EFinM.
by apply: integrableZl => //; exact: integrable_x4.
Qed.

Lemma quad_sum_mean (A : 'M[R]_d) :
  \int[P]_t (quad_sum A t)%:E = (\tr A)%:E.
Proof.
have iab a b : P.-integrable setT
    (fun t => (A a b * ((tnth t a : R) * tnth t b))%:E).
  under eq_fun do rewrite EFinM.
  by apply: integrableZl => //; exact: integrable_x2.
rewrite /quad_sum integral_sum_ord.
  by move=> a; exact: integrable_sum_ord.
rewrite /mxtrace -sumEFin; apply: eq_bigr => a _.
rewrite integral_sum_ord //.
transitivity (\sum_(b < d) (A a b * (a == b)%:R)%:E)%R.
  apply: eq_bigr => b _; under eq_integral do rewrite EFinM.
  rewrite integralZl //; first exact: integrable_x2.
  by rewrite moment2 -EFinM.
rewrite sumEFin (bigD1 a) //= eqxx mulr1 big1 ?addr0 // => b ba.
by rewrite eq_sym (negbTE ba) mulr0.
Qed.

Lemma quad_sum_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_sum A t * quad_sum B t)%:E =
  (\tr A * \tr B + mxdot A B + mxdot A B^T +
   (kappa - 3) * \sum_(a < d) A a a * B a a)%:E.
Proof.
pose X t (a b c e : 'I_d) :=
  ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%R.
have it a b c e : P.-integrable setT
    (fun t => ((A a b * B c e) * X t a b c e)%:E).
  under eq_fun do rewrite EFinM.
  by apply: integrableZl => //; exact: integrable_x4.
transitivity (\int[P]_t (\sum_(a < d) \sum_(b < d) \sum_(c < d) \sum_(e < d)
    (A a b * B c e) * X t a b c e)%:E).
  apply: eq_integral => t _; congr EFin.
  rewrite /quad_sum mulr_suml; apply: eq_bigr => a _.
  rewrite mulr_suml; apply: eq_bigr => b _.
  rewrite mulr_sumr; apply: eq_bigr => c _.
  by rewrite mulr_sumr; apply: eq_bigr => e _; rewrite /X; ring.
have i3 a b c : P.-integrable setT
    (fun t => (\sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: integrable_sum_ord.
have i2 a b : P.-integrable setT (fun t =>
    (\sum_(c < d) \sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: integrable_sum_ord.
have i1 a : P.-integrable setT (fun t => (\sum_(b < d) \sum_(c < d)
    \sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: integrable_sum_ord.
rewrite integral_sum_ord //.
transitivity (\sum_(a < d) (\sum_(b < d) \sum_(c < d) \sum_(e < d)
  A a b * B c e * ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
  (a == e)%:R * (b == c)%:R +
  (kappa - 3) * (((a == b) && (a == c)) && (a == e))%:R))%:E)%R.
  apply: eq_bigr => a _.
  rewrite integral_sum_ord // -sumEFin; apply: eq_bigr => b _.
  rewrite integral_sum_ord // -sumEFin; apply: eq_bigr => c _.
  rewrite integral_sum_ord // -sumEFin; apply: eq_bigr => e _.
  under eq_integral do rewrite EFinM.
  rewrite integralZl //; first exact: integrable_x4.
  by rewrite moment4 -EFinM.
rewrite sumEFin; congr EFin.
transitivity (\sum_(a < d) \sum_(b < d) A a b * ((a == b)%:R * \tr B +
  B a b + B b a + (kappa - 3) * (a == b)%:R * B a a))%R.
  apply: eq_bigr => a _; apply: eq_bigr => b _.
  rewrite -moment4_sum mulr_sumr; apply: eq_bigr => c _.
  by rewrite mulr_sumr; apply: eq_bigr => e _; ring.
transitivity (\sum_(a < d) \sum_(b < d)
  ((A a b * \tr B + (kappa - 3) * A a b * B a a) * (a == b)%:R +
   A a b * B a b + A a b * B b a))%R.
  by apply: eq_bigr => a _; apply: eq_bigr => b _; ring.
under eq_bigr => a _ do rewrite !big_split /= sum_delta.
rewrite !big_split /= /mxdot /mxtrace -mulr_suml.
under [X in (_ + X + _ + _)%R = _]eq_bigr do rewrite -mulrA.
rewrite -mulr_sumr.
under [X in _ = (_ + _ + X + _)%R]eq_bigr do under eq_bigr do rewrite mxE.
ring.
Qed.

Lemma integrable_quad_form (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t)%:E).
Proof.
under eq_fun do rewrite quad_formE EFinB.
apply: integrableB => //; first exact: integrable_quad_sum.
exact: finite_measure_integrable_cst.
Qed.

Lemma integrable_quad_form2 (A B : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t * quad_form B t)%:E).
Proof.
apply: (@eq_integrable _ _ _ P setT measurableT (fun t =>
  (quad_sum A t * quad_sum B t -
   (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B))%:E)).
  by move=> t _; rewrite !quad_formE; congr EFin; ring.
under eq_fun do rewrite EFinB.
apply: integrableB => //; first exact: integrable_quad_sum2.
under eq_fun do rewrite EFinB EFinD !EFinM.
apply: integrableB => //; last exact: finite_measure_integrable_cst.
by apply: integrableD => //; apply: integrableZl => //;
  exact: integrable_quad_sum.
Qed.

(* Covariance matching: the covariance of the features is C_kappa. *)
Lemma quad_form_mean (A : 'M[R]_d) : \int[P]_t (quad_form A t)%:E = 0.
Proof.
under eq_integral do rewrite quad_formE EFinB.
rewrite integralB_EFin //.
- exact: integrable_quad_sum.
- exact: finite_measure_integrable_cst.
rewrite quad_sum_mean integral_cst //.
by rewrite [X in _ - _ * X]probability_setT mule1 subee.
Qed.

Lemma quad_form_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_form A t * quad_form B t)%:E =
  (mxdot A B + mxdot A B^T + (kappa - 3) * \sum_(a < d) A a a * B a a)%:E.
Proof.
have iA := integrable_quad_sum A; have iB := integrable_quad_sum B.
have iAB := integrable_quad_sum2 A B.
have iL : P.-integrable setT (fun t =>
    (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B)%:E).
  under eq_fun do rewrite EFinB EFinD !EFinM.
  apply: integrableB => //; last exact: finite_measure_integrable_cst.
  by apply: integrableD => //; apply: integrableZl.
transitivity (\int[P]_t ((quad_sum A t * quad_sum B t)%:E -
    (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B)%:E)).
  apply: eq_integral => t _.
  by rewrite -EFinB !quad_formE; congr EFin; ring.
rewrite integralB_EFin // quad_sum_cov.
have -> : \int[P]_x
    (\tr B * quad_sum A x + \tr A * quad_sum B x - \tr A * \tr B)%:E =
    (\tr A * \tr B)%:E.
  under eq_integral do rewrite EFinB EFinD !EFinM.
  rewrite integralB //.
  - by apply: integrableD => //; apply: integrableZl.
  - by rewrite -EFinM; exact: finite_measure_integrable_cst.
  rewrite integralD //; try by apply: integrableZl.
  rewrite (integralZl measurableT iA) (integralZl measurableT iB).
  rewrite !quad_sum_mean integral_cst //.
  rewrite [X in _ - _ * X]probability_setT mule1 -!EFinM -EFinD.
  by congr EFin; ring.
by rewrite -EFinB; congr EFin; ring.
Qed.

Lemma coord_moment8 (j : 'I_d) :
  \int[nu j]_s ((s : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof.
have := @coordinate_law_moment _ _ _ (hnu j (ltn_ord j)) 4.
by rewrite /= -natrM.
Qed.

Lemma coord_tuple_moment8 (j : 'I_d) :
  \int[P]_t ((tnth t j : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof.
rewrite (ge0_integral_tuple_prod_coord nu j
  (f := fun s => ((s : R) ^+ 8)%:E)).
- by apply/measurable_EFinP; exact: measurable_funX.
- by move=> s; rewrite lee_fin exprn8_ge0.
exact: coord_moment8.
Qed.

(* The eighth moment of a linear form, from Hoeffding's inequality
   (probability/subgaussian.v): E <c, x>^8 <= 48 4^8 K^8 |c|^8. *)
Lemma lin_form_moment8 (c : 'I_d -> R) :
  \int[P]_t ((\sum_(b < d) c b * tnth t b) ^+ 8)%:E <=
  (48 * 4 ^+ 8 * K ^+ 8 * (\sum_(b < d) c b ^+ 2) ^+ 4)%:E.
Proof.
have [S0|S0] := eqVneq (\sum_(b < d) c b ^+ 2)%R 0%R.
  have c0 b : c b = 0%R.
    apply/eqP; rewrite -sqrf_eq0; apply/eqP.
    by move/psumr_eq0P : S0 => -> // b' _; exact: sqr_ge0.
  rewrite integral0_eq.
    by move=> t _; rewrite big1 ?expr0n // => b _; rewrite c0 mul0r.
  by rewrite S0 expr0n /= mulr0.
have K0 : (0 < K)%R.
  case: (pickP (fun b : 'I_d => true)) => [b _|h].
    exact: (@coordinate_law_K _ _ _ (hnu b (ltn_ord b))).
  by move: S0; rewrite big1 ?eqxx // => b _; move: (h b).
pose a := ord_fun c.
have aE (b : 'I_d) : a b = c b := ord_funE _ c b.
have Spos : (0 < \sum_(b < d) c b ^+ 2)%R.
  by rewrite lt_def S0 /=; apply: sumr_ge0 => b _; exact: sqr_ge0.
have S0' : (0 < \sum_(j < d) a j ^+ 2 * K ^+ 2)%R.
  under eq_bigr do rewrite aE.
  by rewrite -mulr_suml mulr_gt0 // exprn_gt0.
have sg : forall j, (j < d)%N -> subgaussian (nu j) (fun x : R => x) K.
  by move=> j jd; exact: (@coordinate_law_subgaussian _ _ _ (hnu j jd)).
have m0 : forall j, (j < d)%N -> (\int[nu j]_t (fun x : R => x) t)%R = 0%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (@coordinate_law_mean _ _ _ (hnu j jd)).
have := subgaussian_moment 4 (subgaussian_sum (mu := nu) (n := d)
  (f := fun=> fun x : measurableTypeR R => (x : R)) (K := fun=> K) (a := a)
  sg m0 S0') => h.
under eq_integral do under eq_bigr do rewrite -aE.
apply: le_trans h _; rewrite lee_fin.
under eq_bigr do rewrite aE.
rewrite -mulr_suml exprMn (exprM (Num.sqrt _) 2 4) sqr_sqrtr.
  by rewrite mulr_ge0 ?sqr_ge0 // sumr_ge0 // => b _; exact: sqr_ge0.
rewrite (_ : 4`! = 24)%N // (_ : 2 * 4 = 8)%N //.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma integrable_quad_form_pow4 (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t ^+ 4)%:E).
Proof.
apply: (integrable_poly 8 (fun t => quad_form A t ^+ 4 : RR)%R
  (8 * (d * d)%:R ^+ 2 * mxdot A A ^+ 2)%R).
  by apply: measurable_funX; exact: measurable_quad_form.
move=> t; rewrite ger0_norm ?exprn4_ge0 //; exact: quad_form_pow4_le.
Qed.

Lemma quad_form_pow4_fin (A : 'M[R]_d) :
  \int[P]_t (quad_form A t ^+ 4)%:E < +oo.
Proof.
have /integrableP[_ h] := integrable_quad_form_pow4 A.
apply: le_lt_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_integral => t _; rewrite gee0_abs // lee_fin exprn4_ge0.
Qed.

(* The fourth moment of the difference after resampling the coordinate i:
   E (Q_A (x) - Q_A (x^(i)))^4 <= (2^16 K^4 r_i)^2, where r_i is the
   squared norm of the row and the column i of A. *)
Lemma quad_form_resample4 (A : 'M[R]_d) (i : 'I_d) :
  \int[P]_t \int[nu i]_s
    ((quad_form A t - quad_form A (tuple_set t i s)) ^+ 4)%:E <=
  ((2 ^+ 16 * K ^+ 4 * \sum_(b < d) (A i b ^+ 2 + A b i ^+ 2)) ^+ 2)%:E.
Proof.
set r := (\sum_(b < d) _)%R.
have r0 : (0 <= r)%R by apply: sumr_ge0 => b _; rewrite addr_ge0 ?sqr_ge0.
have K0 : (0 < K)%R := @coordinate_law_K _ _ _ (hnu i (ltn_ord i)).
pose G (p : d.-tuple (measurableTypeR R) * measurableTypeR R) :=
  ((quad_form A p.1 - quad_form A (tuple_set p.1 i p.2)) ^+ 4)%:E.
have mG : measurable_fun setT G.
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurableT_comp (measurable_quad_form d A) measurable_fst.
  exact: measurableT_comp (measurable_quad_form d A)
    (measurable_tuple_set_pair i).
have G0 p : 0 <= G p by rewrite lee_fin exprn4_ge0.
rewrite (resample_prod d nu i G mG G0).
have [rz|rp] := eqVneq r 0%R.
  have A0 b : (A i b = 0 /\ A b i = 0)%R.
    have h : (A i b ^+ 2 + A b i ^+ 2 = 0)%R.
      apply: (psumr_eq0P _ rz) => // b' _.
      by rewrite addr_ge0 ?sqr_ge0.
    move/eqP: h; rewrite paddr_eq0 ?sqr_ge0 // !sqrf_eq0.
    by move=> /andP[/eqP-> /eqP->].
  rewrite integral0_eq; last by rewrite lee_fin sqr_ge0.
  move=> p _; rewrite /G quad_form_set (proj1 (A0 i)).
  rewrite big1 ?mul0r ?subr0 ?mulr0 ?expr0n // => b _.
  by rewrite (proj1 (A0 b)) (proj2 (A0 b)) addr0 mul0r.
have rpos : (0 < r)%R by rewrite lt_def rp r0.
set c := fun b : 'I_d => (A i b + A b i)%R.
set C1 : R := ((2 ^+ 6 + 2^-1) * r ^+ 2 * 2 ^+ 7)%R.
set C2 : R := (2 ^+ 6 / r ^+ 2)%R.
have C10 : (0 <= C1)%R by rewrite /C1 !mulr_ge0 ?addr_ge0 ?exprn_ge0 ?sqr_ge0.
have C20 : (0 <= C2)%R by rewrite /C2 divr_ge0 ?exprn_ge0 ?sqr_ge0.
pose l (t : d.-tuple (measurableTypeR R)) := (\sum_(b < d) c b * tnth t b)%R.
have ml : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) => l t : RR).
  apply: measurable_sum => b; apply: measurable_funM => //.
  exact: measurable_tnth.
have mx8 : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) => ((tnth t i : RR) ^+ 8)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_tnth.
have ms8 : measurable_fun setT
    (fun s : measurableTypeR R => ((s : RR) ^+ 8)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have ml8 : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) => ((l t : RR) ^+ 8)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
apply: (@le_trans _ _ (\int[P \x nu i]_p
    ((C1%:E * ((tnth p.1 i : R) ^+ 8)%:E + C1%:E * ((p.2 : R) ^+ 8)%:E) +
     C2%:E * ((l p.1) ^+ 8)%:E))).
  apply: ge0_le_integral => //.
    apply: emeasurable_funD; first apply: emeasurable_funD.
    - by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
    - by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
    - by apply: measurable_funeM; exact: measurableT_comp ml8 measurable_fst.
  move=> p _; rewrite /G -!EFinM -!EFinD lee_fin quad_form_set.
  have ar : (A i i ^+ 2 <= r)%R.
    rewrite /r (bigD1 i) //= -addrA lerDl addr_ge0 ?sqr_ge0 //.
    by apply: sumr_ge0 => b _; rewrite addr_ge0 ?sqr_ge0.
  have h2 := resample4_le r (tnth p.1 i - p.2)%R (l p.1) (A i i) rpos ar.
  have h1 := pow8_sub_le (tnth p.1 i) p.2.
  have e : (\sum_(b < d) (A i b + A b i) * tnth p.1 b)%R = l p.1 by [].
  rewrite e; apply: le_trans h2 _.
  rewrite /C1 /C2; have h3 : (0 <= r ^+ 2)%R := sqr_ge0 _.
  nra.
clear mG G0 ml G.
rewrite ge0_integralD //.
- by move=> p _; rewrite adde_ge0 // mule_ge0 ?lee_fin ?exprn8_ge0.
- apply: emeasurable_funD.
  + by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
  + by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
- by move=> p _; rewrite mule_ge0 ?lee_fin ?exprn8_ge0.
- by apply: measurable_funeM; exact: measurableT_comp ml8 measurable_fst.
rewrite ge0_integralD //.
- by move=> p _; rewrite mule_ge0 ?lee_fin ?exprn8_ge0.
- by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
- by move=> p _; rewrite mule_ge0 ?lee_fin ?exprn8_ge0.
- by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
rewrite ge0_integralZl_EFin //.
- by move=> p _; rewrite lee_fin exprn8_ge0.
- exact: measurableT_comp mx8 measurable_fst.
rewrite ge0_integralZl_EFin //.
- by move=> p _; rewrite lee_fin exprn8_ge0.
- exact: measurableT_comp ms8 measurable_snd.
rewrite ge0_integralZl_EFin //.
- by move=> p _; rewrite lee_fin exprn8_ge0.
- exact: measurableT_comp ml8 measurable_fst.
have e80 (y : R) : 0 <= (y ^+ 8)%:E by rewrite lee_fin exprn8_ge0.
rewrite (resample_fst d nu i _ mx8); first by move=> t; exact: e80.
rewrite (resample_snd d nu i _ ms8); first by move=> s; exact: e80.
rewrite (resample_fst d nu i _ ml8); first by move=> t; exact: e80.
clear mx8 ms8 ml8.
have B1 := coord_tuple_moment8 i.
have B2 := coord_moment8 i.
have B3 := lin_form_moment8 c.
have hc : (\sum_(b < d) c b ^+ 2 <= 2 * r)%R.
  rewrite /r mulr_sumr; apply: ler_sum => b _; rewrite /c.
  by have := sqr_ge0 (A i b - A b i); nra.
have hc4 : ((\sum_(b < d) c b ^+ 2) ^+ 4 <= (2 * r) ^+ 4)%R.
  rewrite ler_pXn2r // nnegrE ?mulr_ge0 //.
  by apply: sumr_ge0 => b _; exact: sqr_ge0.
have C1' : 0 <= C1%:E by rewrite lee_fin.
have C2' : 0 <= C2%:E by rewrite lee_fin.
apply: le_trans (leeD (leeD (lee_wpmul2l C1' B1) (lee_wpmul2l C1' B2))
  (lee_wpmul2l C2' B3)) _.
rewrite -!EFinM -!EFinD lee_fin.
have K8 : (0 <= K ^+ 8)%R by rewrite exprn_ge0 // ltW.
have step : (C2 * (48 * 4 ^+ 8 * K ^+ 8 * (\sum_(b < d) c b ^+ 2) ^+ 4) <=
    C2 * (48 * 4 ^+ 8 * K ^+ 8 * (2 * r) ^+ 4))%R.
  by rewrite ler_wpM2l // ler_wpM2l // mulr_ge0.
apply: le_trans (lerD (lexx _) step) _.
have e : (C2 * (48 * 4 ^+ 8 * K ^+ 8 * (2 * r) ^+ 4) =
    2 ^+ 6 * 48 * 4 ^+ 8 * 16 * (r ^+ 2 * K ^+ 8))%R.
  by rewrite /C2; field; rewrite expf_neq0.
have rK : (0 <= r ^+ 2 * K ^+ 8)%R by rewrite mulr_ge0 ?sqr_ge0.
have e2 : ((2 ^+ 16 * K ^+ 4 * r) ^+ 2 = 2 ^+ 32 * (r ^+ 2 * K ^+ 8))%R.
  by ring.
rewrite e /C1 e2; lra.
Qed.

(* The fourth moment of the quadratic form, by the moment bound of
   Efron-Stein (probability/efron_stein.v):
   E (x^T A x - tr A)^4 <= 9 2^33 K^8 |A|_F^4. *)
Lemma quad_form_moment4 (A : 'M[R]_d) :
  \int[P]_t (quad_form A t ^+ 4)%:E <=
  (9 * 2 ^+ 33 * K ^+ 8 * mxdot A A ^+ 2)%:E.
Proof.
pose r (k : 'I_d) := (\sum_(b < d) (A k b ^+ 2 + A b k ^+ 2))%R.
pose D := ord_fun (fun k => 2 ^+ 16 * K ^+ 4 * r k)%R.
have DE (k : 'I_d) : D k = (2 ^+ 16 * K ^+ 4 * r k)%R by exact: ord_funE.
have D0 j : (0 <= D j)%R.
  apply: sumr_ge0 => k _; apply: mulr_ge0.
    by apply: mulr_ge0; [exact: exprn_ge0 | exact: exprn4_ge0].
  by rewrite /r /=; apply: sumr_ge0 => b _; rewrite addr_ge0 ?sqr_ge0.
have HD (k : 'I_d) : \int[P]_x \int[nu k]_s
    ((quad_form A x - quad_form A (tuple_set x k s)) ^+ 4)%:E <=
    ((D k) ^+ 2)%:E.
  by rewrite DE; exact: quad_form_resample4.
have := efron_stein_fourth (measurable_quad_form d A) (quad_form_pow4_fin A)
  D0 HD.
rewrite quad_form_mean /= => h.
have -> : \int[P]_t (quad_form A t ^+ 4)%:E =
    \int[P]_x ((quad_form A x - 0) ^+ 4)%:E.
  by apply: eq_integral => x _; rewrite subr0.
apply: le_trans h _; rewrite lee_fin.
under eq_bigr do rewrite DE.
have Sr : (\sum_(k < d) r k = 2 * mxdot A A)%R.
  rewrite /r /=; under eq_bigr do rewrite big_split /=.
  rewrite big_split /= [X in (_ + X)%R]exchange_big /= mulrDl mul1r /mxdot.
  by under [in RHS]eq_bigr do under eq_bigr do rewrite -expr2.
rewrite -mulr_sumr Sr.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

End product_moments.

Lemma measurable_mxdotl n (th : 'rV[R]_n) :
  measurable_fun [set: 'rV[RR]_n] (fun z => mxdot z th : RR).
Proof.
rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM => //; exact: measurable_mxentry.
Qed.

(* The operator norm of C_kappa is at least (kappa - 1) / d: the entry of
   E_11 x E_11. *)
Lemma unsat_cov_opnorm_ge (kappa : R) d : (0 < d)%N ->
  (kappa - 1) / d%:R <= opnorm (unsat_cov kappa d).
Proof.
move=> d0; pose i0 : 'I_d := Ordinal d0; pose p := mxvec_index i0 i0.
apply: le_trans (mx_norm_le_opnorm _); apply: le_trans (mx_norm_entry_le _ p p).
apply: le_trans (ler_norm _); rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite mxE vec_mx_delta /unsat_cov_form !RmultE !RplusE ?RminusE.
rewrite trmx_delta mxdot_delta mxE eqxx /=.
rewrite (bigD1 i0) //= big1 ?addr0.
  by move=> j ji; rewrite mxE (negbTE ji) /= mul0r.
by rewrite !mxE eqxx /= mulr1n mulr1; ring.
Qed.

(* On symmetric matrices, C_kappa is the form feature_cov of
   Gaussian/Cones. *)
Lemma unsat_cov_form_sym (kappa : R) d (A B : 'M[R]_d) :
  B \is symmetricmx -> unsat_cov_form kappa d A B = feature_cov kappa A B.
Proof.
move=> /symmetricmxP BT; rewrite /unsat_cov_form BT.
have -> : feature_cov kappa A B = (2 * mxdot A B +
    (kappa - 3) * \sum_(i < d) A i i * B i i) / d%:R by [].
by rewrite !RmultE !RplusE ?RminusE; ring.
Qed.

(* The coercivity of feature_cov: min (2, kappa - 1) |A|_F^2 / d <=
   feature_cov kappa A A, for every A. *)
Lemma feature_cov_ge (kappa : R) d (A : 'M[R]_d) : 1 < kappa ->
  Num.min 2 (kappa - 1) / d%:R * mxdot A A <= feature_cov kappa A A.
Proof.
move=> k1.
have -> : feature_cov kappa A A = (2 * mxdot A A +
    (kappa - 3) * \sum_(i < d) A i i * A i i) / d%:R by [].
set s := \sum_(i < d) A i i * A i i.
have sA : s <= mxdot A A.
  rewrite /s /mxdot; apply: ler_sum => i _.
  rewrite (bigD1 i) //= lerDl; apply: sumr_ge0 => j _.
  by rewrite -expr2 sqr_ge0.
have A0 : 0 <= mxdot A A := mxdot_ge0 A.
have key : Num.min 2 (kappa - 1) * mxdot A A <= 2 * mxdot A A + (kappa - 3) * s.
  have [k3|k3] := lerP 3 kappa.
    apply: le_trans (_ : 2 * mxdot A A <= _).
      by rewrite ler_wpM2r // ge_min lexx.
    rewrite lerDl mulr_ge0 // ?subr_ge0 //.
    by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
  apply: le_trans (_ : (kappa - 1) * mxdot A A <= _).
    by rewrite ler_wpM2r // ge_min lexx orbT.
  have h : 0 <= (3 - kappa) * (mxdot A A - s).
    by rewrite mulr_ge0 // subr_ge0 // ltW.
  lra.
by rewrite mulrAC; apply: ler_wpM2r => //; rewrite invr_ge0 ler0n.
Qed.

Section data_feature.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).
Local Notation P := (tuple_prod nu d).
Local Notation mu := (data_feature_law nu d).

Lemma data_feature_expectation (f : 'rV[RR]_(d * d) -> RR) :
  measurable_fun setT f ->
  'E_mu[f] = \int[P]_t (f (data_feature_map d t))%:E.
Proof.
move=> mf; rewrite unlock /data_feature_law.
by rewrite integral_distribution_measurable //; exact/measurable_EFinP.
Qed.

Lemma data_feature_dotE (th : 'rV[R]_(d * d)) t :
  mxdot (data_feature_map d t) th =
  ((Num.sqrt d%:R)^-1 * quad_form (vec_mx th) t)%R.
Proof. by rewrite -data_feature_dot vec_mxK. Qed.

Lemma sqrt_inv_sqr : ((Num.sqrt d%:R)^-1 * (Num.sqrt d%:R)^-1 = d%:R^-1 :> R)%R.
Proof. by rewrite -invfM -expr2 sqr_sqrtr ?ler0n. Qed.

(* Covariance matching: E <W, theta> = 0 and
   E <W, theta> <W, theta'> = theta C_kappa theta'^T. *)
Lemma data_feature_mean (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => mxdot z th] = 0.
Proof.
rewrite (data_feature_expectation (fun z => mxdot z th : RR)
  (measurable_mxdotl _ th)).
under eq_integral do rewrite data_feature_dotE EFinM.
rewrite (integralZl measurableT
  (integrable_quad_form _ _ _ _ hnu (vec_mx th))).
by rewrite (quad_form_mean _ _ _ _ hnu) mule0.
Qed.

Lemma data_feature_cov (th th' : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th * mxdot z th')%R] =
  (mxdot (th *m unsat_cov kappa d) th')%:E.
Proof.
have mf : measurable_fun setT
    (fun z : 'rV[RR]_(d * d) => (mxdot z th * mxdot z th')%R : RR).
  by apply: measurable_funM; exact: measurable_mxdotl.
rewrite (data_feature_expectation _ mf).
transitivity (\int[P]_t ((d%:R^-1)%:E *
    (quad_form (vec_mx th) t * quad_form (vec_mx th') t)%:E)).
  apply: eq_integral => t _; rewrite !data_feature_dotE -EFinM; congr EFin.
  by rewrite mulrACA sqrt_inv_sqr.
rewrite (integralZl measurableT
  (integrable_quad_form2 _ _ _ _ hnu (vec_mx th) (vec_mx th'))).
rewrite (quad_form_cov _ _ _ _ hnu) -EFinM unsat_covE /unsat_cov_form.
by rewrite !RmultE !RplusE ?RminusE.
Qed.

(* (F1) for the features: E <W, theta>^4 <= 9 2^33 K^8 |theta|^4 / d^2. *)
Lemma data_feature_fourth (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th ^+ 4)%R] <=
  (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2)%:E.
Proof.
have mf : measurable_fun setT
    (fun z : 'rV[RR]_(d * d) => (mxdot z th ^+ 4)%R : RR).
  by apply: measurable_funX; exact: measurable_mxdotl.
rewrite (data_feature_expectation _ mf).
set c : R := (d%:R ^- 2)%R.
have -> : \int[P]_t (mxdot (data_feature_map d t) th ^+ 4)%:E =
    \int[P]_t (c%:E * (quad_form (vec_mx th) t ^+ 4)%:E).
  apply: eq_integral => t _; rewrite data_feature_dotE -EFinM; congr EFin.
  rewrite exprMn (_ : 4 = 2 * 2)%N // exprM [in X in (X * _)%R]expr2.
  have h : ((Num.sqrt d%:R)^-1 ^+ 2 = d%:R^-1 :> R)%R.
    by rewrite expr2 sqrt_inv_sqr.
  by rewrite h -expr2 exprVn.
have k0 : 0 <= c%:E by rewrite lee_fin /c invr_ge0 exprn_ge0.
rewrite ge0_integralZl_EFin //.
- by move=> t _; rewrite lee_fin exprn4_ge0.
- by apply/measurable_EFinP; apply: measurable_funX;
    exact: measurable_quad_form.
apply: le_trans (lee_wpmul2l k0 (quad_form_moment4 _ _ _ _ hnu _)) _.
rewrite -EFinM lee_fin.
have -> : mxdot (vec_mx th) (vec_mx th) = mxdot th th.
  by rewrite -mxdot_mxvec !vec_mxK.
by rewrite /c le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* Lane C's forms (Unsat/Ridge): E <W, A> <W, B> = feature_cov kappa A B
   for B symmetric, and (F1): E <W, A>^4 <= C feature_cov kappa A A^2. *)
Lemma data_feature_cov_sym (A B : 'M[R]_d) : B \is symmetricmx ->
  'E_mu[fun z => (mxdot z (mxvec A) * mxdot z (mxvec B))%R] =
  (feature_cov kappa A B)%:E.
Proof.
by move=> sB; rewrite data_feature_cov unsat_covE !mxvecK unsat_cov_form_sym.
Qed.

Lemma data_feature_fourth_cov (A : 'M[R]_d) : (1 < kappa)%R ->
  'E_mu[fun z => (mxdot z (mxvec A) ^+ 4)%R] <=
  (9 * 2 ^+ 33 * K ^+ 8 / Num.min 2 (kappa - 1) ^+ 2 *
   feature_cov kappa A A ^+ 2)%:E.
Proof.
move=> k1; apply: le_trans (data_feature_fourth _) _; rewrite lee_fin.
rewrite mxdot_mxvec; set m := (Num.min 2 (kappa - 1))%R.
have m0 : (0 < m)%R by rewrite lt_min ltr0n subr_gt0 k1.
have h := feature_cov_ge kappa d A k1; rewrite -/m in h.
have h0 : (0 <= m / d%:R * mxdot A A)%R.
  by rewrite mulr_ge0 ?divr_ge0 ?ler0n ?mxdot_ge0 // ltW.
have h2 : ((m / d%:R * mxdot A A) ^+ 2 <= feature_cov kappa A A ^+ 2)%R.
  by rewrite ler_pXn2r // nnegrE //; apply: le_trans h.
have c0 : (0 <= 9 * 2 ^+ 33 * K ^+ 8)%R by rewrite mulr_ge0 // exprn8_ge0.
have X : (mxdot A A ^+ 2 / d%:R ^+ 2 <= feature_cov kappa A A ^+ 2 / m ^+ 2)%R.
  rewrite ler_pdivlMr ?exprn_gt0 //; apply: le_trans h2.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by rewrite !exprMn -exprVn; ring.
have H := ler_wpM2l c0 X; apply: le_trans (le_trans _ H) _;
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite -!exprVn; ring.
Qed.

End data_feature.
