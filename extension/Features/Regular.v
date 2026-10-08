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
   - (F2) as data_feature_variance: Var (z T z^T) <= 2^31 K^8 |T|_F^2 / d
     for every T, by Efron-Stein. Resampling the coordinate j changes W
     only in the row and the column j (feature_set_support), so
     F (x) - F (x^(j)) = <D, z T> + <D, z' T^T> with D = z - z'
     (quad_stat_diff) is bounded by |D|_F times the part of z T in that
     row and column (feature_diff_dot_le, rc_proj). Cauchy-Schwarz and the
     fourth moments E |D|_F^4 <= 2^20 K^8 (feature_diff_moment4) and
     E |rc_j (W M)|^4 <= (2^19 K^4 rc_weight j M / d)^2
     (proj_feature_moment4, from (F1) and integral_sum_sqr_le) give
     quad_stat_resample2; each entry lies in at most two rows and columns
     (sum_rc_weight).
   - Proposition 2.6 as data_feature_regular: for kappa > 1 and d > 0,
     data_feature_law nu d is a regular feature (regular_feature of
     convex/least_squares.v) with covariance unsat_cov kappa d,
     K_feat = 2^10 K^2 / sqrt (kappa - 1) and tau = sqrt (2^31 K^8 / d).
   - The same in the vocabulary of Gaussian/Cones, for Unsat/Ridge:
     unsat_cov_form_sym and data_feature_cov_sym (feature_cov kappa A B, B
     symmetric), feature_cov_ge (min (2, kappa - 1) |A|_F^2 / d <=
     feature_cov kappa A A for kappa > 1) and data_feature_fourth_cov
     (E <W, A>^4 <= 9 2^33 K^8 feature_cov kappa A A^2 /
     min (2, kappa - 1)^2).

   - The Gaussian feature: gaussian_feature kappa A (Gaussian/Cones) is
     c (G + (s - 1) diag G) with G = (A + A^T) / 2, c = sqrt (2 / d) and
     s = sqrt ((kappa - 1) / 2) (gaussian_featureE). For kappa >= 1,
     <gaussian_feature kappa A, gaussian_feature kappa B> =
     unsat_cov_form kappa d A B (mxdot_gaussian_feature); the matrix
     S = gaussian_feature_mx kappa d of g |-> mxvec (gaussian_feature kappa
     (vec_mx g)) (gaussian_feature_mxE) is symmetric and satisfies
     S^T S = unsat_cov kappa d (gaussian_feature_mx_cov), so
     gaussian_feature_law kappa d, the law of g *m S under gauss (d * d),
     has covariance C_kappa.

   - Subexponential quadratic forms, for Unsat/Ridge (Lemma 2.12): for
     |v| <= 1 and d > 0, z |-> <z, mxvec (v^T v)> is subexponential with
     constant 48 K^2 / sqrt d under data_feature_law nu d
     (data_feature_quad_subexponential: it is ((v x)^2 - |v|^2) / sqrt d,
     with v x subgaussian by Hoeffding's inequality), and with constant
     4 sqrt (kappa + 1) / sqrt d under gaussian_feature_law kappa d
     (gaussian_feature_quad_subexponential: a Gaussian linear form <g, a>
     is subexponential with constant 4 |a|, gauss_mxdot_subexponential, and
     |a|^2 = C_kappa (v^T v, v^T v) <= (kappa + 1) / d, unsat_cov_form_le).
     For every A, by the Hanson-Wright inequality, <W, A> is
     subexponential with constant L / sqrt d for every L >= 252 K^2 |A|_F
     (data_feature_subexponential; data_feature_subexponential_frob with
     L = 252 K^2 |A|_F for A != 0).

   - Component laws. The bounds above that do not involve kappa hold for
     coordinates with laws as mixture_component_law K asks (mean 0,
     variance 1 and E exp (x^2 / K^2) <= 2, MixtureDefinitions), the
     components of the mixture theorem. The sections component_moments and
     component_feature state them with the prefix component_:
     component_feature_mean, component_feature_fourth,
     component_feature_variance, component_feature_quad_subexponential and
     component_feature_subexponential, and the lemmas they rest on, such as
     component_lin_form_moment8, component_quad_form_mean,
     component_quad_form_moment4, component_proj_feature_moment4,
     component_feature_diff_moment4 and component_quad_stat_resample2. The
     lemmas without the prefix are their corollaries for
     universality_coordinate_law, by coordinate_law_component
     (Mixture/Component). The covariance is stated for coordinates with
     different fourth moments kap j: component_moment4,
     component_quad_form_cov (E Q_A Q_B = <A, B> + <A, B^T> +
     sum_a (kap a - 3) A_aa B_aa) and component_feature_cov
     (E <W, theta> <W, theta'> = theta (coord_cov kap d) theta'^T, where
     coord_covE says that coord_cov kap d is the matrix of the form
     coord_cov_form, and coord_cov_const that coord_cov (fun=> kappa) d is
     unsat_cov kappa d); moment4, quad_form_cov and data_feature_cov are
     their corollaries for kap = kappa.

   - gaussian_feature_regular: for kappa > 1 and d > 0,
     gaussian_feature_law kappa d is a regular feature with covariance
     unsat_cov kappa d and constants 3^(1/4) and
     sqrt 2 opnorm (unsat_cov kappa d), from (2.10) of the paper
     (gauss_regular_feature, convex/gauss_feature.v) and
     gaussian_feature_mx_cov. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import normedtype sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import sesquilinear.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.comparison Require Import gauss_linear.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.probability Require Import efron_stein hanson_wright.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.convex Require Import least_squares gauss_feature.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component.
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

(* The covariance form of the features of a point whose coordinate j has
   fourth moment kap j; unsat_cov_form kappa d is the case of the constant
   kap = kappa (coord_cov_const). *)
Definition coord_cov_form (kap : nat -> R) d (A B : 'M[R]_d) : RR :=
  d%:R^-1 * (mxdot A B + mxdot A B^T +
             \sum_(j < d) (kap j - 3) * (A j j * B j j)).

(* Its matrix in the mxvec coordinates. *)
Definition coord_cov (kap : nat -> R) d : 'M[R]_(d * d) :=
  \matrix_(p, q)
    coord_cov_form kap d (vec_mx (delta_mx 0 p : 'rV[R]_(d * d)))
                         (vec_mx (delta_mx 0 q : 'rV[R]_(d * d))).

Lemma coord_cov_formC (kap : nat -> R) d (A B : 'M[R]_d) :
  coord_cov_form kap d A B = coord_cov_form kap d B A.
Proof.
rewrite /coord_cov_form mxdotC; congr (_ * (_ + _ + _)).
  by rewrite -(mxdot_trmx A B^T) trmxK mxdotC.
by apply: eq_bigr => j _; rewrite (mulrC (A j j)).
Qed.

Lemma coord_cov_form_dot (kap : nat -> R) d (A B : 'M[R]_d) :
  coord_cov_form kap d A B =
  mxdot A (d%:R^-1 *: (B + B^T + diag_mx (\row_j ((kap j - 3) * B j j)))).
Proof.
rewrite /coord_cov_form mxdotZr !mxdotDr.
congr (_ * (_ + _ + _)); apply: eq_bigr => i _.
rewrite (bigD1 i) //= big1 ?addr0.
  by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0n mulr0.
by rewrite !mxE eqxx mulr1n; ring.
Qed.

Lemma coord_cov_form_suml (kap : nat -> R) d I (r : seq I) (c : I -> R)
    (M : I -> 'M[R]_d) (B : 'M[R]_d) :
  coord_cov_form kap d (\sum_(k <- r) c k *: M k) B =
  \sum_(k <- r) c k * coord_cov_form kap d (M k) B.
Proof.
rewrite coord_cov_form_dot mxdot_suml; apply: eq_bigr => k _.
by rewrite mxdotZl coord_cov_form_dot.
Qed.

(* The matrix coord_cov kap d represents the form coord_cov_form. *)
Lemma coord_covE (kap : nat -> R) d (th th' : 'rV[R]_(d * d)) :
  mxdot (th *m coord_cov kap d) th' =
  coord_cov_form kap d (vec_mx th) (vec_mx th').
Proof.
rewrite (vec_mx_sum _ _ th) coord_cov_form_suml /mxdot big_ord1.
under eq_bigr do rewrite mxE big_distrl /=.
rewrite exchange_big /=; apply: eq_bigr => p _.
rewrite coord_cov_formC (vec_mx_sum _ _ th') coord_cov_form_suml mulr_sumr.
by apply: eq_bigr => q _; rewrite coord_cov_formC mxE; ring.
Qed.

Lemma coord_cov_const (kappa : R) d : coord_cov (fun=> kappa) d = unsat_cov kappa d.
Proof.
apply/matrixP => p q; rewrite !mxE /coord_cov_form /unsat_cov_form.
rewrite !RmultE !RplusE ?RminusE; congr (_ * (_ + _ + _)).
by rewrite mulr_sumr.
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

(* The moments of the coordinates and of the quadratic forms under the
   product of component laws (mixture_component_law of MixtureDefinitions):
   mean 0, variance 1 and subgaussian constant K, without assumption on the
   fourth moment. product_moments below states the same for the coordinate
   laws of the universality theorem, and adds the moments that involve
   kappa. *)
Section component_moments.
Local Open Scope ereal_scope.
Variables (K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> mixture_component_law K (nu j).

Local Notation P := (tuple_prod nu d).

Lemma component_integrable_coord_pow (a : 'I_d) k :
  P.-integrable setT (fun t => ((tnth t a : R) ^+ k)%:E).
Proof.
have ia := @component_law_integrable _ _ (hnu a (ltn_ord a)) k.
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
Lemma component_integrable_poly p (f : d.-tuple (measurableTypeR R) -> RR) (C : R) :
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
  by move=> i _; exact: component_integrable_coord_pow.
apply: le_integrable ig => //; first exact/measurable_EFinP.
move=> t _; change (`|(f t)%:E| <=
  `|(C * (1 + \sum_(i < d) tnth t i ^+ p))%:E|).
by rewrite !abse_EFin lee_fin; apply: le_trans (fC t) _; exact: ler_norm.
Qed.

Lemma component_coord_pow4_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  ((tnth t k : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
have e4 (r : R) : (0 <= r ^+ 4)%R by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
rewrite (bigD1 k) //=.
have s0 : (0 <= \sum_(i < d | i != k) (tnth t i : R) ^+ 4)%R.
  by rewrite sumr_ge0.
lra.
Qed.

(* A product of four factors, each a coordinate or 1. *)
Lemma component_prod4_le (t : d.-tuple (measurableTypeR R)) (y1 y2 y3 y4 : R) :
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
Lemma component_coord_extract (a : 'I_d) k (H : d.-tuple (measurableTypeR R) -> RR) :
  measurable_fun setT H ->
  (forall t, `|H t| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (forall t s, H (tuple_set t a s) = H t) ->
  \int[P]_t (((tnth t a : R) ^+ k) * H t)%:E =
  \int[nu a]_s ((s : R) ^+ k)%:E * \int[P]_t (H t)%:E.
Proof.
move=> mH Hb Hind.
have iH : P.-integrable setT (EFin \o H).
  by apply: (component_integrable_poly 4 _ 1) => // t; rewrite mul1r.
have ik := @component_law_integrable _ _ (hnu a (ltn_ord a)) k.
by have [_ ->] := integral_tuple_prod_coordM
  (f := fun s : measurableTypeR R => ((s : R) ^+ k)%R) ik iH Hind.
Qed.

Lemma component_one_pow4_le (t : d.-tuple (measurableTypeR R)) :
  ((1 : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
rewrite expr1n lerDl sumr_ge0 // => i _.
by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
Qed.

Lemma component_coord_abs_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  (`|(tnth t k : R)| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof.
have one4 := component_one_pow4_le t.
have := @component_prod4_le t (tnth t k) 1 1 1 (component_coord_pow4_le t k) one4 one4 one4.
by rewrite !mulr1.
Qed.

Lemma component_moment1 (a : 'I_d) : \int[P]_t ((tnth t a : R))%:E = 0.
Proof.
rewrite (integral_tuple_prod_coord nu a
  (f := fun s : measurableTypeR R => ((s : R))%:E)).
- by apply/measurable_EFinP.
- exact: (@component_law_mean _ _ (hnu a (ltn_ord a))).
Qed.

Lemma component_moment2 (a b : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b)%:E = ((a == b)%:R)%:E.
Proof.
case: (eqVneq a b) => [<-|ab].
  under eq_integral do rewrite -expr2.
  rewrite (integral_tuple_prod_coord nu a
    (f := fun s : measurableTypeR R => ((s : R) ^+ 2)%:E)).
  - by apply/measurable_EFinP; exact: measurable_funX.
  - by rewrite (@component_law_second _ _ (hnu a (ltn_ord a))).
rewrite -[RHS](mule0 (\int[P]_t (tnth t b : R)%:E)) muleC.
rewrite -(@component_law_mean _ _ (hnu a (ltn_ord a))).
have Hind (t : d.-tuple (measurableTypeR R)) s :
    (tnth (tuple_set t a s) b : RR) = tnth t b.
  by rewrite tnth_tuple_set_neq // eq_sym.
have := component_coord_extract a 1 (fun t => (tnth t b : RR)) (measurable_tnth b)
  (fun t => component_coord_abs_le t b) Hind.
under eq_integral do rewrite expr1.
by under [X in _ = X * _]eq_integral do rewrite expr1.
Qed.

Lemma component_integral_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  \int[P]_t (\sum_(i < d) f i t)%:E = \sum_(i < d) \int[P]_t (f i t)%:E.
Proof.
move=> fi; under eq_integral do rewrite -sumEFin.
by rewrite integral_sum.
Qed.

Lemma component_integrable_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  P.-integrable setT (fun t => (\sum_(i < d) f i t)%:E).
Proof.
move=> fi; under eq_fun do rewrite -sumEFin.
by apply: integrable_sum => // i _.
Qed.

Lemma component_integrable_x2 (a b : 'I_d) :
  P.-integrable setT (fun t => ((tnth t a : R) * tnth t b)%:E).
Proof.
apply: (component_integrable_poly 4 (fun t => ((tnth t a : RR) * (tnth t b : RR))%R) 1).
  by apply: measurable_funM; exact: measurable_tnth.
move=> t; rewrite mul1r.
have := @component_prod4_le t _ _ _ _ (component_coord_pow4_le t a) (component_coord_pow4_le t b)
  (component_one_pow4_le t) (component_one_pow4_le t).
by rewrite !mulr1.
Qed.

Lemma component_integrable_x4 (a b c e : 'I_d) :
  P.-integrable setT
    (fun t => ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E).
Proof.
apply: (component_integrable_poly 4 (fun t =>
  ((tnth t a : RR) * (tnth t b : RR) * (tnth t c : RR) * (tnth t e : RR))%R) 1).
  apply: measurable_funM; last exact: measurable_tnth.
  apply: measurable_funM; last exact: measurable_tnth.
  by apply: measurable_funM; exact: measurable_tnth.
move=> t; rewrite mul1r.
exact: (@component_prod4_le t _ _ _ _ (component_coord_pow4_le t a) (component_coord_pow4_le t b)
  (component_coord_pow4_le t c) (component_coord_pow4_le t e)).
Qed.

Lemma component_integrable_quad_sum (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_sum A t)%:E).
Proof.
apply: component_integrable_sum_ord => a; apply: component_integrable_sum_ord => b.
under eq_fun do rewrite EFinM.
by apply: integrableZl => //; exact: component_integrable_x2.
Qed.

Lemma component_integrable_quad_sum2 (A B : 'M[R]_d) :
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
apply: component_integrable_sum_ord => a; apply: component_integrable_sum_ord => b.
apply: component_integrable_sum_ord => c; apply: component_integrable_sum_ord => e.
under eq_fun do rewrite EFinM.
by apply: integrableZl => //; exact: component_integrable_x4.
Qed.

Lemma component_quad_sum_mean (A : 'M[R]_d) :
  \int[P]_t (quad_sum A t)%:E = (\tr A)%:E.
Proof.
have iab a b : P.-integrable setT
    (fun t => (A a b * ((tnth t a : R) * tnth t b))%:E).
  under eq_fun do rewrite EFinM.
  by apply: integrableZl => //; exact: component_integrable_x2.
rewrite /quad_sum component_integral_sum_ord.
  by move=> a; exact: component_integrable_sum_ord.
rewrite /mxtrace -sumEFin; apply: eq_bigr => a _.
rewrite component_integral_sum_ord //.
transitivity (\sum_(b < d) (A a b * (a == b)%:R)%:E)%R.
  apply: eq_bigr => b _; under eq_integral do rewrite EFinM.
  rewrite integralZl //; first exact: component_integrable_x2.
  by rewrite component_moment2 -EFinM.
rewrite sumEFin (bigD1 a) //= eqxx mulr1 big1 ?addr0 // => b ba.
by rewrite eq_sym (negbTE ba) mulr0.
Qed.

Lemma component_integrable_quad_form (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t)%:E).
Proof.
under eq_fun do rewrite quad_formE EFinB.
apply: integrableB => //; first exact: component_integrable_quad_sum.
exact: finite_measure_integrable_cst.
Qed.

Lemma component_integrable_quad_form2 (A B : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t * quad_form B t)%:E).
Proof.
apply: (@eq_integrable _ _ _ P setT measurableT (fun t =>
  (quad_sum A t * quad_sum B t -
   (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B))%:E)).
  by move=> t _; rewrite !quad_formE; congr EFin; ring.
under eq_fun do rewrite EFinB.
apply: integrableB => //; first exact: component_integrable_quad_sum2.
under eq_fun do rewrite EFinB EFinD !EFinM.
apply: integrableB => //; last exact: finite_measure_integrable_cst.
by apply: integrableD => //; apply: integrableZl => //;
  exact: component_integrable_quad_sum.
Qed.

(* Covariance matching: the covariance of the features is C_kappa. *)
Lemma component_quad_form_mean (A : 'M[R]_d) : \int[P]_t (quad_form A t)%:E = 0.
Proof.
under eq_integral do rewrite quad_formE EFinB.
rewrite integralB_EFin //.
- exact: component_integrable_quad_sum.
- exact: finite_measure_integrable_cst.
rewrite component_quad_sum_mean integral_cst //.
by rewrite [X in _ - _ * X]probability_setT mule1 subee.
Qed.

Lemma component_coord_moment8 (j : 'I_d) :
  \int[nu j]_s ((s : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof.
have := @component_law_moment _ _ (hnu j (ltn_ord j)) 4.
by rewrite /= -natrM.
Qed.

Lemma component_coord_tuple_moment8 (j : 'I_d) :
  \int[P]_t ((tnth t j : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof.
rewrite (ge0_integral_tuple_prod_coord nu j
  (f := fun s => ((s : R) ^+ 8)%:E)).
- by apply/measurable_EFinP; exact: measurable_funX.
- by move=> s; rewrite lee_fin exprn8_ge0.
exact: component_coord_moment8.
Qed.

(* The eighth moment of a linear form, from Hoeffding's inequality
   (probability/subgaussian.v): E <c, x>^8 <= 48 4^8 K^8 |c|^8. *)
Lemma component_lin_form_moment8 (c : 'I_d -> R) :
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
    exact: (@component_law_K _ _ (hnu b (ltn_ord b))).
  by move: S0; rewrite big1 ?eqxx // => b _; move: (h b).
pose a := ord_fun c.
have aE (b : 'I_d) : a b = c b := ord_funE _ c b.
have Spos : (0 < \sum_(b < d) c b ^+ 2)%R.
  by rewrite lt_def S0 /=; apply: sumr_ge0 => b _; exact: sqr_ge0.
have S0' : (0 < \sum_(j < d) a j ^+ 2 * K ^+ 2)%R.
  under eq_bigr do rewrite aE.
  by rewrite -mulr_suml mulr_gt0 // exprn_gt0.
have sg : forall j, (j < d)%N -> subgaussian (nu j) (fun x : R => x) K.
  by move=> j jd; exact: (@component_law_subgaussian _ _ (hnu j jd)).
have m0 : forall j, (j < d)%N -> (\int[nu j]_t (fun x : R => x) t)%R = 0%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_mean _ _ (hnu j jd)).
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

Lemma component_integrable_quad_form_pow4 (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t ^+ 4)%:E).
Proof.
apply: (component_integrable_poly 8 (fun t => quad_form A t ^+ 4 : RR)%R
  (8 * (d * d)%:R ^+ 2 * mxdot A A ^+ 2)%R).
  by apply: measurable_funX; exact: measurable_quad_form.
move=> t; rewrite ger0_norm ?exprn4_ge0 //; exact: quad_form_pow4_le.
Qed.

Lemma component_quad_form_pow4_fin (A : 'M[R]_d) :
  \int[P]_t (quad_form A t ^+ 4)%:E < +oo.
Proof.
have /integrableP[_ h] := component_integrable_quad_form_pow4 A.
apply: le_lt_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_integral => t _; rewrite gee0_abs // lee_fin exprn4_ge0.
Qed.

(* The fourth moment of the difference after resampling the coordinate i:
   E (Q_A (x) - Q_A (x^(i)))^4 <= (2^16 K^4 r_i)^2, where r_i is the
   squared norm of the row and the column i of A. *)
Lemma component_quad_form_resample4 (A : 'M[R]_d) (i : 'I_d) :
  \int[P]_t \int[nu i]_s
    ((quad_form A t - quad_form A (tuple_set t i s)) ^+ 4)%:E <=
  ((2 ^+ 16 * K ^+ 4 * \sum_(b < d) (A i b ^+ 2 + A b i ^+ 2)) ^+ 2)%:E.
Proof.
set r := (\sum_(b < d) _)%R.
have r0 : (0 <= r)%R by apply: sumr_ge0 => b _; rewrite addr_ge0 ?sqr_ge0.
have K0 : (0 < K)%R := @component_law_K _ _ (hnu i (ltn_ord i)).
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
have B1 := component_coord_tuple_moment8 i.
have B2 := component_coord_moment8 i.
have B3 := component_lin_form_moment8 c.
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
Lemma component_quad_form_moment4 (A : 'M[R]_d) :
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
  by rewrite DE; exact: component_quad_form_resample4.
have := efron_stein_fourth (measurable_quad_form d A) (component_quad_form_pow4_fin A)
  D0 HD.
rewrite component_quad_form_mean /= => h.
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

(* The coordinates may have different fourth moments: kap j for the
   coordinate j. *)
Variable kap : nat -> R.
Hypothesis hkap :
  forall j, (j < d)%N -> \int[nu j]_x ((x : R) ^+ 4)%:E = (kap j)%:E.

Lemma component_moment4 (a b c e : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E =
  ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
   (a == e)%:R * (b == c)%:R +
   (kap a - 3) * (((a == b) && (a == c)) && (a == e))%:R)%:E.
Proof.
have one4 := component_one_pow4_le; have c4 := component_coord_pow4_le.
have h2 := @component_law_second _ _ (hnu a (ltn_ord a)).
have h4 := hkap a (ltn_ord a).
have ind (k : 'I_d) (t : d.-tuple (measurableTypeR R)) s :
    k != a -> (tnth (tuple_set t a s) k : R) = tnth t k.
  by move=> ka; rewrite tnth_tuple_set_neq.
(* x_a^k times one, two or three coordinates other than a *)
have ext1 k (k1 : 'I_d) : k1 != a ->
    \int[P]_t (((tnth t a : R) ^+ k) * tnth t k1)%:E =
    \int[nu a]_s ((s : R) ^+ k)%:E * \int[P]_t ((tnth t k1 : R))%:E.
  move=> k1a.
  apply: (component_coord_extract a k (fun t => (tnth t k1 : RR))) => //.
  - exact: measurable_tnth.
  - by move=> t; exact: component_coord_abs_le.
  - by move=> t s /=; rewrite ind.
have ext2 k (k1 k2 : 'I_d) : k1 != a -> k2 != a ->
    \int[P]_t (((tnth t a : R) ^+ k) * (tnth t k1 * tnth t k2))%:E =
    \int[nu a]_s ((s : R) ^+ k)%:E *
      \int[P]_t ((tnth t k1 : R) * tnth t k2)%:E.
  move=> k1a k2a.
  refine (component_coord_extract a k
    (fun t => ((tnth t k1 : RR) * (tnth t k2 : RR))%R) _ _ _).
  - by apply: measurable_funM; exact: measurable_tnth.
  - move=> t; have := @component_prod4_le t _ _ _ _ (c4 t k1) (c4 t k2) (one4 t)
      (one4 t).
    by rewrite !mulr1.
  - by move=> t s /=; rewrite !ind.
have ext3 (k1 k2 k3 : 'I_d) : k1 != a -> k2 != a -> k3 != a ->
    \int[P]_t (((tnth t a : R) ^+ 1) *
      (tnth t k1 * tnth t k2 * tnth t k3))%:E =
    \int[nu a]_s ((s : R) ^+ 1)%:E *
      \int[P]_t ((tnth t k1 : R) * tnth t k2 * tnth t k3)%:E.
  move=> k1a k2a k3a.
  refine (component_coord_extract a 1 (fun t =>
    ((tnth t k1 : RR) * (tnth t k2 : RR) * (tnth t k3 : RR))%R) _ _ _).
  - apply: measurable_funM; last exact: measurable_tnth.
    by apply: measurable_funM; exact: measurable_tnth.
  - move=> t; have := @component_prod4_le t _ _ _ _ (c4 t k1) (c4 t k2) (c4 t k3)
      (one4 t).
    by rewrite !mulr1.
  - by move=> t s /=; rewrite !ind.
have m1 : \int[nu a]_s ((s : R) ^+ 1)%:E = 0.
  under eq_integral do rewrite expr1.
  exact: (@component_law_mean _ _ (hnu a (ltn_ord a))).
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
  by rewrite (ext1 3%N e ea) component_moment1 mule0; congr EFin; ring.
- (* a = b = e, c <> a *)
  have ca : c != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 3 * tnth t c)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext1 3%N c ca) component_moment1 mule0 (negbTE ca).
  by rewrite /= !(mulr0, mul0r, addr0, mulr0n).
- (* a = b, c <> a, e <> a *)
  have ca : c != a by rewrite eq_sym.
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t c * tnth t e))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  by rewrite (ext2 2%N c e ca ea) h2 mul1e component_moment2; congr EFin; ring.
- (* a = c = e, b <> a *)
  have ba : b != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 3 * tnth t b)%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext1 3%N b ba) component_moment1 mule0 (negbTE ba).
  by rewrite /= !(mulr0, mul0r, addr0, mulr0n).
- (* a = c, b <> a, e <> a *)
  have ba : b != a by rewrite eq_sym.
  have ea : e != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t b * tnth t e))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  rewrite (ext2 2%N b e ba ea) h2 mul1e component_moment2 (negbTE ba).
  by congr EFin; ring.
- (* a = e, b <> a, c <> a *)
  have ba : b != a by rewrite eq_sym.
  have ca : c != a by rewrite eq_sym.
  transitivity (\int[P]_t ((tnth t a : R) ^+ 2 * (tnth t b * tnth t c))%:E).
    by apply: eq_integral => t _; congr EFin; ring.
  by rewrite (ext2 2%N b c ba ca) h2 mul1e component_moment2; congr EFin; ring.
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

Lemma component_quad_sum_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_sum A t * quad_sum B t)%:E =
  (\tr A * \tr B + mxdot A B + mxdot A B^T +
   \sum_(a < d) (kap a - 3) * (A a a * B a a))%:E.
Proof.
pose X t (a b c e : 'I_d) :=
  ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%R.
have it a b c e : P.-integrable setT
    (fun t => ((A a b * B c e) * X t a b c e)%:E).
  under eq_fun do rewrite EFinM.
  by apply: integrableZl => //; exact: component_integrable_x4.
transitivity (\int[P]_t (\sum_(a < d) \sum_(b < d) \sum_(c < d) \sum_(e < d)
    (A a b * B c e) * X t a b c e)%:E).
  apply: eq_integral => t _; congr EFin.
  rewrite /quad_sum mulr_suml; apply: eq_bigr => a _.
  rewrite mulr_suml; apply: eq_bigr => b _.
  rewrite mulr_sumr; apply: eq_bigr => c _.
  by rewrite mulr_sumr; apply: eq_bigr => e _; rewrite /X; ring.
have i3 a b c : P.-integrable setT
    (fun t => (\sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: component_integrable_sum_ord.
have i2 a b : P.-integrable setT (fun t =>
    (\sum_(c < d) \sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: component_integrable_sum_ord.
have i1 a : P.-integrable setT (fun t => (\sum_(b < d) \sum_(c < d)
    \sum_(e < d) (A a b * B c e) * X t a b c e)%:E).
  exact: component_integrable_sum_ord.
rewrite component_integral_sum_ord //.
transitivity (\sum_(a < d) (\sum_(b < d) \sum_(c < d) \sum_(e < d)
  A a b * B c e * ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
  (a == e)%:R * (b == c)%:R +
  (kap a - 3) * (((a == b) && (a == c)) && (a == e))%:R))%:E)%R.
  apply: eq_bigr => a _.
  rewrite component_integral_sum_ord // -sumEFin; apply: eq_bigr => b _.
  rewrite component_integral_sum_ord // -sumEFin; apply: eq_bigr => c _.
  rewrite component_integral_sum_ord // -sumEFin; apply: eq_bigr => e _.
  under eq_integral do rewrite EFinM.
  rewrite integralZl //; first exact: component_integrable_x4.
  by rewrite component_moment4 -EFinM.
rewrite sumEFin; congr EFin.
transitivity (\sum_(a < d) \sum_(b < d) A a b * ((a == b)%:R * \tr B +
  B a b + B b a + (kap a - 3) * (a == b)%:R * B a a))%R.
  apply: eq_bigr => a _; apply: eq_bigr => b _.
  rewrite -moment4_sum mulr_sumr; apply: eq_bigr => c _.
  by rewrite mulr_sumr; apply: eq_bigr => e _; ring.
transitivity (\sum_(a < d) \sum_(b < d)
  ((A a b * \tr B + (kap a - 3) * A a b * B a a) * (a == b)%:R +
   A a b * B a b + A a b * B b a))%R.
  by apply: eq_bigr => a _; apply: eq_bigr => b _; ring.
under eq_bigr => a _ do rewrite !big_split /= sum_delta.
rewrite !big_split /= /mxdot /mxtrace -mulr_suml.
under [X in (_ + X + _ + _)%R = _]eq_bigr do rewrite -mulrA.
under [X in _ = (_ + _ + X + _)%R]eq_bigr do under eq_bigr do rewrite mxE.
ring.
Qed.

Lemma component_quad_form_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_form A t * quad_form B t)%:E =
  (mxdot A B + mxdot A B^T + \sum_(a < d) (kap a - 3) * (A a a * B a a))%:E.
Proof.
have iA := component_integrable_quad_sum A; have iB := component_integrable_quad_sum B.
have iAB := component_integrable_quad_sum2 A B.
have iL : P.-integrable setT (fun t =>
    (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B)%:E).
  under eq_fun do rewrite EFinB EFinD !EFinM.
  apply: integrableB => //; last exact: finite_measure_integrable_cst.
  by apply: integrableD => //; apply: integrableZl.
transitivity (\int[P]_t ((quad_sum A t * quad_sum B t)%:E -
    (\tr B * quad_sum A t + \tr A * quad_sum B t - \tr A * \tr B)%:E)).
  apply: eq_integral => t _.
  by rewrite -EFinB !quad_formE; congr EFin; ring.
rewrite integralB_EFin // component_quad_sum_cov.
have -> : \int[P]_x
    (\tr B * quad_sum A x + \tr A * quad_sum B x - \tr A * \tr B)%:E =
    (\tr A * \tr B)%:E.
  under eq_integral do rewrite EFinB EFinD !EFinM.
  rewrite integralB //.
  - by apply: integrableD => //; apply: integrableZl.
  - by rewrite -EFinM; exact: finite_measure_integrable_cst.
  rewrite integralD //; try by apply: integrableZl.
  rewrite (integralZl measurableT iA) (integralZl measurableT iB).
  rewrite !component_quad_sum_mean integral_cst //.
  rewrite [X in _ - _ * X]probability_setT mule1 -!EFinM -EFinD.
  by congr EFin; ring.
by rewrite -EFinB; congr EFin; ring.
Qed.

End component_moments.

Section product_moments.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).
Let hnuc : forall j, (j < d)%N -> mixture_component_law K (nu j) :=
  fun j jd => coordinate_law_component kappa K (nu j) (hnu j jd).
Let hkapc : forall j, (j < d)%N -> \int[nu j]_x ((x : R) ^+ 4)%:E = kappa%:E :=
  fun j jd => @coordinate_law_fourth _ _ _ (hnu j jd).

Local Notation P := (tuple_prod nu d).

Lemma integrable_coord_pow (a : 'I_d) k :
  P.-integrable setT (fun t => ((tnth t a : R) ^+ k)%:E).
Proof. first [exact: (component_integrable_coord_pow K d nu hnuc) | exact: component_integrable_coord_pow]. Qed.

(* A function bounded by C (1 + sum_i x_i^p) is integrable. *)
Lemma integrable_poly p (f : d.-tuple (measurableTypeR R) -> RR) (C : R) :
  measurable_fun setT f ->
  (forall t, `|f t| <= C * (1 + \sum_(i < d) (tnth t i : R) ^+ p))%R ->
  P.-integrable setT (EFin \o f).
Proof. first [exact: (component_integrable_poly K d nu hnuc) | exact: component_integrable_poly]. Qed.

Lemma coord_pow4_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  ((tnth t k : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof. first [exact: (component_coord_pow4_le K d nu hnuc) | exact: component_coord_pow4_le]. Qed.

(* A product of four factors, each a coordinate or 1. *)
Lemma prod4_le (t : d.-tuple (measurableTypeR R)) (y1 y2 y3 y4 : R) :
  (y1 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y2 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y3 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (y4 ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (`|y1 * y2 * y3 * y4| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof. first [exact: (component_prod4_le K d nu hnuc) | exact: component_prod4_le]. Qed.

(* A power of the coordinate a and a function of the other coordinates. *)
Lemma coord_extract (a : 'I_d) k (H : d.-tuple (measurableTypeR R) -> RR) :
  measurable_fun setT H ->
  (forall t, `|H t| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R ->
  (forall t s, H (tuple_set t a s) = H t) ->
  \int[P]_t (((tnth t a : R) ^+ k) * H t)%:E =
  \int[nu a]_s ((s : R) ^+ k)%:E * \int[P]_t (H t)%:E.
Proof. first [exact: (component_coord_extract K d nu hnuc) | exact: component_coord_extract]. Qed.

Lemma one_pow4_le (t : d.-tuple (measurableTypeR R)) :
  ((1 : R) ^+ 4 <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof. first [exact: (component_one_pow4_le K d nu hnuc) | exact: component_one_pow4_le]. Qed.

Lemma coord_abs_le (t : d.-tuple (measurableTypeR R)) (k : 'I_d) :
  (`|(tnth t k : R)| <= 1 + \sum_(i < d) (tnth t i : R) ^+ 4)%R.
Proof. first [exact: (component_coord_abs_le K d nu hnuc) | exact: component_coord_abs_le]. Qed.

Lemma moment1 (a : 'I_d) : \int[P]_t ((tnth t a : R))%:E = 0.
Proof. first [exact: (component_moment1 K d nu hnuc) | exact: component_moment1]. Qed.

Lemma moment2 (a b : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b)%:E = ((a == b)%:R)%:E.
Proof. first [exact: (component_moment2 K d nu hnuc) | exact: component_moment2]. Qed.

Lemma moment4 (a b c e : 'I_d) :
  \int[P]_t ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E =
  ((a == b)%:R * (c == e)%:R + (a == c)%:R * (b == e)%:R +
   (a == e)%:R * (b == c)%:R +
   (kappa - 3) * (((a == b) && (a == c)) && (a == e))%:R)%:E.
Proof. exact: (component_moment4 K d nu hnuc (fun=> kappa) hkapc a b c e). Qed.

Lemma integral_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  \int[P]_t (\sum_(i < d) f i t)%:E = \sum_(i < d) \int[P]_t (f i t)%:E.
Proof. first [exact: (component_integral_sum_ord K d nu hnuc) | exact: component_integral_sum_ord]. Qed.

Lemma integrable_sum_ord (f : 'I_d -> d.-tuple (measurableTypeR R) -> R) :
  (forall i, P.-integrable setT (fun t => (f i t)%:E)) ->
  P.-integrable setT (fun t => (\sum_(i < d) f i t)%:E).
Proof. first [exact: (component_integrable_sum_ord K d nu hnuc) | exact: component_integrable_sum_ord]. Qed.

Lemma integrable_x2 (a b : 'I_d) :
  P.-integrable setT (fun t => ((tnth t a : R) * tnth t b)%:E).
Proof. first [exact: (component_integrable_x2 K d nu hnuc) | exact: component_integrable_x2]. Qed.

Lemma integrable_x4 (a b c e : 'I_d) :
  P.-integrable setT
    (fun t => ((tnth t a : R) * tnth t b * tnth t c * tnth t e)%:E).
Proof. first [exact: (component_integrable_x4 K d nu hnuc) | exact: component_integrable_x4]. Qed.

Lemma integrable_quad_sum (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_sum A t)%:E).
Proof. first [exact: (component_integrable_quad_sum K d nu hnuc) | exact: component_integrable_quad_sum]. Qed.

Lemma integrable_quad_sum2 (A B : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_sum A t * quad_sum B t)%:E).
Proof. first [exact: (component_integrable_quad_sum2 K d nu hnuc) | exact: component_integrable_quad_sum2]. Qed.

Lemma quad_sum_mean (A : 'M[R]_d) :
  \int[P]_t (quad_sum A t)%:E = (\tr A)%:E.
Proof. first [exact: (component_quad_sum_mean K d nu hnuc) | exact: component_quad_sum_mean]. Qed.

Lemma quad_sum_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_sum A t * quad_sum B t)%:E =
  (\tr A * \tr B + mxdot A B + mxdot A B^T +
   (kappa - 3) * \sum_(a < d) A a a * B a a)%:E.
Proof.
by rewrite (component_quad_sum_cov K d nu hnuc (fun=> kappa) hkapc) [((kappa - 3) * _)%R]mulr_sumr.
Qed.

Lemma integrable_quad_form (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t)%:E).
Proof. first [exact: (component_integrable_quad_form K d nu hnuc) | exact: component_integrable_quad_form]. Qed.

Lemma integrable_quad_form2 (A B : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t * quad_form B t)%:E).
Proof. first [exact: (component_integrable_quad_form2 K d nu hnuc) | exact: component_integrable_quad_form2]. Qed.

(* Covariance matching: the covariance of the features is C_kappa. *)
Lemma quad_form_mean (A : 'M[R]_d) : \int[P]_t (quad_form A t)%:E = 0.
Proof. first [exact: (component_quad_form_mean K d nu hnuc) | exact: component_quad_form_mean]. Qed.

Lemma quad_form_cov (A B : 'M[R]_d) :
  \int[P]_t (quad_form A t * quad_form B t)%:E =
  (mxdot A B + mxdot A B^T + (kappa - 3) * \sum_(a < d) A a a * B a a)%:E.
Proof.
by rewrite (component_quad_form_cov K d nu hnuc (fun=> kappa) hkapc) [((kappa - 3) * _)%R]mulr_sumr.
Qed.

Lemma coord_moment8 (j : 'I_d) :
  \int[nu j]_s ((s : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof. first [exact: (component_coord_moment8 K d nu hnuc) | exact: component_coord_moment8]. Qed.

Lemma coord_tuple_moment8 (j : 'I_d) :
  \int[P]_t ((tnth t j : R) ^+ 8)%:E <= (48 * K ^+ 8)%:E.
Proof. first [exact: (component_coord_tuple_moment8 K d nu hnuc) | exact: component_coord_tuple_moment8]. Qed.

(* The eighth moment of a linear form, from Hoeffding's inequality
   (probability/subgaussian.v): E <c, x>^8 <= 48 4^8 K^8 |c|^8. *)
Lemma lin_form_moment8 (c : 'I_d -> R) :
  \int[P]_t ((\sum_(b < d) c b * tnth t b) ^+ 8)%:E <=
  (48 * 4 ^+ 8 * K ^+ 8 * (\sum_(b < d) c b ^+ 2) ^+ 4)%:E.
Proof. first [exact: (component_lin_form_moment8 K d nu hnuc) | exact: component_lin_form_moment8]. Qed.

Lemma integrable_quad_form_pow4 (A : 'M[R]_d) :
  P.-integrable setT (fun t => (quad_form A t ^+ 4)%:E).
Proof. first [exact: (component_integrable_quad_form_pow4 K d nu hnuc) | exact: component_integrable_quad_form_pow4]. Qed.

Lemma quad_form_pow4_fin (A : 'M[R]_d) :
  \int[P]_t (quad_form A t ^+ 4)%:E < +oo.
Proof. first [exact: (component_quad_form_pow4_fin K d nu hnuc) | exact: component_quad_form_pow4_fin]. Qed.

(* The fourth moment of the difference after resampling the coordinate i:
   E (Q_A (x) - Q_A (x^(i)))^4 <= (2^16 K^4 r_i)^2, where r_i is the
   squared norm of the row and the column i of A. *)
Lemma quad_form_resample4 (A : 'M[R]_d) (i : 'I_d) :
  \int[P]_t \int[nu i]_s
    ((quad_form A t - quad_form A (tuple_set t i s)) ^+ 4)%:E <=
  ((2 ^+ 16 * K ^+ 4 * \sum_(b < d) (A i b ^+ 2 + A b i ^+ 2)) ^+ 2)%:E.
Proof. first [exact: (component_quad_form_resample4 K d nu hnuc) | exact: component_quad_form_resample4]. Qed.

(* The fourth moment of the quadratic form, by the moment bound of
   Efron-Stein (probability/efron_stein.v):
   E (x^T A x - tr A)^4 <= 9 2^33 K^8 |A|_F^4. *)
Lemma quad_form_moment4 (A : 'M[R]_d) :
  \int[P]_t (quad_form A t ^+ 4)%:E <=
  (9 * 2 ^+ 33 * K ^+ 8 * mxdot A A ^+ 2)%:E.
Proof. first [exact: (component_quad_form_moment4 K d nu hnuc) | exact: component_quad_form_moment4]. Qed.

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

Lemma sqrt_inv_sqr d :
  (Num.sqrt d%:R)^-1 * (Num.sqrt d%:R)^-1 = d%:R^-1 :> R.
Proof. by rewrite -invfM -expr2 sqr_sqrtr ?ler0n. Qed.

(* The matrix W of the feature of a point t is quad_mx t / sqrt d. *)
Lemma vec_mx_feature d (t : d.-tuple (measurableTypeR R)) :
  vec_mx (data_feature_map d t) = (Num.sqrt d%:R)^-1 *: quad_mx t.
Proof.
rewrite /data_feature_map /unsat_feature mxvecK; apply/matrixP => a b.
by rewrite !mxE big_ord1 !mxE.
Qed.

Lemma quad_mx_entry2_le d (t : d.-tuple (measurableTypeR R)) (a b : 'I_d) :
  quad_mx t a b ^+ 2 <= 4 * (1 + \sum_(k < d) (tnth t k : R) ^+ 4).
Proof.
rewrite mxE; set x := (tnth t a : R); set y := (tnth t b : R).
set v : R := (a == b)%:R; set S := \sum_(k < d) _.
have S0 : 0 <= S by apply: sumr_ge0 => k _; exact: exprn4_ge0.
have v2 : v ^+ 2 <= 1 by rewrite /v; case: (a == b); rewrite ?expr1n ?expr0n.
have ha : x ^+ 4 <= 1 + S := coord_pow4_le d t a.
have hb : y ^+ 4 <= 1 + S := coord_pow4_le d t b.
have u2 : (x * y) ^+ 2 <= 1 + S.
  have h := sqr_ge0 (x ^+ 2 - y ^+ 2).
  rewrite exprMn; rewrite (_ : 4 = 2 * 2)%N // !exprM in ha hb; nra.
have := sqr_ge0 ((x * y)%R + v); nra.
Qed.

(* |W|_F^2 <= 4 d (1 + sum_k x_k^4). *)
Lemma feature_norm_le d (t : d.-tuple (measurableTypeR R)) :
  mxdot (data_feature_map d t) (data_feature_map d t) <=
  4 * d%:R * (1 + \sum_(k < d) (tnth t k : R) ^+ 4).
Proof.
set S := 1 + _.
have S0 : 0 <= S by rewrite addr_ge0 // sumr_ge0 // => k _; exact: exprn4_ge0.
rewrite -[data_feature_map d t]vec_mxK mxdot_mxvec vec_mx_feature.
rewrite mxdotZl mxdotZr mulrA sqrt_inv_sqr.
have GG : mxdot (quad_mx t) (quad_mx t) <= (d * d)%:R * (4 * S).
  apply: le_trans (_ : \sum_(a < d) \sum_(b < d) (4 * S) <= _).
    apply: ler_sum => a _; apply: ler_sum => b _; rewrite -expr2.
    exact: quad_mx_entry2_le.
  under eq_bigr do rewrite sumr_const card_ord.
  rewrite sumr_const card_ord -mulrnA [in X in _ <= X]mulr_natl.
  exact: lexx.
apply: le_trans (ler_wpM2l _ GG) _; first by rewrite invr_ge0 ler0n.
rewrite natrM; have [->|d0] := eqVneq (d%:R : R) 0.
  by rewrite invr0 !mul0r mulr0 mul0r.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* |z T z^T| <= |T|_F |z|^2. *)
Lemma quad_stat_le n (z : 'rV[R]_n) (T : 'M[R]_n) :
  `|mxdot z (z *m T)| <= frobenius T * mxdot z z.
Proof.
apply: le_trans (mxdot_le _ _) _.
apply: le_trans (ler_wpM2l (frobenius_ge0 _) (frobenius_mulmx _ _)) _.
by rewrite mulrA -expr2 frobenius_sqr mulrC.
Qed.

Lemma measurable_quad_stat d (T : 'M[R]_(d * d)) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun t => mxdot (data_feature_map d t) (data_feature_map d t *m T) : RR).
Proof.
have mz := measurable_data_feature_map d.
have mzT : measurable_fun [set: d.-tuple (measurableTypeR R)]
    (fun t => data_feature_map d t *m T).
  by apply: measurable_mulmx => //; exact: measurable_cst.
rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
apply: measurable_funM.
  exact: measurableT_comp (measurable_mxentry i j) mz.
exact: measurableT_comp (measurable_mxentry i j) mzT.
Qed.

(* Resampling: z T z^T - z' T z'^T = <z - z', z T> + <z - z', z' T^T>. *)
Lemma quad_stat_diff n (z z' : 'rV[R]_n) (T : 'M[R]_n) :
  mxdot z (z *m T) - mxdot z' (z' *m T) =
  mxdot (z - z') (z *m T) + mxdot (z - z') (z' *m T^T).
Proof.
have e : mxdot z' (z *m T) - mxdot z' (z' *m T) =
    mxdot (z - z') (z' *m T^T).
  by rewrite -mxdotBr -mulmxBl mxdotC mxdot_mulmxr.
by rewrite mxdotBl -e; ring.
Qed.

(* The part of a d x d matrix in the row and the column j. *)
Definition rc_proj {d} (j : 'I_d) (M : 'M[R]_d) : 'M[R]_d :=
  \matrix_(a, b) (((a == j) || (b == j))%:R * M a b).

Lemma mxdot_rc_proj d (j : 'I_d) (X Y : 'M[R]_d) :
  (forall a b, a != j -> b != j -> X a b = 0) ->
  mxdot X Y = mxdot X (rc_proj j Y).
Proof.
move=> X0; apply: eq_bigr => a _; apply: eq_bigr => b _; rewrite mxE.
case: (boolP ((a == j) || (b == j))) => [_|]; first by rewrite mul1r.
by rewrite negb_or => /andP[aj bj]; rewrite X0 // !mul0r.
Qed.

(* Resampling the coordinate j changes the feature only in the row and the
   column j. *)
Lemma feature_set_support d (t : d.-tuple (measurableTypeR R)) (j : 'I_d)
    (s : R) (a b : 'I_d) : a != j -> b != j ->
  vec_mx (data_feature_map d t - data_feature_map d (tuple_set t j s)) a b = 0.
Proof.
move=> aj bj; rewrite linearB /= !vec_mx_feature !mxE.
by rewrite !tnth_tuple_set_neq // subrr.
Qed.

Lemma feature_diff_dot_le d (t : d.-tuple (measurableTypeR R)) (j : 'I_d)
    (s : R) (v : 'rV[R]_(d * d)) :
  mxdot (data_feature_map d t - data_feature_map d (tuple_set t j s)) v ^+ 2
  <= mxdot (data_feature_map d t - data_feature_map d (tuple_set t j s))
       (data_feature_map d t - data_feature_map d (tuple_set t j s)) *
     mxdot (rc_proj j (vec_mx v)) (rc_proj j (vec_mx v)).
Proof.
set D := data_feature_map d t - _.
have -> : mxdot D v = mxdot (vec_mx D) (vec_mx v).
  by rewrite -[in RHS]mxdot_mxvec !vec_mxK.
have -> : mxdot D D = mxdot (vec_mx D) (vec_mx D).
  by rewrite -[in RHS]mxdot_mxvec !vec_mxK.
rewrite (mxdot_rc_proj _ j (vec_mx D) (vec_mx v)
  (fun a b aj bj => feature_set_support d t j s a b aj bj)).
exact: mxdot_cauchy_schwarz.
Qed.

Lemma sum_eq1 d (k : 'I_d) : \sum_(e < d) (e == k)%:R = 1 :> R.
Proof. by have := sum_delta' d (fun=> 1) k; under eq_bigr do rewrite mul1r. Qed.

(* |W - W^(j)|_F^2 <= (6 D^2 sum_b x_b^2 + 3 D^4) / d, D = s - x_j. *)
Lemma feature_diff_norm_le d (t : d.-tuple (measurableTypeR R)) (j : 'I_d)
    (s : R) :
  mxdot (data_feature_map d t - data_feature_map d (tuple_set t j s))
        (data_feature_map d t - data_feature_map d (tuple_set t j s)) <=
  d%:R^-1 * (6 * (s - tnth t j) ^+ 2 * \sum_(b < d) (tnth t b : R) ^+ 2 +
             3 * (s - tnth t j) ^+ 4).
Proof.
set Z := (_ - _ : 'rV[R]_(d * d)); set D := s - tnth t j.
have -> : mxdot Z Z = mxdot (vec_mx Z) (vec_mx Z).
  by rewrite -[in RHS]mxdot_mxvec !vec_mxK.
rewrite /Z linearB /= !vec_mx_feature -scalerBr mxdotZl mxdotZr mulrA.
rewrite sqrt_inv_sqr; apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
set G := quad_mx t - quad_mx (tuple_set t j s).
pose x (b : 'I_d) : R := tnth t b; pose e (a : 'I_d) : R := (a == j)%:R.
have hab a b : G a b * G a b <=
    3 * D ^+ 2 * (e a * x b ^+ 2 + x a ^+ 2 * e b) +
    3 * D ^+ 4 * (e a * e b).
  rewrite /G !mxE !tnth_tuple_setE -/D /e /x.
  have D2 := sqr_ge0 D; have D4 := exprn4_ge0 D; clearbody D.
  case: (a =P j) => [->|aj]; case: (b =P j) => [->|bj] /=.
  - by have := sqr_ge0 (D * (tnth t j - D)); nra.
  - by have := sqr_ge0 (D * tnth t b); nra.
  - by have := sqr_ge0 (D * tnth t a); nra.
  - nra.
apply: le_trans (_ : \sum_a \sum_b (3 * D ^+ 2 * (e a * x b ^+ 2 +
    x a ^+ 2 * e b) + 3 * D ^+ 4 * (e a * e b)) <= _).
  by apply: ler_sum => a _; apply: ler_sum => b _; exact: hab.
have e1 : \sum_(a < d) e a = 1 by exact: sum_eq1.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
have s1 : \sum_(a < d) \sum_(b < d) e a * x b ^+ 2 =
    \sum_(b < d) tnth t b ^+ 2.
  by under eq_bigr do rewrite -mulr_sumr; rewrite -mulr_suml e1 mul1r.
have s2 : \sum_(a < d) \sum_(b < d) x a ^+ 2 * e b =
    \sum_(b < d) tnth t b ^+ 2.
  by under eq_bigr do rewrite -mulr_sumr e1 mulr1.
have s3 : \sum_(a < d) \sum_(b < d) e a * e b = 1.
  by under eq_bigr do rewrite -mulr_sumr e1 mulr1.
transitivity (3 * D ^+ 2 * (\sum_(a < d) \sum_(b < d) e a * x b ^+ 2 +
    \sum_(a < d) \sum_(b < d) x a ^+ 2 * e b) +
    3 * D ^+ 4 * \sum_(a < d) \sum_(b < d) e a * e b).
  rewrite mulrDr !mulr_sumr -!big_split /=; apply: eq_bigr => a _.
  rewrite !mulr_sumr -!big_split /=; apply: eq_bigr => b _; ring.
by rewrite s1 s2 s3; ring.
Qed.

Lemma sqr_sum1_le n (y : 'I_n -> R) :
  (\sum_i y i) ^+ 2 <= n%:R * \sum_i y i ^+ 2.
Proof. by have := sqr_sum_le 1 n (fun=> y); rewrite !big_ord1 mul1n. Qed.

(* |W - W^(j)|_F^4 <= 54 2^7 (x_j^8 + s^8) + 36 sum_b x_b^8 / d. *)
Lemma feature_diff_norm4_le d (t : d.-tuple (measurableTypeR R)) (j : 'I_d)
    (s : R) :
  mxdot (data_feature_map d t - data_feature_map d (tuple_set t j s))
        (data_feature_map d t - data_feature_map d (tuple_set t j s)) ^+ 2
  <= 54 * 2 ^+ 7 * ((tnth t j : R) ^+ 8 + s ^+ 8) +
     36 / d%:R * \sum_(b < d) (tnth t b : R) ^+ 8.
Proof.
set Z := (_ - _ : 'rV[R]_(d * d)); set D := s - tnth t j.
set q := \sum_(b < d) (tnth t b : R) ^+ 2.
set Q4 := \sum_(b < d) (tnth t b : R) ^+ 4.
set Q8 := \sum_(b < d) (tnth t b : R) ^+ 8.
have r1 : 1 <= d%:R :> R by rewrite ler1n (leq_ltn_trans (leq0n j)).
have r0 : 0 < d%:R :> R by apply: lt_le_trans r1.
have h := feature_diff_norm_le d t j s; rewrite -/Z -/D -/q in h.
have Z0 : 0 <= mxdot Z Z := mxdot_ge0 Z.
have D4 := exprn4_ge0 D; have D8 := exprn8_ge0 D.
have q0 : 0 <= q by apply: sumr_ge0 => b _; exact: sqr_ge0.
have F2 : q ^+ 2 <= d%:R * Q4.
  have := sqr_sum1_le d (fun b => (tnth t b : R) ^+ 2).
  by rewrite /Q4; under [X in _ <= _ * X]eq_bigr do rewrite -exprM.
have F3 : D ^+ 4 * Q4 <= (d%:R * D ^+ 8 + Q8) / 2.
  rewrite /Q4 /Q8 mulr_sumr.
  apply: le_trans (_ : \sum_(b < d) (D ^+ 8 + (tnth t b : R) ^+ 8) / 2 <= _).
    apply: ler_sum => b _; have := sqr_ge0 (D ^+ 4 - (tnth t b : R) ^+ 4).
    have e8 (y : R) : y ^+ 8 = (y ^+ 4) ^+ 2 by rewrite -exprM.
    by rewrite !e8; nra.
  rewrite -mulr_suml big_split /= sumr_const card_ord -mulr_natl.
  rewrite [in X in _ <= X]mulr_natl; exact: lexx.
have F4 : D ^+ 8 <= 2 ^+ 7 * ((tnth t j : R) ^+ 8 + s ^+ 8).
  by rewrite addrC; exact: pow8_sub_le.
have S1 : mxdot Z Z ^+ 2 <=
    (d%:R^-1 * (6 * D ^+ 2 * q + 3 * D ^+ 4)) ^+ 2.
  by rewrite ler_pXn2r // nnegrE // (le_trans Z0 h).
have S2 : (6 * D ^+ 2 * q + 3 * D ^+ 4) ^+ 2 <=
    36 * d%:R ^+ 2 * D ^+ 8 + 36 * d%:R * Q8 + 18 * D ^+ 8.
  have a1 : (6 * D ^+ 2 * q + 3 * D ^+ 4) ^+ 2 <=
      72 * (D ^+ 4 * q ^+ 2) + 18 * D ^+ 8.
    have := sqr_ge0 (6 * D ^+ 2 * q - 3 * D ^+ 4).
    have e4 : D ^+ 4 = (D ^+ 2) ^+ 2 by rewrite -exprM.
    have e8 : D ^+ 8 = (D ^+ 2) ^+ 4 by rewrite -exprM.
    by rewrite e4 e8; nra.
  have a2 : D ^+ 4 * q ^+ 2 <= D ^+ 4 * (d%:R * Q4) by rewrite ler_wpM2l.
  have a3 : D ^+ 4 * (d%:R * Q4) <= d%:R * ((d%:R * D ^+ 8 + Q8) / 2).
    by rewrite mulrCA ler_wpM2l // ltW.
  by clearbody D q Q4 Q8; nra.
apply: le_trans S1 _; rewrite exprMn exprVn.
apply: le_trans (ler_wpM2l _ S2) _; first by rewrite invr_ge0 exprn_ge0 // ltW.
have e : (d%:R ^+ 2)^-1 * (36 * d%:R ^+ 2 * D ^+ 8 + 36 * d%:R * Q8 +
    18 * D ^+ 8) = 36 * D ^+ 8 + 36 / d%:R * Q8 + 18 * D ^+ 8 / d%:R ^+ 2.
  have dn : d%:R != 0 :> R by rewrite gt_eqF.
  by field.
rewrite e.
have d2 : 18 * D ^+ 8 / d%:R ^+ 2 <= 18 * D ^+ 8.
  rewrite ler_pdivrMr ?exprn_gt0 //.
  have h18 : 0 <= 18 * D ^+ 8 by rewrite mulr_ge0.
  have hd : 1 <= d%:R ^+ 2 :> R by rewrite expr2; nra.
  nra.
by clearbody D q Q4 Q8; nra.
Qed.

Lemma mulmx_row_dot n (z : 'rV[R]_n) (M : 'M[R]_n) q :
  (z *m M) 0 q = mxdot z (row q M^T).
Proof.
by rewrite mxE /mxdot big_ord1; apply: eq_bigr => p _; rewrite !mxE.
Qed.

Lemma rc_proj_norm d (j : 'I_d) (w : 'rV[R]_(d * d)) :
  mxdot (rc_proj j (vec_mx w)) (rc_proj j (vec_mx w)) =
  \sum_(p : 'I_d * 'I_d)
    ((p.1 == j) || (p.2 == j))%:R * w 0 (mxvec_index p.1 p.2) ^+ 2.
Proof.
rewrite /mxdot pair_big /=; apply: eq_bigr => -[a b] _ /=.
rewrite !mxE; case: ((a == j) || (b == j)).
  by rewrite !mul1r expr2.
by rewrite !mul0r.
Qed.

Lemma measurable_mxdot_fun dU (U : measurableType dU) m n
    (f g : U -> 'M[RR]_(m, n)) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun x => mxdot (f x) (g x) : RR).
Proof.
move=> /measurable_fun_mxP mf /measurable_fun_mxP mg.
rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
exact: measurable_funM.
Qed.

Lemma measurable_rc_proj dU (U : measurableType dU) d (j : 'I_d)
    (f : U -> 'M[RR]_d) :
  measurable_fun setT f ->
  measurable_fun setT (fun x => rc_proj j (f x) : 'M[RR]_d).
Proof.
move=> /measurable_fun_mxP mf; apply/measurable_fun_mxP => a b.
apply: (eq_measurable_fun (fun x => ((a == j) || (b == j))%:R * f x a b : RR)).
  by move=> x _; rewrite mxE.
by apply: measurable_funM => //; exact: mf.
Qed.

Lemma measurable_vec_mx dU (U : measurableType dU) m n
    (f : U -> 'rV[RR]_(m * n)) :
  measurable_fun setT f -> measurable_fun setT (fun x => vec_mx (f x)).
Proof.
move=> /measurable_fun_mxP mf; apply/measurable_fun_mxP => a b.
apply: (eq_measurable_fun (fun x => f x 0 (mxvec_index a b))).
  by move=> x _; rewrite mxE.
exact: mf.
Qed.

(* The squared norm of the part of a linear map M on d x d matrices that
   the row and the column j see: sum over (a, b) in the row or the column j
   of the squared norm of the column (a, b) of M. *)
Definition rc_weight {d} (j : 'I_d) (M : 'M[R]_(d * d)) : R :=
  \sum_(p : 'I_d * 'I_d) ((p.1 == j) || (p.2 == j))%:R *
    mxdot (row (mxvec_index p.1 p.2) M^T) (row (mxvec_index p.1 p.2) M^T).

Lemma rc_weight_ge0 d (j : 'I_d) (M : 'M[R]_(d * d)) : 0 <= rc_weight j M.
Proof. by apply: sumr_ge0 => p _; rewrite mulr_ge0 ?ler0n ?mxdot_ge0. Qed.

(* Each entry (a, b) is in at most two of the rows and columns j. *)
Lemma sum_rc_weight d (M : 'M[R]_(d * d)) :
  \sum_(j < d) rc_weight j M <= 2 * mxdot M M.
Proof.
rewrite /rc_weight exchange_big /=.
have -> : mxdot M M = \sum_(p : 'I_d * 'I_d)
    mxdot (row (mxvec_index p.1 p.2) M^T) (row (mxvec_index p.1 p.2) M^T).
  rewrite -mxdot_trmx -[LHS]/(\sum_q \sum_k M^T q k * M^T q k).
  rewrite (reindex (uncurry (@mxvec_index d d))) /=.
    exact: (curry_mxvec_bij d d).
  apply: eq_bigr => -[a b] _ /=; rewrite /mxdot big_ord1.
  by apply: eq_bigr => k _; rewrite !mxE.
rewrite mulr_sumr; apply: ler_sum => p _; rewrite -mulr_suml.
apply: ler_wpM2r; first exact: mxdot_ge0.
apply: le_trans (_ : \sum_(j < d) ((p.1 == j)%:R + (p.2 == j)%:R) <= _).
  apply: ler_sum => j _.
  by case: (p.1 == j); case: (p.2 == j); rewrite /= ?addr0 ?add0r ?lerDl.
have one (k : 'I_d) : \sum_(e < d) (k == e)%:R = 1 :> R.
  by have := sum_delta d (fun=> 1) k; under eq_bigr do rewrite mul1r.
by rewrite big_split /= !one; lra.
Qed.

Section sum_l2.
Local Open Scope ereal_scope.
Context dT (T : measurableType dT) (mu : {measure set T -> \bar R}).

Lemma lee_sqr_fin (x : \bar R) (y : R) : 0 <= x -> (0 <= y)%R ->
  x ^+ 2 <= (y ^+ 2)%:E -> x <= y%:E.
Proof.
case: x => [r| |] // r0 y0.
  rewrite -EFin_expe !lee_fin => h.
  by rewrite -(ler_pXn2r (_ : (0 < 2)%N)) ?nnegrE.
Qed.

(* Cauchy-Schwarz for nonnegative functions with bounded second moments:
   E f g <= a b when E f^2 <= a^2 and E g^2 <= b^2. *)
Lemma integral_mul_le (f g : T -> RR) (a b : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (forall x, (0 <= f x)%R) -> (forall x, (0 <= g x)%R) ->
  (0 <= a)%R -> (0 <= b)%R ->
  \int[mu]_x (f x ^+ 2)%:E <= (a ^+ 2)%:E ->
  \int[mu]_x (g x ^+ 2)%:E <= (b ^+ 2)%:E ->
  \int[mu]_x (f x * g x)%:E <= (a * b)%:E.
Proof.
move=> mf mg f0 g0 a0 b0 hf hg.
apply: lee_sqr_fin.
- by apply: integral_ge0 => x _; rewrite lee_fin mulr_ge0.
- by rewrite mulr_ge0.
have := cauchy_schwarz mu mf mg.
under eq_integral do rewrite ger0_norm ?mulr_ge0 //.
move/le_trans; apply; rewrite exprMn EFinM.
by apply: lee_pmul => //; apply: integral_ge0 => x _;
  rewrite lee_fin sqr_ge0.
Qed.

(* || sum_i Y_i ||_2 <= sum_i c_i when || Y_i ||_2 <= c_i, for nonnegative
   Y_i, in squared form. *)
Lemma integral_sum_sqr_le (I : finType) (Y : I -> T -> RR) (c : I -> R) :
  (forall i, measurable_fun setT (Y i)) -> (forall i x, (0 <= Y i x)%R) ->
  (forall i, (0 <= c i)%R) ->
  (forall i, \int[mu]_x ((Y i x) ^+ 2)%:E <= ((c i) ^+ 2)%:E) ->
  \int[mu]_x ((\sum_i Y i x) ^+ 2)%:E <= ((\sum_i c i) ^+ 2)%:E.
Proof.
move=> mY Y0 c0 hY.
have e x : ((\sum_i Y i x) ^+ 2 = \sum_i \sum_k Y i x * Y k x)%R.
  by rewrite expr2 mulr_suml; apply: eq_bigr => i _; rewrite mulr_sumr.
have m2 i k : measurable_fun setT (fun x => (Y i x * Y k x)%:E).
  by apply/measurable_EFinP; exact: measurable_funM.
have p2 i k x : 0 <= (Y i x * Y k x)%:E by rewrite lee_fin mulr_ge0.
under eq_integral do rewrite e -sumEFin.
under eq_integral do under eq_bigr do rewrite -sumEFin.
rewrite ge0_integral_sum //.
- by move=> i; apply: emeasurable_sum => k; exact: m2.
- by move=> i x _; apply: sume_ge0 => k _; exact: p2.
have h i k : \int[mu]_x (Y i x * Y k x)%:E <= (c i * c k)%:E.
  apply: lee_sqr_fin; first by apply: integral_ge0 => x _; exact: p2.
    by rewrite mulr_ge0.
  have := cauchy_schwarz mu (mY i) (mY k).
  under eq_integral do rewrite ger0_norm ?mulr_ge0 //.
  move/le_trans; apply; rewrite exprMn EFinM.
  by apply: lee_pmul => //; apply: integral_ge0 => x _;
    rewrite lee_fin sqr_ge0.
have E k : \int[mu]_x (\sum_i (Y k x * Y i x)%:E) =
    \sum_i \int[mu]_x (Y k x * Y i x)%:E.
  by rewrite ge0_integral_sum.
under eq_bigr do rewrite E.
apply: (@le_trans _ _ (\sum_k \sum_i (c k * c i)%:E)).
  by apply: lee_sum => k _; apply: lee_sum => i _; exact: h.
under eq_bigr do rewrite sumEFin.
rewrite sumEFin lee_fin le_eqVlt; apply/orP; left; apply/eqP.
by rewrite expr2 mulr_suml; apply: eq_bigr => k _; rewrite mulr_sumr.
Qed.

End sum_l2.

(* The covariance of the Gaussian feature: gaussian_feature kappa (Cones)
   is c (G + (s - 1) diag G) with G = (A + A^T) / 2, c = sqrt (2 / d) and
   s = sqrt ((kappa - 1) / 2). *)
Lemma mxdot_diag_part d (A B : 'M[R]_d) :
  mxdot A (diag_part B) = \sum_i A i i * B i i.
Proof.
apply: eq_bigr => i _; rewrite (bigD1 i) //= big1 ?addr0.
  by move=> j ji; rewrite mxE eq_sym (negbTE ji) mulr0.
by rewrite mxE eqxx.
Qed.

Lemma mxdot_goe_part d (A B : 'M[R]_d) :
  mxdot (goe_part A) B = (2%:R)^-1 * (mxdot A B + mxdot A B^T).
Proof.
rewrite /goe_part mxdotZl mxdotDl; congr (_ * (_ + _)).
by rewrite -[X in mxdot _ X]trmxK mxdot_trmx.
Qed.

Lemma goe_part_diag d (A : 'M[R]_d) (i : 'I_d) : goe_part A i i = A i i.
Proof. by rewrite !mxE; field. Qed.

Lemma gaussian_featureE (kappa : R) d (A : 'M[R]_d) :
  gaussian_feature kappa A = Num.sqrt (2%:R / d%:R) *:
    (goe_part A + (Num.sqrt ((kappa - 1) / 2%:R) - 1) *:
      diag_part (goe_part A)).
Proof.
rewrite /gaussian_feature /cone_map; congr (_ *: _).
by rewrite scalerBl scale1r addrA addrAC.
Qed.

Lemma gaussian_feature_entry (kappa : R) d (A : 'M[R]_d) (i j : 'I_d) :
  gaussian_feature kappa A i j = Num.sqrt (2%:R / d%:R) *
    ((2%:R)^-1 * (A i j + A j i) +
     (Num.sqrt ((kappa - 1) / 2%:R) - 1) * ((i == j)%:R * A i i)).
Proof.
rewrite gaussian_featureE !mxE; congr (_ * (_ + _ * _)).
by case: eqP => [->|ij]; [rewrite mul1r; field | rewrite mul0r].
Qed.

Lemma gaussian_feature_sym (kappa : R) d (A : 'M[R]_d) :
  (gaussian_feature kappa A)^T = gaussian_feature kappa A.
Proof.
apply/matrixP => i j; rewrite mxE !gaussian_feature_entry.
case: (eqVneq i j) => [->//|ij].
by rewrite /=; ring.
Qed.

(* <gaussian_feature A, B> is symmetric in A and B. *)
Lemma mxdot_gaussian_featurel (kappa : R) d (A B : 'M[R]_d) :
  mxdot (gaussian_feature kappa A) B = Num.sqrt (2%:R / d%:R) *
    ((2%:R)^-1 * (mxdot A B + mxdot A B^T) +
     (Num.sqrt ((kappa - 1) / 2%:R) - 1) * \sum_i A i i * B i i).
Proof.
rewrite gaussian_featureE mxdotZl mxdotDl mxdotZl.
rewrite mxdotDl mxdotZl [mxdot (diag_part _) _]mxdotC mxdot_diag_part.
rewrite -[X in mxdot A^T X]trmxK mxdot_trmx.
congr (_ * (_ + _ * _)).
by apply: eq_bigr => i _; rewrite goe_part_diag mulrC.
Qed.

Lemma mxdot_gaussian_featureC (kappa : R) d (A B : 'M[R]_d) :
  mxdot (gaussian_feature kappa A) B = mxdot A (gaussian_feature kappa B).
Proof.
rewrite [RHS]mxdotC !mxdot_gaussian_featurel; congr (_ * (_ * _ + _ * _)).
  rewrite [mxdot B A]mxdotC; congr (_ + _).
  by rewrite -[RHS]mxdot_trmx trmxK mxdotC.
by apply: eq_bigr => i _; rewrite mulrC.
Qed.

Lemma mxdot_gaussian_feature (kappa : R) d (A B : 'M[R]_d) : 1 <= kappa ->
  mxdot (gaussian_feature kappa A) (gaussian_feature kappa B) =
  unsat_cov_form kappa d A B.
Proof.
move=> k1.
have gs := gaussian_feature_sym kappa d B.
have gd (i : 'I_d) : gaussian_feature kappa B i i =
    Num.sqrt (2%:R / d%:R) * Num.sqrt ((kappa - 1) / 2%:R) * B i i.
  by rewrite gaussian_feature_entry eqxx mul1r; field.
rewrite mxdot_gaussian_featurel gs.
have -> : (2%:R)^-1 * (mxdot A (gaussian_feature kappa B) +
    mxdot A (gaussian_feature kappa B)) = mxdot A (gaussian_feature kappa B).
  by field.
rewrite -mxdot_gaussian_featureC mxdot_gaussian_featurel.
have -> : \sum_i A i i * gaussian_feature kappa B i i =
    Num.sqrt (2%:R / d%:R) * Num.sqrt ((kappa - 1) / 2%:R) *
    \sum_i A i i * B i i.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite gd; ring.
rewrite /unsat_cov_form !RmultE !RplusE ?RminusE.
set c := Num.sqrt (2%:R / d%:R); set s := Num.sqrt ((kappa - 1) / 2%:R).
have c2 : c ^+ 2 = 2%:R / d%:R by rewrite sqr_sqrtr // divr_ge0 ?ler0n.
have s2 : s ^+ 2 = (kappa - 1) / 2%:R.
  by rewrite sqr_sqrtr // divr_ge0 ?subr_ge0 ?ler0n.
move: c2 s2; clearbody c s => c2 s2.
set S := \sum_i _; set X := mxdot A B + _.
have -> : c * (c * (2%:R^-1 * X + (s - 1) * S) + (s - 1) * (c * s * S)) =
    c ^+ 2 * (2%:R^-1 * X + (s ^+ 2 - 1) * S) by ring.
rewrite c2 s2.
by clearbody S X; set u := (d%:R^-1)%R; clearbody u; field.
Qed.

(* The matrix of the Gaussian feature is symmetric, its covariance matrix
   S^T S is unsat_cov kappa d, and g *m S is the mxvec of the Gaussian
   feature of vec_mx g. *)
Lemma gaussian_featureD (kappa : R) d (A B : 'M[R]_d) :
  gaussian_feature kappa (A + B) =
  gaussian_feature kappa A + gaussian_feature kappa B.
Proof.
apply/matrixP => i j; rewrite [RHS]mxE !gaussian_feature_entry !mxE.
by ring.
Qed.

Lemma gaussian_featureZ (kappa : R) d a (A : 'M[R]_d) :
  gaussian_feature kappa (a *: A) = a *: gaussian_feature kappa A.
Proof.
apply/matrixP => i j; rewrite [RHS]mxE !gaussian_feature_entry !mxE.
by ring.
Qed.

Lemma gaussian_feature0 (kappa : R) d :
  gaussian_feature kappa (0 : 'M[R]_d) = 0.
Proof.
by apply/matrixP => i j; rewrite gaussian_feature_entry !mxE; ring.
Qed.

Lemma gaussian_feature_mxE (kappa : R) d (g : 'rV[R]_(d * d)) :
  g *m gaussian_feature_mx kappa d =
  mxvec (gaussian_feature kappa (vec_mx g)).
Proof.
apply/rowP => q; rewrite mxE (vec_mx_sum _ _ g).
have -> : gaussian_feature kappa
    (\sum_(p < d * d) g 0 p *: vec_mx (delta_mx 0 p)) =
    \sum_(p < d * d) g 0 p *: gaussian_feature kappa (vec_mx (delta_mx 0 p)).
  elim/big_rec2: _ => [|p A B _ <-]; first exact: gaussian_feature0.
  by rewrite gaussian_featureD gaussian_featureZ.
rewrite linear_sum summxE; apply: eq_bigr => p _.
by rewrite linearZ !mxE.
Qed.

Lemma gaussian_feature_mx_entry (kappa : R) d (p q : 'I_(d * d)) :
  gaussian_feature_mx kappa d p q =
  mxdot (gaussian_feature kappa (vec_mx (delta_mx 0 p)))
        (vec_mx (delta_mx 0 q : 'rV[R]_(d * d))).
Proof.
rewrite mxE -mxdot_mxvec vec_mxK.
by rewrite (mxdot_delta (mxvec (gaussian_feature kappa _)) 0 q).
Qed.

Lemma gaussian_feature_mx_symE (kappa : R) d (p q : 'I_(d * d)) :
  gaussian_feature_mx kappa d p q = gaussian_feature_mx kappa d q p.
Proof.
by rewrite !gaussian_feature_mx_entry mxdot_gaussian_featureC mxdotC.
Qed.

Lemma gaussian_feature_mx_cov (kappa : R) d : 1 <= kappa ->
  (gaussian_feature_mx kappa d)^T *m gaussian_feature_mx kappa d =
  unsat_cov kappa d.
Proof.
move=> k1; apply/matrixP => p q.
rewrite [RHS]mxE -(mxdot_gaussian_feature _ d _ _ k1) -mxdot_mxvec.
rewrite -!gaussian_feature_mxE /mxdot big_ord1 mxE; apply: eq_bigr => r _.
rewrite -!rowE [in LHS]mxE (gaussian_feature_mx_symE _ _ r p).
by rewrite (gaussian_feature_mx_symE _ _ r q) !mxE.
Qed.

Section subexponential_facts.
Local Open Scope ereal_scope.
Context dT (T : measurableType dT) (Q : probability T RR).

(* The subexponential constant can be increased, and scales. *)
Lemma subexponential_le (Y : T -> RR) (L L' : R) :
  subexponential Q Y L -> (L <= L')%R -> subexponential Q Y L'.
Proof.
case=> L0 mY h LL'; have L'0 : (0 < L')%R by exact: lt_le_trans LL'.
split => //; apply: le_trans h; apply: ge0_le_integral => //.
- apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
- apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
move=> t _; rewrite lee_fin ler_expR ler_wpM2l //.
by rewrite lef_pV2.
Qed.

Lemma subexponential_scale (Y : T -> RR) (L c : R) : (0 < c)%R ->
  subexponential Q Y L -> subexponential Q (fun t => Y t / c)%R (L / c).
Proof.
move=> c0 [L0 mY h]; split; first by rewrite divr_gt0.
  by apply: measurable_funM => //; exact: measurable_cst.
apply: le_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_integral => t _.
have cn : (c != 0)%R by rewrite gt_eqF.
have Ln : (L != 0)%R by rewrite gt_eqF.
have e : (`|Y t / c| / (L / c) = `|Y t| / L)%R.
  have c1 : (0 <= c^-1)%R by rewrite invr_ge0 ltW.
  by rewrite normrM (ger0_norm c1); field.
by rewrite e.
Qed.

Lemma subexponential_distribution dW (W : measurableType dW)
    (X : {mfun T >-> W}) (f : W -> RR) (L : R) : measurable_fun setT f ->
  subexponential (distribution Q X) f L <-> subexponential Q (f \o X) L.
Proof.
move=> mf; have me : measurable_fun setT (fun w => (expR (`|f w| / L))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurableT_comp.
rewrite /subexponential integral_distribution_measurable //.
split => -[L0 _ h]; split => //.
exact: measurableT_comp mf (measurable_funPT X).
Qed.

End subexponential_facts.

Lemma quad_sum_outer d (v : 'rV[R]_d) (t : d.-tuple (measurableTypeR R)) :
  quad_sum (v^T *m v) t = (\sum_(b < d) v 0 b * tnth t b) ^+ 2.
Proof.
rewrite /quad_sum expr2 mulr_suml; apply: eq_bigr => a _.
rewrite mulr_sumr; apply: eq_bigr => b _.
by rewrite !mxE big_ord1 !mxE; ring.
Qed.

Lemma trace_outer d (v : 'rV[R]_d) : \tr (v^T *m v) = mxdot v v.
Proof.
rewrite /mxtrace /mxdot big_ord1; apply: eq_bigr => a _.
by rewrite !mxE big_ord1 !mxE.
Qed.

(* C_kappa (V, V) <= (kappa + 1) |V|_F^2 / d for V symmetric. *)
Lemma unsat_cov_form_le (kappa : R) d (V : 'M[R]_d) : 1 <= kappa ->
  V \is symmetricmx ->
  unsat_cov_form kappa d V V <= (kappa + 1) / d%:R * mxdot V V.
Proof.
move=> k1 /symmetricmxP VT; rewrite /unsat_cov_form VT.
rewrite !RmultE !RplusE ?RminusE.
set S := \sum_(j < d) V j j * V j j.
have S0 : 0 <= S by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
have SV : S <= mxdot V V.
  rewrite /S /mxdot; apply: ler_sum => i _.
  rewrite (bigD1 i) //= lerDl; apply: sumr_ge0 => j _.
  by rewrite -expr2 sqr_ge0.
have V0 : 0 <= mxdot V V := mxdot_ge0 V.
rewrite mulrC [X in _ <= X]mulrAC; apply: ler_wpM2r.
  by rewrite invr_ge0 ler0n.
have [k3|k3] := lerP 3 kappa.
  have h : (kappa - 3) * S <= (kappa - 3) * mxdot V V.
    by rewrite ler_wpM2l // subr_ge0.
  nra.
have h : 0 <= (3 - kappa) * S by rewrite mulr_ge0 // subr_ge0 ltW.
nra.
Qed.

(* The constant 1 is subgaussian with constant 2: e^(1/4) <= 2. *)
Lemma subgaussian_one dT (T : measurableType dT) (Q : probability T RR) :
  subgaussian Q (fun=> 1%R) 2.
Proof.
split => //.
rewrite (@integral_cst _ _ _ Q _ measurableT (expR (1 ^+ 2 / 2 ^+ 2))%:E).
rewrite [X in (_ * X)%E]probability_setT mule1 lee_fin expr1n.
have h1 := @expR_le_quad RR (1 / 2 ^+ 2).
have q0 : (0 <= 1 / 2 ^+ 2 :> RR)%R by rewrite divr_ge0 ?exprn_ge0.
rewrite ger0_norm // in h1.
have h2 := @expR_gt0 RR (1 / 2 ^+ 2).
by move: h1 h2; clear; set e := expR _ => h1 h2; lra.
Qed.

(* A Gaussian linear form <g, a> is subexponential with constant 4 |a|. *)
Lemma gauss_mxdot_subexponential n (a : 'rV[R]_n) : a != 0 ->
  subexponential (gauss n) (fun g => mxdot g a : RR) (4 * frobenius a).
Proof.
move=> a0; have fa : 0 < frobenius a by rewrite frobenius_gt0.
have sY : subgaussian (gauss n) (fun g => mxdot g a : RR) (2 * frobenius a).
  apply: (subgaussian_of_mgf (s := frobenius a / Num.sqrt 2)).
  - exact: measurable_mxdot.
  - by rewrite mulr_gt0.
  - rewrite expr_div_n (@sqr_sqrtr _ 2) // exprMn frobenius_sqr.
    by have := mxdot_ge0 a; lra.
  move=> l; rewrite integral_gauss_expR_mxdot lee_fin ler_expR.
  rewrite expr_div_n (@sqr_sqrtr _ 2) //.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
have := subexponential_mul sY (subgaussian_one _ _ (gauss n)).
have -> : (fun t : 'rV[R]_n => mxdot t a * 1)%R = (fun g => mxdot g a : RR).
  by apply/boolp.funext => g; rewrite mulr1.
by move=> h; apply: (subexponential_le _ _ _ _ _ _ h); lra.
Qed.

(* The Gaussian twin of Proposition 2.6: for kappa > 1 and d > 0, the law
   of the Gaussian feature is a regular feature with covariance C_kappa, by
   (2.10) (gauss_regular_feature) and gaussian_feature_mx_cov. *)
Theorem gaussian_feature_regular (kappa : R) d : 1 < kappa -> (0 < d)%N ->
  regular_feature (3 `^ (1 / 4)) (Num.sqrt 2 * opnorm (unsat_cov kappa d))
    (unsat_cov kappa d) (gaussian_feature_law kappa d).
Proof.
move=> k1 d0; have k1' : 1 <= kappa by exact: ltW.
rewrite -(gaussian_feature_mx_cov kappa d k1').
apply: gauss_regular_feature => //.
apply/eqP => S0; have := unsat_cov_opnorm_ge kappa d d0.
rewrite -(gaussian_feature_mx_cov kappa d k1') S0 mulmx0 opnorm0.
by apply/negP; rewrite -ltNge divr_gt0 ?ltr0n // subr_gt0.
Qed.

(* The quadratic features of a product of component laws: their mean, and
   the bounds on their moments and their subexponential constants, which do
   not involve the fourth moment of the coordinates. data_feature below
   states the same for the coordinate laws of the universality theorem, and
   adds the covariance, which involves kappa, and Proposition 2.6. *)
Section component_feature.
Local Open Scope ereal_scope.
Variables (K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> mixture_component_law K (nu j).
Local Notation P := (tuple_prod nu d).
Local Notation mu := (data_feature_law nu d).

Lemma component_feature_expectation (f : 'rV[RR]_(d * d) -> RR) :
  measurable_fun setT f ->
  'E_mu[f] = \int[P]_t (f (data_feature_map d t))%:E.
Proof.
move=> mf; rewrite unlock /data_feature_law.
by rewrite integral_distribution_measurable //; exact/measurable_EFinP.
Qed.

Lemma component_feature_dotE (th : 'rV[R]_(d * d)) t :
  mxdot (data_feature_map d t) th =
  ((Num.sqrt d%:R)^-1 * quad_form (vec_mx th) t)%R.
Proof. by rewrite -data_feature_dot vec_mxK. Qed.

(* Covariance matching: E <W, theta> = 0 and
   E <W, theta> <W, theta'> = theta C_kappa theta'^T. *)
Lemma component_feature_mean (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => mxdot z th] = 0.
Proof.
rewrite (component_feature_expectation (fun z => mxdot z th : RR)
  (measurable_mxdotl _ th)).
under eq_integral do rewrite component_feature_dotE EFinM.
rewrite (integralZl measurableT
  (component_integrable_quad_form _ _ _ hnu (vec_mx th))).
by rewrite (component_quad_form_mean _ _ _ hnu) mule0.
Qed.

(* (F1) for the features: E <W, theta>^4 <= 9 2^33 K^8 |theta|^4 / d^2. *)
Lemma component_feature_dot_moment4 (th : 'rV[R]_(d * d)) :
  \int[P]_t (mxdot (data_feature_map d t) th ^+ 4)%:E <=
  (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2)%:E.
Proof.
set c : R := (d%:R ^- 2)%R.
have -> : \int[P]_t (mxdot (data_feature_map d t) th ^+ 4)%:E =
    \int[P]_t (c%:E * (quad_form (vec_mx th) t ^+ 4)%:E).
  apply: eq_integral => t _; rewrite component_feature_dotE -EFinM; congr EFin.
  rewrite exprMn (_ : 4 = 2 * 2)%N // exprM [in X in (X * _)%R]expr2.
  have h : ((Num.sqrt d%:R)^-1 ^+ 2 = d%:R^-1 :> R)%R.
    by rewrite expr2 sqrt_inv_sqr.
  by rewrite h -expr2 exprVn.
have k0 : 0 <= c%:E by rewrite lee_fin /c invr_ge0 exprn_ge0.
rewrite ge0_integralZl_EFin //.
- by move=> t _; rewrite lee_fin exprn4_ge0.
- by apply/measurable_EFinP; apply: measurable_funX;
    exact: measurable_quad_form.
apply: le_trans (lee_wpmul2l k0 (component_quad_form_moment4 _ _ _ hnu _)) _.
rewrite -EFinM lee_fin.
have -> : mxdot (vec_mx th) (vec_mx th) = mxdot th th.
  by rewrite -mxdot_mxvec !vec_mxK.
by rewrite /c le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

Lemma component_feature_fourth (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th ^+ 4)%R] <=
  (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2)%:E.
Proof.
have mf : measurable_fun setT
    (fun z : 'rV[RR]_(d * d) => (mxdot z th ^+ 4)%R : RR).
  by apply: measurable_funX; exact: measurable_mxdotl.
by rewrite (component_feature_expectation _ mf); exact: component_feature_dot_moment4.
Qed.

(* The same with a square: E <W, theta>^4 <= (2^19 K^4 |theta|^2 / d)^2. *)
Lemma component_feature_dot_moment4_sqr (th : 'rV[R]_(d * d)) :
  \int[P]_t ((mxdot (data_feature_map d t) th ^+ 2) ^+ 2)%:E <=
  ((2 ^+ 19 * K ^+ 4 / d%:R * mxdot th th) ^+ 2)%:E.
Proof.
under eq_integral do rewrite -exprM.
apply: le_trans (component_feature_dot_moment4 th) _; rewrite lee_fin.
have K8 : (0 <= K ^+ 8)%R := exprn8_ge0 K.
have A : (0 <= mxdot th th ^+ 2 / d%:R ^+ 2)%R.
  by rewrite divr_ge0 ?sqr_ge0 ?exprn_ge0.
have e1 : (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2 =
    (9 * 2 ^+ 33) * (K ^+ 8 * (mxdot th th ^+ 2 / d%:R ^+ 2)))%R.
  by ring.
have e2 : ((2 ^+ 19 * K ^+ 4 / d%:R * mxdot th th) ^+ 2 =
    2 ^+ 38 * (K ^+ 8 * (mxdot th th ^+ 2 / d%:R ^+ 2)))%R.
  by rewrite -exprVn; ring.
rewrite e1 e2; apply: ler_wpM2r; first exact: mulr_ge0 K8 A.
lra.
Qed.

(* The fourth moment of the part of W M in the row and the column j:
   E |rc_j (W M)|^4 <= (2^19 K^4 rc_weight j M / d)^2. *)
Lemma component_proj_feature_moment4 (M : 'M[R]_(d * d)) (j : 'I_d) :
  \int[P]_t (mxdot (rc_proj j (vec_mx (data_feature_map d t *m M)))
                   (rc_proj j (vec_mx (data_feature_map d t *m M))) ^+ 2)%:E
  <= ((2 ^+ 19 * K ^+ 4 / d%:R * rc_weight j M) ^+ 2)%:E.
Proof.
under eq_integral do rewrite rc_proj_norm.
under eq_integral do under eq_bigr do rewrite mulmx_row_dot.
rewrite /rc_weight mulr_sumr.
pose S (p : 'I_d * 'I_d) : R := ((p.1 == j) || (p.2 == j))%:R.
pose th (p : 'I_d * 'I_d) := row (mxvec_index p.1 p.2) M^T.
apply: (integral_sum_sqr_le _ _ P _
  (fun p t => (S p * mxdot (data_feature_map d t) (th p) ^+ 2)%R : RR)
  (fun p => 2 ^+ 19 * K ^+ 4 / d%:R * (S p * mxdot (th p) (th p)))%R).
- move=> p; apply: measurable_funM => //; apply: measurable_funX.
  exact: measurableT_comp (measurable_mxdotl _ _)
    (measurable_data_feature_map d).
- by move=> p t; rewrite mulr_ge0 ?ler0n ?sqr_ge0.
- move=> p; apply: mulr_ge0; last by rewrite mulr_ge0 ?ler0n ?mxdot_ge0.
  apply: divr_ge0; last exact: ler0n.
  by apply: mulr_ge0; [exact: exprn_ge0 | exact: exprn4_ge0].
move=> p; rewrite /S; case: (_ || _).
  under eq_integral do rewrite mul1r.
  by rewrite mul1r; exact: component_feature_dot_moment4_sqr.
under eq_integral do rewrite mul0r expr0n.
by rewrite integral0 mul0r mulr0 expr0n.
Qed.

(* E |W - W^(j)|_F^4 <= 2^20 K^8, x^(j) the point x with its coordinate j
   resampled. *)
Lemma component_feature_diff_moment4 (j : 'I_d) :
  \int[P \x nu j]_p
    (mxdot (data_feature_map d p.1 - data_feature_map d (tuple_set p.1 j p.2))
           (data_feature_map d p.1 - data_feature_map d (tuple_set p.1 j p.2))
     ^+ 2)%:E <= (2 ^+ 20 * K ^+ 8)%:E.
Proof.
have K0 : (0 < K)%R := @component_law_K _ _ (hnu j (ltn_ord j)).
have d1 : (1 <= d%:R :> R)%R by rewrite ler1n (leq_ltn_trans (leq0n j)).
set C1 : R := (54 * 2 ^+ 7)%R; set C2 : R := (36 / d%:R)%R.
have C10 : (0 <= C1)%R by rewrite /C1 mulr_ge0 // exprn_ge0.
have C20 : (0 <= C2)%R by rewrite /C2 divr_ge0 // ler0n.
have mz := measurable_data_feature_map d.
have mD : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => (data_feature_map d p.1 -
      data_feature_map d (tuple_set p.1 j p.2))%R).
  apply: measurable_addmx; first exact: measurableT_comp mz measurable_fst.
  apply: measurable_oppmx.
  exact: measurableT_comp mz (measurable_tuple_set_pair j).
have mx8 : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) => ((tnth t j : RR) ^+ 8)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_tnth.
have ms8 : measurable_fun setT
    (fun s : measurableTypeR R => ((s : RR) ^+ 8)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have mS8 : measurable_fun setT (fun t : d.-tuple (measurableTypeR R) =>
    ((\sum_(b < d) (tnth t b : RR) ^+ 8)%R)%:E).
  apply/measurable_EFinP; apply: measurable_sum => b.
  by apply: measurable_funX; exact: measurable_tnth.
have e80 (y : R) : 0 <= (y ^+ 8)%:E by rewrite lee_fin exprn8_ge0.
have S80 (t : d.-tuple (measurableTypeR R)) :
    0 <= ((\sum_(b < d) (tnth t b : R) ^+ 8)%R)%:E.
  by rewrite lee_fin sumr_ge0 // => b _; exact: exprn8_ge0.
apply: (@le_trans _ _ (\int[P \x nu j]_p
    ((C1%:E * ((tnth p.1 j : R) ^+ 8)%:E + C1%:E * ((p.2 : R) ^+ 8)%:E) +
     C2%:E * ((\sum_(b < d) (tnth p.1 b : R) ^+ 8)%R)%:E))).
  apply: ge0_le_integral => //.
  - by move=> p _; rewrite lee_fin sqr_ge0.
  - apply/measurable_EFinP; apply: measurable_funX.
    exact: measurable_mxdot_fun.
  - apply: emeasurable_funD; first apply: emeasurable_funD.
    + by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
    + by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
    + by apply: measurable_funeM; exact: measurableT_comp mS8 measurable_fst.
  move=> p _; rewrite -!EFinM -!EFinD lee_fin /C1 /C2 -mulrDr.
  exact: feature_diff_norm4_le.
rewrite ge0_integralD //.
- by move=> p _; rewrite adde_ge0 // mule_ge0 ?lee_fin ?exprn8_ge0.
- apply: emeasurable_funD.
  + by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
  + by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
- by move=> p _; apply: mule_ge0; [rewrite lee_fin | exact: S80].
- by apply: measurable_funeM; exact: measurableT_comp mS8 measurable_fst.
rewrite ge0_integralD //.
- by move=> p _; rewrite mule_ge0 ?lee_fin ?exprn8_ge0.
- by apply: measurable_funeM; exact: measurableT_comp mx8 measurable_fst.
- by move=> p _; rewrite mule_ge0 ?lee_fin ?exprn8_ge0.
- by apply: measurable_funeM; exact: measurableT_comp ms8 measurable_snd.
rewrite ge0_integralZl_EFin //;
  first exact: measurableT_comp mx8 measurable_fst.
rewrite ge0_integralZl_EFin //;
  first exact: measurableT_comp ms8 measurable_snd.
rewrite ge0_integralZl_EFin //;
  first exact: measurableT_comp mS8 measurable_fst.
rewrite (resample_fst d nu j _ mx8); first by move=> t; exact: e80.
rewrite (resample_snd d nu j _ ms8); first by move=> s; exact: e80.
rewrite (resample_fst d nu j _ mS8); first by move=> t; exact: S80.
clear mD mz mx8 ms8 mS8.
have B1 := component_coord_tuple_moment8 _ _ _ hnu j.
have B2 := component_coord_moment8 _ _ _ hnu j.
have B3 : \int[P]_t ((\sum_(b < d) (tnth t b : R) ^+ 8)%R)%:E <=
    (d%:R * (48 * K ^+ 8))%:E.
  under eq_integral do rewrite -sumEFin.
  rewrite ge0_integral_sum //.
  - move=> b; apply/measurable_EFinP; apply: measurable_funX.
    exact: measurable_tnth.
  apply: (@le_trans _ _ (\sum_(k < d) (48 * K ^+ 8)%:E)).
    by apply: lee_sum => k _; exact: (component_coord_tuple_moment8 _ _ _ hnu k).
  rewrite sumEFin sumr_const card_ord lee_fin [X in (_ <= X)%R]mulr_natl.
  exact: lexx.
have C1' : 0 <= C1%:E by rewrite lee_fin.
have C2' : 0 <= C2%:E by rewrite lee_fin.
apply: le_trans (leeD (leeD (lee_wpmul2l C1' B1) (lee_wpmul2l C1' B2))
  (lee_wpmul2l C2' B3)) _.
rewrite -!EFinM -!EFinD lee_fin /C1 /C2.
have K8 : (0 <= K ^+ 8)%R := exprn8_ge0 K.
have e : (36 / d%:R * (d%:R * (48 * K ^+ 8)) = 36 * 48 * K ^+ 8)%R.
  have dn : (d%:R != 0 :> R)%R by rewrite gt_eqF // (lt_le_trans ltr01 d1).
  by field.
by rewrite e; lra.
Qed.

(* Resampling the coordinate j changes F (x) = z T z^T, z the feature of x,
   by at most 2^30 K^8 (rc_weight j T + rc_weight j T^T) / d in mean
   square. *)
Lemma component_quad_stat_resample2 (T : 'M[R]_(d * d)) (j : 'I_d) :
  \int[P]_t \int[nu j]_s
    ((mxdot (data_feature_map d t) (data_feature_map d t *m T) -
      mxdot (data_feature_map d (tuple_set t j s))
            (data_feature_map d (tuple_set t j s) *m T)) ^+ 2)%:E <=
  (2 ^+ 30 * K ^+ 8 / d%:R * (rc_weight j T + rc_weight j T^T))%:E.
Proof.
have K0 : (0 < K)%R := @component_law_K _ _ (hnu j (ltn_ord j)).
have K4 : (0 <= K ^+ 4)%R := exprn4_ge0 K.
have K8 : (0 <= K ^+ 8)%R := exprn8_ge0 K.
have dinv : (0 <= d%:R^-1 :> R)%R by rewrite invr_ge0 ler0n.
set z := data_feature_map d.
have mz : measurable_fun setT z := measurable_data_feature_map d.
have mz1 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => z p.1) := measurableT_comp mz measurable_fst.
have mz2 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => z (tuple_set p.1 j p.2)).
  exact: measurableT_comp mz (measurable_tuple_set_pair j).
have mq (f : d.-tuple (measurableTypeR R) * measurableTypeR R ->
    'rV[RR]_(d * d)) : measurable_fun setT f ->
    measurable_fun setT (fun p => mxdot (f p) (f p *m T) : RR).
  move=> mf; apply: measurable_mxdot_fun => //.
  by apply: measurable_mulmx => //; exact: measurable_cst.
have mR (M : 'M[R]_(d * d)) : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) =>
      mxdot (rc_proj j (vec_mx (z t *m M)))
            (rc_proj j (vec_mx (z t *m M))) : RR).
  have m1 : measurable_fun setT (fun t : d.-tuple (measurableTypeR R) =>
      rc_proj j (vec_mx (z t *m M)) : 'M[RR]_d).
    apply: measurable_rc_proj; apply: measurable_vec_mx.
    by apply: measurable_mulmx => //; exact: measurable_cst.
  exact: measurable_mxdot_fun.
pose D2 (p : d.-tuple (measurableTypeR R) * measurableTypeR R) : R :=
  mxdot (z p.1 - z (tuple_set p.1 j p.2)) (z p.1 - z (tuple_set p.1 j p.2)).
have mD2 : measurable_fun setT (fun p => D2 p : RR).
  have mD : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
      measurableTypeR R => (z p.1 - z (tuple_set p.1 j p.2))%R).
    by apply: measurable_addmx => //; exact: measurable_oppmx.
  exact: measurable_mxdot_fun.
pose R1 (t : d.-tuple (measurableTypeR R)) : R :=
  mxdot (rc_proj j (vec_mx (z t *m T))) (rc_proj j (vec_mx (z t *m T))).
pose R2 (t : d.-tuple (measurableTypeR R)) : R :=
  mxdot (rc_proj j (vec_mx (z t *m T^T))) (rc_proj j (vec_mx (z t *m T^T))).
have mR1 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => R1 p.1 : RR).
  exact: measurableT_comp (mR T) measurable_fst.
have mR2 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => R2 (tuple_set p.1 j p.2) : RR).
  exact: measurableT_comp (mR T^T) (measurable_tuple_set_pair j).
have D20 p : (0 <= D2 p)%R by exact: mxdot_ge0.
have R10 t : (0 <= R1 t)%R by exact: mxdot_ge0.
have R20 t : (0 <= R2 t)%R by exact: mxdot_ge0.
pose G (p : d.-tuple (measurableTypeR R) * measurableTypeR R) :=
  ((mxdot (z p.1) (z p.1 *m T) -
    mxdot (z (tuple_set p.1 j p.2)) (z (tuple_set p.1 j p.2) *m T)) ^+ 2)%:E.
have mG : measurable_fun setT G.
  apply/measurable_EFinP; apply: measurable_funX.
  by apply: measurable_funB; apply: mq.
have G0 p : 0 <= G p by rewrite lee_fin sqr_ge0.
rewrite (resample_prod d nu j G mG G0).
(* pointwise: (F - F')^2 <= 2 |D|^2 R1 + 2 |D|^2 R2 *)
apply: (@le_trans _ _ (\int[P \x nu j]_p
    (2%:E * (D2 p * R1 p.1)%:E + 2%:E * (D2 p * R2 (tuple_set p.1 j p.2))%:E))).
  apply: ge0_le_integral => //.
  - apply: emeasurable_funD; apply: measurable_funeM;
      by apply/measurable_EFinP; exact: measurable_funM.
  move=> p _; rewrite /G -!EFinM -EFinD lee_fin quad_stat_diff.
  have h1 := feature_diff_dot_le d p.1 j p.2 (z p.1 *m T).
  have h2 := feature_diff_dot_le d p.1 j p.2
    (z (tuple_set p.1 j p.2) *m T^T).
  rewrite -/(D2 p) -/(R1 p.1) in h1.
  rewrite -/(D2 p) -/(R2 (tuple_set p.1 j p.2)) in h2.
  move: h1 h2; set a := mxdot _ (z p.1 *m T); set b := mxdot _ (_ *m T^T).
  move=> h1 h2; have := sqr_ge0 (a - b); nra.
clear mG G0 G mq mz mz1 mz2.
have D2m : \int[P \x nu j]_p ((D2 p) ^+ 2)%:E <= ((2 ^+ 10 * K ^+ 4) ^+ 2)%:E.
  rewrite (_ : (2 ^+ 10 * K ^+ 4) ^+ 2 = 2 ^+ 20 * K ^+ 8)%R.
    by rewrite exprMn -!exprM.
  exact: component_feature_diff_moment4.
have R1m : \int[P \x nu j]_p ((R1 p.1) ^+ 2)%:E <=
    ((2 ^+ 19 * K ^+ 4 / d%:R * rc_weight j T) ^+ 2)%:E.
  rewrite (resample_fst d nu j (fun t => ((R1 t) ^+ 2)%:E)).
  - by apply/measurable_EFinP; apply: measurable_funX; exact: mR.
  - by move=> t; rewrite lee_fin sqr_ge0.
  exact: component_proj_feature_moment4.
have R2m : \int[P \x nu j]_p ((R2 (tuple_set p.1 j p.2)) ^+ 2)%:E <=
    ((2 ^+ 19 * K ^+ 4 / d%:R * rc_weight j T^T) ^+ 2)%:E.
  rewrite (resample_set d nu j (fun t => ((R2 t) ^+ 2)%:E)).
  - by apply/measurable_EFinP; apply: measurable_funX; exact: mR.
  - by move=> t; rewrite lee_fin sqr_ge0.
  exact: component_proj_feature_moment4.
have c10 := rc_weight_ge0 d j T; have c20 := rc_weight_ge0 d j T^T.
have a0 : (0 <= 2 ^+ 10 * K ^+ 4)%R by rewrite mulr_ge0 // exprn_ge0.
have b0 (c : R) : (0 <= c)%R -> (0 <= 2 ^+ 19 * K ^+ 4 / d%:R * c)%R.
  move=> c0; apply: mulr_ge0 => //; apply: mulr_ge0 => //.
  by apply: mulr_ge0 => //; exact: exprn_ge0.
have I1 := integral_mul_le _ _ (P \x nu j) _ _ _ _ mD2 mR1 D20
  (fun p => R10 p.1) a0 (b0 _ c10) D2m R1m.
have I2 := integral_mul_le _ _ (P \x nu j) _ _ _ _ mD2 mR2 D20
  (fun p => R20 _) a0 (b0 _ c20) D2m R2m.
have m1 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => (D2 p * R1 p.1)%:E).
  by apply/measurable_EFinP; exact: measurable_funM.
have m2 : measurable_fun setT (fun p : d.-tuple (measurableTypeR R) *
    measurableTypeR R => (D2 p * R2 (tuple_set p.1 j p.2))%:E).
  by apply/measurable_EFinP; exact: measurable_funM.
rewrite ge0_integralD //.
- by move=> p _; rewrite mule_ge0 // lee_fin mulr_ge0.
- exact: measurable_funeM.
- by move=> p _; rewrite mule_ge0 // lee_fin mulr_ge0.
- exact: measurable_funeM.
rewrite !ge0_integralZl_EFin //.
- by move=> p _; rewrite lee_fin mulr_ge0.
- by move=> p _; rewrite lee_fin mulr_ge0.
have t0 : (0 : \bar R) <= 2 by rewrite lee_fin ler0n.
apply: le_trans (leeD (lee_wpmul2l t0 I1) (lee_wpmul2l t0 I2)) _.
rewrite -!EFinM -EFinD lee_fin le_eqVlt; apply/orP; left; apply/eqP.
by ring.
Qed.

Lemma component_integrable_quad_stat (T : 'M[R]_(d * d)) :
  P.-integrable setT (fun t =>
    (mxdot (data_feature_map d t) (data_feature_map d t *m T))%:E).
Proof.
apply: (component_integrable_poly _ _ _ hnu 4 (fun t =>
  mxdot (data_feature_map d t) (data_feature_map d t *m T) : RR)
  (frobenius T * (4 * d%:R))%R).
  exact: measurable_quad_stat.
move=> t; apply: le_trans (quad_stat_le _ _ _) _; rewrite -mulrA.
by apply: ler_wpM2l; [exact: frobenius_ge0 | exact: feature_norm_le].
Qed.

(* (F2) for the features: Var (z T z^T) <= 2^31 K^8 |T|_F^2 / d. *)
Lemma component_feature_variance (T : 'M[R]_(d * d)) :
  'V_mu[fun z => mxdot z (z *m T)] <= (2 ^+ 31 * K ^+ 8 / d%:R * mxdot T T)%:E.
Proof.
have mF : measurable_fun setT
    (fun z : 'rV[RR]_(d * d) => mxdot z (z *m T) : RR).
  apply: measurable_mxdot_fun; first exact: measurable_id.
  by apply: measurable_mulmx; [exact: measurable_id | exact: measurable_cst].
rewrite /data_feature_law (variance_distribution _ _ mF).
apply: le_trans (efron_stein_resample (component_integrable_quad_stat T)) _.
have h0 : (0 : \bar R) <= (2^-1)%:E by rewrite lee_fin invr_ge0.
apply: (le_trans (lee_wpmul2l h0 _)).
  by apply: lee_sum => j _; exact: component_quad_stat_resample2.
rewrite /= sumEFin -EFinM lee_fin -mulr_sumr big_split /=.
have K8 : (0 <= K ^+ 8)%R := exprn8_ge0 K.
have c0 : (0 <= 2 ^+ 30 * K ^+ 8 / d%:R)%R.
  by rewrite divr_ge0 ?ler0n // mulr_ge0 // exprn_ge0.
have S := lerD (sum_rc_weight d T) (sum_rc_weight d T^T).
rewrite mxdot_trmx in S.
apply: le_trans (ler_wpM2l _ (ler_wpM2l c0 S)) _; first by rewrite invr_ge0.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by set u := (d%:R^-1)%R; clearbody u; field.
Qed.

(* For |v| <= 1, the quadratic form z |-> <z, mxvec (v^T v)> of the
   features, ((v x)^2 - |v|^2) / sqrt d, is subexponential with constant
   48 K^2 / sqrt d. Corollary 2.13 (ii) takes it as hypothesis on the
   features (uni_subexp_data of Unsat/Universality, fmt_subexp_data of
   Unsat/FourthMomentThree). *)
Lemma component_feature_quad_subexponential (v : 'rV[R]_d) :
  (0 < d)%N -> (mxdot v v <= 1)%R ->
  subexponential mu (fun z => mxdot z (mxvec (v^T *m v)) : RR)
    (48 * K ^+ 2 / Num.sqrt d%:R)%R.
Proof.
move=> d0 v1; rewrite /data_feature_law.
apply/subexponential_distribution; first exact: measurable_mxdotl.
have K0 : (0 < K)%R := @component_law_K _ _ (hnu 0 d0).
have sd : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
set X := fun t : d.-tuple (measurableTypeR R) =>
  (\sum_(b < d) v ord0 b * tnth t b)%R.
have -> : (mxdot (n:=d * d))^~ (mxvec (v^T *m v)) \o data_feature_map d =
    (fun t => (X t ^+ 2 - mxdot v v) / Num.sqrt d%:R)%R.
  apply/boolp.funext => t /=; rewrite data_feature_dot quad_formE.
  by rewrite quad_sum_outer trace_outer mulrC.
have mX : measurable_fun setT
    (fun t : d.-tuple (measurableTypeR R) => X t : RR).
  apply: measurable_sum => b; apply: measurable_funM => //.
  exact: measurable_tnth.
have [v0|v0] := eqVneq (mxdot v v) 0%R.
  have vb (b : 'I_d) : (v ord0 b = 0)%R.
    have := mxdot_entry v ord0 b; rewrite v0 => h.
    by apply/eqP; rewrite -sqrf_eq0 eq_le h sqr_ge0.
  have X0 t : X t = 0%R by rewrite /X big1 // => b _; rewrite vb mul0r.
  split; first by rewrite divr_gt0 // mulr_gt0 // exprn_gt0.
    apply: measurable_funM => //; apply: measurable_funB => //.
    exact: measurable_funX.
  under eq_integral do
    rewrite X0 expr0n /= v0 subrr mul0r normr0 mul0r expR0.
  by rewrite integral_cst // [X in _ * X]probability_setT mule1 lee_fin ler1n.
pose a := ord_fun (fun b : 'I_d => v ord0 b).
have aE (b : 'I_d) : a b = v ord0 b := ord_funE _ _ b.
have Sv : (\sum_(j < d) v ord0 j ^+ 2 = mxdot v v)%R.
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite expr2.
have S0' : (0 < \sum_(j < d) a j ^+ 2 * K ^+ 2)%R.
  under eq_bigr do rewrite aE.
  rewrite -mulr_suml Sv mulr_gt0 ?exprn_gt0 //.
  by rewrite lt_def v0 mxdot_ge0.
have sg : forall j, (j < d)%N ->
    subgaussian (nu j) (fun x : measurableTypeR R => (x : R)) K.
  by move=> j jd; exact: (@component_law_subgaussian _ _ (hnu j jd)).
have m0 : forall j, (j < d)%N ->
    (\int[nu j]_t (fun x : measurableTypeR R => (x : R)) t)%R = 0%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_mean _ _ (hnu j jd)).
have sX := subgaussian_sum (mu := nu) (n := d)
  (f := fun=> fun x : measurableTypeR R => (x : R)) (K := fun=> K) (a := a)
  sg m0 S0'.
have eX : (fun x : d.-tuple (measurableTypeR R) =>
    (\sum_(i < d) a i * tnth x i)%R) = X.
  by apply/boolp.funext => t; rewrite /X; apply: eq_bigr => i _; rewrite aE.
rewrite eX in sX.
have sC := subexponential_center (subexponential_sqr sX).
have EX2 : (\int[P]_s (X s ^+ 2))%R = mxdot v v.
  rewrite /Rintegral.
  under eq_integral do rewrite /X -quad_sum_outer.
  by rewrite (component_quad_sum_mean _ _ _ hnu) /= trace_outer.
rewrite EX2 in sC.
apply: subexponential_le (subexponential_scale _ _ _ _ _ _ sd sC) _.
apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
under eq_bigr do rewrite aE.
have m0' : (0 <= mxdot v v * K ^+ 2)%R.
  by rewrite mulr_ge0 ?mxdot_ge0 ?sqr_ge0.
rewrite -mulr_suml Sv exprMn (sqr_sqrtr m0').
have K2 : (0 <= K ^+ 2)%R := sqr_ge0 K.
by have := ler_wpM2r K2 v1; nra.
Qed.

(* Every quadratic form of the features, by the Hanson-Wright inequality
   (probability/hanson_wright.v): <W, A> = (x^T A x - tr A) / sqrt d is
   subexponential with constant L / sqrt d for every L >= 252 K^2 |A|_F
   (used by data_feature_hw of Sat/Apriori and sat_subexp of
   Sat/ApproximateFit). *)
Lemma component_feature_subexponential (A : 'M[R]_d) (L : R) :
  (0 < d)%N -> (0 < L)%R -> (252 * K ^+ 2 * frobenius A <= L)%R ->
  subexponential mu (fun z => mxdot z (mxvec A) : RR) (L / Num.sqrt d%:R)%R.
Proof.
move=> d0 L0 hL; rewrite /data_feature_law.
apply/subexponential_distribution; first exact: measurable_mxdotl.
have sd : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
have sg : forall j, (j < d)%N ->
    subgaussian (nu j) (fun x : measurableTypeR R => (x : R)) K.
  by move=> j jd; exact: (@component_law_subgaussian _ _ (hnu j jd)).
have m0 : forall j, (j < d)%N ->
    (\int[nu j]_t (fun x : measurableTypeR R => (x : R)) t)%R = 0%R.
  move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_mean _ _ (hnu j jd)).
have hw := @hanson_wright_subexponential _ _ RR nu d
  (fun=> fun x : measurableTypeR R => (x : R)) K sg m0 A L L0 hL.
have hc : hw_center nu (fun=> fun x : measurableTypeR R => (x : R)) A = \tr A.
  rewrite /hw_center /mxtrace; apply: eq_bigr => i _.
  rewrite /hw_sqmean /Rintegral (@component_law_second _ _ (hnu i (ltn_ord i))).
  by rewrite /= mulr1.
rewrite hc in hw.
have e : (fun z => mxdot z (mxvec A) : RR) \o data_feature_map d =
    (fun t => (hw_quad (fun=> fun x : measurableTypeR R => (x : R)) A t -
       \tr A) / Num.sqrt d%:R)%R.
  by apply/boolp.funext => t /=; rewrite data_feature_dot quad_formE mulrC.
by rewrite e; exact: subexponential_scale.
Qed.

(* The same with the constant 252 K^2 |A|_F / sqrt d itself, for
   A != 0. *)
Lemma component_feature_subexponential_frob (A : 'M[R]_d) :
  (0 < d)%N -> (A != 0)%R ->
  subexponential mu (fun z => mxdot z (mxvec A) : RR)
    (252 * K ^+ 2 * frobenius A / Num.sqrt d%:R)%R.
Proof.
move=> d0 A0; have K0 : (0 < K)%R := @component_law_K _ _ (hnu 0 d0).
apply: component_feature_subexponential => //.
by rewrite !mulr_gt0 ?exprn_gt0 ?frobenius_gt0 // ltr0n.
Qed.

(* The coordinates may have different fourth moments: kap j for the
   coordinate j. The features have the covariance matrix coord_cov kap d. *)
Variable kap : nat -> R.
Hypothesis hkap :
  forall j, (j < d)%N -> \int[nu j]_x ((x : R) ^+ 4)%:E = (kap j)%:E.

Lemma component_feature_cov (th th' : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th * mxdot z th')%R] =
  (mxdot (th *m coord_cov kap d) th')%:E.
Proof.
have mf : measurable_fun setT
    (fun z : 'rV[RR]_(d * d) => (mxdot z th * mxdot z th')%R : RR).
  by apply: measurable_funM; exact: measurable_mxdotl.
rewrite (component_feature_expectation _ mf).
transitivity (\int[P]_t ((d%:R^-1)%:E *
    (quad_form (vec_mx th) t * quad_form (vec_mx th') t)%:E)).
  apply: eq_integral => t _; rewrite !component_feature_dotE -EFinM; congr EFin.
  by rewrite mulrACA sqrt_inv_sqr.
rewrite (integralZl measurableT
  (component_integrable_quad_form2 _ _ _ hnu (vec_mx th) (vec_mx th'))).
by rewrite (component_quad_form_cov _ _ _ hnu _ hkap) -EFinM coord_covE.
Qed.

End component_feature.

Section data_feature.
Local Open Scope ereal_scope.
Variables (kappa K : R) (d : nat).
Variable nu : nat -> probability (measurableTypeR R) R.
Hypothesis hnu :
  forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j).
Let hnuc : forall j, (j < d)%N -> mixture_component_law K (nu j) :=
  fun j jd => coordinate_law_component kappa K (nu j) (hnu j jd).
Let hkapc : forall j, (j < d)%N -> \int[nu j]_x ((x : R) ^+ 4)%:E = kappa%:E :=
  fun j jd => @coordinate_law_fourth _ _ _ (hnu j jd).
Local Notation P := (tuple_prod nu d).
Local Notation mu := (data_feature_law nu d).

Lemma data_feature_expectation (f : 'rV[RR]_(d * d) -> RR) :
  measurable_fun setT f ->
  'E_mu[f] = \int[P]_t (f (data_feature_map d t))%:E.
Proof. first [exact: (component_feature_expectation K d nu hnuc) | exact: component_feature_expectation]. Qed.

Lemma data_feature_dotE (th : 'rV[R]_(d * d)) t :
  mxdot (data_feature_map d t) th =
  ((Num.sqrt d%:R)^-1 * quad_form (vec_mx th) t)%R.
Proof. first [exact: (component_feature_dotE K d nu hnuc) | exact: component_feature_dotE]. Qed.

(* Covariance matching: E <W, theta> = 0 and
   E <W, theta> <W, theta'> = theta C_kappa theta'^T. *)
Lemma data_feature_mean (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => mxdot z th] = 0.
Proof. first [exact: (component_feature_mean K d nu hnuc) | exact: component_feature_mean]. Qed.

Lemma data_feature_cov (th th' : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th * mxdot z th')%R] =
  (mxdot (th *m unsat_cov kappa d) th')%:E.
Proof.
by rewrite (component_feature_cov K d nu hnuc (fun=> kappa) hkapc) coord_cov_const.
Qed.

(* (F1) for the features: E <W, theta>^4 <= 9 2^33 K^8 |theta|^4 / d^2. *)
Lemma feature_dot_moment4 (th : 'rV[R]_(d * d)) :
  \int[P]_t (mxdot (data_feature_map d t) th ^+ 4)%:E <=
  (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2)%:E.
Proof. first [exact: (component_feature_dot_moment4 K d nu hnuc) | exact: component_feature_dot_moment4]. Qed.

Lemma data_feature_fourth (th : 'rV[R]_(d * d)) :
  'E_mu[fun z => (mxdot z th ^+ 4)%R] <=
  (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 * mxdot th th ^+ 2)%:E.
Proof. first [exact: (component_feature_fourth K d nu hnuc) | exact: component_feature_fourth]. Qed.

(* The same with a square: E <W, theta>^4 <= (2^19 K^4 |theta|^2 / d)^2. *)
Lemma feature_dot_moment4_sqr (th : 'rV[R]_(d * d)) :
  \int[P]_t ((mxdot (data_feature_map d t) th ^+ 2) ^+ 2)%:E <=
  ((2 ^+ 19 * K ^+ 4 / d%:R * mxdot th th) ^+ 2)%:E.
Proof. first [exact: (component_feature_dot_moment4_sqr K d nu hnuc) | exact: component_feature_dot_moment4_sqr]. Qed.


(* The fourth moment of the part of W M in the row and the column j:
   E |rc_j (W M)|^4 <= (2^19 K^4 rc_weight j M / d)^2. *)
Lemma proj_feature_moment4 (M : 'M[R]_(d * d)) (j : 'I_d) :
  \int[P]_t (mxdot (rc_proj j (vec_mx (data_feature_map d t *m M)))
                   (rc_proj j (vec_mx (data_feature_map d t *m M))) ^+ 2)%:E
  <= ((2 ^+ 19 * K ^+ 4 / d%:R * rc_weight j M) ^+ 2)%:E.
Proof. first [exact: (component_proj_feature_moment4 K d nu hnuc) | exact: component_proj_feature_moment4]. Qed.

(* E |W - W^(j)|_F^4 <= 2^20 K^8, x^(j) the point x with its coordinate j
   resampled. *)
Lemma feature_diff_moment4 (j : 'I_d) :
  \int[P \x nu j]_p
    (mxdot (data_feature_map d p.1 - data_feature_map d (tuple_set p.1 j p.2))
           (data_feature_map d p.1 - data_feature_map d (tuple_set p.1 j p.2))
     ^+ 2)%:E <= (2 ^+ 20 * K ^+ 8)%:E.
Proof. first [exact: (component_feature_diff_moment4 K d nu hnuc) | exact: component_feature_diff_moment4]. Qed.

(* Resampling the coordinate j changes F (x) = z T z^T, z the feature of x,
   by at most 2^30 K^8 (rc_weight j T + rc_weight j T^T) / d in mean
   square. *)
Lemma quad_stat_resample2 (T : 'M[R]_(d * d)) (j : 'I_d) :
  \int[P]_t \int[nu j]_s
    ((mxdot (data_feature_map d t) (data_feature_map d t *m T) -
      mxdot (data_feature_map d (tuple_set t j s))
            (data_feature_map d (tuple_set t j s) *m T)) ^+ 2)%:E <=
  (2 ^+ 30 * K ^+ 8 / d%:R * (rc_weight j T + rc_weight j T^T))%:E.
Proof. first [exact: (component_quad_stat_resample2 K d nu hnuc) | exact: component_quad_stat_resample2]. Qed.

Lemma integrable_quad_stat (T : 'M[R]_(d * d)) :
  P.-integrable setT (fun t =>
    (mxdot (data_feature_map d t) (data_feature_map d t *m T))%:E).
Proof. first [exact: (component_integrable_quad_stat K d nu hnuc) | exact: component_integrable_quad_stat]. Qed.

(* (F2) for the features: Var (z T z^T) <= 2^31 K^8 |T|_F^2 / d. *)
Lemma data_feature_variance (T : 'M[R]_(d * d)) :
  'V_mu[fun z => mxdot z (z *m T)] <= (2 ^+ 31 * K ^+ 8 / d%:R * mxdot T T)%:E.
Proof. first [exact: (component_feature_variance K d nu hnuc) | exact: component_feature_variance]. Qed.

(* Proposition 2.6: for kappa > 1, the law of the quadratic features is a
   regular feature with covariance C_kappa, K_feat = 2^10 K^2 /
   sqrt (kappa - 1) and tau = sqrt (2^31 K^8 / d), of order 1 / sqrt d. *)
Theorem data_feature_regular : (1 < kappa)%R -> (0 < d)%N ->
  regular_feature (2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1))%R
    (Num.sqrt (2 ^+ 31 * K ^+ 8 / d%:R))%R (unsat_cov kappa d) mu.
Proof.
move=> k1 d0.
have kp : (0 < kappa - 1)%R by rewrite subr_gt0.
have dp : (0 < d%:R :> R)%R by rewrite ltr0n.
have lam := unsat_cov_opnorm_ge kappa d d0.
have lam0 : (0 < (kappa - 1) / d%:R)%R by rewrite divr_gt0.
split.
- exact: lt_le_trans lam0 lam.
- move=> th; apply: le_trans (data_feature_fourth th) _; rewrite lee_fin.
  have K8 : (0 <= K ^+ 8)%R := exprn8_ge0 K.
  have t2 : (0 <= mxdot th th ^+ 2)%R by exact: sqr_ge0.
  have e : ((2 ^+ 10 * K ^+ 2 / Num.sqrt (kappa - 1)) ^+ 4 =
      2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2)%R.
    have s4 : (Num.sqrt (kappa - 1) ^+ 4 = (kappa - 1) ^+ 2)%R.
      by rewrite -[4%N]/(2 * 2)%N exprM sqr_sqrtr // ltW.
    by rewrite expr_div_n s4; ring.
  rewrite e; set L := opnorm _.
  have l2 : ((kappa - 1) ^+ 2 / d%:R ^+ 2 <= L ^+ 2)%R.
    rewrite -expr_div_n ler_pXn2r // nnegrE ?(ltW lam0) //.
    exact: ltW (lt_le_trans lam0 lam).
  have kn : (kappa - 1 != 0)%R by rewrite gt_eqF.
  have dn : (d%:R != 0 :> R)%R by rewrite gt_eqF.
  have X : (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 <=
      2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2 * L ^+ 2)%R.
    apply: le_trans (_ : _ <= 2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2 *
      ((kappa - 1) ^+ 2 / d%:R ^+ 2))%R _.
      have -> : (2 ^+ 40 * K ^+ 8 / (kappa - 1) ^+ 2 *
          ((kappa - 1) ^+ 2 / d%:R ^+ 2) =
          2 ^+ 40 * (K ^+ 8 / d%:R ^+ 2))%R by field.
      have k0 : (0 <= K ^+ 8 / d%:R ^+ 2)%R.
        by rewrite divr_ge0 // exprn_ge0 // ltW.
      have -> : (9 * 2 ^+ 33 * K ^+ 8 / d%:R ^+ 2 =
          9 * 2 ^+ 33 * (K ^+ 8 / d%:R ^+ 2))%R by ring.
      by apply: ler_wpM2r => //; lra.
    apply: ler_wpM2l => //.
    apply: divr_ge0; first by rewrite mulr_ge0 // exprn_ge0.
    by rewrite exprn_ge0 // ltW.
  by apply: ler_wpM2r.
- exact: data_feature_mean.
- exact: data_feature_cov.
move=> T _; apply: le_trans (data_feature_variance T) _.
rewrite sqr_sqrtr ?frobenius_sqr //.
apply: divr_ge0; last exact: ler0n.
by apply: mulr_ge0; [exact: exprn_ge0 | exact: exprn8_ge0].
Qed.

(* For |v| <= 1, the quadratic form z |-> <z, mxvec (v^T v)> of the
   features, ((v x)^2 - |v|^2) / sqrt d, is subexponential with constant
   48 K^2 / sqrt d. Corollary 2.13 (ii) takes it as hypothesis on the
   features (uni_subexp_data of Unsat/Universality, fmt_subexp_data of
   Unsat/FourthMomentThree). *)
Lemma data_feature_quad_subexponential (v : 'rV[R]_d) :
  (0 < d)%N -> (mxdot v v <= 1)%R ->
  subexponential mu (fun z => mxdot z (mxvec (v^T *m v)) : RR)
    (48 * K ^+ 2 / Num.sqrt d%:R)%R.
Proof. first [exact: (component_feature_quad_subexponential K d nu hnuc) | exact: component_feature_quad_subexponential]. Qed.

(* Every quadratic form of the features, by the Hanson-Wright inequality
   (probability/hanson_wright.v): <W, A> = (x^T A x - tr A) / sqrt d is
   subexponential with constant L / sqrt d for every L >= 252 K^2 |A|_F
   (used by data_feature_hw of Sat/Apriori and sat_subexp of
   Sat/ApproximateFit). *)
Lemma data_feature_subexponential (A : 'M[R]_d) (L : R) :
  (0 < d)%N -> (0 < L)%R -> (252 * K ^+ 2 * frobenius A <= L)%R ->
  subexponential mu (fun z => mxdot z (mxvec A) : RR) (L / Num.sqrt d%:R)%R.
Proof. first [exact: (component_feature_subexponential K d nu hnuc) | exact: component_feature_subexponential]. Qed.

(* The same with the constant 252 K^2 |A|_F / sqrt d itself, for
   A != 0. *)
Lemma data_feature_subexponential_frob (A : 'M[R]_d) :
  (0 < d)%N -> (A != 0)%R ->
  subexponential mu (fun z => mxdot z (mxvec A) : RR)
    (252 * K ^+ 2 * frobenius A / Num.sqrt d%:R)%R.
Proof. first [exact: (component_feature_subexponential_frob K d nu hnuc) | exact: component_feature_subexponential_frob]. Qed.

(* The same for the Gaussian feature: constant 4 sqrt (kappa + 1) / sqrt d
   (uni_subexp_gauss of Unsat/Universality, fmt_subexp_gauss of
   Unsat/FourthMomentThree). *)
Lemma gaussian_feature_quad_subexponential (v : 'rV[R]_d) :
  (1 <= kappa)%R -> (0 < d)%N -> (mxdot v v <= 1)%R ->
  subexponential (gaussian_feature_law kappa d)
    (fun z => mxdot z (mxvec (v^T *m v)) : RR)
    (4 * Num.sqrt (kappa + 1) / Num.sqrt d%:R)%R.
Proof.
move=> k1 d0 v1; rewrite /gaussian_feature_law.
apply/subexponential_distribution; first exact: measurable_mxdotl.
set S := gaussian_feature_mx kappa d; set th := mxvec (v^T *m v).
set a := th *m S^T.
have -> : (mxdot (n:=d * d))^~ th \o gaussian_feature_vec kappa d =
    (fun g => mxdot g a).
  by apply/boolp.funext => g /=; rewrite /gaussian_feature_vec mxdot_mulmxr.
have sd : (0 < Num.sqrt d%:R :> R)%R by rewrite sqrtr_gt0 ltr0n.
have k0 : (0 < kappa + 1)%R by apply: lt_le_trans (_ : 0 < 1)%R _ => //; lra.
have Vs : v^T *m v \is symmetricmx.
  by apply/symmetricmxP; rewrite trmx_mul trmxK.
have VV : (mxdot (v^T *m v) (v^T *m v) <= 1)%R.
  have -> : (mxdot (v^T *m v) (v^T *m v) = mxdot v v ^+ 2)%R.
    rewrite /mxdot big_ord1 expr2 mulr_suml; apply: eq_bigr => i _.
    rewrite mulr_sumr; apply: eq_bigr => j _; rewrite !mxE !big_ord1 !mxE.
    by ring.
  by rewrite expr_le1 // mxdot_ge0.
have a2 : (mxdot a a <= (kappa + 1) / d%:R)%R.
  have -> : mxdot a a = unsat_cov_form kappa d (v^T *m v) (v^T *m v).
    rewrite /a mxdot_mulmxr trmxK -mulmxA (gaussian_feature_mx_cov _ _ k1).
    by rewrite mxdotC unsat_covE /th mxvecK.
  apply: le_trans (unsat_cov_form_le _ _ _ k1 Vs) _.
  rewrite -[X in (_ <= X)%R]mulr1; apply: ler_wpM2l => //.
  by rewrite divr_ge0 ?ler0n // ltW.
have L0 : (0 < 4 * Num.sqrt (kappa + 1) / Num.sqrt d%:R)%R.
  by rewrite divr_gt0 // mulr_gt0 // sqrtr_gt0.
have [a0|a0] := eqVneq a 0%R.
  split => //; first exact: measurable_mxdot.
  under eq_integral do rewrite a0 mxdot0r normr0 mul0r expR0.
  by rewrite integral_cst // [X in _ * X]probability_setT mule1 lee_fin ler1n.
apply: (subexponential_le _ _ _ _ _ _ (gauss_mxdot_subexponential _ _ a0)).
rewrite -mulrA; apply: ler_wpM2l => //.
have -> : (Num.sqrt (kappa + 1) / Num.sqrt d%:R =
    Num.sqrt ((kappa + 1) / d%:R))%R.
  by rewrite sqrtrM ?sqrtrV ?ler0n // ltW.
rewrite /frobenius ler_sqrt //.
by rewrite divr_ge0 ?ler0n // ltW.
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
