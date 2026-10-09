# Universality and finite mixtures of product laws

This directory, under the logical root `EllipsoidUniversality`, holds
three theorems beyond the three theorems of Misiakiewicz and Wen for
Gaussian points.

- **The finite-mixture theorem**, the main result of phase 6:
  `mixture_theorem : mixture_theorem_statement` (`MixtureTheorem.v`).
  Both phases of Theorem 1.2 of F. Koehler and Y. Sohn, *Universality and
  sharp thresholds for ellipsoid fitting* (arXiv 2608.27372 v1), and its
  small-residual interpolation (Theorem 1.9), for i.i.d. points whose law
  is, at each dimension d, a finite mixture of product laws, with a number
  of components that may grow with d, under (M1)-(M3): in every component
  the coordinates are independent, of mean 0, variance 1 and subgaussian
  norm at most K, and every coordinate has the same unconditional fourth
  moment kappa > 1 under the mixture. No matching theorem was found in a
  targeted literature search; priority is not confirmed. Section (f).
- **Its corollaries.** `paired_theorem : paired_statement`
  (`PairedTheorem.v`): exact fitting for the paired law, whose
  coordinates come in dependent pairs, over the whole range
  -1 <= eps <= 7/3, with constants uniform in eps. Phase 7 adds the
  latent-sign law, (1/2) lambda_s^(x)d + (1/2) lambda_-s^(x)d with
  0 <= s <= 1, in which one hidden sign couples all the coordinates of a
  point (`LatentSignStatement.v`).
- **The universality theorem** of Koehler and Sohn, for points with
  independent coordinates: `universality_theorem : universality_statement`
  (`UniversalityTheorem.v`), proved in phase 5. The finite-mixture theorem
  contains it, with one component (`Mixture/OneComponent.v`).

Sections (a) to (e) are the feasibility study written before phase 5, for
extending the formal result of this repository to Theorem 1.2 of Koehler
and Sohn. It had two deliverables:

1. this plan;
2. the formal statement of the theorem, in `UniversalityDefinitions.v`
   (definitions only) and `UniversalityStatement.v` (one `Prop`), under the
   logical root `EllipsoidUniversality`, compiled against the library and
   the frozen definitions. Phase 5 proved it (`UniversalityTheorem.v`).

**How claims are cited.** Lines "l." refer to the paper's LaTeX source
`arxiv_v1.tex` (6953 lines). The paper numbers its results with one counter
per section shared by all environments (`\newtheorem{...}[theorem]`,
l.20-39), so Theorem 1.2 is `thm:phase-transition` (l.164), Proposition 1.4
is `thm:gaussian-master` (l.323), Theorem 1.7 is
`thm:intro-approx-tensorization-squared-loss` (l.447) and Theorem 1.9 is
`thm:small-residual-interpolation` (l.549); the same convention gives the
numbers of sections 2 to 5 and of appendix A below. Code is cited as
`Module.declaration` (`File.v:line`) at commit `3998195` of `main`, the
base of the branch `extension/feasibility`; `library:dir.file` is a library
file. Everything cited was read in the sources; claims that were not
checked are marked **unverified**. The classification of the Gaussian
parts of the existing proof follows section (e) of
`doc/paper_correspondence.md` where that document is cited.

Sections: (a) the theorem; (b) the proof, component by component, with the
categories *exists*, *new general library* and *new paper-specific work*,
the dependencies and the critical path; (c) the staged plan, starting with
the examination of the first milestone; (d) the rules of the repository
that the extension would need to change; (e) the formal statement and the
choices made in it; (f) phase 6, the theorem for finite mixtures of product
laws and its corollary for the paired law.

---

## (a) The theorem of Koehler and Sohn

### The model

Points x_1, ..., x_n in R^d, i.i.d., such that x_1 = (x_1j)_{j<=d} has
independent coordinates with

    E x_1j = 0,   E x_1j^2 = 1,   E x_1j^4 = kappa,   sup_j ||x_1j||_{psi_2} <= K_x

(`eq:independent:coordinate:distribution:assumption`, l.167-170), where
kappa > 1 and K_x > 0 do not depend on n and d (l.171), and n, d -> oo with
n/d^2 -> alpha in (0, oo) (l.171-172). The subgaussian norm is
||Z||_{psi_2} = inf {t > 0 : E exp(Z^2/t^2) <= 2} (l.160-163). The laws of
the coordinates may differ with j and with d; only kappa and K_x are fixed.
The paper notes that kappa = 1 forces x in {-1, 1}^d, where S = I/d fits
every sample, so kappa > 1 is the nondegenerate range (l.223), and that
centered Bernoulli coordinates are covered (l.225).

An ellipsoid fit is R >= 0 with x_i^T R x_i = 1 for all i (l.98-104). The
quadratic features are W_i = (x_i x_i^T - I_d)/sqrt d, the linear map
L_X(R) = (<W_i, R>)_i on symmetric matrices with the Frobenius product
(`eq:definition:L`, l.252-255), and A_X = P_{1^perp} L_X, with P_{1^perp}
the projection that subtracts the empirical mean (l.256-264). The optimal
squared fitting error is

    Gamma_X = inf_{R >= 0, Tr R = d} inf_{r >= 0} (1/n) sum_i (x_i^T R x_i / sqrt d - r)^2
            = inf_{R >= 0, Tr R = d} (1/n) ||A_X R||_2^2

(`eq:thm:least:squares`, l.183-187, and l.258-264). Gamma_X = 0 attained
at r > 0 gives a fit S = R/(r sqrt d); Gamma_X > 0 rules out a fit (l.215).

The covariance of the features depends on the law only through kappa:
E <W_i, A> <W_i, B> = (1/d)(2 <A, B> + (kappa - 3) <diag A, diag B>) =:
C_kappa(A, B) (`eq:C-kappa-trace`, l.268-280); Sigma_kappa is the
corresponding operator on symmetric matrices (l.678-683). The Gaussian
model replaces the W_i by independent symmetric Gaussian matrices G_i with
independent upper-triangular entries, (G_1)_jj ~ N(0, (kappa-1)/d) and
(G_1)_jl ~ N(0, 1/d) for j < l (`eq:def:gaussian:features`, l.281-290),
which have covariance C_kappa; L_{G,kappa}, A_{G,kappa} and
Gamma_{G,kappa} are defined as for the data (l.293-303). At kappa = 3 the
G_i are GOE matrices and the threshold d^2/4 is the statistical dimension
of the positive semidefinite cone (l.304-320).

### The threshold alpha*(kappa) and the error e*(alpha, kappa) (l.343-404)

nu is the semicircle law on [-sqrt 2, sqrt 2], d nu(x) = (1/pi)
sqrt(2 - x^2) 1_{|x| <= sqrt 2} dx (l.345-349), normalized so that
int x^2 d nu = 1/2 (l.5123-5125). For omega < sqrt 2,

    s(omega) = int (x - omega)_+^2 d nu(x),    m(omega) = int (x - omega)_+ d nu(x)

(l.350-353), and E_kappa(omega) = s(omega) + ((kappa - 3)/2) m(omega)^2
(l.357-361). Then

    alpha*(kappa) = E_kappa(omega_kappa),   omega_kappa in [-sqrt 2, sqrt 2] the unique solution of
    omega_kappa = ((kappa - 3)/2) m(omega_kappa)

(`eq:alpha-star-scalar-main`, l.364-377); for kappa = 3, omega_3 = 0 and
alpha*(3) = s(0) = 1/4 (l.377). The paper also proves the variational
representation

    alpha*(kappa) = sup { (int x f d nu)^2 / (int f^2 d nu + (kappa-3)/2) : f in L^2(nu), f >= 0, int f d nu = 1 }

(`eq:alpha-star-def`, l.380-389), which Theorem 1.2 cites as the
definition (l.173), and alpha*(kappa) -> 1/2 as kappa -> 1 (l.392). The
limiting error is

    e*(alpha, kappa) = (2/alpha) ( ((kappa-3)/2) m(omega_{alpha,kappa}) - omega_{alpha,kappa} )_+^2,
    omega_{alpha,kappa} < sqrt 2 the unique solution of E_kappa(omega) = alpha

(`eq:optimal-fitting-error-main`, l.394-404). Existence and uniqueness of
both solutions, alpha*(kappa) in [0, 1/2], the equality of the two
definitions of alpha*(kappa) and the equivalence e* > 0 iff alpha > alpha*
are Proposition 5.10 (l.5312-5349). The transition is second order:
e*(alpha, kappa) = (alpha - alpha*)^2 / (2 alpha* m(omega_kappa)^2) +
o((alpha - alpha*)^2) (Remark 1.6, l.416-429; Lemma 5.12, l.5782-5794).

### The statements

**Theorem 1.2** (l.164-190). Under the model above, with n/d^2 -> alpha:
(i) if alpha < alpha*(kappa), then with probability tending to one there is
R > 0 with x_i^T R x_i = 1 for all i (l.176-179), and R can be chosen with
lambda_max(R)/lambda_min(R) = O(1) (l.180); (ii) if alpha > alpha*(kappa),
then with probability tending to one there is no R >= 0 with x_i^T R x_i =
1 for all i, and Gamma_X -> e*(alpha, kappa) in probability (l.181-187);
e*(alpha, kappa) > 0 for alpha > alpha*(kappa), so no approximate fit with
R >= 0 and Tr R = d exists (l.188). Corollary 1.3 (l.192-194): the Gaussian
conjecture holds, since alpha*(3) = 1/4.

**Proposition 1.4** (l.323-342), the Gaussian model. Fix kappa > 1 and
n/d^2 -> alpha in (0, oo). (i) If alpha < alpha*(kappa), there are
constants 0 < m < M depending only on alpha and kappa such that with
probability tending to one some R satisfies m I <= R <= M I, Tr R = d and
A_{G,kappa} R = 0 (l.327-336). (ii) Gamma_{G,kappa} -> e*(alpha, kappa) in
probability; if alpha > alpha*(kappa) then e*(alpha, kappa) > 0 and
P(Gamma_{G,kappa} >= c_0) -> 1 for some c_0(alpha, kappa) > 0 (l.338-340).

**Theorem 1.7** (l.447-467), universality of the error. x_1, ..., x_n
i.i.d. with E x_1 = 0, Cov(x_1) = I_d, feature covariance C_kappa for a
fixed kappa > 1 (l.450-458), approximate tensorization of variance with a
dimension-free constant C, that is Var f(x_1) <= C sum_j E Var(f(x_1) |
x_{1,-j}) for every f with finite variance
(`eq:approximate-variance-tensorization`, l.436-442), and sup_j E |x_1j|^8
<= M (l.461). If n/d^2 -> alpha, then Gamma_X -> e*(alpha, kappa) in
probability (l.463-466). Independent coordinates give the tensorization
with C = 1 by Efron-Stein (l.443, l.1623-1625).

**Theorem 1.9** (l.549-566), small-residual interpolation. Under the model
of Theorem 1.2 with n/d^2 -> alpha in (0, 1/2), there is C depending only
on alpha and K_x such that with probability tending to one, every y in
Ran(A_X) has Delta_y symmetric with A_X Delta_y = y and ||Delta_y||_op <=
C (||y||_2 / d + (log d)^4 ||y||_oo / sqrt d). The range alpha < 1/2 is
the optimal one and is needed because alpha*(kappa) -> 1/2 as kappa -> 1
(l.898-903).

---

## (b) The proof, component by component

Categories. *Exists*: a result of `library/` or `theories/` serves as is
or after the stated generalization. *New general library*: a result
stated in the form the library would state it, over `R : realType`. *New
paper-specific*: work tied to the ellipsoid problem, in a new directory
of `theories/` or in `extension/`. Line estimates are lines of Rocq, by
comparison with the sizes of the corresponding parts of the existing
development (for instance the Gaussian hybrid comparison, `Hybrid/`,
`Loss/`, `Projection/`, is 8,074 lines; `library/probability/lindeberg.v`
is 287 lines; `Head/SmallBall*` is 2,406 lines). They are rough:
take them as plus or minus fifty percent, and more for the items marked
*hard*.

### The architecture of the paper's proof (section 2, l.694-706)

Both phases go through the Gaussian model: Proposition 1.4 is proved in
section 5 by the convex Gaussian min-max theorem and the semicircle law.
The unsatisfiable phase transfers Gamma_{G,kappa} to Gamma_X by a
Lindeberg argument on a ridge- and barrier-regularized least squares
problem (Theorem 2.9, Corollary 2.13). The satisfiable phase builds an
approximate well-conditioned fit from the same universality (Proposition
2.1) and makes it exact by a uniform interpolation estimate (Theorem 1.9),
whose heart is a nuclear-norm lower bound (Theorem 2.3) proved with a
vector anti-concentration inequality (Proposition 2.4).

The existing formal proof has a different architecture for the
unsatisfiable phase (a bounded loss, a soft minimum over a finite prior, a
head/bulk split in a net of orientations, and a Gaussian hybrid model;
`Unsat/`, `Orientation/`, `Hybrid/`, `Loss/`, `Projection/`,
`Projected/`) and for the satisfiable phase (widths, Gordon's inequality,
a dual kernel element; `Head/`, `Gordon/`, `Cone/`). Section (c) says
which parts carry over.

### Unsatisfiable phase

| # | Component (paper) | What the proof uses | Category | Formal counterpart, or the statement to add | Lines |
|---|---|---|---|---|---|
| U1 | Regular features, Definition 2.5 (l.1067-1086): (F1) ||<Z, theta>||_{L^4}^2 <= K^2 lambda_Sigma ||theta||^2, (F2) Var(Z^T T Z) <= tau^2 ||T||_F^2 | definitions | new general library | the predicate on a probability on `'rV[R]_N` | 100 |
| U2 | Proposition 2.6 (l.1117-1134; proof l.4233-4438): the quadratic feature of x with approximate tensorization and eighth moments is (C, C d^{-1/2})-regular | Efron-Stein / approximate tensorization (l.4241-4248), an L^p recursion for p = 2, 4, 8 by Young's inequality (l.4249-4323), Hoelder, Minkowski | new general library: Efron-Stein inequality for `tuple_prod` and the L^p moment bounds from it (Poincare to L^p, l.4231); new paper-specific: (F1), (F2) for W = (x x^T - I)/sqrt d (l.4326-4437) | the Gaussian case exists in part: `Projection.Variance.paper_main_projection_quadratic_variance` (Variance.v:51) gives Var(x^T A x - Tr A) = 2 ||A||_F^2 for Gaussian x, and `Gaussian.Orthogonal.HansonWright.paper_main_gaussian_quadratic_tail` (HansonWright.v:57) the Gaussian tail | 1,200 + 1,200 |
| U3 | Subgaussian toolkit (cited: Vershynin Theorems 3.1.1, 4.4.5, 6.2.1, Proposition 2.7.1; l.2179-2184, l.2226-2228, l.2255-2258) | MGF bound from the psi_2 norm, sums of independent subgaussians, squares are subexponential, Bernstein's inequality, norm concentration, operator norm of a matrix with subgaussian entries | new general library | the library has the Gaussian cases only: `library:comparison.normal_mgf.measure_ge_expR` (normal_mgf.v:40, Chernoff), `gauss_mxdot_abs_tail`, `library:comparison.chi_square.gauss_centered_chi2_abs_tail` (chi_square.v:351), `library:comparison.escape.gauss_opnorm_tail` (escape.v:847), `Gaussian.Tail.Operator.paper_main_gaussian_operator_tail` (Operator.v:74) | 2,000 |
| U4 | Self-concordant barriers, Definition 2.7 (l.1150-1179), Lemma 2.15 (l.1899-1927), Lemma 2.10 (l.1359-1368) | the ODE comparison for phi'' along a segment (l.1930-1941), the bounds omega(r) <= D_B <= omega*(r) (l.1944-1955), the gradient bound D Psi(z)[y - z] <= vartheta (l.1370-1379, cited Nesterov Theorem 4.2.4) | new general library | nothing exists | 1,200 |
| U5 | Lemma 2.8 (l.1215-1237): -log det is a d-self-concordant barrier on the trace-d slice of the positive definite cone, and the two-sided barrier B_{m,M} is 2d-self-concordant (cited Nesterov-Nemirovskii Propositions 5.4.5 and 2.3.1) | derivatives of log det along a line (l.1260-1278): with V = R^{-1/2} U R^{-1/2}, D^2 = ||V||_F^2, D^3 = -2 Tr V^3, and \|Tr V\| <= sqrt d ||V||_F | new general library: matrix calculus of log det on positive definite matrices; the spectral theorem reduces it to scalar calculus of t |-> -sum_i log(1 + t lambda_i) | exists: `library:matrix.real_spectral.symmetric_spectral` (real_spectral.v:295), `spectral_psd` (:410); MathComp's `\det`, `invmx` | 1,300 |
| U6 | Theorem 2.9 (l.1282-1344; proof l.1637-2116): barrier-regularized universality, E Phi_W - E Phi_G and the variance bound | leave-one-out optimizer and Hessian (l.1690-1758), the exact insertion formula r^2/(2(n + l)) (l.1869-1878), Proposition 2.14 (l.1796-1820, proof l.4037-4156), Lemma 4.1 (l.3838-3875), Lemma 4.2 (l.3940-3966), Proposition 2.16 (l.1984-2007, proof l.4161-4223), the telescoping over rows (l.1736-1743), Efron-Stein for the variance (l.2081-2113), Chebyshev (exists: `chebyshev`, MathComp-Analysis random_variable.v:1051) | new general library, in the paper's abstract feature form (features in R^N, any bounded relatively open convex domain with a vartheta-self-concordant barrier) | exists after generalization: `library:probability.lindeberg.lindeberg_replacement` (lindeberg.v:230) does the telescoping for a bounded measurable F with per-coordinate bounds uniform in the other coordinates; Theorem 2.9 needs F integrable (Phi is unbounded) with per-row bounds that depend integrably on the other rows (l.2056-2076), and the conditional expectations E_i of l.1667-1675, which are the Fubini forms `Rintegral_tuple_prodS` (lindeberg.v:197) and `Rintegral_tuple_prodS'` (:209). Convex analysis (existence and uniqueness of the minimizer of a strongly convex objective with a barrier on a relatively open bounded convex set, first-order condition, Taylor's formula with the Bregman remainder, l.1835-1867) does not exist in MathComp-Analysis 1.16 or in the repository, except the compactness lemmas of `Cone/` and `library:matrix.real_spectral.compact_unit_sphere` (real_spectral.v:134) | 6,000 |
| U7 | Lemma 2.11 (l.1386-1405) and `eq:general-barrier-removal-comparison` (l.1428-1441): removing the barrier costs eps F_Z(theta_ref) + gamma B(theta_ref) + gamma vartheta log(1/eps) | convexity of F_Z, Lemma 2.10 | new general library | nothing exists | 400 |
| U8 | Lemma 2.12 (l.1476-1494; proof l.4684-4832): removing the ridge, 0 <= Phi_Z(R_d^o; beta) - Phi_Z(R_d^o) <= C beta log d | the small-ball method (cited Koltchinskii-Mendelson Theorem 2.1, l.4764-4779), Rademacher complexity (l.4749-4762), Paley-Zygmund (l.4739-4747), Lemma 4.3 (l.4604-4615, matrix Bernstein cited at l.4653), Chebyshev (l.4792-4799) | new general library: symmetrization, the small-ball method for pointwise separable classes (bounded differences for the supremum of an empirical process, Paley-Zygmund); Lemma 4.3 is provable without matrix Bernstein by the net bound of `library:matrix.nets.opnorm_net_sym` (nets.v:177) and a scalar Bernstein inequality for the subexponential variables ((u^T x)^2 - 1)/sqrt d (U3) | exists: `library:probability.moments.paley_zygmund` (moments.v:87), `paley_zygmund_sqr` (:134); the nets | 3,900 |
| U9 | Corollary 2.13 (l.1499-1531; proof l.1533-1601): universality of Phi_W(D_d; beta_d) with rate (1 + beta_d^{-1})^2 (tau_d + (log d/d)^{1/3}), and Phi_W(R_d^o) - Phi_G(R_d^o) -> 0 in probability | U5-U8, the reference point (I_d, 0) (l.1537-1545), the choice gamma = d^{-4/3} (log d)^{-2/3} (l.1546-1551), beta_d = (q_d / log d)^{1/3} (l.1590) | new paper-specific | the relations Phi_{W(X)}(R_d^o) = Phi_{W(X)}(R_d) = Gamma_X/2 (`eq:unregularized-affine-energy-value`, l.1054-1058) need the density of R_d^o in R_d and the continuity of the objective; the formal proof has the matrix side of Tr R = d normalizations in `Geometry.Homogeneous.paper_main_homogeneous_witness` (Homogeneous.v:162) and `Projection.PinchingLoss.paper_main_fit_unit_witness` (PinchingLoss.v:16) | 1,200 |
| U10 | Proofs of Theorem 1.7 and Theorem 1.2 (ii) (l.1602-1635) | U2, U9, Proposition 1.4 (ii), Gamma_X = 0 for a fit | new paper-specific | the fit-to-Gamma direction is elementary; the fixed-density reductions `Fixed.Density.paper_main_unsat_from_fixed` (Density.v:232) are stated for limsup/liminf and for `gaussian_product_law`; a convergence form over `universality_sample_law` is needed, with a product-law version of `Gaussian.Sample.Deletion.paper_main_drop_points_law` (Deletion.v:117) if trimming is kept | 1,000 |
| U11 | Measurability of the events of the statement | countable rational approximation, as `Measurability.Fit.pm_fit_event_measurable` (Fit.v:372) | exists for the fit event (law-independent); new paper-specific for `universality_pd_fit_event`, `universality_conditioned_fit_event`, `universality_error_event` | `Measurability/` (1,533 lines) is the model | 800 |
| U12 | The product law of the data and its bookkeeping | `tuple_prod` and its Fubini lemmas | exists: `library:probability.lindeberg.tuple_prod` (lindeberg.v:49); new: the reshaping between the flat law on `(N*d).-tuple` and the law of N rows on `N.-tuple (d.-tuple T)`, the marginal of a block of coordinates, the independence of disjoint blocks | the Gaussian versions are `Gaussian.Law.LibraryBridge.gauss_gaussian_product_law` (LibraryBridge.v:101), `Hybrid.FiniteArray.paper_main_hybrid_finite_split_law` (FiniteArray.v:364), `Head.Law.paper_main_split_coordinates_section_bound` (Law.v:183) | 1,100 |

### Gaussian model (section 5, l.4834-6220)

| # | Component (paper) | What the proof uses | Category | Formal counterpart, or the statement to add | Lines |
|---|---|---|---|---|---|
| G1 | The cones S^d_kappa = T_kappa(S^d_+), T_kappa R = R_off + sqrt((kappa-1)/2) R_diag, and C_kappa(R, S) = (2/d) <T_kappa R, T_kappa S> (l.4848-4870); Lemma 5.2, the involution kappa -> 1 + 4/(kappa - 1) and the dual cones (l.4934-4950) | self-duality of the positive semidefinite cone | new paper-specific | the positive semidefinite cone and its duality exist in `Cone/` and `Geometry/` (`Geometry.Separation.paper_main_fit_alternative`, Separation.v:380, is the separation that the formal proof uses) | 800 |
| G2 | Lemma 5.1, Moreau's decomposition for a closed convex cone (l.4894-4921; cited Bauschke-Combettes) | nearest-point projection | exists for the positive semidefinite cone only: `Cone.Projection.paper_main_psd_moreau` (Projection.v:229), `paper_main_psd_moreau_norm` (:290); new general library for a closed convex cone of `'rV[R]_N` (projection onto a closed convex set, the polar cone, `eq:cone-projection-support`) | 1,200 |
| G3 | Theorem 5.3, the convex Gaussian min-max theorem (l.4972-4990; cited Thrampoulidis-Oymak-Hassibi Theorem 3 (i)-(ii)): P(Phi(K) < c) <= 2 P(phi(K) <= c) and P(Phi(K) > c) <= 2 P(phi(K) >= c) for compact convex K | Gordon's inequality in probability form, a minimax theorem for the convex part | exists after generalization: `library:comparison.gordon.gordon` (gordon.v:648) and `library:comparison.escape.auxT_bilT_minmax` (escape.v:409) are the expectation forms for finite index sets, `library:comparison.gauss_concentration.gauss_concentration` (gauss_concentration.v:930) gives the tails of the Lipschitz functionals; the formal proof passes from expectations to tails in `Gaussian.Lipschitz.LowerMargin.paper_main_gaussian_lipschitz_lower_margin` (LowerMargin.v:40). New general library: the probability form on compact sets (nets plus continuity, or Gordon's original form), and the minimax exchange over compact convex sets for (ii) | 3,800 |
| G4 | Lemma 5.4, the representation A_{G,kappa}(R) = sqrt(2/d) A T_kappa R with A an (n-1) x N_d standard Gaussian matrix (l.4992-5018); Lemmas 5.5, 5.6 (l.5040-5076) | covariance matching, the projection P_{1^perp} as n - 1 independent rows, positive homogeneity | exists after generalization: `library:comparison.gauss_law.gauss_mulmx_law` (gauss_law.v:569) identifies centered Gaussian vectors with equal covariances, `Projected.BulkLaw.paper_main_projected_law` (BulkLaw.v:187) is the orthonormal projection of a Gaussian array, `Projection.Public.paper_main_projection_goe_covariance` (Public.v:55) the GOE covariance at kappa = 3 | 1,200 |
| G5 | Lemma 5.7, the scalar variational lemma for a probability mu on R with finite second moment (l.5160-5181); Lemma 5.8, its stability (l.5219-5236); Lemma 5.9, the shift duality (l.5253-5274); Proposition 5.10 (l.5312-5349) | m_mu decreasing and 1-Lipschitz, the inner product Q_c, Cauchy-Schwarz, dominated convergence at +-oo, m' = -nu((omega, oo)), s' = -2m (l.5360-5375), the inverse function theorem for Lemma 5.12 | new general library (Lemma 5.7, 5.8 for a general mu); new paper-specific (5.9, 5.10, the explicit semicircle facts: mass one, second moment 1/2, the symmetry identities m(-w) = m(w) + w and s(-w) + s(w) = 1/2 + w^2 at l.5281-5283, E_kappa(w) = ((kappa-1)/2) w^2 + 1/2 for w <= -sqrt 2 at l.5384-5391) | the library has the continuity of parameter integrals (`library:gaussian.parameter_integral.continuity_under_integral_at`) and MathComp-Analysis 1.16 has the fundamental theorem of calculus (`ftc.v`) and `trigo.v`; nothing on the semicircle law exists | 2,500 + 1,500 |
| G6 | Lemma 5.13, Haar diagonal averaging (l.5820-5841), used with the fact that the eigenvector matrix of a GOE matrix is Haar and independent of the eigenvalues (l.5816) | moments of a uniform point of the sphere | new general library, with a change of route: Haar measure on O(d) does not exist in MathComp-Analysis; the same second-moment identity follows from the rotation invariance of the GOE and of the Gaussian vector (`library:comparison.gauss_law.gauss_orthogonal_law`, gauss_law.v:607) with a uniform direction v = g/\|g\| and the invariance of its law under fixed rotations, which gives E v_1^2 = 1/d, E v_1^4 = 3 E v_1^2 v_2^2 and the identity of l.5853-5860 without a measurable choice of eigenvectors, because the optimizer R_d = sqrt d ((G/sqrt d) - omega_d I)_+ is a continuous matrix function | 1,500 |
| G7 | Lemma 5.14, the spectral comparison value (l.5877-5902): the semicircle law and the spectral-norm bound for the GOE (cited Anderson-Guionnet-Zeitouni chapter 2, l.5905-5908), von Neumann's trace inequality (cited Bhatia, l.5909-5911) | convergence of the empirical spectral measure, local uniform convergence of m_d and s_d | new general library *hard*: Wigner's semicircle law for the GOE by the moment method (traces of powers, Catalan numbers), with the second moments int x^2 d nu_d -> 1/2; a crude spectral-norm bound suffices (G = (A + A^T)/2 for a square Gaussian matrix A, so ||G||_op <= ||A||_op, and `library:comparison.escape.gauss_opnorm_tail`, escape.v:847); von Neumann's inequality for symmetric matrices from the spectral theorem | the walk-counting machinery of `SquareFree/Walk*` (10,300 lines in `SquareFree/`) counts related objects for the feature matrices; its reuse is **unverified** | 5,000 + 800 |
| G8 | Proposition 5.15, the shifted cone-projection limit (l.5934-5946; proof l.5948-6067), Lemma 5.16 (l.6073-6081), the proof of Proposition 1.4 (l.6205-6220) | G2-G7, the duality for 1 < kappa < 3 (l.6020-6066), the law of large numbers for ||G||_F^2/d^2 | new paper-specific | measurability of the spectrum as a function of the matrix, and continuity of the positive part of a symmetric matrix, do not exist (`Orientation.Spectral` chooses decompositions classically, Spectral.v:175) | 3,000 + 1,000 |
| G9 | Lemma 5.17, the well-conditioned Gaussian fit below the threshold (l.6117-6131) = Proposition 1.4 (i) | the equality case of Lemma 5.7, the profile q = (x - omega_kappa)_+ + l (l.6134-6148), G6, G7, the CGMT upper-tail inequality (ii) on the compact convex set K_{m,M} (l.6187-6198) | new paper-specific | the formal proof's well-conditioned fit (`Conditioned.SpectralReduction.paper_main_subcritical_spectral_reduction`, SpectralReduction.v:56) is for Gaussian data, not for the GOE feature model, and does not transfer | 1,200 |

### Satisfiable phase

| # | Component (paper) | What the proof uses | Category | Formal counterpart, or the statement to add | Lines |
|---|---|---|---|---|---|
| S1 | Proposition 2.1, the approximate fit (l.725-740; proof l.4443-4596): well-conditioned R_hat with (1/n)||A_X R_hat||^2 <= (log d/d)^{1/10} and ||A_X R_hat||_oo <= (log d)^2 | Corollary 2.13 (i) on R_d^{(m,M)} with the two-sided barrier (l.4479-4495), Proposition 1.4 (i) for the Gaussian witness (l.4453-4473), the operator norm of the average of the G_i (l.4465), a leave-one-out argument with Hanson-Wright for the l_oo bound (l.4525-4595) | new paper-specific, on top of U5-U9 and G9; new general library: the Hanson-Wright inequality for independent subgaussian coordinates (Lemma 3.2, l.2157-2177, cited Vershynin Theorem 6.2.1), whose standard proof needs decoupling | the Gaussian Hanson-Wright exists (`Gaussian.Orthogonal.HansonWright.paper_main_gaussian_quadratic_tail`, HansonWright.v:57) | 2,500 + 2,500 |
| S2 | Lemma 2.2, range duality Xi_op(y) = sup {<lambda, y> : lambda in 1^perp, ||L_X^* lambda||_* <= 1} (l.794-826; cited Boyd-Vandenberghe) | nuclear norm, duality with the operator norm, Slater's condition | new general library: the nuclear norm of a real matrix (for symmetric matrices, the sum of the absolute eigenvalues through `symmetric_spectral`), its duality with `opnorm`, and a finite-dimensional Hahn-Banach or minimax argument; the paper uses it only to produce Delta_y from the lower bound on ||L_X^* lambda||_* | `library:matrix.opnorm.opnorm` (opnorm.v:43) and its characterizations (`opnorm_leP`, :94); no nuclear norm exists | 1,500 |
| S3 | Proposition 3.1, the a priori estimates (l.2133-2153; proof l.2187-2300): sup over \|I\| <= C d log d of ||Q_I - I||_op <= C (log d)^{3/2}/sqrt d and ||X_I||_op <= C sqrt d log d, and ||L_X R||_2 <= C sqrt d ||R||_F | the restricted isometry estimate for matrices with subexponential columns (cited Adamczak-Litvak-Pajor-Tomczak-Jaegermann Theorem 3.2, l.2192-2221), norm concentration, the subgaussian operator norm, a union bound over subsets | new general library *hard*: the ALPT theorem, or a self-contained substitute for the two uniform bounds; the second estimate of `eq:second:thm:apriori-estimates` is the subgaussian analogue of the upper feature edge | the Gaussian upper edge exists, by exact Gaussian moments: `Feature.UpperProbability.paper_main_feature_upper_edge` (UpperProbability.v:54), proved in `SquareFree/`, `Column/`, `Feature/`; it does not transfer | 5,000 |
| S4 | Proposition 3.3, the sparse lower bound (l.2303-2314; proof l.2318-2418) | S3, the dual certificate A = (1/d) sum_I y_i W_i with y = Q_I^{-1} eps (l.2339-2348) | new paper-specific | nothing exists | 600 |
| S5 | Proposition 2.4, the vector small-ball estimate (l.906-927; proof l.2531-2781) | the Kolmogorov-Rogozin/Esseen concentration inequality (`eq:kolmogorov:rogozin`, l.2539-2548, cited), Lemma 3.5 (l.2565-2578, a Fourier estimate with characteristic functions and symmetrization), the geometric Brascamp-Lieb inequality (Theorem 3.7, l.2660-2675, cited), Lemma 3.8 (l.2677-2693, Gaussian regularization, Fourier inversion), volumes of Euclidean balls (l.2759-2765) | new general library *hard*: MathComp-Analysis 1.16 has no Fourier transform, no characteristic function and no inversion theorem; the Brascamp-Lieb inequality is a deep theorem (Ball's or Barthe's proof); Esseen's inequality needs the Fourier machinery too | for Gaussian coordinates the estimate is trivial (`Head.SmallBallPZ`, `Projected.BulkEscape` do the Gaussian cases); nothing non-Gaussian exists | 12,000 |
| S6 | Lemma 3.10, covering the nuclear-norm ball by product balls (l.2880-2891; proof l.2893-2953) | the volumetric packing bound, Urysohn's inequality (cited Pisier, l.2918-2927), E ||G||_op <= C sqrt d, volumes of balls | new general library *hard*: Lebesgue measure on matrices, volumes of balls (needs the Gamma function or an induction with `gauss_integral.v`), Urysohn's inequality or another entropy bound for nuclear-norm balls | `library:comparison.escape.gauss_opnorm_mean` (escape.v:778) is E ||G||_op <= sqrt N + sqrt M | 3,000 |
| S7 | Lemma 3.12, the effective-rank bound (l.3314-3334), Corollary 3.13 (l.3408-3436) | S3 in dimension p, a counting argument | new paper-specific | nothing exists | 800 |
| S8 | Lemma 3.14, the one-stage small-ball bound (l.3475-3496; proof l.3498-3608) | S5, S6, conditional independence of the fresh columns given the filtration F^I_{l-1} (l.3258-3297) | new paper-specific; new general library: conditioning on a block of coordinates of `tuple_prod` and the conditional independence of the other block | the Gaussian section bounds `Head.Law.paper_main_split_coordinates_section_bound` (Law.v:183) and `Projected.BulkConditional.paper_main_projected_fixed_head_tail` (BulkConditional.v:871) are the pattern | 1,200 + 1,000 |
| S9 | Proposition 3.4, the light-tail quotient-norm lower bound (l.2436-2450; proof l.3610-3805): sequential block revealing over L blocks, nets of light tails and sparse heads, the union bound with exponent ((1 - eps)(1 - 1/L)/2 - alpha) d^2 log gamma | S7, S8, nets (volume estimates, l.3748-3755), the tower property over the filtration | new paper-specific | nets of unit vectors exist: `library:matrix.nets.net_exists` (nets.v:406); l_1-nets do not | 2,500 |
| S10 | Theorem 2.3 (l.878-893; proof l.2464-2528, the shelling argument) and Theorem 1.9 (proof l.957-974) | S3, S4, S9, S2 | new paper-specific | nothing exists | 1,200 |
| S11 | Theorem 1.2 (i) (proof l.976-991): S1, Theorem 1.9, alpha*(kappa) <= 1/2 (Proposition 5.10 (iii)), P(some x_i != 0) -> 1 from P(x_11 != 0) >= 1/kappa (l.990) | | new paper-specific | the frozen `paper_main_conditioned_event` cannot be reused: the paper's fit has value 1 and no trace normalization (section (e)) | 800 |

### Dependencies and critical path

Arrows mean "is needed by".

- U3 -> U2, U8, S1, S3. U4 -> U5, U6, U7. U5, U6, U7, U8 -> U9. U12 -> U6,
  U10, S8.
- U2, U9, G8 (Proposition 1.4 (ii)) -> U10 (Theorem 1.7 and Theorem 1.2
  (ii)).
- G5 -> G7, G8, G9. G1, G2, G3 (i), G4, G6, G7 -> G8. G3 (ii), G6, G7 ->
  G9.
- U9 (the two-sided barrier of U5, Corollary 2.13 (i)), G9, Hanson-Wright
  (S1) -> S1. S3 -> S4, S7. S5, S6, S7, S8 -> S9. S3, S4, S9 -> S10 (with
  S2). S1, S10, G5 -> S11 (Theorem 1.2 (i)).

The critical path runs through the satisfiable phase: the Fourier
machinery and the Brascamp-Lieb inequality (S5), then Lemma 3.14 (S8),
Proposition 3.4 (S9), Theorem 2.3 and Theorem 1.9 (S10), the assembly
(S11); about 18,000 sequential lines, with S6 (Urysohn) in parallel and
S3 (the a priori estimates) feeding S4, S7 and S9. The second longest
chain is the Gaussian model: the semicircle law (G7), Proposition 5.10
(G5), the CGMT (G3), Proposition 5.15 and Lemma 5.16 (G8), then U10 for
the unsatisfiable phase and G9 then S1 for the satisfiable phase. The
Lindeberg chain U4 -> U6 -> U9 is shorter and independent of both until
the assemblies.

Everything cited by the paper without proof and absent from the formal
development: the ALPT restricted-isometry theorem (S3), Vershynin's
subgaussian estimates (U3), Hanson-Wright (S1), the Nesterov-Nemirovskii
calculus of self-concordance (U4, U5), Koltchinskii-Mendelson's small-ball
theorem and matrix Bernstein (U8), Boyd-Vandenberghe duality (S2), the
Kolmogorov-Rogozin/Esseen inequality, Brascamp-Lieb and Fourier inversion
(S5), Urysohn's inequality (S6), Moreau's decomposition (G2), the CGMT (G3),
the semicircle law and the Haar structure of GOE eigenvectors (G6, G7),
von Neumann's trace inequality (G7).

---

## (c) The staged plan

### Milestone 1, as proposed: the unsatisfiable phase at fourth moment 3 by transporting the formal Gaussian risk gap

The hypothesis to examine was: universality of the unsatisfiable phase for
coordinate laws with kappa = 3 holds if the formal proof's Gaussian risk
gap is a quantity that the Lindeberg argument controls. The check against
the formal statements follows. The conclusion is negative: the quantity is
not controlled by a Lindeberg argument, for three separate reasons, each
tied to a precise statement.

**The formal Gaussian risk gap.** The unsatisfiable phase of the formal
proof is `Unsat.Limit.paper_main_unsat_supercritical_limit` (Limit.v:259),
reduced to the fixed density N = floor(gamma d^2), gamma in (1/4, 1/2), by
`Fixed.Density.paper_main_unsat_from_fixed` (Density.v:232), and at fixed
density to P(fit) <= P(E_d) + P(F_d) (`paper_main_unsat_fixed_density_limit_from_events`,
Limit.v:74): E_d is the upper feature edge event
(`Feature.UpperProbability.paper_main_feature_upper_edge`,
UpperProbability.v:54) and F_d a union over a net of orientations of the
events of `Unsat.Orientation.paper_main_unsat_orientation_constants`
(Orientation.v:32). For one orientation O, that event is the preimage
under the rotation x_i |-> O x_i of the sample
(`Orientation.Exception.paper_main_orientation_exception`, Exception.v:51)
of the event {Z_data <= z}, where

    Z_data = paper_main_hybrid_finite_data N r mi beta I Hs bs Bs   (Hybrid.FiniteArray.v:159)

is the entropy-shifted normalized soft minimum, over a finite prior I of
states (H_j, b_j, B_j), of the loss arrays sum_i phi(g_i^T H_j g_i - Tr
H_j - b_j + y_i^T B_j y_i - Tr B_j) on the rows (g_i, y_i) of r + (mi + 1)
coordinates of the rotated sample, with phi(t) = 1 - exp(-t^2)
(`Loss.Translated.paper_main_loss`, Translated.v:19). The Gaussian risk
gap is the tail bound `Unsat.FiniteTail.paper_main_unsat_ordered_tail`
(FiniteTail.v:41):

    gaussian_product_law (N (r + mi + 1)) {Z_data <= e (1 - exp(-c d^2)) - (2 eta + C eps S_f) - t} <= exp(-N t^2/2),

obtained from three statements: the mean of the hybrid functional,
E Z_goe >= e (1 - exp(-c d^2))
(`Hybrid.FiniteMean.paper_main_hybrid_finite_goe_mean`, FiniteMean.v:177,
where Z_goe = `paper_main_hybrid_finite_goe`, FiniteArray.v:163, replaces
the bulk quadratic forms by Gaussian linear forms of the same covariance);
the mean comparison |E Z_data - E Z_goe| <= 2 eta + C eps S_f
(`paper_main_hybrid_finite_mean_comparison`, FiniteMean.v:100); and the
lower tail of Z_data
(`Hybrid.FiniteTail.paper_main_hybrid_finite_data_lower_tail`,
FiniteTail.v:35). Here eps bounds the operator norms of the bulk blocks
B_j and S_f their Frobenius norms.

**Where the Gaussian law of the data enters, statement by statement.**

1. The rotation. `Orientation.Rotation.paper_main_orientation_rotate_law`
   (Rotation.v:148): the preimage of a measurable E under the rotation of
   the sample by an orthogonal O has the same gaussian_product_law (N d)
   probability as E. The whole head/bulk
   architecture (the head coordinates are the first r coordinates of the
   rotated points, `Orientation.Blocks`, `Hybrid.Residual`) rests on it.
   For a product law of non-Gaussian coordinates the rotated law is not a
   product law and is not the original law: there is no bridge, the step
   has to disappear.
2. The mean comparison. `paper_main_hybrid_finite_mean_comparison`
   (FiniteMean.v:100) compares two iterated Gaussian expectations
   (`Gaussian.Iterated.Definitions.gaussian_iterated_expectation`,
   Definitions.v:19): the data side integrates Z_data over N rows of
   r + mi + 1 standard Gaussian coordinates. Its proof is the row
   replacement `Loss.Replacement.paper_main_loss_array_comparison`
   (Replacement.v:62), which replaces the row functional (the data loss
   ell_Q on R^{r+m}) by another functional (the hybrid loss ell_G on
   R^{r+D}) one row at a time, with the Gaussian law fixed on both sides;
   it is a Lindeberg telescoping over functionals, not over laws. The
   one-row step `paper_main_hybrid_finite_row_comparison` (FiniteMean.v:41)
   first integrates the head block g with
   `Loss.BlockComparison.paper_main_loss_conditional_suffix_comparison`
   (BlockComparison.v:58), which needs the head and bulk coordinates of a
   row to be independent, then compares, for fixed g, the soft minimum at
   the quadratic forms y^T B_j y - Tr B_j of a Gaussian y with the soft
   minimum at Gaussian linear forms of the same covariance,
   `Loss.RowIncrement.paper_main_loss_row_increment_comparison`
   (RowIncrement.v:120), proved by the Gaussian interpolation
   `Projection.Comparison.paper_main_projection_smooth_comparison`
   (Comparison.v:68) along sqrt t Q + sqrt(1 - t) L with Gaussian
   integration by parts; the error 2 eta + C eps S_f is small because eps
   bounds the operator norms of the bulk blocks (the third cumulant of
   y^T B y is 8 Tr B^3 <= 8 eps ||B||_F^2).
3. The hybrid mean. `paper_main_hybrid_finite_goe_mean` (FiniteMean.v:177)
   comes from `Hybrid.Assembly.paper_main_hybrid_gap_event_joint`
   (Assembly.v:365), whose sample space is a pair (head sample, bulk
   array) with law gaussian_product_law (N r) x gaussian_product_law (N
   D) (Assembly.v:142-147): the head is Gaussian data. Its head small-ball
   event `Head.SmallBallUniform.paper_main_head_small_ball_uniform`
   (SmallBallUniform.v:483) uses the Gaussian moments E Y^2 = 2 ||H||_F^2
   + b^2 and E Y^4 <= 19 sigma^4 of
   `Head.SmallBallFourth.paper_main_head_small_ball_moments`
   (SmallBallFourth.v:349) with Paley-Zygmund
   (`Head.SmallBallPZ.paper_main_head_small_ball_probability`,
   SmallBallPZ.v:190); the bulk event `Hybrid.Bulk.paper_main_hybrid_bulk_event`
   (Bulk.v:29) is about the Gaussian surrogate and conditions on the head
   through the product structure
   (`Projected.BulkConditional.paper_main_projected_psd_conditional_tail`,
   BulkConditional.v:949).
4. The concentration. `paper_main_hybrid_finite_data_lower_tail`
   (FiniteTail.v:35) is `Loss.ConcentrationSoftMin.paper_main_softmin_lower_tail`
   (ConcentrationSoftMin.v:112) with row oscillation 1/N, proved from the
   exponential moment bound for Gaussian rows
   `Loss.ConcentrationRow.paper_main_concentration_rows`
   (ConcentrationRow.v:292) and `Loss.ConcentrationTail.paper_main_concentration_lower_tail`
   (ConcentrationTail.v:29); the same inequality holds for any product law
   (McDiarmid).
5. The feature edge `paper_main_feature_upper_edge` (UpperProbability.v:54),
   the Gram bound K <= N L^2 that the prior construction
   `Orientation.Prior.paper_main_orientation_prior` (Prior.v:48) and
   `Feature.LossControl.paper_main_quadratic_risk_lipschitz`
   (LossControl.v:62) need, is proved by the moment method with exact
   Gaussian moments (`SquareFree/`, `Column/`, `Feature/`).
6. The reduction to fixed densities,
   `Gaussian.Sample.Deletion.paper_main_drop_points_law` (Deletion.v:117),
   is stated for `gaussian_product_law`.
7. The measurability of the fit event, `pm_fit_event_measurable`
   (Fit.v:372), is law-independent and is reused as it is.

**Why a Lindeberg argument does not control Z_data.** Suppose the data law
is a product law mu^{N d} with independent coordinates of fourth moment 3,
and consider the functional on the unrotated sample, Z(x) = Z_data(O x),
the soft minimum of the losses phi(x_i^T A_j x_i - Tr A_j - b_j) with the
unrotated candidates A_j = O^T diag(H_j, B_j) O. A Lindeberg transfer of
E_mu Z to E_Gauss Z has two possible granularities, and both fail.

- Row by row (the library's `lindeberg_replacement`, lindeberg.v:230, with
  T the row type, after the reshaping bridge of U12): the per-row cost is
  the one-row universality error |E_mu softmin(f + l(row)) - E_Gauss
  softmin(f + l(row))|, uniform in the other rows f, which must be o(1)
  (there are N rows and each contributes with weight 1/N). Replacing a
  whole row at once is an expansion in the feature vector of the row to
  second order with a third-order remainder of size O(1/N) x E|features|^3
  = O(1/N), total O(1), because the loss phi is bounded and not quadratic;
  this is exactly why the paper's Lindeberg argument is written for the
  squared loss with a barrier, where the insertion cost has the exact
  second-order form r^2/(2(n + l)) with remainder O(gamma^{-1/2} n^{-3/2})
  (Proposition 2.14, l.1811-1819).
- Coordinate by coordinate inside a row (an invariance principle for the
  quadratic forms, the non-Gaussian version of
  `paper_main_projection_smooth_comparison`): the error is governed by the
  influences of the coordinates on the quadratic forms, that is by the
  columns of the A_j. For the bulk block O^T B_j O the influences are at
  most eps and the error has the form C eps S_f^2 that the Gaussian
  comparison already has; this part is new general library work with a
  genuine difficulty, since the matching of the second moments of the
  pair (x_k, x_k^2 - 1) with the Gaussian pair needs E x_k^3 = 0 as well
  as kappa = 3, and a non-symmetric law needs an additional cancellation
  argument (**unverified** whether it holds for this functional). For the
  head block O^T H_j O, of rank at most r and operator norm up to 2, the
  influences are O(1), and the error is not small: with O = I and H_j =
  e_1 e_1^T, the loss phi(x_1^2 - 1 - b) has a law that depends on the
  law of x_1 beyond its first four moments (for a four-point law with
  fourth moment 3, x_1^2 takes two values), so E_mu Z and E_Gauss Z differ
  by a constant for suitable priors. The paper's own discussion of
  spectral spikes (l.487-496) is the same obstruction.

The formal architecture handles the head by anti-concentration (the head
small ball) rather than by comparison, which is why it needs the rotation
to a fixed basis and the independence of head and bulk: both are Gaussian
facts. So the hypothesis fails: the Gaussian risk gap of the formal proof
is not a quantity that the Lindeberg argument controls, because of the
rotation (item 1), the head block (item 3 and the coordinate-wise failure
above) and the bounded loss (the row-wise failure above).

**What is missing, listed as bridges.** Even in the most favorable
reading (kappa = 3 and symmetric coordinate laws), to run the formal
architecture on non-Gaussian data one would need: (B1) the reshaping
bridge between `universality_sample_law` on `(N d).-tuple` and
`tuple_prod` of row laws on `N.-tuple (d.-tuple T)`, and its Gaussian
twin with `gaussian_product_law`, so that `lindeberg_replacement` can act
on rows; (B2) `lindeberg_replacement` for rows of different dimensions on
the two sides (the formal `paper_main_loss_array_comparison` allows p and
q, the library lemma does not); (B3) a non-Gaussian one-row comparison for
the bulk forms (new general library, novel); (B4) a non-Gaussian head
small ball in an arbitrary orientation: for kappa = 3 the second moment
E Y^2 = 2 ||H||_F^2 + b^2 holds in every basis because Var(x^T A x) = 2
||A||_F^2 + (kappa - 3) sum_k A_kk^2, and the fourth moment bound follows
from the L^4 bound of U2 (`eq:approx-tensorization-quadratic-l4`,
l.4364-4368); (B5) a hybrid gap whose head is the data's head in an
arbitrary orientation and whose bulk is the GOE surrogate, replacing the
product law of Assembly.v:142-147 by the product of the data law and the
GOE law; but then (B6) the mean comparison between the data functional
and this hybrid, with head and bulk forms depending on the same
non-Gaussian row, which is where the head/bulk dependence enters and where
the argument has no counterpart in the paper; (B7) McDiarmid's inequality
for product laws; (B8) the subgaussian feature edge; (B9) the deletion law
for `tuple_prod`. B6 is not a bridge but a new theorem of uncertain truth
for non-symmetric laws. The recommendation is to drop this route.

### Milestone 1, re-scoped: the unsatisfiable phase at fourth moment 3 by the paper's route

**Goal.** For every family of coordinate laws with kappa = 3 and n/d^2 ->
alpha > 1/4: P(fit) -> 0, that is the first conjunct of Theorem 1.2 (ii)
in `universality_statement` at kappa = 3, without the limit of the error.
alpha*(3) = 1/4 is a computation on the semicircle law that this milestone
does not need: it suffices to state the goal for alpha > 1/4 and to prove
later that `universality_alpha_star 3 = 1/4`.

**Why kappa = 3 helps here and only here.** The Lindeberg part (U2-U9) is
the same for every kappa. What kappa = 3 saves is the Gaussian model: at
kappa = 3 the Gaussian features are GOE matrices, and the formal proof
already contains, in substance, the lower bound P(Gamma_{G,3} >= c_0) -> 1
of Proposition 1.4 (ii): the hybrid gap `paper_main_hybrid_gap_event`
(Assembly.v:135) at head dimension r = 0 (`Hybrid.Residual` and
`Hybrid.FiniteArray` include r = 0, Residual.v:10-12 and :435, FiniteArray.v:25)
says that outside an event of probability exp(-c d^2), every positive
semidefinite B with ||B||_F^2 >= 1/4 and every offset b give a bounded-loss
risk at least e for the GOE array, through the escape-through-the-mesh
bound `Projected.BulkEscape.paper_main_projected_escape_tail`
(BulkEscape.v:35) on the positive semidefinite unit sphere
(`paper_main_projected_psd_set`, :67, width at most sqrt(D/2), :70).
Since phi(t) <= t^2 (`paper_main_loss_sandwich`, Translated.v:108), a
bounded-loss gap is a squared-loss gap, and for R >= 0 with Tr R = d one
has ||R||_F >= sqrt d, so the squared loss of the paper's normalization
dominates the bounded-loss risk of the unit-Frobenius normalization. The
bridge from `paper_main_hybrid_gap_event` at r = 0 to P(Gamma_{G,3} >=
c_0) -> 1 is new paper-specific work (normalizations, the GOE row scaling
`paper_main_hybrid_bulk_value`, Residual.v:123, the deletion sets J taken
to be all rows, and the identification of the formal GOE array with the
features of l.281-290), estimated at 1,500 lines. For kappa != 3 the
Gaussian features are anisotropic and the whole of section 5 is needed.

**Components.** U3 (2,000), U2 at kappa = 3 (2,400), U4 (1,200), U5
(1,300), U6 (6,000), U7 (400), U8 (3,900), U9 (1,200), U10 (1,000), U11
for the fit event only (existing), U12 (1,100), the GOE gap bridge
(1,500): about 22,000 lines. Order: U3 and U4 first (they unblock
everything), then U5, U6 in parallel with U2 and U8, then U7, U9, the GOE
bridge, U12, U10.

**Deliverable.** A theorem `universality_unsat_fourth_moment_three` in a
new module, stating the first conjunct of Theorem 1.2 (ii) at kappa = 3
for all laws of `universality_coordinate_law 3 K`, and the general
statements of U1-U8 in `library/`. This milestone reuses nothing from the
formal unsatisfiable phase except the GOE gap and the measurability of the
fit event; it replaces `Orientation/`, `Hybrid/` (the data side),
`Loss/` and `Projection/` by the paper's barrier argument.

**Possible shortcut, not recommended.** For symmetric coordinate laws
with kappa = 3, a partial interpolation that keeps the head forms of the
unrotated data row and replaces only the bulk forms by Gaussian linear
forms has second-order structure that matches in every orientation (the
head and bulk blocks are orthogonal, so their quadratic forms are
uncorrelated and the correction (kappa - 3) sum_k A_kk B_kk vanishes), and
every Stein-error term carries a bulk influence, so the error may be O(eps
S_f^2). This would keep the formal hybrid gap (with B4, B5) and cost about
14,000 lines instead of 22,000, but it rests on a new invariance principle
that the paper does not contain, it fails as computed for non-symmetric
laws (a term E x^3 . <A diag B, x> of order one appears), and it proves
nothing reusable for milestones 2 and 3. It is recorded for completeness.

### Milestone 2: general fourth moment, the unsatisfiable phase with the error limit

**Goal.** Theorem 1.2 (ii) and Theorem 1.7 for independent coordinates:
the second conjunct of `universality_statement`, for every kappa > 1,
including Gamma_X -> e*(alpha, kappa) and e* > 0 above the threshold.

**Components.** The Gaussian model G1-G8 (about 22,000 lines, of which
the semicircle law G7 is the hard part), U2 for general kappa (the
regularity constants depend on kappa), the identification of
`universality_alpha_star`, `universality_level_cutoff` and
`universality_e_star` with the paper's objects (Proposition 5.10,
included in G5), U10 for the error limit (Chebyshev on Theorem 2.9's
variance bound, Corollary 2.13 (ii), Proposition 1.4 (ii)), and U11 for
the error event. About 24,000 lines on top of milestone 1.

**Order.** G5 (the scalar problem, which also validates the definitions of
section (e)) and G7 (the semicircle law) first, in parallel; then G2, G3,
G4; then G6, G8; then the assembly.

### Milestone 3: the satisfiable phase

**Goal.** Theorem 1.2 (i): the first conjunct of `universality_statement`.

**Components.** G9 (1,200), S1 (5,000, needs U5's two-sided barrier and
G3 (ii)), S2 (1,500), S3 (5,000, hard), S4 (600), S5 (12,000, hard), S6
(3,000, hard), S7 (800), S8 (2,200), S9 (2,500), S10 (1,200), S11 (800),
U11 for the two new events (800): about 36,500 lines, with three hard
items. S5 and S6 are the risk: a formalization of the Brascamp-Lieb
inequality, of Fourier inversion for densities and of Urysohn's
inequality has no precedent in MathComp-Analysis. Two mitigations: for S6,
replace the volume argument by a direct covering bound of the nuclear-norm
ball in the (1,2)-norm, if one is found (**unverified**: the author of
this study knows no elementary proof with the constant C^{mq}); for S5,
restrict the first version to coordinate laws with a bounded density, for
which the paper notes (l.930-932) that the estimate follows from
Rudelson-Vershynin's Theorem 1.1, which however also uses Fourier analysis
and Brascamp-Lieb. There is no Fourier-free route in the paper.

**Order.** S3 first (it feeds S4, S7, S9), S2 and S5-S6 in parallel; then
S7, S8, S9, S10; S1 after G9; then S11.

### Totals

| Milestone | New general library | New paper-specific | Total (lines) |
|---|---|---|---|
| 1. kappa = 3, no fit above 1/4 | about 15,000 | about 7,000 | about 22,000 |
| 2. general kappa, error limit | about 15,000 | about 9,000 | about 24,000 |
| 3. satisfiable phase | about 25,000 | about 11,500 | about 36,500 |

For scale, the present proof is 86,410 lines in `theories/` and 11,097
in `library/` (README.md). The totals are rough estimates, plus or minus
fifty percent, and the three hard items (S3, S5, S6; G7 to a lesser
degree) carry the risk of not fitting in that range.

**What carries over from the existing development.** The library:
`tuple_prod`, `lindeberg_replacement` and the Fubini lemmas (after
generalization), `paley_zygmund`, `gordon`, `gordon_escape` and the
Gaussian concentration (for the CGMT after generalization),
`gauss_mulmx_law` and `gauss_orthogonal_law` (for the Gaussian model),
`symmetric_spectral` and `opnorm` (for the barrier and the nets), the
nets. The proof: the measurability of the fit event, the fixed-density
reductions as a pattern, the GOE gap at r = 0, the psd Moreau
decomposition at kappa = 3, the matrix normalizations
(`paper_main_homogeneous_witness`, `paper_main_fit_unit_witness`), the
real-analysis bridge `Analysis.RealsBridge` (RealsBridge.v:22-31) between
Stdlib's functions and MathComp's. Nothing of the formal unsatisfiable
architecture (`Orientation/`, the data side of `Hybrid/`, `Loss/`,
`Projection/`) and nothing of the formal satisfiable architecture
(`Head/`, `Gordon/`, `Cone/` beyond the Moreau decomposition) is on the
path, because both depend on the Gaussian law of the data as section (e)
of `doc/paper_correspondence.md` already classifies.

---

## (d) Rules of the repository that the extension would need to change

Listed for the user; nothing below was changed on this branch except the
three lines added to `_CoqProject`.

1. `scripts/check_sources.py` scans `theories/` and `library/` only
   (`sources = ...rglob("*.v")` at check_sources.py:90) for `Admitted`,
   `Axiom`, `Parameter` and `Conjecture`, and checks the import rule of
   `library/` only: `extension/` is not checked. If the extension stays,
   add it to the scan and decide its import rule (it requires both
   `EllipsoidFitting` and `GaussianAnalysis`, and Stdlib's reals through
   the frozen definitions).
2. `scripts/stale_citations.py` reads the comments and `.glob` files of
   `theories/` and `library/` only (its docstring, stale_citations.py:1-20):
   the names cited in the comments of `extension/` are not checked.
3. The `Makefile` has the pattern rule `theories/%.vo library/%.vo` but
   no `extension/%.vo` (Makefile:36): `make extension/X.vo` has no rule.
   This study used `make -f Makefile.rocq extension/X.vo` directly after
   `make Makefile.rocq`. `make build` and `make check` build the extension
   because it is in `_CoqProject`.
4. `_CoqProject` now has `-Q extension EllipsoidUniversality` and the two
   files (allowed for this task). The invariant "`make check` passes after
   every commit" holds (section (e)).
5. `CLAUDE.md`: the ownership table has no lane for `extension/`; the
   list of frozen files does not include `UniversalityDefinitions.v` and
   `UniversalityStatement.v`, which should be frozen once the user has
   reviewed them against the paper, with the same code-unchanged check
   (`FROZEN` list of `check_sources.py`); the rule that no lane A module
   requires a lane B or C module says nothing about `extension/`; the
   invariant and the "What to read" section of `README.md` describe one
   statement.
6. `scripts/unused.py` computes what the main theorem uses from the
   frozen files of `theories/` (its docstring, unused.py:1-30); a future
   deletion pass would delete the extension's statement and everything
   only it uses, unless `extension/` is added to its roots.
7. `check/Assumptions.v` prints the axioms of `ellipsoid_fitting_main`
   only; a proved universality theorem needs its own `Print Assumptions`
   and expected list (the statement alone already depends on seven of the
   eight classical axioms, section (e)).
8. New general results need homes and owners: a directory of `library/`
   for product laws, Efron-Stein, McDiarmid and the subgaussian toolkit
   (`probability/` fits), one for self-concordant barriers and convex
   analysis (new), one for Gordon/CGMT (`comparison/`), one for random
   matrices and the semicircle law (new); the table of main results in
   `library/README.md` has rows per file and per lane.
9. The CI (`.github/workflows/build.yml`) runs `make check` with the
   MathComp image, so it builds the extension; its time limit is 360
   minutes, and the extension's size will grow.
10. Naming: the frozen definitions use the prefix `paper_main_`; the
    extension uses `universality_`. The logical root `EllipsoidUniversality`
    is separate from `EllipsoidFitting`; the alternative, a folder
    `theories/Universality/`, would put the new statement under the root
    of the old proof and inside the scans of items 1, 2 and 6 at once.
11. The protocol "if the work seems to require changing a frozen file,
    stop and ask" does not apply to `extension/`, but the extension's
    definitions reuse frozen ones; a review of the reuse (section (e))
    is the natural first step.

---

## (e) The formal statement

### Files

- `extension/UniversalityDefinitions.v` (253 lines): definitions only;
  the header reads them in the paper's language.
- `extension/UniversalityStatement.v` (98 lines): `universality_statement :
  Prop`, in the shape of `MainStatement.v`, with a header that reads it
  line by line.
- `_CoqProject`: `-Q extension EllipsoidUniversality` and the two files.

Both compile against the library (`GaussianAnalysis.probability.lindeberg`)
and the frozen `PaperMainDefinitions` with its four definition modules,
with no `Admitted`, no `Axiom` and no lemma or proof. `Print Assumptions universality_statement` lists seven of the
eight classical axioms of `check/assumptions.expected` (all but
`Classical_Prop.classic`): `ClassicalDedekindReals.sig_not_dec` and
`sig_forall_dec`, `propositional_extensionality`,
`functional_extensionality_dep` (both `boolp`'s and Stdlib's),
`Epsilon.epsilon_statement`, `constructive_indefinite_description`; they
enter through MathComp's `sup` (Hilbert's choice) and through Stdlib's
reals, as for the frozen definitions. The elaborated definitions contain
no Stdlib numeral (checked with `Set Printing All`: no `IZR`); MathComp's
operations at Stdlib's `R` print as `Rplus`, `Rmult`, `Rdiv`, `Rminus`,
which they unfold to, as in the frozen files.

### What is reused from the frozen definitions

`paper_main_quadratic_form`, `paper_main_symmetric`, `paper_main_psd`,
`paper_main_pd`, `paper_main_loewner_le`, `paper_main_trace`, the sample
type `paper_main_sample n d` and `paper_main_point`, `paper_main_fit_event`
(for the unsatisfiable claim), `paper_main_density` and
`paper_main_tends_to` (PaperMainDefinitions.v). None depends on the law.
`paper_main_conditioned_event` and `paper_main_balanced_pd_event` are not
reused: the first asks for a fit of value d with trace d, which Theorem
1.2 (i) does not give (its witness R = R_hat + Delta has no trace
normalization, l.986-990); the second has no counterpart in Theorem 1.2
(appendix A.1 of the paper, l.6231-6350, has the dual certificate instead).

### New definitions

| Definition | Paper | Notes |
|---|---|---|
| `universality_coordinate_law kappa K mu` | l.160-171 | `mu : probability (measurableTypeR R) R`; conjuncts `0 < K`, `'E_mu[x] = 0`, `'E_mu[x^2] = 1`, `'E_mu[x^4] = kappa`, `'E_mu[exp(x^2/K^2)] <= 2`, with MathComp's `expectation` (extended reals) applied to `universality_power k` and `universality_subgaussian_test K` |
| `universality_product_law mu n` | l.166 | `tuple_prod mu n` of the library: the law of n independent coordinates, on `n.-tuple (measurableTypeR R)`, the construction of `gaussian_product_law` (lindeberg.v:49 and GaussianProbabilityProductDefinitions.v) |
| `universality_sample_law nu n d` | l.166-171 | coordinate k of the tuple has law `nu (k mod d)`: n i.i.d. points whose coordinate j has law `nu j` |
| `universality_probability nu n d E` | | the measure of E under that law |
| `universality_positive_part`, `universality_semicircle_density`, `universality_semicircle_integral`, `universality_semicircle_integrable` | l.345-349 | density `Num.sqrt (2 - x^2) / pi`, zero outside the support since `Num.sqrt` is zero on negative numbers; integrals are `Rintegral` against `lebesgue_measure` |
| `universality_m`, `universality_s`, `universality_energy kappa` | l.350-361 | m, s, E_kappa |
| `universality_cutoff kappa` | l.373-376 | omega_kappa, as `sup {w | w <= (kappa-3)/2 m(w)}` |
| `universality_alpha_star kappa` | l.364-372 | E_kappa(omega_kappa), primary |
| `universality_alpha_star_variational kappa` | l.380-389 | the supremum over f >= 0, f and f^2 integrable against nu, int f d nu = 1, of (int x f d nu)^2 / (int f^2 d nu + (kappa-3)/2) |
| `universality_level_cutoff alpha kappa` | l.401-404 | omega_{alpha,kappa}, as `sup {w < sqrt 2 | alpha <= E_kappa(w)}` |
| `universality_e_star alpha kappa` | l.394-400 | (2/alpha)((kappa-3)/2 m(omega_{alpha,kappa}) - omega_{alpha,kappa})_+^2 |
| `universality_fitting_error n d x` | l.183-187 | Gamma_X as `inf` over S >= 0 with trace d and r >= 0 |
| `universality_pd_fit_event n d` | l.176-179 | S > 0 with x_i^T S x_i = 1 for all i |
| `universality_conditioned_fit_event n d c` | l.180 | S with lm I <= S <= c lm I for some lm > 0 and x_i^T S x_i = 1 for all i |
| `universality_error_event n d e eps` | l.183-187 | |Gamma_X - e| > eps |
| `universality_density_tends_to n alpha` | l.171-172 | n(d)/d^2 -> alpha |

### The statement

`universality_statement` quantifies over kappa > 1, K > 0 and alpha > 0,
then states, for alpha < alpha*(kappa): a constant c >= 1, the
measurability of the positive definite fit event and of the conditioned
fit event, and for every family nu of laws (nu d j for coordinate j of
dimension d, each a `universality_coordinate_law kappa K`) and every n
with n/d^2 -> alpha, the two limits P(positive definite fit) -> 1 and
P(fit with condition number at most c) -> 1; and for alpha >
alpha*(kappa): e*(alpha, kappa) > 0, the measurability of the frozen fit
event and of the error events, and for every such nu and n, P(frozen fit
event) -> 0 and P(|Gamma_X - e*| > eps) -> 0 for every eps > 0.

### Choices, for the user's review

1. **Mode of the limit.** The paper assumes n/d^2 -> alpha (l.172); the
   statement does so (`universality_density_tends_to`), unlike
   `MainStatement`, which has limsup < and liminf > conditions. The
   paper's form is needed for the error limit, which depends on alpha,
   and is what the paper proves; a limsup/liminf form of the fit claims
   would be stronger than the paper's statement.
2. **The family of laws.** The laws may depend on the coordinate j and on
   d (`nu : nat -> nat -> probability ...`), as l.166-171 allow; a single
   law for all coordinates and all d is the special case `nu d j = mu`.
3. **Subgaussian norm.** ||X||_{psi_2} <= K is rendered as E exp(X^2/K^2)
   <= 2, with K > 0. The two are equivalent by monotone convergence (the
   infimum of l.162 is attained), **unverified** formally. The three
   moment equations are equations between extended reals; the subgaussian
   bound makes every power integrable, so they are equations between
   finite numbers (**unverified** formally; a lemma, not a definition).
4. **Threshold.** The scalar formula `eq:alpha-star-scalar-main` is the
   primary definition, because e* is built from the same functions; the
   variational form `eq:alpha-star-def`, which Theorem 1.2 cites (l.173),
   is a second definition. Their equality is Proposition 5.10 (ii).
5. **The cutoffs.** omega_kappa and omega_{alpha,kappa} are least upper
   bounds of half-lines rather than "the unique solution": they equal the
   paper's solutions when w - (kappa-3)/2 m(w) is strictly increasing and
   E_kappa is strictly decreasing below sqrt 2 (Proposition 5.10, proof
   l.5360-5393), and are real numbers in every case (MathComp's `sup` is 0
   on an empty or unbounded set). Equality with the paper's objects is
   **unverified** formally; it is the first lemma of milestone 2.
6. **Normalization of the fits.** The paper's fit has value 1 (l.178);
   `paper_main_fit_event` has value d. They coincide for d >= 1 up to S
   |-> d S (**unverified** formally, elementary). The new events use the
   paper's value 1.
7. **Well-conditioning.** "lambda_max(R)/lambda_min(R) = O(1)" (l.180) is
   stated as: a constant c >= 1 depending only on alpha, kappa and K
   (quantified before the laws and the sequence) such that some fit S
   satisfies lm I <= S <= c lm I for some lm > 0. This follows the proof
   (l.986-990: lambda_max/lambda_min <= 4M/m with m, M from Proposition
   2.1, which depend on alpha, kappa, K_x, l.730-731). The event with the
   constant implies the plain positive definite fit event (**unverified**
   formally, elementary); both limits are stated.
8. **The error.** Gamma_X is an infimum over a set of reals (`inf`); the
   set is nonempty (S = I, r = 0, for d >= 1) and bounded below by 0, so
   the infimum is the paper's. The convergence in probability is written
   as P(|Gamma_X - e*| > eps) -> 0 for every eps > 0, with its
   measurability conjunct.
9. **The positivity e* > 0** above the threshold (l.188) is stated as a
   conjunct; it is part of Proposition 1.4 (ii) and of Proposition 5.10.
10. **Numerals and scopes.** MathComp's at Stdlib's `R`, as the frozen
    files; `2%:R`, `3%:R` are written with `%:R` because the files open
    Stdlib's `R_scope` through the frozen imports and a bare numeral would
    be Stdlib's.

### Verification

The two modules were compiled with the project's flags
(`make -f Makefile.rocq extension/UniversalityDefinitions.vo
extension/UniversalityStatement.vo`, after `make Makefile.rocq`) in the
pinned image; the elaborated terms were inspected with `Print` and
`Set Printing All`; the assumptions with `Print Assumptions`. A full `make
check` was run once at the end on this branch (`JOBS=3`, the wrapper's
default limits): it recompiled the 488 modules downstream of the frozen
definitions, including the two new ones, and passed (8 frozen files
unchanged, no `Admitted`, `Axiom`, `Parameter` or `Conjecture`, 26 library
modules independent of the paper and of Stdlib's reals, the axioms of the
main theorem allowed, no stale citation). Nothing in `theories/`,
`library/`, `scripts/`, the `Makefile` or the READMEs outside `extension/`
was changed.

---

## (f) Phase 6: finite mixtures of product laws and the paired law

Phase 6 proves a generalization of Theorem 1.2 that is not in the
literature checked so far: both phases of exact ellipsoid fitting for
i.i.d. points whose law is, at each dimension `d`, a finite mixture of
product laws, the assumptions (M1) to (M3) of
`notes/mixture-product-universality.md` (on the VM, under
`/srv/ellipsoid-fitting/`); and its corollary, exact fitting for the
paired law of `notes/paired-dependent-sat.md`. The plan is
`notes/paired-law-plan-v2.md`, section 4.

### Files

| File | Content |
|---|---|
| `MixtureDefinitions.v` | the definitions of the general statement (below); definitions only |
| `MixtureStatement.v` | `mixture_statement`, `mixture_interpolation_statement` and `mixture_theorem_statement`, their conjunction |
| `PairedDefinitions.v` | the uniform law on `[-sqrt 3, sqrt 3]` (`paired_uniform_spec`), `h = P_4(x / sqrt 3)` (`paired_kernel`), the pair and sample densities, `paired_probability` |
| `PairedStatement.v` | `paired_statement` |
| `Mixture/Component.v` | the consequences of (M2): subgaussian coordinates, integrable powers, `E x^4 <= 4 K^4`, `E x^2 1_{|x| <= sqrt 8 K^2} >= 1/2`, `P(x != 0) >= 1 / (4 K^4)` |
| `Mixture/Flat.v` | flat families `tuple_prod lam (n * d)`: the points and their features are independent, with the laws of each point; the labelled law of a mixture and `universality_sample_law` are flat families |
| `Mixture/Points.v` | some point of a sample is not zero with probability tending to one |
| `Mixture/Interpolation.v` | Theorem 1.9 for mixtures (`mixture_small_residual`) and `mixture_interpolation_holds` |
| `Mixture/OneComponent.v` | `mixture_universality_statement`: `mixture_statement` implies `universality_statement` |
| `Mixture/Theorem.v`, `MixtureTheorem.v` | `mixture_statement_holds`, then `mixture_theorem : mixture_theorem_statement` |
| `Paired/Uniform.v` | the uniform law, the range of `h`, the laws `(1 + a h) mu` for `-1 <= a <= 7/3` |
| `Paired/Law.v` | the paired law as a finite mixture of product laws |
| `Paired/Theorem.v`, `PairedTheorem.v` | `paired_of_mixture`, then `paired_theorem : paired_statement` |

The modules `Mixture/Theorem` and `Paired/Theorem` are required by their
full names (`Require Import EllipsoidUniversality.Mixture.Theorem`), since
`Theorem` is a keyword.

### The definitions

| Definition | Meaning |
|---|---|
| `mixture_component_law K mu` | (M2): `0 < K`, mean 0, variance 1, `E exp(x^2 / K^2) <= 2`; `universality_coordinate_law` without the fourth moment |
| `mixture_family K N w mu` | (M1) and (M2): for every `d`, `N d` components with weights `w d s >= 0` of sum one and coordinate laws `mu d s j`, `s < N d`, `j < d`, that are component laws |
| `mixture_fourth_moment kappa N w mu` | (M3): under the mixture, every coordinate has fourth moment `kappa` |
| `mixture_label s i`, `mixture_labelled_law N mu n d s` | the label of point `i` in a tuple `s` of labels; given the labels, the `n * d` coordinates are independent, coordinate `k` (coordinate `k mod d` of point `k / d`) with law `mu (s_(k / d)) (k mod d)` |
| `mixture_probability N w mu n d E` | the probability of `E` for `n` i.i.d. points of the mixture: the average over the label tuples, with product weights, of the labelled laws |
| `mixture_interpolation n d C x` | Theorem 1.9 at a sample: every `y` is `(<W_i, Delta>)_i` up to a constant, for a symmetric `Delta` with `|v^T Delta v| <= C (|y|_2 / d + (ln d)^4 |y|_oo / sqrt d) |v|^2`, written with the frozen quadratic form |

The number of components `N d` may grow with `d`. The paired law has
`2^(d / 2)` components, one bit per pair of coordinates.

### The statements

`mixture_statement` has the three parts of Theorem 1.2, for every
`kappa > 1`, `K > 0` and `alpha > 0`, with `mixture_probability` in place
of `universality_probability` and (M1)-(M3) in place of
`universality_coordinate_law`: below the threshold `alpha*(kappa)`, a
positive definite fit, and a fit of condition number at most `c`, with
probability tending to one, `c` depending only on `alpha`, `kappa` and
`K`; above it, `e*(alpha, kappa) > 0` and no positive semidefinite fit;
for every `alpha`, the optimal squared fitting error tends to
`e*(alpha, kappa)` in probability. `mixture_interpolation_statement` is
Theorem 1.9 under (M1)-(M2), for `alpha < 1/2`, with `C` chosen before the
mixture. `paired_statement` is the corollary for the paired law, with a
parameter `-1 <= eps d <= 7/3` that may depend on `d`: the threshold
`alpha*(9/5)`, the error `e*(alpha, 9/5)` and the interpolation estimate.
The user accepted the four statement files at commit `eef4694`, with
the error limit for every `alpha > 0` and the constants `c` and `C` of
`paired_statement` chosen before `eps`, hence uniform over
`eps` in `[-1, 7/3]`. They are frozen like `UniversalityDefinitions.v` and
`UniversalityStatement.v`: their code does not change, and
`scripts/check_sources.py` compares it with that commit.

### The proof

The route of `notes/mixture-product-universality.md`: the interpolation
chain is proved given the labels of the points, uniformly in them, and the
exceptional events of the label tuples are intersected; the approximate
fit and the unsatisfiable phase use the mixture of the feature laws.

- Library: `probability/density_law.v` (laws given by a density),
  `probability/mixture.v` (finite mixtures, total variance, the product of
  copies of a mixture, `mixture_cover`), `convex/feature_mixture.v` (a
  mixture of regular feature laws is regular, in Hilbert-Schmidt form).
- Flat families: the a priori estimates (`Sat/Apriori.v`,
  `Sat/AprioriSparse.v`, `Sat/SparseLimit.v`), the light-tail bound
  (`Sat/OneStage.v`, `Sat/LightTail.v`, `Sat/LightTailBound.v`) and the
  small-residual interpolation (`Sat/Interpolation.v`,
  `Sat/SmallResidual.v`) hold for every flat family of component laws,
  with the dimension threshold chosen before the laws; the statements of
  phase 5 for `universality_sample_law` are now their corollaries.
- Features: the bounds of `Features/Regular.v` for component laws, and
  `Features/Mixture.v`: the mixture feature law, regular with covariance
  `unsat_cov kappa d` under (M3), and the features of a mixture sample,
  i.i.d. with that law.
- Assemblies: the approximate fit from a feature law
  (`approximate_fit_law` of `Sat/ApproximateFit.v`), for a family of
  feature laws `rho d` that are regular features with the covariance
  `unsat_cov kappa d` and a parameter `tau d` tending to 0, and whose
  linear forms `<z, mxvec A>` are subexponential with constant
  `L / sqrt d` whenever `Ls |A|_F <= L`; the satisfiable phase
  (`Sat/Universality.v`),
  the unsatisfiable phase and Theorem 1.7 (`Unsat/Universality.v`), then
  `Mixture/Theorem.v`.
- The paired law: `paired_probability_mixture` writes it as a mixture of
  product laws with the identities (M16) (`eps < 0`) and (M17)
  (`eps >= 0`) of the note; the component laws `(1 + a h) mu` have
  constant 3 and fourth moment `9/5 + 8 a / 35`, and the parameters have
  mean 0 under the weights, so the fourth moment of the mixture is `9/5`.

### Verification

`make check` compiles `check/MixtureAssumptions.v` and
`check/PairedAssumptions.v`, which check that `mixture_theorem` proves
`mixture_theorem_statement` and `paired_theorem` proves
`paired_statement`, and compares their axioms with
`check/mixture_assumptions.expected` and
`check/paired_assumptions.expected` (`scripts/check_sources.py`). Both
theorems use seven of the eight classical axioms of
`check/assumptions.expected`, all but `Classical_Prop.classic`, as
`universality_theorem` does. `Mixture/OneComponent.v` checks that the
general statement contains the theorem of phase 5.

### The latent-sign corollary (phase 7)

`LatentSignDefinitions.v` defines the latent-sign law by its density
against the product of the uniform laws: for each point,
(prod_j (1 + s h(x_j)) + prod_j (1 - s h(x_j))) / 2, the law
(1/2) lambda_s^(x)d + (1/2) lambda_-s^(x)d with lambda_a = (1 + a h) mu.
One hidden sign, + or - with probability 1/2, couples all the coordinates
of a point. `LatentSignStatement.v` states `latent_sign_statement`, the
four parts of `paired_statement` for this law, for every sequence s with
0 <= s d <= 1 and constants chosen before s. It is a mixture of two
product laws whose components, `paired_law mu s` and `paired_law mu (- s)`,
are component laws with constant 3 and have the fourth moments
9/5 + 8 s / 35 and 9/5 - 8 s / 35, of mean 9/5. The statement files are
under the user's review; the proof, from `mixture_theorem`, is item 3 of
phase 7.
