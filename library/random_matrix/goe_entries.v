From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions.
From mathcomp Require Import interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.comparison Require Import gauss_linear chi_square.
From GaussianAnalysis.comparison Require Import gauss_law gauss_smoothing.
From GaussianAnalysis.random_matrix Require Import goe goe_rotation.

(**md**************************************************************************)
(* # Tails of the entries of the GOE matrix                                   *)
(*                                                                            *)
(* For a of law gauss (d * d) and the GOE matrix W = goe_mx a of              *)
(* random_matrix/goe.v, each entry of W is a linear form of a:                *)
(* W_ij = <a, goe_coef i j> (goe_mx_mxdot). The coefficient vector of a       *)
(* diagonal entry has squared norm 2 / d (frobenius_goe_coef_diag), and the   *)
(* coefficient vectors of the entries of a row outside the diagonal are       *)
(* orthogonal, of squared norm 1 / d (mxdot_goe_coef_row). Hence, for s >= 0  *)
(* and u > 0,                                                                 *)
(*   P(|W_ii| >= s) <= 2 exp (- d s^2 / 4)               (goe_mx_diag_tail),  *)
(*   P(|W_ij| >= s) <= 2 exp (- d s^2 / 2) if i != j  (goe_mx_offdiag_tail),  *)
(*   P(sum_(j != i) W_ij^2 >= 1 + u) <= exp (- d u^2 / (4 (1 + u))),          *)
(* the last one (goe_mx_row_tail) because d sum_(j != i) W_ij^2 has the law   *)
(* of a chi-square with d - 1 degrees of freedom (gauss_mulmx_law, then       *)
(* gauss_centered_chi2_upper_tail of comparison/chi_square.v). Union bounds   *)
(* over the d diagonal entries, the d^2 entries and the d rows give the tails *)
(* of the maxima, with the factors 2 d, 2 d^2 and d (goe_mx_diag_max_tail,    *)
(* goe_mx_offdiag_max_tail, goe_mx_row_max_tail); their events are measurable *)
(* (measurable_goe_diag_max and the next two).                                *)
(*                                                                            *)
(* Three general facts are proved on the way: removing the diagonal of a      *)
(* square matrix A costs at most max_i |A_ii| in operator norm                *)
(* (opnorm_sub_diag_le, from opnorm_diag_mx_le); the union bound              *)
(* mu (\bigcup_i F i) <= \sum_i mu (F i) for a measure mu, a finite index     *)
(* type and measurable sets F i (measure_bigcup_fin_le); and                  *)
(* x^k exp (- x c) <= 6 / (c^3 x) for c > 0, x >= 1 and k <= 2                *)
(* (exprn_expRN_le), so that such tails, times at most d^2 events, are of     *)
(* order 1 / d.                                                               *)
(*                                                                            *)
(* Part of target T4 of phase 12: a Rocq formalization of the credited        *)
(* argument of the proof of the proposition 'Good disorder'                   *)
(* (rcut:prop:good-disorder) of 'Cutoff throughout the high-temperature       *)
(* Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd, file appendices/entropy.tex), for the diagonal         *)
(* entries, the entries and the row sums of the disorder; the proposition     *)
(* itself is in applications/SKGap/Disorder.v. It follows the TeX, not a Lean *)
(* module of the collection. The manuscript bounds a row sum by the           *)
(* exponential Markov bound with E exp (theta (g^2 - 1)) <= exp (C theta^2)   *)
(* for |theta| <= 1/4; the chi-square tail used here has the same form with   *)
(* explicit constants.                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* goe_coef i j == the row vector c of 'rV[R]_(d * d) such that               *)
(*                 goe_mx a i j = <a, c> for every a                          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section opnorm_diag.
Context {R : realType}.

(* The operator norm of a diagonal matrix is at most a bound of its
   entries. *)
Lemma opnorm_diag_mx_le n (v : 'rV[R]_n) (b : R) : 0 <= b ->
  (forall i, `|v 0 i| <= b) -> opnorm (diag_mx v) <= b.
Proof.
move=> b0 vb; apply/(opnorm_leP _ b0) => x.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?frobenius_ge0 //.
rewrite exprMn !frobenius_sqr /mxdot mulr_sumr; apply: ler_sum => i _.
rewrite !big_ord1 mul_diag_mx !mxE.
have := vb i; have := normr_ge0 (v 0 i).
move: (v 0 i) (x i ord0) => p q _ pb.
have hp : p ^+ 2 <= b ^+ 2.
  by rewrite -real_normK ?num_real //; apply: lerXn2r => //; rewrite nnegrE.
have -> : p * q * (p * q) = p ^+ 2 * q ^+ 2 by rewrite !expr2 mulrACA.
by rewrite -expr2; apply: ler_wpM2r; rewrite ?sqr_ge0.
Qed.

(* Removing the diagonal of A costs at most a bound of its entries. *)
Lemma opnorm_sub_diag_le n (A : 'M[R]_n) (b : R) : 0 <= b ->
  (forall i, `|A i i| <= b) ->
  opnorm (A - diag_mx (\row_i A i i)) <= opnorm A + b.
Proof.
move=> b0 Ab.
apply: le_trans (opnormD _ _) _; rewrite opnormN lerD //.
by apply: opnorm_diag_mx_le => // i; rewrite mxE; exact: Ab.
Qed.

End opnorm_diag.

Section union_bound.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

(* The union bound for a family indexed by a finite type. *)
Lemma measure_bigcup_fin_le (I : finType) (F : I -> set T) :
  (forall i, measurable (F i)) -> mu (\bigcup_i F i) <= \sum_i mu (F i).
Proof.
move=> mF.
have -> : \bigcup_i F i = \big[setU/set0]_(i <- index_enum I) F i.
  rewrite -bigcup_seq; congr (\bigcup_(i in _) _).
  by apply/seteqP; split => i //= _; exact: mem_index_enum.
elim: (index_enum I) => [|i s IH]; first by rewrite !big_nil measure0.
rewrite !big_cons; apply: le_trans (measureU2 _ _ _) _ => //.
  by apply: bigsetU_measurable => j _; exact: mF.
by apply: leeD.
Qed.

End union_bound.

Section exp_poly.
Context {R : realType}.

(* x^k exp (- x c) <= 6 / (c^3 x) for c > 0, x >= 1 and k <= 2. *)
Lemma exprn_expRN_le (c x : R) (k : nat) : 0 < c -> 1 <= x -> (k <= 2)%N ->
  x ^+ k * expR (- (x * c)) <= 6 / c ^+ 3 / x.
Proof.
move=> c0 x1 k2.
have x0 : 0 < x by apply: lt_le_trans x1.
have y0 : 0 <= x * c by rewrite mulr_ge0 // ltW.
have e : (x * c) ^+ 3 / 6 <= expR (x * c).
  have := expR_ge1Dxn 2 y0; rewrite (_ : 3`!%:R = 6 :> R) //.
  by move=> h; apply: le_trans h; rewrite lerDr.
have xk : x ^+ k <= x ^+ 2.
  case: k k2 => [|[|[|]]] //= _; rewrite ?expr0 ?expr1.
    by rewrite exprn_ege1.
  by rewrite expr2 ler_peMl // (le_trans ler01 x1).
rewrite -mulrA -invfM expRN.
have E0 : 0 < expR (x * c) := expR_gt0 _.
have Ei : 0 <= (expR (x * c))^-1 by rewrite invr_ge0 ltW.
apply: le_trans (ler_wpM2r Ei xk) _.
rewrite ler_pdivlMr ?mulr_gt0 ?exprn_gt0 // mulrAC ler_pdivrMr //.
have -> : x ^+ 2 * (c ^+ 3 * x) = (x * c) ^+ 3 by ring.
by move: e; move: (x * c) => y; move: (expR y) => E h; lra.
Qed.

End exp_poly.

Section goe_entries.
Context {R : realType} (d : nat).

(* The entry (i, j) of goe_mx a is the inner product of a with goe_coef i j. *)
Definition goe_coef (i j : 'I_d) : 'rV[R]_(d * d) :=
  (Num.sqrt (2 * d%:R))^-1 *:
    (delta_mx 0 (mxvec_index i j) + delta_mx 0 (mxvec_index j i)).

Lemma goe_mx_mxdot (a : 'rV[R]_(d * d)) i j :
  goe_mx a i j = mxdot a (goe_coef i j).
Proof. by rewrite goe_mxE /goe_coef mxdotZr mxdotDr !mxdot_delta. Qed.

Lemma delta_mxvec_index (i j i' j' : 'I_d) :
  (delta_mx 0 (mxvec_index i j) : 'rV[R]_(d * d)) 0 (mxvec_index i' j') =
  ((i' == i) && (j' == j))%:R.
Proof.
have := congr1 (fun M : 'M[R]_d => M i' j') (vec_mx_delta R i j).
by rewrite !mxE /=.
Qed.

(* Within the row i, the vectors goe_coef i j, j != i, are orthogonal, of
   squared norm 1 / d. *)
Lemma mxdot_goe_coef_row (i j j' : 'I_d) : j != i -> j' != i ->
  mxdot (goe_coef i j) (goe_coef i j') = (j == j')%:R / d%:R.
Proof.
move=> ji j'i.
have d0 : (0 < d)%N by case: d i {ji j'i} => [[]|].
rewrite /goe_coef mxdotZl mxdotZr !mxdotDl !mxdotDr !mxdot_delta.
rewrite !delta_mxvec_index eqxx (negbTE j'i) [i == j]eq_sym (negbTE ji) /=.
rewrite andbT [j' == j]eq_sym.
have c2 : (Num.sqrt (2 * d%:R))^-1 * (Num.sqrt (2 * d%:R) : R)^-1 =
    (2 * d%:R)^-1.
  by rewrite -invfM -expr2 sqr_sqrtr // mulr_ge0 ?ler0n.
rewrite mulrA c2.
have dn : (d%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by case: (j == j'); rewrite /= ?addr0 ?add0r; field.
Qed.

Lemma frobenius_goe_coef_diag (i : 'I_d) :
  frobenius (goe_coef i i) ^+ 2 = 2 / d%:R.
Proof.
have d0 : (0 < d)%N by case: d i => [[]|].
rewrite frobenius_sqr /goe_coef mxdotZl mxdotZr !mxdotDl !mxdotDr !mxdot_delta.
rewrite !delta_mxvec_index eqxx /=.
have c2 : (Num.sqrt (2 * d%:R))^-1 * (Num.sqrt (2 * d%:R) : R)^-1 =
    (2 * d%:R)^-1.
  by rewrite -invfM -expr2 sqr_sqrtr // mulr_ge0 ?ler0n.
rewrite mulrA c2.
have dn : (d%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

(* Gaussian tails of the entries, of variance 2 / d on the diagonal and
   1 / d off the diagonal. *)
Theorem goe_mx_diag_tail (i : 'I_d) (s : R) : 0 <= s ->
  (gauss (d * d) [set a | s <= `|goe_mx a i i|]%R <=
   (2 * expR (- (d%:R * s ^+ 2 / 4)))%:E)%E.
Proof.
move=> s0.
have d0 : (0 < d)%N by case: d i => [[]|].
have dn : (d%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have f2 := frobenius_goe_coef_diag i.
have c0 : goe_coef i i != 0.
  apply/eqP => c0; move: f2; rewrite c0 frobenius0 expr0n /= => /eqP.
  by rewrite eq_sym mulf_eq0 invr_eq0 (negbTE dn) pnatr_eq0.
have -> : [set a | (s <= `|goe_mx a i i|)%R] =
    [set a | (s <= `|mxdot a (goe_coef i i)|)%R].
  by apply/seteqP; split => a /=; rewrite goe_mx_mxdot.
apply: le_trans (gauss_mxdot_abs_tail c0 s0) _.
rewrite lee_fin ler_pM2l // ler_expR f2.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

Theorem goe_mx_offdiag_tail (i j : 'I_d) (s : R) : i != j -> 0 <= s ->
  (gauss (d * d) [set a | s <= `|goe_mx a i j|]%R <=
   (2 * expR (- (d%:R * s ^+ 2 / 2)))%:E)%E.
Proof.
move=> ij s0.
have d0 : (0 < d)%N by case: d i {ij} => [[]|].
have dn : (d%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have ji : j != i by rewrite eq_sym.
have f2 : frobenius (goe_coef i j) ^+ 2 = d%:R^-1.
  by rewrite frobenius_sqr mxdot_goe_coef_row // eqxx mul1r.
have c0 : goe_coef i j != 0.
  apply/eqP => c0; move: f2; rewrite c0 frobenius0 expr0n /= => /eqP.
  by rewrite eq_sym invr_eq0 (negbTE dn).
have -> : [set a | (s <= `|goe_mx a i j|)%R] =
    [set a | (s <= `|mxdot a (goe_coef i j)|)%R].
  by apply/seteqP; split => a /=; rewrite goe_mx_mxdot.
apply: le_trans (gauss_mxdot_abs_tail c0 s0) _.
rewrite lee_fin ler_pM2l // ler_expR f2.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* The squares of the row i off the diagonal sum to 1 / d times a
   chi-square with d - 1 degrees of freedom: their tail above 1 + u. *)
Theorem goe_mx_row_tail (i : 'I_d) (u : R) : 0 < u ->
  (gauss (d * d) [set a | 1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R <=
   (expR (- (d%:R * u ^+ 2 / (4 * (1 + u)))))%:E)%E.
Proof.
move=> u0.
have d0 : (0 < d)%N by case: d i => [[]|].
have dn : (d%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have dp : (0 : R) < d%:R by rewrite ltr0n.
(* the columns of A are sqrt d goe_coef i j, j != i, and 0 for j = i *)
pose v (j : 'I_d) : 'rV[R]_(d * d) :=
  if j == i then 0 else Num.sqrt d%:R *: goe_coef i j.
pose A : 'M[R]_(d * d, d) := \matrix_(k, j) v j 0 k.
pose B : 'M[R]_d := diag_mx (\row_j (if j == i then 0 else 1 : R)).
have Acol (a : 'rV[R]_(d * d)) j : (a *m A) 0 j = mxdot a (v j).
  rewrite mxE /mxdot big_ord1; apply: eq_bigr => k _.
  by rewrite mxE.
have AE (a : 'rV[R]_(d * d)) j :
    (a *m A) 0 j = if j == i then 0 else Num.sqrt d%:R * goe_mx a i j.
  rewrite Acol /v; case: ifP => _; first by rewrite mxdot0r.
  by rewrite mxdotZr goe_mx_mxdot.
have AtA j j' : (A^T *m A) j j' = mxdot (v j) (v j').
  rewrite mxE /mxdot big_ord1; apply: eq_bigr => k _.
  by rewrite !mxE.
(* the columns of A are orthonormal, except the zero column i *)
have AB : A^T *m A = B^T *m B.
  apply/matrixP => j j'.
  rewrite AtA tr_diag_mx mul_diag_mx !mxE /v.
  case: (eqVneq j i) => [_|ji]; first by rewrite mxdot0l mul0r.
  case: (eqVneq j' i) => [j'i|j'i].
    rewrite mxdot0r mul1r; case: eqP => // jj'.
    by move: ji; rewrite jj' j'i eqxx.
  rewrite mxdotZl mxdotZr mxdot_goe_coef_row // mulrA -expr2.
  by rewrite sqr_sqrtr ?ler0n // mul1r mulrCA mulfV // mulr1.
pose F (w : 'rV[R]_d) := \sum_j w 0 j ^+ 2.
have mF : measurable_fun setT F.
  apply: measurable_sum => j; apply: measurable_funX.
  exact: measurable_mxentry.
pose X : set 'rV[R]_d := [set w | d%:R * (1 + u) <= F w]%R.
have mX : measurable X.
  have -> : X = F @^-1` `[d%:R * (1 + u), +oo[%classic.
    by apply/seteqP; split => w; rewrite /X /= in_itv /= andbT.
  by rewrite -[X in measurable X]setTI; exact: mF.
have sumA a : F (a *m A) = d%:R * \sum_(j | j != i) goe_mx a i j ^+ 2.
  rewrite /F (bigID (fun j => j == i)) /= big1 => [j /eqP ->|].
    by rewrite AE eqxx expr0n.
  rewrite add0r mulr_sumr; apply: eq_bigr => j /negbTE ji.
  by rewrite AE ji exprMn sqr_sqrtr ?ler0n.
have -> : [set a | (1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2)%R] =
    [set a | X (a *m A)].
  by apply/seteqP; split => a; rewrite /X /= sumA ler_pM2l.
(* so the row has the law of 1 / d times a chi-square with d - 1 degrees *)
rewrite (gauss_mulmx_law AB mX).
pose c : 'rV[R]_d := \row_j (if j == i then 0 else 1 : R).
have sumB y : F (y *m B) = \sum_(j | j != i) y 0 j ^+ 2.
  rewrite /F (bigID (fun j => j == i)) /= big1 => [j /eqP ->|].
    by rewrite mul_mx_diag !mxE eqxx mulr0 expr0n.
  rewrite add0r; apply: eq_bigr => j /negbTE ji.
  by rewrite mul_mx_diag !mxE ji mulr1.
have chiE y : centered_chi2 c y =
    \sum_(j | j != i) y 0 j ^+ 2 - \sum_(j | j != i) (1 : R).
  rewrite /centered_chi2 (bigID (fun j => j == i)) /= big1 => [j /eqP ->|].
    by rewrite mxE eqxx mul0r.
  rewrite add0r -sumrB; apply: eq_bigr => j /negbTE ji.
  by rewrite mxE ji mul1r.
have cnt : \sum_(j | j != i) (1 : R) <= d%:R.
  have -> : (d%:R : R) = \sum_(j : 'I_d) 1 by rewrite sumr_const card_ord.
  rewrite [X in _ <= X](bigID (fun j => j != i)) /= lerDl.
  by apply: sumr_ge0.
have sub : [set y | X (y *m B)] `<=`
    [set y | (d%:R * u <= centered_chi2 c y)%R].
  move=> y; rewrite /X /= sumB chiE => h.
  move: h cnt; move: (\sum_(j | j != i) y 0 j ^+ 2) (\sum_(j | j != i) (1 : R)).
  by move=> S K h k; lra.
have mB : measurable_fun setT (fun y : 'rV[R]_d => y *m B).
  by apply: measurable_mulmx => //; exact: measurable_cst.
have mXB : measurable [set y : 'rV[R]_d | X (y *m B)].
  by rewrite -[X in measurable X]setTI; exact: mB.
have mY : measurable [set y : 'rV[R]_d | (d%:R * u <= centered_chi2 c y)%R].
  have -> : [set y : 'rV[R]_d | (d%:R * u <= centered_chi2 c y)%R] =
      centered_chi2 c @^-1` `[d%:R * u, +oo[%classic.
    by apply/seteqP; split => y; rewrite /= in_itv /= andbT.
  rewrite -[X in measurable X]setTI.
  exact: measurable_centered_chi2.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
have cb j : `|c 0 j| <= 1 by rewrite mxE; case: ifP; rewrite ?normr0 ?normr1.
have cc0 : 0 <= mxdot c c := mxdot_ge0 c.
have ccd : mxdot c c <= d%:R.
  have -> : (d%:R : R) = \sum_(j : 'I_d) 1 by rewrite sumr_const card_ord.
  rewrite /mxdot big_ord1; apply: ler_sum => j _.
  by rewrite mxE; case: ifP; rewrite ?mul0r ?mul1r.
have du : 0 < d%:R * u by rewrite mulr_gt0.
have pos : 0 < mxdot c c + 1 * (d%:R * u) by rewrite mul1r ltr_wpDl.
apply: le_trans (gauss_centered_chi2_upper_tail ler01 cb du pos) _.
rewrite lee_fin ler_expR mulNr lerN2 mul1r.
have p1 : 0 < 4 * (1 + u) by rewrite mulr_gt0 // addr_gt0.
have p2 : 0 < 4 * (mxdot c c + d%:R * u).
  by rewrite mulr_gt0 // -[_ * u]mul1r.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
move: (mxdot c c) cc0 ccd p2 => m m0 md p2.
have e : (d%:R * u) ^+ 2 * (4 * (1 + u)) -
    d%:R * u ^+ 2 * (4 * (m + d%:R * u)) = 4 * d%:R * u ^+ 2 * (d%:R - m).
  by ring.
rewrite -subr_ge0 e; apply: mulr_ge0; last by rewrite subr_ge0.
by rewrite !mulr_ge0 // ?sqr_ge0 ltW.
Qed.

Lemma measurable_goe_entry (i j : 'I_d) :
  measurable_fun [set: 'rV[R]_(d * d)] (fun a => goe_mx a i j).
Proof.
by apply: measurableT_comp (measurable_mxentry i j) _; exact: measurable_goe_mx.
Qed.

Lemma measurable_goe_entry_ge (i j : 'I_d) (c : R) :
  measurable [set a : 'rV[R]_(d * d) | c <= `|goe_mx a i j|]%R.
Proof.
have -> : [set a : 'rV[R]_(d * d) | c <= `|goe_mx a i j|]%R =
    (fun a => `|goe_mx a i j|) @^-1` `[c, +oo[%classic.
  by apply/seteqP; split => a; rewrite /= in_itv /= andbT.
rewrite -[X in measurable X]setTI.
have mf : measurable_fun setT (fun a : 'rV[R]_(d * d) => `|goe_mx a i j|).
  apply: measurableT_comp (measurable_goe_entry i j).
  exact: normr_measurable.
exact: mf.
Qed.

Lemma measurable_goe_row_ge (i : 'I_d) (c : R) :
  measurable
    [set a : 'rV[R]_(d * d) | c <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R.
Proof.
have E (a : 'rV[R]_(d * d)) : \sum_(j | j != i) goe_mx a i j ^+ 2 =
    \sum_j (j != i)%:R * goe_mx a i j ^+ 2.
  rewrite big_mkcond; apply: eq_bigr => j _.
  by case: ifP => _; rewrite ?mul1r ?mul0r.
have mf : measurable_fun setT
    (fun a : 'rV[R]_(d * d) => \sum_j (j != i)%:R * goe_mx a i j ^+ 2).
  apply: measurable_sum => j; apply: measurable_funM => //.
  by apply: measurable_funX; exact: measurable_goe_entry.
have -> : [set a : 'rV[R]_(d * d) |
    c <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R =
    (fun a => \sum_j (j != i)%:R * goe_mx a i j ^+ 2) @^-1` `[c, +oo[%classic.
  by apply/seteqP; split => a; rewrite /= in_itv /= andbT E.
by rewrite -[X in measurable X]setTI; exact: mf.
Qed.

Lemma measurable_goe_opnorm_ge (c : R) :
  measurable [set a : 'rV[R]_(d * d) | c <= opnorm (goe_mx a)]%R.
Proof.
have L (a b : 'rV[R]_(d * d)) :
    `|opnorm (goe_mx a) - opnorm (goe_mx b)| <=
    Num.sqrt (2 / d%:R) * frobenius (a - b).
  have hA := opnormD (goe_mx b) (goe_mx a - goe_mx b).
  rewrite addrC subrK in hA.
  have hB := opnormD (goe_mx a) (goe_mx b - goe_mx a).
  rewrite addrC subrK -opprB opnormN in hB.
  have h1 : `|opnorm (goe_mx a) - opnorm (goe_mx b)| <=
      opnorm (goe_mx a - goe_mx b).
    by rewrite ler_norml; apply/andP; split; lra.
  apply: le_trans h1 _; rewrite -goe_mxB.
  exact: le_trans (opnorm_le_frobenius _) (frobenius_goe_mx _).
have mf : measurable_fun setT (fun a : 'rV[R]_(d * d) => opnorm (goe_mx a)).
  exact: continuous_measurable_mx (lipschitz_frobenius_continuous L).
have -> : [set a : 'rV[R]_(d * d) | c <= opnorm (goe_mx a)]%R =
    (fun a => opnorm (goe_mx a)) @^-1` `[c, +oo[%classic.
  by apply/seteqP; split => a; rewrite /= in_itv /= andbT.
by rewrite -[X in measurable X]setTI; exact: mf.
Qed.

(* The events of the three maxima below are measurable. *)
Lemma measurable_goe_diag_max (s : R) :
  measurable [set a : 'rV[R]_(d * d) | exists i, s <= `|goe_mx a i i|]%R.
Proof.
have -> : [set a : 'rV[R]_(d * d) | exists i, (s <= `|goe_mx a i i|)%R] =
    \bigcup_i [set a | (s <= `|goe_mx a i i|)%R].
  apply/seteqP; split => a /= [i].
    by move=> h; exists i.
  by move=> _ h; exists i.
apply: fin_bigcup_measurable => [|i _]; first exact: cardinality.finite_finset.
exact: measurable_goe_entry_ge.
Qed.

Lemma measurable_goe_offdiag_max (s : R) :
  measurable [set a : 'rV[R]_(d * d) |
    exists i j, i != j /\ s <= `|goe_mx a i j|]%R.
Proof.
have -> : [set a : 'rV[R]_(d * d) |
    exists i j, i != j /\ (s <= `|goe_mx a i j|)%R] =
    \bigcup_i \bigcup_(j in [set j | i != j])
      [set a | (s <= `|goe_mx a i j|)%R].
  apply/seteqP; split => a /=.
    by case=> i [j [ij h]]; exists i => //; exists j.
  by case=> i _ [j ij h]; exists i, j.
apply: fin_bigcup_measurable => [|i _]; first exact: cardinality.finite_finset.
apply: fin_bigcup_measurable => [|j _]; first exact: cardinality.finite_finset.
exact: measurable_goe_entry_ge.
Qed.

Lemma measurable_goe_row_max (c : R) :
  measurable [set a : 'rV[R]_(d * d) |
    exists i, c <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R.
Proof.
have -> : [set a : 'rV[R]_(d * d) |
    exists i, (c <= \sum_(j | j != i) goe_mx a i j ^+ 2)%R] =
    \bigcup_i [set a | (c <= \sum_(j | j != i) goe_mx a i j ^+ 2)%R].
  apply/seteqP; split => a /= [i].
    by move=> h; exists i.
  by move=> _ h; exists i.
apply: fin_bigcup_measurable => [|i _]; first exact: cardinality.finite_finset.
exact: measurable_goe_row_ge.
Qed.

(* The largest diagonal entry, the largest entry off the diagonal and the
   largest row sum of squares off the diagonal, by the union bound. *)
Theorem goe_mx_diag_max_tail (s : R) : 0 <= s ->
  (gauss (d * d) [set a | exists i, s <= `|goe_mx a i i|]%R <=
   (2 * d%:R * expR (- (d%:R * s ^+ 2 / 4)))%:E)%E.
Proof.
move=> s0.
have -> : [set a : 'rV[R]_(d * d) | exists i, (s <= `|goe_mx a i i|)%R] =
    \bigcup_i [set a | (s <= `|goe_mx a i i|)%R].
  apply/seteqP; split => a /= [i].
    by move=> h; exists i.
  by move=> _ h; exists i.
apply: le_trans (measure_bigcup_fin_le _
  (fun i => measurable_goe_entry_ge i i s)) _.
apply: (@le_trans _ _
  (\sum_(i < d) (2 * expR (- (d%:R * s ^+ 2 / 4)))%:E)%E).
  by apply: lee_sum => i _; exact: goe_mx_diag_tail.
rewrite sumEFin sumr_const card_ord lee_fin.
by rewrite -[_ *+ d]mulr_natr mulrAC.
Qed.

Theorem goe_mx_offdiag_max_tail (s : R) : 0 <= s ->
  (gauss (d * d)
     [set a | exists i j, i != j /\ s <= `|goe_mx a i j|]%R <=
   (2 * d%:R ^+ 2 * expR (- (d%:R * s ^+ 2 / 2)))%:E)%E.
Proof.
move=> s0.
pose G (p : 'I_d * 'I_d) : set 'rV[R]_(d * d) :=
  if p.1 == p.2 then set0 else [set a | s <= `|goe_mx a p.1 p.2|]%R.
have mG p : measurable (G p).
  rewrite /G; case: ifP => _; first exact: measurable0.
  exact: measurable_goe_entry_ge.
have -> : [set a : 'rV[R]_(d * d) |
    exists i j, i != j /\ (s <= `|goe_mx a i j|)%R] = \bigcup_p G p.
  apply/seteqP; split => a /=.
    by case=> i [j [ij h]]; exists (i, j) => //; rewrite /G /= (negbTE ij).
  case=> [[i j]] _; rewrite /G /=; case: eqP => // /eqP ij h.
  by exists i, j.
apply: le_trans (measure_bigcup_fin_le _ mG) _.
apply: (@le_trans _ _
  (\sum_(p : 'I_d * 'I_d) (2 * expR (- (d%:R * s ^+ 2 / 2)))%:E)%E).
  apply: lee_sum => [[i j]] _; rewrite /G /=; case: eqP => [_|/eqP ij].
    by rewrite measure0 lee_fin mulr_ge0 ?expR_ge0.
  exact: goe_mx_offdiag_tail.
rewrite sumEFin sumr_const card_prod !card_ord lee_fin.
by rewrite -[_ *+ (d * d)]mulr_natr natrM expr2 mulrAC.
Qed.

Theorem goe_mx_row_max_tail (u : R) : 0 < u ->
  (gauss (d * d)
     [set a | exists i, 1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R <=
   (d%:R * expR (- (d%:R * u ^+ 2 / (4 * (1 + u)))))%:E)%E.
Proof.
move=> u0.
have -> : [set a : 'rV[R]_(d * d) |
    exists i, (1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2)%R] =
    \bigcup_i [set a | (1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2)%R].
  apply/seteqP; split => a /= [i].
    by move=> h; exists i.
  by move=> _ h; exists i.
apply: le_trans (measure_bigcup_fin_le _
  (fun i => measurable_goe_row_ge i (1 + u))) _.
apply: (@le_trans _ _
  (\sum_(i < d) (expR (- (d%:R * u ^+ 2 / (4 * (1 + u)))))%:E)%E).
  by apply: lee_sum => i _; exact: goe_mx_row_tail.
rewrite sumEFin sumr_const card_ord lee_fin.
by rewrite -[_ *+ d]mulr_natr mulrC.
Qed.

End goe_entries.
