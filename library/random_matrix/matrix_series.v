From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_ibp.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.matrix Require Import psd_part.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.comparison Require Import gauss_concentration escape.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # Gaussian matrix series                                                   *)
(*                                                                            *)
(* For matrices H_1, ..., H_r in 'M[R]_n and g of law gauss r, the Gaussian   *)
(* matrix series X = \sum_j g_j H_j (written \sum_j g 0 j *: H j) has trace   *)
(* moments bounded by its variance S = \sum_j H_j^2 alone: no dimension of    *)
(* the matrices enters the bounds. Through the symmetric dilation of          *)
(* rectangular matrices, the same holds for the operator norm of              *)
(* \sum_j g_j B_j.                                                            *)
(*                                                                            *)
(* This file is a Rocq formalization of the credited argument of Lemma 4.2,   *)
(* "A Gaussian matrix estimate", of "Pointwise convergence of fourfold        *)
(* ergodic averages for mixing transformations" (OpenAI, 4 October 2026),     *)
(* family 154 of the OpenAI math collection at revision 1581d4cbd. The same   *)
(* lemma is in the section "Tensor packing" of its companion "Pointwise       *)
(* Multiple Ergodic Averages for Mixing Transformations". There is no Lean    *)
(* version. The formalization differs from the manuscript in four points:     *)
(* - the recursion holds for every q, and the manuscript states it for        *)
(*   q >= 2;                                                                  *)
(* - the trace inequality uses x^a y^b + y^a x^b <= x^(a+b) + y^(a+b) for     *)
(*   x, y >= 0, where the manuscript uses the weighted arithmetic-geometric   *)
(*   mean;                                                                    *)
(* - the hypotheses opnorm S <= sqrt d and tr S <= 2 d on the dilation S are  *)
(*   stated on its two diagonal blocks, \sum_j B_j B_j^T and                  *)
(*   \sum_j B_j^T B_j;                                                        *)
(* - the constant of the last bound is explicit, 5, with                      *)
(*   q = floor (ln (2 + d)) + 1, where the manuscript takes q >= 2 comparable *)
(*   to log (2 + d).                                                          *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - mxtrace_sandwich_le: |tr (K A^a K A^b)| <= tr (K^2 A^(a+b)) for K, A     *)
(*   symmetric and a + b even, in an eigenbasis of A; mxtrace_mul_psd_le:     *)
(*   tr (S T) <= opnorm S tr T for T positive semidefinite.                   *)
(* - moment_root_le, moment_root_powR: E f <= (E f^(k+1))^(1/(k+1)) for a     *)
(*   measurable f >= 0 and a probability, the integrals in the extended       *)
(*   reals, from Young's inequality with integer exponents (young_exprn).     *)
(* - gauss_mx_series_ibp: E tr X^(k+1) = \sum_j E tr (H_j D_j), where         *)
(*   D_j = mxpow_deriv X H_j k is the derivative of X^k along H_j, by         *)
(*   Gaussian integration by parts in each coordinate (gauss_ibp_polyfun,     *)
(*   is_derive_mxpow); gauss_mx_series_trace_sqr: E tr X^2 = tr S.            *)
(* - gauss_mx_series_trace_rec: for H_j symmetric,                            *)
(*   E tr X^(2q+2) <= (2q + 1) opnorm S E tr X^(2q).                          *)
(* - gauss_mx_series_moment: for H_j symmetric and q >= 1,                    *)
(*   E tr X^(2q) <= (2q - 1)!! opnorm S^(q-1) tr S, with                      *)
(*   (2q - 1)!! = \prod_(i < q) (2i + 1), the integral in the extended reals. *)
(* - sym_dilation B is symmetric, linear in B, with square                    *)
(*   block_mx (B B^T) 0 0 (B^T B), and opnorm B <= opnorm (sym_dilation B);   *)
(*   opnorm_block_diag_le: the operator norm of block_mx A 0 0 D is at most   *)
(*   the larger of opnorm A and opnorm D.                                     *)
(* - gauss_mx_series_opnorm_moment, gauss_mx_series_opnorm: for B_j in        *)
(*   'M[R]_(m, p) and q >= 1,                                                 *)
(*   E opnorm (\sum_j g_j B_j)^(2q) <= (2q - 1)!! sigma^(2(q-1)) tau, hence   *)
(*   E opnorm (\sum_j g_j B_j) <= ((2q - 1)!! sigma^(2(q-1)) tau)^(1/(2q)),   *)
(*   where                                                                    *)
(*   sigma^2 = max (opnorm (\sum_j B_j B_j^T), opnorm (\sum_j B_j^T B_j)) and *)
(*   tau = 2 tr (\sum_j B_j B_j^T).                                           *)
(* - gauss_mx_series_opnorm_log: if opnorm (\sum_j B_j B_j^T) and             *)
(*   opnorm (\sum_j B_j^T B_j) are at most sqrt d and                         *)
(*   tr (\sum_j B_j B_j^T) <= d for a real d >= 1, then                       *)
(*   E opnorm (\sum_j g_j B_j) <= 5 d^(1/4) sqrt (ln (2 + d)).                *)
(*                                                                            *)
(* ```                                                                        *)
(* sym_dilation B == the symmetric matrix [[0, B], [B^T, 0]] of size m + p of *)
(*                   B : 'M[R]_(m, p)                                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section trace_inequalities.
Context {R : realType} {n : nat}.

(* x^a y^b + y^a x^b <= x^(a+b) + y^(a+b) for x, y >= 0, since
   (x^a - y^a) (x^b - y^b) >= 0. *)
Lemma exprn_cross_le (x y : R) a b : 0 <= x -> 0 <= y ->
  x ^+ a * y ^+ b + y ^+ a * x ^+ b <= x ^+ (a + b) + y ^+ (a + b).
Proof.
move=> x0 y0.
have h : 0 <= (x ^+ a - y ^+ a) * (x ^+ b - y ^+ b).
  have [xy|yx] := leP x y.
    apply: mulr_le0; rewrite subr_le0; exact: lerXn2r.
  apply: mulr_ge0; rewrite subr_ge0; apply: lerXn2r => //; exact: ltW.
rewrite !exprD; move: h; set xa := x ^+ a; set xb := x ^+ b.
set ya := y ^+ a; set yb := y ^+ b; nra.
Qed.

Lemma mxtrace_diag_sandwich (C : 'M[R]_n) (x y : 'rV[R]_n) :
  \tr (C *m diag_mx x *m C *m diag_mx y) =
  \sum_u \sum_v C u v * C v u * (x 0 v * y 0 u).
Proof.
rewrite /mxtrace; apply: eq_bigr => u _.
rewrite mul_mx_diag mxE mxE mulr_suml; apply: eq_bigr => v _.
by rewrite mul_mx_diag mxE; ring.
Qed.

(* |tr (K A^a K A^b)| <= tr (K^2 A^(a+b)) for K, A symmetric and a + b even. In
   an eigenbasis of A, with C = P K P^T, the left side is at most
   \sum_(u, v) C_uv^2 |d_v|^a |d_u|^b, which exprn_cross_le and the symmetry
   of C bound by \sum_(u, v) C_uv^2 |d_u|^(a+b). *)
Lemma mxtrace_sandwich_le (K A : 'M[R]_n) a b :
  K \is symmetricmx -> A \is symmetricmx -> ~~ odd (a + b) ->
  `|\tr (K *m A ^+ a *m K *m A ^+ b)| <= \tr (K ^+ 2 *m A ^+ (a + b)).
Proof.
move=> /symmetricmxP KT Asym ev.
have [P Po [d AE]] := symmetric_spectral Asym.
set C := P *m K *m P^T.
have CT : C^T = C by rewrite /C !trmx_mul trmxK KT mulmxA.
have conj (x y : 'rV[R]_n) :
    \tr (K *m (P^T *m diag_mx x *m P) *m K *m (P^T *m diag_mx y *m P)) =
    \tr (C *m diag_mx x *m C *m diag_mx y).
  by rewrite !mulmxA mxtrace_mulC /C !mulmxA.
have I1 : P^T *m diag_mx (const_mx 1) *m P = 1%:M.
  by rewrite diag_const_mx mulmx1 orthogonalmxT.
have -> : \tr (K *m A ^+ a *m K *m A ^+ b) =
    \tr (C *m diag_mx (\row_i d 0 i ^+ a) *m C *m diag_mx (\row_i d 0 i ^+ b)).
  by rewrite (spectral_exp a Po AE) (spectral_exp b Po AE) conj.
have -> : \tr (K ^+ 2 *m A ^+ (a + b)) =
    \tr (C *m diag_mx (const_mx 1) *m C *m diag_mx (\row_i d 0 i ^+ (a + b))).
  by rewrite -conj I1 mulmx1 -(spectral_exp _ Po AE) expr2 mulmxE.
rewrite !mxtrace_diag_sandwich.
have Cs u v : C v u = C u v by rewrite -{1}CT mxE.
pose c u v := C u v ^+ 2.
have cs u v : c v u = c u v by rewrite /c Cs.
clearbody C.
pose e (u : 'I_n) : R := `|d 0 u|.
have e0 u : 0 <= e u by rewrite /e normr_ge0.
have es u : d 0 u ^+ (a + b) = e u ^+ (a + b).
  by rewrite /e -normrX ger0_norm // exprn_even_ge0.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_u \sum_v c u v * (e v ^+ a * e u ^+ b) <= _).
  apply: ler_sum => u _; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: ler_sum => v _; rewrite !mxE Cs -expr2 normrM !normrX.
  by rewrite real_normK ?num_real // Cs normrM !normrX.
have sw (F : 'I_n -> 'I_n -> R) :
    \sum_u \sum_v c u v * F u v = \sum_u \sum_v c u v * F v u.
  rewrite exchange_big; apply: eq_bigr => u _; apply: eq_bigr => v _.
  by rewrite cs.
under [X in _ <= X]eq_bigr do under eq_bigr do rewrite !mxE mul1r es Cs -expr2.
have -> : \sum_i \sum_i0 C i0 i ^+ 2 * e i ^+ (a + b) =
    \sum_u \sum_v c u v * e u ^+ (a + b).
  by apply: eq_bigr => u _; apply: eq_bigr => v _; rewrite -cs.
set T := \sum_u \sum_v c u v * (e v ^+ a * e u ^+ b).
set U := \sum_u \sum_v c u v * e u ^+ (a + b).
suff : T + T <= U + U by lra.
have TT : T = \sum_u \sum_v c u v * (e u ^+ a * e v ^+ b) :=
  sw (fun u v => e v ^+ a * e u ^+ b).
have UU : U = \sum_u \sum_v c u v * e v ^+ (a + b) :=
  sw (fun u v => e u ^+ (a + b)).
rewrite {2}TT {2}UU /T /U -!big_split /=; apply: ler_sum => u _.
rewrite -!big_split /=; apply: ler_sum => v _; rewrite -!mulrDr.
apply: ler_wpM2l; first exact: sqr_ge0.
by rewrite [X in _ <= X]addrC; exact: exprn_cross_le.
Qed.

(* tr (S T) <= opnorm S tr T for T positive semidefinite: in an eigenbasis
   of T, the diagonal entries of S are at most opnorm S. *)
Lemma mxtrace_mul_psd_le (S T : 'M[R]_n) : psdmx T ->
  \tr (S *m T) <= opnorm S * \tr T.
Proof.
move=> [Tsym Tpsd]; have [P Po [d TE]] := symmetric_spectral Tsym.
have d0 i : 0 <= d 0 i := (spectral_psd Po TE).1 Tpsd i.
have -> : \tr (S *m T) = \sum_i (P *m S *m P^T) i i * d 0 i.
  rewrite TE !mulmxA mxtrace_mulC !mulmxA /mxtrace; apply: eq_bigr => i _.
  by rewrite mul_mx_diag mxE.
rewrite (spectral_trace Po TE) mulr_sumr; apply: ler_sum => i _.
apply: (ler_wpM2r (d0 i)).
apply: le_trans (ler_norm _) _.
have d1 : frobenius (delta_mx i 0 : 'cV[R]_n) = 1.
  by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
have := mxdot_delta_opnorm (P *m S *m P^T) i i.
rewrite opnorm_orthogonalmxr ?trmx_orthogonal // opnorm_orthogonalmxl //.
by rewrite d1 !mulr1.
Qed.

Lemma psdmx_exp_even (A : 'M[R]_n) k : A \is symmetricmx -> psdmx (A ^+ k.*2).
Proof.
move=> Asym; have [P Po [d AE]] := symmetric_spectral Asym.
rewrite (spectral_exp _ Po AE); apply: psd_conj => // i.
by rewrite mxE exprn_even_ge0 // odd_double.
Qed.

End trace_inequalities.

Section moment_root.
Context d (T : measurableType d) (R : realType) (P : probability T R).

(* Young's inequality with integer exponents:
   (p + 1) x t^p <= p t^(p+1) + x^(p+1) for x, t >= 0. *)
Lemma young_exprn (x t : R) p : 0 <= x -> 0 <= t ->
  p.+1%:R * x * t ^+ p <= p%:R * t ^+ p.+1 + x ^+ p.+1.
Proof.
move=> x0 t0; elim: p => [|p IH].
  by rewrite !expr0 mul1r mulr1 mul0r add0r expr1.
have h1 := ler_wpM2l x0 IH.
have h2 : 0 <= p.+1%:R * t ^+ p * (x - t) ^+ 2.
  by rewrite mulr_ge0 ?sqr_ge0 // mulr_ge0 ?ler0n ?exprn_ge0.
rewrite -[p.+2%:R]natr1.
move: h1 h2; rewrite !exprS expr0 mulr1; set u := t ^+ p; set w := x ^+ p.
set a := p%:R; rewrite -[p.+1%:R]natr1 -/a => h1 h2.
have a0 : 0 <= a by exact: ler0n.
lra.
Qed.

(* The moment inequality E f <= (E f^(k+1))^(1/(k+1)) for f >= 0, in the
   form: E f^(k+1) <= t^(k+1) with t > 0 gives E f <= t. Integrate Young's
   inequality (k + 1) t^k f <= k t^(k+1) + f^(k+1). *)
Lemma moment_root_le (f : T -> R) k (t : R) : measurable_fun [set: T] f ->
  (forall x, 0 <= f x) -> 0 < t ->
  (\int[P]_x (f x ^+ k.+1)%:E <= (t ^+ k.+1)%:E)%E ->
  (\int[P]_x (f x)%:E <= t%:E)%E.
Proof.
move=> mf f0 t0 hk; set c := k.+1%:R * t ^+ k.
have c0 : 0 < c by rewrite mulr_gt0 ?ltr0n ?exprn_gt0.
have mfk := measurable_funX k.+1 mf.
have h1 : (\int[P]_x (c * f x)%:E = c%:E * \int[P]_x (f x)%:E)%E.
  under eq_integral do rewrite EFinM.
  apply: ge0_integralZl => //; first exact/measurable_EFinP.
  - by move=> x _; rewrite lee_fin.
  - by rewrite lee_fin ltW.
have h2 : (\int[P]_x (k%:R * t ^+ k.+1 + f x ^+ k.+1)%:E =
    (k%:R * t ^+ k.+1)%:E + \int[P]_x (f x ^+ k.+1)%:E)%E.
  under eq_integral do rewrite EFinD.
  rewrite ge0_integralD //.
  - by move=> x _; rewrite lee_fin mulr_ge0 ?ler0n ?exprn_ge0 ?ltW.
  - by move=> x _; rewrite lee_fin exprn_ge0.
  - exact/measurable_EFinP.
  by rewrite integral_cst //= probability_setT mule1.
have h3 : (\int[P]_x (c * f x)%:E <=
    \int[P]_x (k%:R * t ^+ k.+1 + f x ^+ k.+1)%:E)%E.
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin; apply: mulr_ge0 => //; exact: ltW.
  - by apply/measurable_EFinP; exact: measurable_funM.
  - by apply/measurable_EFinP; apply: measurable_funD.
  - move=> x _; rewrite lee_fin /c mulrAC.
    by apply: young_exprn => //; exact: ltW.
rewrite h1 h2 in h3.
have h4 : (c%:E * \int[P]_x (f x)%:E <= (c * t)%:E)%E.
  apply: le_trans h3 _; rewrite /c -mulrA -exprSr.
  apply: le_trans (leeD (lexx _) hk) _.
  by rewrite -EFinD lee_fin -[X in _ + X]mul1r -mulrDl natr1.
by move: h4; rewrite -lee_pdivlMl // -EFinM mulKf // gt_eqF.
Qed.

(* The same with a bound M of E f^(k+1): E f <= M^(1/(k+1)). *)
Lemma moment_root_powR (f : T -> R) k (M : R) : measurable_fun [set: T] f ->
  (forall x, 0 <= f x) ->
  (\int[P]_x (f x ^+ k.+1)%:E <= M%:E)%E ->
  (\int[P]_x (f x)%:E <= (M `^ k.+1%:R^-1)%:E)%E.
Proof.
move=> mf f0 hM.
have M0 : 0 <= M.
  rewrite -lee_fin; apply: le_trans hM; apply: integral_ge0 => x _.
  by rewrite lee_fin exprn_ge0.
have k0 : k.+1%:R^-1 != 0 :> R by rewrite invr_eq0 pnatr_eq0.
have [M00|Mp] := eqVneq M 0.
  rewrite M00 powR0 //; apply/lee_addgt0Pr => e e0; rewrite add0e.
  apply: moment_root_le => //; apply: le_trans hM _.
  by rewrite M00 lee_fin exprn_ge0 ?ltW.
have Mg : 0 < M by rewrite lt_def Mp.
apply: (moment_root_le (k := k)) => //; first by rewrite powR_gt0.
rewrite -powR_mulrn ?powR_ge0 // -powRrM mulVf ?pnatr_eq0 // powRr1 //.
Qed.

End moment_root.

Section gauss_mx_series.
Context {R : realType} {n r : nat}.
Local Notation gauss := (@gauss R).
Variable H : 'I_r -> 'M[R]_n.

Lemma series_sym (g : 'rV[R]_r) : (forall j, H j \is symmetricmx) ->
  \sum_j g 0 j *: H j \is symmetricmx.
Proof.
move=> Hs; apply/symmetricmxP; rewrite raddf_sum /=; apply: eq_bigr => j _.
by rewrite linearZ /=; have /symmetricmxP -> := Hs j.
Qed.

Lemma mx_polyfun_series : mx_polyfun (fun g : 'rV[R]_r => \sum_j g 0 j *: H j).
Proof.
move=> u v; under eq_fun do rewrite summxE.
apply: polyfun_sum => j; under eq_fun do rewrite mxE.
by apply: polyfunM; [exact: polyfun_coord | exact: polyfun_cst].
Qed.

Lemma series_lin (h : R) (x v : 'rV[R]_r) :
  \sum_j (h *: v + x) 0 j *: H j =
  h *: (\sum_j v 0 j *: H j) + \sum_j x 0 j *: H j.
Proof.
rewrite scaler_sumr -big_split /=; apply: eq_bigr => j _.
by rewrite !mxE scalerDl scalerA.
Qed.

Lemma series_delta (j : 'I_r) :
  \sum_l (delta_mx 0 j : 'rV[R]_r) 0 l *: H l = H j.
Proof.
rewrite (bigD1 j) //= big1 ?addr0.
  by move=> l lj; rewrite mxE eqxx (negbTE lj) scale0r.
by rewrite mxE !eqxx scale1r.
Qed.

Lemma is_derive_series_pow k (u v : 'I_n) (x w : 'rV[R]_r) :
  is_derive x w (fun g : 'rV[R]_r => ((\sum_l g 0 l *: H l) ^+ k) u v)
    (mxpow_deriv (\sum_l x 0 l *: H l) (\sum_l w 0 l *: H l) k u v).
Proof.
apply: (is_derive_transfer (G := fun M : 'M[R]_n => (M ^+ k) u v)
  (b := \sum_l x 0 l *: H l) (w := \sum_l w 0 l *: H l)).
  by move=> h; rewrite series_lin.
exact: is_derive_mxpow.
Qed.

(* Gaussian integration by parts in the coordinate g_j:
   E[g_j tr (A X^k)] = E[tr (A D_j)], where D_j is the derivative of X^k
   along H_j. *)
Lemma gauss_mx_series_ibp_coord k (j : 'I_r) (A : 'M[R]_n) :
  \int[gauss r]_g (g 0 j * \tr (A *m (\sum_l g 0 l *: H l) ^+ k)) =
  \int[gauss r]_g \tr (A *m mxpow_deriv (\sum_l g 0 l *: H l) (H j) k).
Proof.
have hX := mx_polyfun_series.
have pXk u v : polyfun (fun g : 'rV[R]_r => ((\sum_l g 0 l *: H l) ^+ k) v u).
  exact: mx_polyfun_exp.
have pD u v : polyfun (fun g : 'rV[R]_r =>
    mxpow_deriv (\sum_l g 0 l *: H l) (H j) k v u).
  exact: mx_polyfun_mxpow_deriv.
have tE (M : 'M[R]_n) : \tr (A *m M) = \sum_u \sum_v A u v * M v u.
  by rewrite /mxtrace; apply: eq_bigr => u _; rewrite mxE.
under eq_Rintegral do rewrite tE mulr_sumr.
under [RHS]eq_Rintegral do rewrite tE.
under eq_Rintegral do under eq_bigr do rewrite mulr_sumr.
under eq_Rintegral do under eq_bigr do under eq_bigr do rewrite mulrCA.
rewrite Rintegral_polyfun_sum.
  move=> u; apply: polyfun_sum => v; apply: polyfunM; first exact: polyfun_cst.
  by apply: polyfunM; [exact: polyfun_coord | exact: pXk].
rewrite Rintegral_polyfun_sum.
  move=> u; apply: polyfun_sum => v; apply: polyfunM; first exact: polyfun_cst.
  exact: pD.
apply: eq_bigr => u _; rewrite Rintegral_polyfun_sum.
  move=> v; apply: polyfunM; first exact: polyfun_cst.
  by apply: polyfunM; [exact: polyfun_coord | exact: pXk].
rewrite Rintegral_polyfun_sum.
  by move=> v; apply: polyfunM; [exact: polyfun_cst | exact: pD].
apply: eq_bigr => v _; rewrite !Rintegral_polyfunZ.
- exact: pD.
- by apply: polyfunM; [exact: polyfun_coord | exact: pXk].
congr (_ * _).
have hd (x : 'rV[R]_r) := is_derive_series_pow k v u x (delta_mx 0 j).
rewrite series_delta in hd.
exact: gauss_ibp_polyfun hd (pXk u v) (pD u v).
Qed.

(* E tr X^(k+1) = \sum_j E tr (H_j D_j), with D_j the derivative of X^k along
   H_j: Gaussian integration by parts in every coordinate. *)
Lemma gauss_mx_series_ibp k :
  \int[gauss r]_g \tr ((\sum_j g 0 j *: H j) ^+ k.+1) =
  \sum_j \int[gauss r]_g \tr (H j *m mxpow_deriv (\sum_l g 0 l *: H l) (H j) k).
Proof.
have hX := mx_polyfun_series.
have htr (g : 'rV[R]_r) : \tr ((\sum_j g 0 j *: H j) ^+ k.+1) =
    \sum_j g 0 j * \tr (H j *m (\sum_l g 0 l *: H l) ^+ k).
  rewrite exprS -mulmxE mulmx_suml raddf_sum /=; apply: eq_bigr => j _.
  by rewrite -scalemxAl mxtraceZ.
under eq_Rintegral do rewrite htr.
rewrite Rintegral_polyfun_sum.
  move=> j; apply: polyfunM; first exact: polyfun_coord.
  apply: polyfun_trace; apply: mx_polyfun_mul; first exact: mx_polyfun_cst.
  exact: mx_polyfun_exp.
by apply: eq_bigr => j _; exact: gauss_mx_series_ibp_coord.
Qed.

(* E tr X^2 = tr S. *)
Lemma gauss_mx_series_trace_sqr :
  \int[gauss r]_g \tr ((\sum_j g 0 j *: H j) ^+ 2) = \tr (\sum_j H j ^+ 2).
Proof.
rewrite gauss_mx_series_ibp raddf_sum /=; apply: eq_bigr => j _.
under eq_Rintegral do rewrite /mxpow_deriv big_ord1 !expr0 mul1mx mulmx1.
rewrite Rintegral_cst // -[X in fine X]/(gauss r setT) probability_setT /=.
by rewrite mulr1 expr2 mulmxE.
Qed.

(* The recursion E tr X^(2q+2) <= (2q+1) opnorm S E tr X^(2q). *)
Theorem gauss_mx_series_trace_rec q : (forall j, H j \is symmetricmx) ->
  \int[gauss r]_g \tr ((\sum_j g 0 j *: H j) ^+ q.+1.*2) <=
  q.*2.+1%:R * opnorm (\sum_j H j ^+ 2) *
    \int[gauss r]_g \tr ((\sum_j g 0 j *: H j) ^+ q.*2).
Proof.
move=> Hs; have hX := mx_polyfun_series.
have -> : q.+1.*2 = (q.*2.+1).+1 by rewrite doubleS.
rewrite gauss_mx_series_ibp -Rintegral_polyfun_sum.
  move=> j; apply: polyfun_trace; apply: mx_polyfun_mul.
    exact: mx_polyfun_cst.
  exact: mx_polyfun_mxpow_deriv.
rewrite -Rintegral_polyfunZ; first exact: polyfun_trace (mx_polyfun_exp _ hX).
apply: le_Rintegral => //.
- apply: integrable_polyfun; apply: polyfun_sum => j; apply: polyfun_trace.
  apply: mx_polyfun_mul; first exact: mx_polyfun_cst.
  exact: mx_polyfun_mxpow_deriv.
- apply: integrable_polyfun; apply: polyfunM; first exact: polyfun_cst.
  exact: polyfun_trace (mx_polyfun_exp _ hX).
move=> g _; set X := \sum_l g 0 l *: H l.
have Xs : X \is symmetricmx by exact: series_sym.
have step j : \tr (H j *m mxpow_deriv X (H j) q.*2.+1) <=
    q.*2.+1%:R * \tr (H j ^+ 2 *m X ^+ q.*2).
  apply: le_trans (_ : \sum_(a < q.*2.+1) \tr (H j ^+ 2 *m X ^+ q.*2) <= _);
    last by rewrite sumr_const card_ord mulr_natl.
  rewrite /mxpow_deriv mulmx_sumr raddf_sum /=; apply: ler_sum => a _.
  have aq : (a <= q.*2)%N by rewrite -ltnS.
  rewrite !mulmxA; apply: le_trans (ler_norm _) _.
  rewrite -[in X in _ <= X](subnKC aq); apply: mxtrace_sandwich_le => //.
  by rewrite subnKC // odd_double.
apply: le_trans (ler_sum _ (fun j _ => step j)) _.
rewrite -mulr_sumr -raddf_sum /= -mulmx_suml -mulrA.
apply: ler_wpM2l; first exact: ler0n.
exact: mxtrace_mul_psd_le (psdmx_exp_even _ Xs).
Qed.

Lemma gauss_mx_series_trace_le q : (forall j, H j \is symmetricmx) ->
  (0 < q)%N ->
  \int[gauss r]_g \tr ((\sum_j g 0 j *: H j) ^+ q.*2) <=
  (\prod_(i < q) i.*2.+1%:R) * opnorm (\sum_j H j ^+ 2) ^+ q.-1 *
    \tr (\sum_j H j ^+ 2).
Proof.
move=> Hs; case: q => // q _; elim: q => [|q IH].
  by rewrite big_ord1 mul1r expr0 mul1r gauss_mx_series_trace_sqr.
apply: le_trans (gauss_mx_series_trace_rec q.+1 Hs) _.
set o := opnorm (\sum_j H j ^+ 2).
have o0 : 0 <= o := opnorm_ge0 _.
apply: le_trans (_ : q.+1.*2.+1%:R * o *
    ((\prod_(i < q.+1) i.*2.+1%:R) * o ^+ q * \tr (\sum_j H j ^+ 2)) <= _).
  by apply: ler_wpM2l IH; rewrite mulr_ge0 ?ler0n.
rewrite [in X in _ <= X]big_ord_recr /= exprS.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(* The moment bound E tr X^(2q) <= (2q - 1)!! opnorm S^(q-1) tr S, as an
   integral of a nonnegative function in the extended reals. *)
Theorem gauss_mx_series_moment q : (forall j, H j \is symmetricmx) ->
  (0 < q)%N ->
  (\int[gauss r]_g (\tr ((\sum_j g 0 j *: H j) ^+ q.*2))%:E <=
   ((\prod_(i < q) i.*2.+1%:R) * opnorm (\sum_j H j ^+ 2) ^+ q.-1 *
     \tr (\sum_j H j ^+ 2))%:E)%E.
Proof.
move=> Hs q0.
have iX := integrable_polyfun (polyfun_trace (mx_polyfun_exp q.*2
  mx_polyfun_series)).
rewrite -(fineK (integrable_fin_num measurableT iX)) lee_fin.
exact: gauss_mx_series_trace_le.
Qed.

End gauss_mx_series.

Section sym_dilation.
Context {R : realType}.

(* The symmetric dilation [[0, B], [B^T, 0]] of a rectangular matrix. *)
Definition sym_dilation m p (B : 'M[R]_(m, p)) : 'M[R]_(m + p) :=
  block_mx 0 B B^T 0.

Lemma sym_dilation_sym m p (B : 'M[R]_(m, p)) : sym_dilation B \is symmetricmx.
Proof.
by apply/symmetricmxP; rewrite /sym_dilation tr_block_mx trmxK !trmx0.
Qed.

Lemma sym_dilation_series m p r (g : 'rV[R]_r) (B : 'I_r -> 'M[R]_(m, p)) :
  sym_dilation (\sum_j g 0 j *: B j) = \sum_j g 0 j *: sym_dilation (B j).
Proof.
have sdD (A C : 'M[R]_(m, p)) :
    sym_dilation (A + C) = sym_dilation A + sym_dilation C.
  by rewrite /sym_dilation add_block_mx !addr0 linearD.
have sd0 : sym_dilation (0 : 'M[R]_(m, p)) = 0.
  by rewrite /sym_dilation trmx0 block_mx0.
rewrite (big_morph _ sdD sd0); apply: eq_bigr => j _.
by rewrite /sym_dilation scale_block_mx !scaler0 linearZ.
Qed.

Lemma sym_dilation_sqr m p (B : 'M[R]_(m, p)) :
  sym_dilation B ^+ 2 = block_mx (B *m B^T) 0 0 (B^T *m B).
Proof.
rewrite expr2 -mulmxE /sym_dilation mulmx_block.
by rewrite !mulmx0 !mul0mx !addr0 !add0r.
Qed.

Lemma mxdot_col_mx m1 m2 n (A C : 'M[R]_(m1, n)) (B D : 'M[R]_(m2, n)) :
  mxdot (col_mx A B) (col_mx C D) = mxdot A C + mxdot B D.
Proof.
rewrite /mxdot big_split_ord /=; congr (_ + _); apply: eq_bigr => i _;
  by apply: eq_bigr => j _; rewrite ?col_mxEu ?col_mxEd.
Qed.

Lemma mxdot_mulmx_opnorm_le m n (N : 'M[R]_(m, n)) (y : 'cV[R]_n) (b : R) :
  opnorm N <= b -> mxdot (N *m y) (N *m y) <= b ^+ 2 * mxdot y y.
Proof.
move=> Nb; have b0 : 0 <= b := le_trans (opnorm_ge0 N) Nb.
rewrite -!frobenius_sqr -exprMn ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 //.
apply: le_trans (frobenius_mulmx_opnorm N y) _.
exact: (ler_wpM2r (frobenius_ge0 y) Nb).
Qed.

Lemma opnorm_block_diag_le m1 n1 m2 n2 (A : 'M[R]_(m1, n1))
    (D : 'M[R]_(m2, n2)) :
  opnorm (block_mx A 0 0 D) <= Num.max (opnorm A) (opnorm D).
Proof.
set M := Num.max (opnorm A) (opnorm D).
have M0 : 0 <= M by rewrite le_max opnorm_ge0.
apply/opnorm_leP => // x; rewrite -[x]vsubmxK mul_block_col !mul0mx addr0 add0r.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // exprMn !frobenius_sqr.
rewrite !mxdot_col_mx mulrDr; apply: lerD; apply: mxdot_mulmx_opnorm_le.
  by rewrite le_max lexx.
by rewrite le_max lexx orbT.
Qed.

Lemma opnorm_le_sym_dilation m p (B : 'M[R]_(m, p)) :
  opnorm B <= opnorm (sym_dilation B).
Proof.
apply/opnorm_leP; first exact: opnorm_ge0.
move=> x; have := frobenius_mulmx_opnorm (sym_dilation B) (col_mx 0 x).
rewrite /sym_dilation mul_block_col !mul0mx mulmx0 !add0r.
have fc m' p' (u : 'cV[R]_m') (w : 'cV[R]_p') :
    frobenius (col_mx u w) = Num.sqrt (mxdot u u + mxdot w w).
  by rewrite /frobenius mxdot_col_mx.
by rewrite !fc !mxdot0l addr0 add0r.
Qed.

End sym_dilation.

Section series_log_bound.
Context {R : realType}.

Lemma expR1_le4 : expR 1 <= 4 :> R.
Proof.
have h : 2^-1 <= expR (- 2^-1) :> R by apply: le_trans (expR_ge1Dx _); lra.
have h2 : expR (2^-1) <= 2 :> R.
  rewrite -[expR _]invrK -expRN.
  by rewrite -[2 in leRHS]invrK lef_pV2 ?posrE ?expR_gt0 ?invr_gt0.
have -> : expR 1 = expR (2^-1) ^+ 2 :> R.
  by rewrite -expRM_natl mulfV ?pnatr_eq0.
have -> : 4 = 2 ^+ 2 :> R by rewrite expr2; lra.
by rewrite lerXn2r ?nnegrE ?expR_ge0.
Qed.

(* ln x >= 1 - 1 / x, at x = 2 + d >= 3. *)
Lemma ln2D_ge (d : R) : 1 <= d -> 2 / 3 <= ln (2 + d).
Proof.
move=> d1; have x0 : 0 < 2 + d by lra.
have := expR_ge1Dx (- ln (2 + d)); rewrite expRN lnK ?posrE //.
have : (2 + d)^-1 <= 3^-1 by rewrite lef_pV2 ?posrE //; lra.
lra.
Qed.

(* The arithmetic of the choice q = floor (ln (2 + d)) + 1: if s2 <= sqrt d
   and tau <= 2 d with d >= 1, then (2q - 1)!! s2^(q-1) tau <=
   (5 d^(1/4) sqrt (ln (2 + d)))^(2q). *)
Lemma series_log_bound (d s2 tau : R) : 1 <= d -> 0 <= s2 ->
  s2 <= Num.sqrt d -> 0 <= tau -> tau <= 2 * d ->
  (\prod_(i < (truncn (ln (2 + d))).+1) i.*2.+1%:R) *
    s2 ^+ truncn (ln (2 + d)) * tau <=
  (5 * d `^ 4^-1 * Num.sqrt (ln (2 + d))) ^+ (truncn (ln (2 + d))).+1.*2.
Proof.
move=> d1 s0 sd t0 td.
set L := ln (2 + d); set k := truncn L; set q := k.+1.
have L23 : 2 / 3 <= L := ln2D_ge d1.
have L0 : 0 <= L by move: L23; clear; lra.
have qL : L < q%:R := truncnS_gt L.
have Lq : q%:R <= L + 1 by rewrite /q -natr1 lerD2r truncn_le.
set y := d `^ 4^-1; set e := Num.sqrt d.
have d0 : 0 < d by lra.
have e1 : 1 <= e by rewrite -sqrtr1 ler_wsqrtr.
have e0 : 0 <= e by lra.
have ee : e * e = d by rewrite -expr2 sqr_sqrtr; lra.
have y2 : y ^+ 2 = e.
  rewrite /y -powR_mulrn ?powR_ge0 // -powRrM (_ : 4^-1 * 2%:R = 2^-1).
    by field.
  by rewrite powR12_sqrt // ltW.
(* (2q - 1)!! <= (2q)^q *)
have P_le : \prod_(i < q) i.*2.+1%:R <= q.*2%:R ^+ q :> R.
  have -> : q.*2%:R ^+ q = \prod_(i < q) (q.*2%:R : R).
    by rewrite prodr_const card_ord.
  by apply: ler_prod => i _; rewrite ler0n ler_nat /= ltn_double.
(* 2 sqrt d <= 2 + d = exp L <= e^q <= 4^q *)
have e4 : 2 * e <= 4 ^+ q.
  have h1 : 2 * e <= 2 + d by have := sqr_ge0 (e - 1); rewrite -ee; nra.
  have h2 : 2 + d = expR L by rewrite lnK // posrE; lra.
  have h3 : expR L <= expR 1 ^+ q by rewrite -expRM_natl mulr1 ler_expR ltW.
  have h4 : expR 1 ^+ q <= 4 ^+ q :> R.
    by rewrite lerXn2r ?nnegrE ?expR_ge0 ?expR1_le4.
  by apply: le_trans h1 _; rewrite h2; exact: le_trans h3 h4.
(* 8 q <= 20 L, since q <= L + 1 and L >= 2 / 3 *)
have q8 : q.*2%:R * e * 4 <= 25 * L * e.
  have hq : q.*2%:R = 2 * q%:R :> R by rewrite -muln2 natrM mulrC.
  rewrite hq [_ * e]mulrC [25 * L * e]mulrC -mulrA; apply: ler_wpM2l => //.
  by move: Lq L23; clear; lra.
have -> : (5 * y * Num.sqrt L) ^+ q.*2 = (25 * L * e) ^+ q.
  rewrite -mul2n exprM; congr (_ ^+ _).
  by rewrite !exprMn y2 sqr_sqrtr // expr2 -natrM mulrAC.
apply: le_trans (_ : q.*2%:R ^+ q * e ^+ k * (2 * d) <= _).
  apply: ler_pM => //; first by rewrite mulr_ge0 ?exprn_ge0 // prodr_ge0.
  apply: ler_pM => //; first by rewrite prodr_ge0.
    exact: exprn_ge0.
  by rewrite lerXn2r ?nnegrE.
have -> : q.*2%:R ^+ q * e ^+ k * (2 * d) = q.*2%:R ^+ q * e ^+ q * (2 * e).
  have -> : e ^+ q = e ^+ k * e by rewrite /q exprSr.
  by rewrite -ee; move: (q.*2%:R ^+ q) (e ^+ k) => a b; ring.
apply: le_trans (_ : q.*2%:R ^+ q * e ^+ q * 4 ^+ q <= _).
  by apply: ler_wpM2l e4; rewrite mulr_ge0 ?exprn_ge0.
by rewrite -!exprMn lerXn2r ?nnegrE ?mulr_ge0.
Qed.

End series_log_bound.

Section gauss_mx_series_rect.
Context {R : realType} {m p r : nat}.
Local Notation gauss := (@gauss R).
Variable B : 'I_r -> 'M[R]_(m, p).

Lemma series_opnorm_lipschitz (g h : 'rV[R]_r) :
  `|opnorm (\sum_j g 0 j *: B j) - opnorm (\sum_j h 0 j *: B j)| <=
  (\sum_j frobenius (B j)) * frobenius (g - h).
Proof.
apply: le_trans (opnorm_lipschitz _ _) _; rewrite -sumrB mulr_suml.
elim/big_ind2: _ => [|A a C c hA hC|j _].
- by rewrite frobenius0.
- by apply: le_trans (frobeniusD _ _) _; exact: lerD.
rewrite -scalerBl frobeniusZ mulrC.
apply: ler_wpM2l; first exact: frobenius_ge0.
by have := frobenius_entry (g - h) 0 j; rewrite !mxE.
Qed.

Lemma measurable_series_opnorm :
  measurable_fun [set: 'rV[R]_r] (fun g => opnorm (\sum_j g 0 j *: B j)).
Proof.
apply: continuous_measurable_mx.
exact: lipschitz_frobenius_continuous series_opnorm_lipschitz.
Qed.

(* E opnorm (\sum_j g_j B_j)^(2q) <= (2q - 1)!! sigma^(2(q-1)) tau, with
   sigma^2 = max (opnorm (\sum_j B_j B_j^T)) (opnorm (\sum_j B_j^T B_j)) and
   tau = 2 tr (\sum_j B_j B_j^T), through the symmetric dilation. *)
Theorem gauss_mx_series_opnorm_moment q : (0 < q)%N ->
  (\int[gauss r]_g (opnorm (\sum_j g 0 j *: B j) ^+ q.*2)%:E <=
   ((\prod_(i < q) i.*2.+1%:R) *
     Num.max (opnorm (\sum_j B j *m (B j)^T)) (opnorm (\sum_j (B j)^T *m B j))
       ^+ q.-1 * (2 * \tr (\sum_j B j *m (B j)^T)))%:E)%E.
Proof.
move=> q0; pose H j := sym_dilation (B j).
have Hs j : H j \is symmetricmx := sym_dilation_sym (B j).
have SE : \sum_j H j ^+ 2 =
    block_mx (\sum_j B j *m (B j)^T) 0 0 (\sum_j (B j)^T *m B j).
  rewrite /H; under eq_bigr do rewrite sym_dilation_sqr.
  elim/big_rec3: _ => [|j A C D _ ->]; first by rewrite block_mx0.
  by rewrite add_block_mx !addr0.
have tS : \tr (\sum_j H j ^+ 2) = 2 * \tr (\sum_j B j *m (B j)^T).
  rewrite SE mxtrace_block mulr_natl mulr2n; congr (_ + _).
  by rewrite !raddf_sum /=; apply: eq_bigr => j _; rewrite mxtrace_mulC.
have tS0 : 0 <= \tr (\sum_j H j ^+ 2).
  rewrite raddf_sum /=; apply: sumr_ge0 => j _.
  have /symmetricmxP HT := Hs j.
  rewrite expr2 -mulmxE -[X in X *m _]HT.
  by rewrite mxtrace_mulC -mxdot_trace mxdot_ge0.
apply: le_trans (_ : \int[gauss r]_g
    (\tr ((\sum_j g 0 j *: H j) ^+ q.*2))%:E <= _)%E.
  apply: ge0_le_integral => //.
  - by move=> g _; rewrite lee_fin exprn_ge0 ?opnorm_ge0.
  - apply/measurable_EFinP; apply: measurable_funX.
    exact: measurable_series_opnorm.
  - apply/measurable_EFinP; apply: continuous_measurable_mx.
    exact: (polyfun_trace (mx_polyfun_exp _ (mx_polyfun_series H))).1.
  move=> g _; rewrite lee_fin -sym_dilation_series.
  apply: le_trans
    (_ : opnorm (sym_dilation (\sum_j g 0 j *: B j)) ^+ q.*2 <= _).
    by rewrite lerXn2r ?nnegrE ?opnorm_ge0 ?opnorm_le_sym_dilation.
  by case: q q0 => // k _; exact: opnorm_exp_le_trace (sym_dilation_sym _).
apply: le_trans (gauss_mx_series_moment Hs q0) _; rewrite lee_fin -tS.
apply: (ler_wpM2r tS0); apply: ler_wpM2l; first by apply: prodr_ge0 => i _.
rewrite lerXn2r ?nnegrE ?opnorm_ge0 //; first by rewrite le_max opnorm_ge0.
by rewrite SE opnorm_block_diag_le.
Qed.

(* The rectangular bound: E opnorm (\sum_j g_j B_j) <=
   ((2q - 1)!! sigma^(2(q-1)) tau)^(1/(2q)) for every q >= 1. No dimension
   of the matrices appears. *)
Theorem gauss_mx_series_opnorm q : (0 < q)%N ->
  (\int[gauss r]_g (opnorm (\sum_j g 0 j *: B j))%:E <=
   (((\prod_(i < q) i.*2.+1%:R) *
     Num.max (opnorm (\sum_j B j *m (B j)^T)) (opnorm (\sum_j (B j)^T *m B j))
       ^+ q.-1 * (2 * \tr (\sum_j B j *m (B j)^T))) `^ (q.*2%:R)^-1)%:E)%E.
Proof.
move=> q0; have := gauss_mx_series_opnorm_moment q0.
case: q q0 => // k _ h; apply: (moment_root_powR (k := k.*2.+1)) => //.
- exact: measurable_series_opnorm.
- by move=> g; exact: opnorm_ge0.
Qed.

(* The form of Lemma 4.2 of the fourfold paper of family 154, with C = 5:
   E opnorm (\sum_j g_j B_j) <= 5 d^(1/4) sqrt (ln (2 + d)) when the
   diagonal blocks \sum_j B_j B_j^T and \sum_j B_j^T B_j of the dilation S
   have operator norms at most sqrt d and tr (\sum_j B_j B_j^T) <= d, that is
   opnorm S <= sqrt d and tr S <= 2 d, for a real d >= 1. The proof takes
   q = floor (ln (2 + d)) + 1 in gauss_mx_series_opnorm_moment. *)
Theorem gauss_mx_series_opnorm_log (d : R) : 1 <= d ->
  opnorm (\sum_j B j *m (B j)^T) <= Num.sqrt d ->
  opnorm (\sum_j (B j)^T *m B j) <= Num.sqrt d ->
  \tr (\sum_j B j *m (B j)^T) <= d ->
  (\int[gauss r]_g (opnorm (\sum_j g 0 j *: B j))%:E <=
   (5 * d `^ 4^-1 * Num.sqrt (ln (2 + d)))%:E)%E.
Proof.
move=> d1 hs1 hs2 ht; set q := (truncn (ln (2 + d))).+1.
have := gauss_mx_series_opnorm_moment (isT : (0 < q)%N).
have -> : q.*2 = q.*2.-1.+1 by [].
move=> h; apply: (moment_root_le (k := q.*2.-1)) => //.
- exact: measurable_series_opnorm.
- by move=> g; exact: opnorm_ge0.
- have L0 : 0 < ln (2 + d) by apply: lt_le_trans (ln2D_ge d1); lra.
  by rewrite !mulr_gt0 ?powR_gt0 ?sqrtr_gt0 //; lra.
apply: le_trans h _; rewrite lee_fin /=.
have t0 : 0 <= \tr (\sum_j B j *m (B j)^T).
  rewrite raddf_sum /=; apply: sumr_ge0 => j _.
  by rewrite -mxdot_trace mxdot_ge0.
apply: series_log_bound => //.
- by rewrite le_max opnorm_ge0.
- by rewrite ge_max hs1 hs2.
- by rewrite mulr_ge0.
- by rewrite ler_pM2l.
Qed.

End gauss_mx_series_rect.
