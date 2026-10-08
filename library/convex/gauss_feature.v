From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals ereal exp.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import real_spectral gauss gauss_moments.
From GaussianAnalysis Require Import gauss_law lindeberg tuple_rows efron_stein.
From GaussianAnalysis Require Import least_squares feature_moments.

(**md**************************************************************************)
(* # Gaussian features are regular                                            *)
(*                                                                            *)
(* (2.10) of Koehler and Sohn (arXiv 2608.27372): the centered Gaussian law   *)
(* with covariance S^T S, the law of x S for x of law gauss k, is a           *)
(* (3^(1/4), sqrt 2 opnorm (S^T S))-regular feature (regular_feature of       *)
(* least_squares.v) when S != 0. The moments needed are those of the          *)
(* quadratic forms of a standard Gaussian vector.                             *)
(*                                                                            *)
(* - gauss_quad_moments: for A symmetric and x of law gauss k,                *)
(*   E x A x^T = tr A and E (x A x^T)^2 = (tr A)^2 + 2 |A|_F^2, by the        *)
(*   spectral theorem and the invariance of gauss k under orthogonal maps.    *)
(* - gauss_mxdot_moments: E <x, a> = 0, E <x, a> <x, b> = <a, b> and          *)
(*   E <x, a>^4 = 3 |a|^4.                                                    *)
(* - gauss_regular_feature: (2.10), for a law nu given by its values,         *)
(*   nu A = gauss k [set x | A (x S)].                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gauss_quadratic.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma mxdot_self_le_norm k (x : 'rV[R]_k) : mxdot x x <= k%:R * `|x| ^+ 2.
Proof.
rewrite /mxdot big_ord1.
apply: le_trans (_ : \sum_(j < k) `|x| ^+ 2 <= _); last first.
  by rewrite sumr_const card_ord mulr_natl.
apply: ler_sum => j _.
rewrite -expr2 -real_normK ?num_real // ler_sqr ?nnegrE ?normr_ge0 //.
exact: mx_norm_entry_le.
Qed.

(* Domination by a + b |x|^4. *)
Lemma gauss_integrable4 k (g : 'rV[R]_k -> R) (a b : R) :
  measurable_fun setT g -> (forall x, `|g x| <= a + b * mxdot x x ^+ 2) ->
  (gauss k).-integrable setT (EFin \o g).
Proof.
move=> mg gb.
apply: (integrable_gauss_poly (C := `|a| + `|b| * k%:R ^+ 2) (k := 4)) => // x.
apply: le_trans (gb x) _.
have m0 := mxdot_ge0 x.
have m1 := mxdot_self_le_norm x.
have n0 : 0 <= `|x| := normr_ge0 x.
have h1 : mxdot x x ^+ 2 <= k%:R ^+ 2 * `|x| ^+ 4.
  have -> : k%:R ^+ 2 * `|x| ^+ 4 = (k%:R * `|x| ^+ 2) ^+ 2.
    by rewrite exprMn -exprM.
  by rewrite ler_sqr ?nnegrE // (le_trans m0 m1).
have h2 : b * mxdot x x ^+ 2 <= `|b| * (k%:R ^+ 2 * `|x| ^+ 4).
  apply: le_trans (ler_norm _) _.
  rewrite normrM [`|mxdot x x ^+ 2|]ger0_norm ?sqr_ge0 //.
  by apply: ler_wpM2l => //; exact: normr_ge0.
have h3 : a <= `|a| := ler_norm a.
have x4 : 0 <= `|x| ^+ 4 by rewrite exprn_ge0.
have k2 : 0 <= (k%:R : R) ^+ 2 by rewrite sqr_ge0.
have kb : 0 <= `|b| * k%:R ^+ 2 by rewrite mulr_ge0.
have ab : 0 <= `|a| * `|x| ^+ 4 by rewrite mulr_ge0.
have e : `|b| * (k%:R ^+ 2 * `|x| ^+ 4) = `|b| * k%:R ^+ 2 * `|x| ^+ 4.
  by rewrite mulrA.
nra.
Qed.

Lemma gauss_coord_moments k (j l : 'I_k) :
  \int[gauss k]_y (y 0 j ^+ 2 * y 0 l ^+ 2) = (if j == l then 3 else 1 : R).
Proof.
have N2 : (\int[N]_t (t ^+ 2)%:E = 1)%E.
  by have := @normal_moment_even R 1; rewrite big_ord1.
have N4 : (\int[N]_t (t ^+ 4)%:E = 3%:R%:E)%E.
  by have := @normal_moment_even R 2; rewrite big_ord_recr big_ord1 /= mul1r.
have m2 : measurable_fun setT (fun t : R => t ^+ 2) by apply: measurable_funX.
case: eqP => [<-|/eqP jl].
  under eq_Rintegral do rewrite -exprD.
  rewrite /Rintegral (ge0_integral_gauss_coord j (f := fun t => (t ^+ 4)%:E)).
  - by apply/measurable_EFinP; apply: measurable_funX.
  - by move=> t; rewrite lee_fin exprn_even_ge0.
  - by rewrite N4.
(* two different coordinates are independent *)
pose f (i : 'I_k) (t : R) :=
  if i == j then t ^+ 2 else if i == l then t ^+ 2 else 1.
have lj : (l == j) = false by apply/negbTE; rewrite eq_sym.
have prodE (y : 'rV[R]_k) :
    \prod_(i < k) f i (y 0 i) = y 0 j ^+ 2 * y 0 l ^+ 2.
  rewrite (bigD1 j) //= (bigD1 l) /=; first by rewrite lj.
  rewrite /f eqxx lj eqxx.
  rewrite big1 ?mulr1 // => i /andP[ij il].
  by rewrite (negbTE ij) (negbTE il).
have mf i : measurable_fun setT (f i).
  rewrite /f; case: (i == j); first exact: m2.
  by case: (i == l); [exact: m2 | exact: measurable_cst].
have f0 i t : 0 <= f i t.
  rewrite /f; case: (i == j); first exact: sqr_ge0.
  by case: (i == l); [exact: sqr_ge0 | exact: ler01].
under eq_Rintegral do rewrite -prodE.
rewrite /Rintegral (ge0_integral_gauss_prod mf f0).
rewrite (bigD1 j) //= (bigD1 l) /=; first by rewrite lj.
rewrite /f eqxx lj eqxx N2 mul1e mul1e.
rewrite big1 //= => i /andP[ij il].
rewrite (negbTE ij) (negbTE il).
by rewrite integral_cst //= probability_setT mule1.
Qed.

Lemma gauss_diag_moments k (d : 'rV[R]_k) :
  \int[gauss k]_y (\sum_j d 0 j * y 0 j ^+ 2) = \sum_j d 0 j /\
  \int[gauss k]_y (\sum_j d 0 j * y 0 j ^+ 2) ^+ 2 =
    (\sum_j d 0 j) ^+ 2 + 2 * \sum_j d 0 j ^+ 2.
Proof.
have mj (j : 'I_k) : measurable_fun setT (fun y : 'rV[R]_k => y 0 j).
  exact: measurable_mxentry.
have iy2 (j : 'I_k) : (gauss k).-integrable setT
    (EFin \o (fun y : 'rV[R]_k => y 0 j ^+ 2)).
  apply: (@gauss_integrable4 k _ 1 1); first exact: measurable_funX.
  move=> y; rewrite ger0_norm ?sqr_ge0 // mul1r.
  by have := mxdot_entry y 0 j; have := le1_sqr (mxdot_ge0 y); lra.
have iy4 (j l : 'I_k) : (gauss k).-integrable setT
    (EFin \o (fun y : 'rV[R]_k => y 0 j ^+ 2 * y 0 l ^+ 2)).
  apply: (@gauss_integrable4 k _ 0 1).
    by apply: measurable_funM; exact: measurable_funX.
  move=> y.
  have p0 : 0 <= y 0 j ^+ 2 * y 0 l ^+ 2 by rewrite mulr_ge0 ?sqr_ge0.
  rewrite (ger0_norm p0) add0r mul1r.
  have h1 := mxdot_entry y 0 j; have h2 := mxdot_entry y 0 l.
  by have := sqr_ge0 (y 0 j); have := sqr_ge0 (y 0 l); nra.
have E2 (j : 'I_k) : \int[@gauss R k]_y (y 0 j ^+ 2) = 1.
  have := gauss_cov j j; rewrite eqxx /= => h.
  by rewrite /Rintegral; under eq_integral do rewrite expr2; rewrite h.
split.
  rewrite (Rintegral_sumr _ (fun j => integrableRZl (d 0 j) (iy2 j))).
  apply: eq_bigr => j _.
  by rewrite (RintegralZl _ measurableT (iy2 j)) E2 mulr1.
(* the second moment *)
have sqE (y : 'rV[R]_k) : (\sum_j d 0 j * y 0 j ^+ 2) ^+ 2 =
    \sum_j \sum_l (d 0 j * d 0 l) * (y 0 j ^+ 2 * y 0 l ^+ 2).
  rewrite expr2 big_distrlr /=; apply: eq_bigr => j _.
  by apply: eq_bigr => l _; rewrite mulrACA.
under eq_Rintegral do rewrite sqE.
have it (j : 'I_k) : (gauss k).-integrable setT (EFin \o (fun y : 'rV[R]_k =>
    \sum_l (d 0 j * d 0 l) * (y 0 j ^+ 2 * y 0 l ^+ 2))).
  by apply: integrableR_sum => l; exact: integrableRZl.
rewrite (Rintegral_sumr _ it).
under eq_bigr => j _ do rewrite (Rintegral_sumr _
  (fun l => integrableRZl (d 0 j * d 0 l) (iy4 j l))).
under eq_bigr => j _ do under eq_bigr => l _ do
  rewrite (RintegralZl _ measurableT (iy4 j l)) gauss_coord_moments.
rewrite expr2 big_distrlr /= mulr_sumr -big_split /=.
apply: eq_bigr => j _.
rewrite (bigD1 j) //= [in RHS](bigD1 j) //= eqxx.
have -> : \sum_(i < k | i != j) d 0 j * d 0 i * (if j == i then 3 else 1) =
    \sum_(i < k | i != j) d 0 j * d 0 i.
  apply: eq_bigr => i ij.
  by rewrite (negbTE (_ : j != i)) ?mulr1 // eq_sym.
by rewrite expr2; ring.
Qed.

Lemma gauss_quad_moments k (A : 'M[R]_k) : A \is symmetricmx ->
  \int[gauss k]_x mxdot x (x *m A) = \tr A /\
  \int[gauss k]_x mxdot x (x *m A) ^+ 2 = \tr A ^+ 2 + 2 * mxdot A A.
Proof.
move=> As; have [P Po [d AE]] := symmetric_spectral As.
have PP : (P^T)^T *m P^T = 1%:M by rewrite trmxK; exact/orthogonalmxP.
(* in the eigenbasis the quadratic form is diagonal *)
have qE (x : 'rV[R]_k) :
    mxdot x (x *m A) = \sum_j d 0 j * (x *m P^T) 0 j ^+ 2.
  rewrite AE !mulmxA.
  have := mxdot_mulmxr x P^T (x *m P^T *m diag_mx d); rewrite trmxK => <-.
  rewrite /mxdot big_ord1; apply: eq_bigr => j _.
  rewrite mul_mx_diag [X in _ * X]mxE.
  have -> : (ord0 : 'I_1) = 0 by [].
  by ring.
(* and x P^T has law gauss k *)
have T (f : 'rV[R]_k -> R) : (gauss k).-integrable setT (EFin \o f) ->
    \int[gauss k]_x f (x *m P^T) = \int[gauss k]_y f y.
  move=> fi; rewrite /Rintegral; congr fine.
  exact: (integral_gauss_orthogonal PP fi).
pose q (y : 'rV[R]_k) := \sum_j d 0 j * y 0 j ^+ 2.
have iq : (gauss k).-integrable setT (EFin \o q).
  apply: integrableR_sum => j; apply: integrableRZl.
  apply: (@gauss_integrable4 k _ 1 1).
    by apply: measurable_funX; exact: measurable_mxentry.
  move=> y; rewrite ger0_norm ?sqr_ge0 // mul1r.
  by have := mxdot_entry y 0 j; have := le1_sqr (mxdot_ge0 y); lra.
have iq2 : (gauss k).-integrable setT (EFin \o (fun y => q y ^+ 2)).
  apply: (@gauss_integrable4 k _ 0 (mxdot d d)).
    apply: measurable_funX; apply: measurable_sum => j.
    apply: measurable_funM => //.
    by apply: measurable_funX; exact: measurable_mxentry.
  move=> y; rewrite ger0_norm ?sqr_ge0 // add0r.
  pose y2 := \row_j (y 0 j ^+ 2).
  have qd : q y = mxdot d y2.
    by rewrite /q /mxdot big_ord1; apply: eq_bigr => j _; rewrite mxE.
  have y2y : mxdot y2 y2 <= mxdot y y ^+ 2.
    rewrite /mxdot !big_ord1.
    rewrite expr2 big_distrlr /= ler_sum // => j _.
    rewrite (bigD1 j) //= mxE -expr2 -exprM lerDl sumr_ge0 // => l _.
    by rewrite mulr_ge0 ?sqr_ge0 -?expr2 ?sqr_ge0.
  rewrite qd; apply: le_trans (mxdot_cauchy_schwarz _ _) _.
  by rewrite ler_wpM2l ?mxdot_ge0.
have trE : \tr A = \sum_j d 0 j.
  rewrite AE mxtrace_mulC mulmxA.
  by rewrite (orthogonalmxP _ Po) mul1mx mxtrace_diag.
have AAE : mxdot A A = \sum_j d 0 j ^+ 2.
  have PTo : P^T \is orthogonalmx by rewrite trmx_orthogonal.
  rewrite AE -mulmxA mxdot_orthogonalmxl // mxdot_orthogonalmxr //.
  by rewrite mxdot_diag; apply: eq_bigr => j _; rewrite expr2.
have [d1 d2] := gauss_diag_moments d.
split.
  under eq_Rintegral do rewrite qE.
  have := T q iq; rewrite /q /= => ->.
  by rewrite d1 trE.
under eq_Rintegral do rewrite qE.
have := T (fun y => q y ^+ 2) iq2; rewrite /q /= => ->.
by rewrite d2 trE AAE.
Qed.

Lemma gauss_mxdot_moments k (a b : 'rV[R]_k) :
  [/\ \int[gauss k]_x mxdot x a = 0,
      \int[gauss k]_x (mxdot x a * mxdot x b) = mxdot a b &
      \int[gauss k]_x mxdot x a ^+ 4 = 3 * mxdot a a ^+ 2].
Proof.
have outE (u v : 'rV[R]_k) (x : 'rV[R]_k) :
    mxdot x (x *m (u^T *m v)) = mxdot x u * mxdot x v.
  rewrite mulmxA (mx11_scalar (x *m u^T)) mul_scalar_mx mxdotZr.
  by rewrite -mxdot_rowE.
have symA (u v : 'rV[R]_k) : (u^T *m v + v^T *m u) \is symmetricmx.
  by apply/symmetricmxP; rewrite linearD /= !trmx_mul !trmxK addrC.
have iQ (M : 'M[R]_k) : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot x (x *m M))).
  apply: (@gauss_integrable4 k _ (frobenius M) (frobenius M)).
    exact: measurable_quad.
  move=> x; apply: le_trans (quad_le_frobenius M x) _.
  by have := le1_sqr (mxdot_ge0 x); have := frobenius_ge0 M; nra.
have tr1 (u v : 'rV[R]_k) : \tr (u^T *m v) = mxdot u v.
  by rewrite mxtrace_mulC /mxtrace big_ord1 -mxdot_rowE mxdotC.
split.
- have ixj (j : 'I_k) :
      (gauss k).-integrable setT (EFin \o (fun x : 'rV[R]_k => x 0 j)).
    apply: (@gauss_integrable4 k _ 2 1); first exact: measurable_mxentry.
    move=> x; have := mxdot_entry x 0 j; have := le1_sqr (mxdot_ge0 x).
    have := le1_sqr (normr_ge0 (x 0 j)).
    by rewrite real_normK ?num_real //; lra.
  have mE (x : 'rV[R]_k) : mxdot x a = \sum_j a 0 j * x 0 j.
    by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite mulrC.
  under eq_Rintegral do rewrite mE.
  rewrite (Rintegral_sumr _ (fun j => integrableRZl (a 0 j) (ixj j))).
  rewrite big1 // => j _; rewrite (RintegralZl _ measurableT (ixj j)).
  by rewrite /Rintegral gauss_mean /= mulr0.
- have e (x : 'rV[R]_k) : mxdot x a * mxdot x b =
      2^-1 * mxdot x (x *m (a^T *m b + b^T *m a)).
    by rewrite mulmxDr mxdotDr !outE; field.
  under eq_Rintegral do rewrite e.
  rewrite (RintegralZl _ measurableT (iQ _)).
  rewrite (gauss_quad_moments (symA a b)).1.
  by rewrite mxtraceD !tr1 mxdotC; field.
- have Aas : a^T *m a \is symmetricmx.
    by apply/symmetricmxP; rewrite trmx_mul trmxK.
  have e4 (x : 'rV[R]_k) :
      mxdot x a ^+ 4 = mxdot x (x *m (a^T *m a)) ^+ 2.
    by rewrite outE -expr2 -exprM.
  under eq_Rintegral do rewrite e4.
  rewrite (gauss_quad_moments Aas).2 tr1.
  have -> : mxdot (a^T *m a) (a^T *m a) = mxdot a a ^+ 2.
    have := mxdot_outer2 a^T a^T a^T a^T.
    by rewrite !trmxK !mxdot_trmx => ->; rewrite expr2.
  ring.
Qed.

End gauss_quadratic.

Section opnorm_gram.
Context {R : realType}.

Lemma opnorm_sqr_le m n (S : 'M[R]_(m, n)) : opnorm S ^+ 2 <= opnorm (S^T *m S).
Proof.
have c0 := opnorm_ge0 (S^T *m S).
have h : opnorm S <= Num.sqrt (opnorm (S^T *m S)).
  apply: opnorm_le => u u1.
  rewrite -(ler_sqr (frobenius_ge0 _) (sqrtr_ge0 _)) ?nnegrE
    ?frobenius_ge0 ?sqrtr_ge0 //.
  rewrite (sqr_sqrtr c0) frobenius_sqr mxdot_mulmxl mulmxA.
  apply: le_trans (ler_mxdot _ _) _.
  apply: le_trans (ler_wpM2l (frobenius_ge0 _) (frobenius_mulmx_opnorm _ _)) _.
  have f0 := frobenius_ge0 u.
  have : frobenius u * (opnorm (S^T *m S) * frobenius u) <=
      1 * (opnorm (S^T *m S) * 1).
    by apply: ler_pM => //; rewrite ?mulr_ge0 //; apply: ler_wpM2l.
  by rewrite !mul1r mulr1.
by rewrite -(sqr_sqrtr c0) ler_sqr ?nnegrE ?opnorm_ge0 ?sqrtr_ge0.
Qed.

End opnorm_gram.

Section gauss_regular.
Context {R : realType} {N : nat}.

(* (2.10): a Gaussian feature is regular. *)
Theorem gauss_regular_feature k (S : 'M[R]_(k, N))
    (nu : probability 'rV[R]_N R) :
  (forall A, measurable A -> nu A = gauss k ((fun x => x *m S) @^-1` A)) ->
  S != 0 ->
  regular_feature (3 `^ (1 / 4)) (Num.sqrt 2 * opnorm (S^T *m S))
    (S^T *m S) nu.
Proof.
move=> nuE S0.
set Sig := S^T *m S.
have mS : measurable_fun setT (fun x : 'rV[R]_k => x *m S).
  by apply: measurable_mulmx => //; exact: measurable_cst.
(* integrals against nu are integrals against gauss k *)
have E (f : 'rV[R]_N -> \bar R) : measurable_fun setT f ->
    (forall z, 0 <= f z)%E ->
    (\int[nu]_z f z = \int[gauss k]_x f (x *m S))%E.
  move=> mf f0.
  by apply: (ge0_integral_image (g := fun x : 'rV[R]_k => x *m S)) => //.
have gnu (A : set 'rV[R]_N) : measurable A ->
    gauss k ((fun x => x *m S) @^-1` A) = nu A.
  by move=> mA; rewrite nuE.
have I (f : 'rV[R]_N -> R) : measurable_fun setT f ->
    (gauss k).-integrable setT (EFin \o (fun x => f (x *m S))) ->
    nu.-integrable setT (EFin \o f) /\
    \int[nu]_z f z = \int[gauss k]_x f (x *m S).
  move=> mf gi.
  have mfa : measurable_fun setT (fun z => `|(f z)%:E|%E).
    by apply: measurableT_comp => //; exact/measurable_EFinP.
  have ni : nu.-integrable setT (EFin \o f).
    apply/integrableP; split; first exact/measurable_EFinP.
    rewrite (E _ mfa (fun z => abse_ge0 _)).
    by case/integrableP : gi.
  split => //; rewrite /Rintegral; congr fine.
  exact: esym (integral_image mS gnu ni).
have lin (th : 'rV[R]_N) (x : 'rV[R]_k) :
    mxdot (x *m S) th = mxdot x (th *m S^T) by rewrite mxdot_mulmxr.
(* polynomials of degree 4 are integrable against gauss k *)
have ig1 (a : 'rV[R]_k) :
    (gauss k).-integrable setT (EFin \o (fun x : 'rV[R]_k => mxdot x a)).
  apply: (@gauss_integrable4 R k _ (1 + mxdot a a) (mxdot a a)).
    exact: measurable_mxdotl.
  move=> x; have cs := mxdot_cauchy_schwarz x a.
  have t0 := mxdot_ge0 a.
  have h1 : `|mxdot x a| <= 1 + mxdot x a ^+ 2.
    by rewrite -real_normK ?num_real //; exact: le1_sqr.
  by have := le1_sqr (mxdot_ge0 x); nra.
have ig2 (a b : 'rV[R]_k) : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot x a * mxdot x b)).
  apply: (@gauss_integrable4 R k _ ((mxdot a a + mxdot b b) / 2)
    ((mxdot a a + mxdot b b) / 2)).
    by apply: measurable_funM; exact: measurable_mxdotl.
  move=> x; have cs := mxdot_cauchy_schwarz x a.
  have cs' := mxdot_cauchy_schwarz x b.
  have t0 := mxdot_ge0 a; have t0' := mxdot_ge0 b.
  have h1 : `|mxdot x a * mxdot x b| <=
      (mxdot x a ^+ 2 + mxdot x b ^+ 2) / 2.
    rewrite normrM -(real_normK (num_real (mxdot x a))).
    rewrite -(real_normK (num_real (mxdot x b))).
    by have := sqr_ge0 (`|mxdot x a| - `|mxdot x b|); nra.
  by have := le1_sqr (mxdot_ge0 x); nra.
have ig4 (a : 'rV[R]_k) : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot x a ^+ 4)).
  apply: (@gauss_integrable4 R k _ 0 (mxdot a a ^+ 2)).
    by apply: measurable_funX; exact: measurable_mxdotl.
  move=> x; rewrite ger0_norm ?exprn_even_ge0 // add0r.
  have cs := mxdot_cauchy_schwarz x a.
  have -> : mxdot x a ^+ 4 = (mxdot x a ^+ 2) ^+ 2 by rewrite -exprM.
  rewrite -exprMn ler_sqr ?nnegrE ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0 //.
  by rewrite mulrC.
have K4 : (3 `^ (1 / 4) : R) ^+ 4 = 3.
  rewrite -powR_mulrn ?powR_ge0 // -powRrM.
  have -> : (1 / 4 * 4%:R : R) = 1 by field.
  by rewrite powRr1.
have SigT : Sig^T = Sig by rewrite /Sig trmx_mul trmxK.
have formE (th th' : 'rV[R]_N) :
    mxdot (th *m S^T) (th' *m S^T) = mxdot (th *m Sig) th'.
  rewrite mxdot_mulmxr trmxK -mulmxA -/Sig.
  by rewrite [RHS]mxdot_mulmxr SigT.
split.
- (* the covariance is not 0 *)
  have [i0 [j0 Sij]] : exists i j, S i j != 0.
    apply: contrapT => h; move/eqP: S0; apply; apply/matrixP => i j.
    rewrite mxE; apply/eqP; apply: contrapT => /negP Sij0.
    by apply: h; exists i, j.
  have Sjj : 0 < Sig j0 j0.
    rewrite /Sig mxE (bigD1 i0) //= !mxE.
    apply: lt_le_trans (_ : 0 < S i0 j0 * S i0 j0) _.
      by rewrite -expr2 exprn_even_gt0.
    rewrite lerDl sumr_ge0 // => i _; rewrite mxE -expr2; exact: sqr_ge0.
  apply: lt_le_trans Sjj _.
  apply: le_trans (ler_norm _) _.
  apply: le_trans (mx_norm_entry_le _ _ _) _.
  exact: mx_norm_le_opnorm.
- (* (F1), with K^4 = 3 *)
  move=> th.
  have mf : measurable_fun setT (fun z : 'rV[R]_N => (mxdot z th ^+ 4)%:E).
    apply/measurable_EFinP; apply: measurable_funX.
    exact: measurable_mxdotl.
  rewrite unlock /= (E _ mf); first by move=> z; rewrite lee_fin exprn_even_ge0.
  under eq_integral do rewrite lin.
  rewrite -(Rintegral_EFin (ig4 (th *m S^T))) lee_fin.
  have [_ _ ->] := gauss_mxdot_moments (th *m S^T) (th *m S^T).
  rewrite K4 formE.
  have h := form_le_opnorm Sig th.
  have h0 : 0 <= mxdot (th *m Sig) th by rewrite -formE mxdot_ge0.
  have h2 : mxdot (th *m Sig) th ^+ 2 <= (opnorm Sig * mxdot th th) ^+ 2.
    by rewrite ler_sqr ?nnegrE // (le_trans h0 h).
  by rewrite exprMn mulrA in h2; lra.
- (* the mean *)
  move=> th.
  have gi : (gauss k).-integrable setT
      (EFin \o (fun x : 'rV[R]_k => mxdot (x *m S) th)).
    by apply: (eq_integrable measurableT _ _ _ (ig1 (th *m S^T))) => x _;
      rewrite /= lin.
  have [ni nE] := I (fun z => mxdot z th) (measurable_mxdotl th) gi.
  rewrite unlock /= -(Rintegral_EFin ni) nE.
  under eq_Rintegral do rewrite lin.
  by have [-> _ _] := gauss_mxdot_moments (th *m S^T) (th *m S^T).
- (* the covariance *)
  move=> th th'.
  have gi : (gauss k).-integrable setT
      (EFin \o (fun x : 'rV[R]_k => mxdot (x *m S) th * mxdot (x *m S) th')).
    by apply: (eq_integrable measurableT _ _ _
      (ig2 (th *m S^T) (th' *m S^T))) => x _; rewrite /= !lin.
  have mf : measurable_fun setT
      (fun z : 'rV[R]_N => mxdot z th * mxdot z th').
    by apply: measurable_funM; exact: measurable_mxdotl.
  have [ni nE] := I (fun z => mxdot z th * mxdot z th') mf gi.
  rewrite unlock /= -(Rintegral_EFin ni) nE.
  under eq_Rintegral do rewrite !lin.
  have [_ -> _] := gauss_mxdot_moments (th *m S^T) (th' *m S^T).
  by rewrite formE.
(* (F2), with tau = sqrt 2 opnorm Sig *)
move=> T Ts.
set A := S *m T *m S^T.
have TT : T^T = T by apply/symmetricmxP.
have As : A \is symmetricmx.
  by apply/symmetricmxP; rewrite /A !trmx_mul trmxK TT mulmxA.
have quadE (x : 'rV[R]_k) :
    mxdot (x *m S) ((x *m S) *m T) = mxdot x (x *m A).
  by rewrite mxdot_mulmxr /A !mulmxA.
have iQ (M : 'M[R]_k) : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot x (x *m M))).
  apply: (@gauss_integrable4 R k _ (frobenius M) (frobenius M)).
    exact: measurable_quad.
  move=> x; apply: le_trans (quad_le_frobenius M x) _.
  by have := le1_sqr (mxdot_ge0 x); have := frobenius_ge0 M; nra.
have gi : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot (x *m S) ((x *m S) *m T))).
  by apply: (eq_integrable measurableT _ _ _ (iQ A)) => x _; rewrite /= quadE.
have [ni nE] := I (fun z => mxdot z (z *m T)) (measurable_quad T) gi.
have [q1 q2] := gauss_quad_moments As.
have EQ : \int[nu]_z mxdot z (z *m T) = \tr A.
  by rewrite nE; under eq_Rintegral do rewrite quadE; exact: q1.
rewrite varianceT.
change (\int[nu]_x ((mxdot x (x *m T) -
    \int[nu]_y mxdot y (y *m T)) ^+ 2)%:E <=
  ((Num.sqrt 2 * opnorm Sig) ^+ 2 * frobenius T ^+ 2)%:E)%E.
rewrite EQ.
have mq2 : measurable_fun setT
    (fun z : 'rV[R]_N => ((mxdot z (z *m T) - \tr A) ^+ 2)%:E).
  apply/measurable_EFinP; apply: measurable_funX.
  by apply: measurable_funB => //; exact: measurable_quad.
rewrite (E _ mq2); first by move=> z; rewrite lee_fin sqr_ge0.
under eq_integral do rewrite quadE.
have iQ2 : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => (mxdot x (x *m A) - \tr A) ^+ 2)).
  apply: (@gauss_integrable4 R k _ (2 * \tr A ^+ 2) (2 * frobenius A ^+ 2)).
    apply: measurable_funX; apply: measurable_funB => //.
    exact: measurable_quad.
  move=> x; rewrite ger0_norm ?sqr_ge0 //.
  have q2' := quad_sqr_le A x.
  by have := sqr_ge0 (mxdot x (x *m A) + \tr A); nra.
rewrite -(Rintegral_EFin iQ2) lee_fin.
have iQsq : (gauss k).-integrable setT
    (EFin \o (fun x : 'rV[R]_k => mxdot x (x *m A) ^+ 2)).
  apply: (@gauss_integrable4 R k _ 0 (frobenius A ^+ 2)) => [|x].
    by apply: measurable_funX; exact: measurable_quad.
  by rewrite ger0_norm ?sqr_ge0 // add0r; exact: quad_sqr_le.
have e2 (x : 'rV[R]_k) : (mxdot x (x *m A) - \tr A) ^+ 2 =
    (mxdot x (x *m A) ^+ 2 - 2 * \tr A * mxdot x (x *m A)) + \tr A ^+ 2.
  by ring.
under eq_Rintegral do rewrite e2.
have iB := integrableRB iQsq (integrableRZl (2 * \tr A) (iQ A)).
rewrite (RintegralD measurableT iB (integrable_cst_prob _ _)).
rewrite (RintegralB measurableT iQsq (integrableRZl (2 * \tr A) (iQ A))).
rewrite (RintegralZl _ measurableT (iQ A)) q1 q2 Rintegral_cst_prob.
have -> : \tr A ^+ 2 + 2 * mxdot A A - 2 * \tr A * \tr A + \tr A ^+ 2 =
    2 * mxdot A A by ring.
(* |A|_F <= opnorm Sig |T|_F *)
have fA : frobenius A <= opnorm Sig * frobenius T.
  rewrite /A -mulmxA.
  apply: le_trans (frobenius_mulmx_mx_opnorm _ _) _.
  have h : frobenius (T *m S^T) <= opnorm S * frobenius T.
    rewrite -frobenius_trmx trmx_mul trmxK TT.
    exact: frobenius_mulmx_mx_opnorm.
  apply: le_trans (ler_wpM2l (opnorm_ge0 _) h) _.
  rewrite mulrA -expr2; apply: ler_wpM2r; first exact: frobenius_ge0.
  exact: opnorm_sqr_le.
have fA2 : frobenius A ^+ 2 <= (opnorm Sig * frobenius T) ^+ 2.
  by rewrite ler_sqr ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?opnorm_ge0
    ?frobenius_ge0.
rewrite -frobenius_sqr exprMn sqr_sqrtr ?ler0n //; first exact: mxdot_ge0.
rewrite sqr_sqrtr ?ler0n // -frobenius_sqr.
by rewrite exprMn in fA2; lra.
Qed.

End gauss_regular.
