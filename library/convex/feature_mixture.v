From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral hoelder probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.probability Require Import moments mixture.
From GaussianAnalysis.convex Require Import least_squares feature_moments.

(**md**************************************************************************)
(* # Mixtures of features                                                     *)
(*                                                                            *)
(* A finite mixture (probability/mixture.v) of laws P i on 'rV[R]_N, each     *)
(* centered with second-moment matrix Sig i, with E_i <z, theta>^4 <=         *)
(* A |theta|^4 and Var_i (z T z^T) <= tau^2 |T|_F^2 for T symmetric, is a     *)
(* regular feature (regular_feature of least_squares.v) with covariance       *)
(* Sigma = sum_i w_i Sig i as soon as opnorm Sigma > 0. The law of total      *)
(* variance adds to tau^2 the spread c^2 of the covariances: for T            *)
(* symmetric, E_i z T z^T - E z T z^T = <Sig i - Sigma, T>, so it suffices    *)
(* that sum_i w_i <Sig i - Sigma, T>^2 <= c^2 |T|_F^2 for every symmetric T.  *)
(* By Cauchy-Schwarz for the Frobenius product, c^2 >=                        *)
(* sum_i w_i |Sig i - Sigma|_F^2 is enough. No structure of Sig i - Sigma     *)
(* is needed.                                                                 *)
(*                                                                            *)
(* - moment4_integrable and its corollaries moment4_int_lin,                  *)
(*   moment4_int_lin2, moment4_int_quad, moment4_Lfun2_quad: under a law with *)
(*   E <z, theta>^4 <= A |theta|^4 for every theta, a measurable g with       *)
(*   |g z| <= a + b |z|^4 is integrable, so the polynomials of degree at      *)
(*   most 4 in the coordinates are (as reg_integrable of feature_moments.v    *)
(*   for a regular feature);                                                  *)
(* - quad_expectation: E z T z^T = <Sig^T, T> for a law with second-moment    *)
(*   matrix Sig, that is E <z, theta> <z, theta'> = theta Sig theta'^T;       *)
(* - mixture_regular_feature_dot: the mixture is a regular feature with       *)
(*   covariance Sigma, any K with A <= K^4 opnorm Sigma^2, and                *)
(*   sqrt (tau^2 + c^2) in place of tau, when                                 *)
(*   sum_i w_i <Sig i - Sigma, T>^2 <= c^2 |T|_F^2 for every symmetric T;     *)
(* - mixture_regular_feature: the same when                                   *)
(*   sum_i w_i |Sig i - Sigma|_F^2 <= c^2.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section fourth_moment.
Context {R : realType} {N : nat}.
Variables (A : R) (mu : probability 'rV[R]_N R).
Hypothesis h4 : forall th : 'rV[R]_N,
  ('E_mu[fun z => (mxdot z th ^+ 4)%R] <= (A * mxdot th th ^+ 2)%:E)%E.

Lemma moment4_int4 (th : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th ^+ 4)).
Proof.
apply/integrableP; split.
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_mxdotl.
have := h4 th; rewrite unlock /= => h.
apply: (le_lt_trans _ (ltry (A * mxdot th th ^+ 2))).
apply: le_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_integral => z _; rewrite ger0_norm ?exprn_even_ge0.
Qed.

Lemma moment4_int_norm4 : mu.-integrable setT (EFin \o (fun z => mxdot z z ^+ 2)).
Proof.
have i4 : mu.-integrable setT
    (fun z => (\sum_a (mxdot z (delta_mx 0 a) ^+ 4)%:E)%E).
  by apply: (integrable_sum measurableT) => a _; exact: moment4_int4.
have iN := integrableZl measurableT N%:R i4.
apply: (le_integrable measurableT _ _ iN).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_norm2.
move=> z _; rewrite /= sumEFin -EFinM /= lee_fin.
rewrite [`|mxdot z z ^+ 2|]ger0_norm ?sqr_ge0 //.
exact: le_trans (mxdot_sqr_sum z) (ler_norm _).
Qed.

(* Domination of |g| by a + b |z|^4. *)
Lemma moment4_integrable (g : 'rV[R]_N -> R) (a b : R) :
  measurable_fun setT g -> (forall z, `|g z| <= a + b * mxdot z z ^+ 2) ->
  mu.-integrable setT (EFin \o g).
Proof.
move=> mg gb.
have ia := integrable_cst_prob mu a.
have ib := integrableZl measurableT b moment4_int_norm4.
have iab := integrableD measurableT ia ib.
apply: (le_integrable measurableT _ _ iab); first exact/measurable_EFinP.
move=> z _ /=; rewrite lee_fin.
exact: le_trans (gb z) (ler_norm _).
Qed.

Lemma moment4_int_lin (th : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th)).
Proof.
apply: (@moment4_integrable _ (1 + mxdot th th) (mxdot th th)).
  exact: measurable_mxdotl.
move=> z; have cs := mxdot_cauchy_schwarz z th.
have t0 := mxdot_ge0 th.
have h1 : `|mxdot z th| <= 1 + mxdot z th ^+ 2.
  by rewrite -real_normK ?num_real //; exact: le1_sqr.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma moment4_int_lin2 (th th' : 'rV[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z th * mxdot z th')).
Proof.
apply: (@moment4_integrable _ ((mxdot th th + mxdot th' th') / 2)
  ((mxdot th th + mxdot th' th') / 2)).
  by apply: measurable_funM; exact: measurable_mxdotl.
move=> z; have cs := mxdot_cauchy_schwarz z th.
have cs' := mxdot_cauchy_schwarz z th'.
have t0 := mxdot_ge0 th; have t0' := mxdot_ge0 th'.
have h1 : `|mxdot z th * mxdot z th'| <=
    (mxdot z th ^+ 2 + mxdot z th' ^+ 2) / 2.
  rewrite normrM -(real_normK (num_real (mxdot z th))).
  rewrite -(real_normK (num_real (mxdot z th'))).
  have := sqr_ge0 (`|mxdot z th| - `|mxdot z th'|); by nra.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma moment4_int_quad (T : 'M[R]_N) :
  mu.-integrable setT (EFin \o (fun z => mxdot z (z *m T))).
Proof.
apply: (@moment4_integrable _ (frobenius T) (frobenius T)).
  exact: measurable_quad.
move=> z; apply: le_trans (quad_le_frobenius T z) _.
have f0 := frobenius_ge0 T.
have := le1_sqr (mxdot_ge0 z); by nra.
Qed.

Lemma moment4_Lfun2_quad (T : 'M[R]_N) :
  (fun z => mxdot z (z *m T)) \in Lfun mu 2%:E.
Proof.
apply: integrable_sqr_Lfun2; first exact: measurable_quad.
apply: (@moment4_integrable _ 0 (frobenius T ^+ 2)).
  by apply: measurable_funX; exact: measurable_quad.
by move=> z; rewrite add0r ger0_norm ?sqr_ge0 //; exact: quad_sqr_le.
Qed.

Lemma moment4_Lfun1_lin (th : 'rV[R]_N) :
  (fun z => mxdot z th) \in Lfun mu 1.
Proof. by apply/Lfun1_integrable; exact: moment4_int_lin. Qed.

Lemma moment4_Lfun1_lin2 (th th' : 'rV[R]_N) :
  (fun z => mxdot z th * mxdot z th') \in Lfun mu 1.
Proof. by apply/Lfun1_integrable; exact: moment4_int_lin2. Qed.

End fourth_moment.

Section quad_expectation.
Context {R : realType} {N : nat}.
Variables (A : R) (mu : probability 'rV[R]_N R) (Sig : 'M[R]_N).
Hypothesis h4 : forall th : 'rV[R]_N,
  ('E_mu[fun z => (mxdot z th ^+ 4)%R] <= (A * mxdot th th ^+ 2)%:E)%E.
Hypothesis h2 : forall th th' : 'rV[R]_N,
  ('E_mu[fun z => (mxdot z th * mxdot z th')%R] = (mxdot (th *m Sig) th')%:E)%E.

(* E z T z^T = sum_(a, b) Sig_(b, a) T_(a, b). *)
Lemma quad_expectation (T : 'M[R]_N) :
  ('E_mu[fun z => mxdot z (z *m T)] = (mxdot Sig^T T)%:E)%E.
Proof.
have iq := moment4_int_quad h4 T.
rewrite unlock -(Rintegral_EFin iq); congr EFin.
under eq_Rintegral do rewrite mxdot_quadE.
rewrite (Rintegral_sumr _ (fun b => moment4_int_lin2 h4 (delta_mx 0 b) (col b T)^T)).
have e b : \int[mu]_z (mxdot z (delta_mx 0 b) * mxdot z (col b T)^T) =
    mxdot (delta_mx 0 b *m Sig) (col b T)^T.
  have := h2 (delta_mx 0 b) (col b T)^T; rewrite unlock => h.
  by rewrite /Rintegral h.
under eq_bigr do rewrite e.
have e2 i : mxdot (delta_mx 0 i *m Sig) (col i T)^T = \sum_j Sig i j * T j i.
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite -rowE !mxE.
under eq_bigr do rewrite e2.
rewrite /mxdot exchange_big /=; apply: eq_bigr => j _; apply: eq_bigr => i _.
by rewrite mxE.
Qed.

End quad_expectation.

Section mixture_regular.
Context {R : realType} {N : nat} (I : finType).
Variables (w : I -> R) (P : I -> probability 'rV[R]_N R).
Variable hw : mixture_weights w.
Variables (Sig : I -> 'M[R]_N) (Sigma : 'M[R]_N) (A tau c K : R).
Hypothesis P2 : forall i (th th' : 'rV[R]_N),
  ('E_(P i)[fun z => (mxdot z th * mxdot z th')%R] =
    (mxdot (th *m Sig i) th')%:E)%E.
Hypothesis P1 : forall i (th : 'rV[R]_N),
  ('E_(P i)[fun z => mxdot z th] = 0)%E.
Hypothesis P4 : forall i (th : 'rV[R]_N),
  ('E_(P i)[fun z => (mxdot z th ^+ 4)%R] <= (A * mxdot th th ^+ 2)%:E)%E.
Hypothesis PV : forall i (T : 'M[R]_N), T \is symmetricmx ->
  ('V_(P i)[fun z => mxdot z (z *m T)] <= (tau ^+ 2 * frobenius T ^+ 2)%:E)%E.
Hypothesis SigmaE : Sigma = \sum_i w i *: Sig i.

Local Notation mu := (mixture P hw).

Let w0 i : 0 <= w i := mixture_weights_ge0 hw i.

Let sum_w : \sum_i w i = 1 := mixture_weights_sum hw.

Theorem mixture_regular_feature_dot :
  0 < opnorm Sigma ->
  (forall T : 'M[R]_N, T \is symmetricmx ->
    \sum_i w i * mxdot (Sig i - Sigma) T ^+ 2 <= c ^+ 2 * frobenius T ^+ 2) ->
  A <= K ^+ 4 * opnorm Sigma ^+ 2 ->
  regular_feature K (Num.sqrt (tau ^+ 2 + c ^+ 2)) Sigma mu.
Proof.
move=> S0 spread AK; split => //.
- move=> th.
  have mf : measurable_fun setT (fun z : 'rV[R]_N => (mxdot z th ^+ 4)%:E).
    by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_mxdotl.
  have nf (z : 'rV[R]_N) : setT z -> (0 <= (mxdot z th ^+ 4)%:E)%E.
    by move=> _; rewrite lee_fin exprn_even_ge0.
  rewrite unlock ge0_integral_mixture //.
  apply: (@le_trans _ _ (\sum_i (w i)%:E * (A * mxdot th th ^+ 2)%:E)%E).
    apply: lee_sum => i _; apply: lee_wpmul2l; first by rewrite lee_fin.
    by have := P4 i th; rewrite unlock.
  rewrite (eq_bigr (fun i => (w i * (A * mxdot th th ^+ 2))%:E)); try
    by move=> i _; rewrite EFinM.
  rewrite sumEFin -mulr_suml sum_w mul1r lee_fin.
  by apply: ler_wpM2r => //; exact: exprn_ge0 (mxdot_ge0 th).
- move=> th; rewrite (expectation_mixture hw (fun i => moment4_Lfun1_lin (P4 i) th)).
  by rewrite big1 // => i _; rewrite P1 mule0.
- move=> th th'.
  rewrite (expectation_mixture hw (fun i => moment4_Lfun1_lin2 (P4 i) th th')).
  rewrite (eq_bigr (fun i => (w i * mxdot (th *m Sig i) th')%:E)); try
    by move=> i _; rewrite P2 EFinM.
  rewrite sumEFin SigmaE mulmx_sumr mxdot_suml; congr EFin.
  by apply: eq_bigr => i _; rewrite -scalemxAr mxdotZl.
- move=> T Ts.
  have l1 i : (fun z => mxdot z (z *m T)) \in Lfun (P i) 1.
    by apply/Lfun1_integrable; exact: moment4_int_quad (P4 i) T.
  have hE i : ('E_(P i)[fun z => mxdot z (z *m T)] = (mxdot (Sig i)^T T)%:E)%E.
    exact: quad_expectation (P4 i) (P2 i) T.
  have hEm : ('E_mu[fun z => mxdot z (z *m T)] = (mxdot Sigma^T T)%:E)%E.
    rewrite (expectation_mixture hw l1).
    rewrite (eq_bigr (fun i => (w i * mxdot (Sig i)^T T)%:E)); try
      by move=> i _; rewrite hE EFinM.
    rewrite sumEFin SigmaE; congr EFin.
    have -> : (\sum_i w i *: Sig i)^T = \sum_i w i *: (Sig i)^T.
      apply/matrixP => a b; rewrite mxE !summxE; apply: eq_bigr => i _.
      by rewrite !mxE.
    by rewrite mxdot_suml; apply: eq_bigr => i _; rewrite mxdotZl.
  rewrite (variance_mixture hw (fun i => moment4_Lfun2_quad (P4 i) T)).
  have Tt : T^T = T by apply/symmetricmxP.
  apply: (@le_trans _ _ (\sum_i (w i)%:E * ((tau ^+ 2 * frobenius T ^+ 2 +
      mxdot (Sig i - Sigma) T ^+ 2)%:E))%E).
    apply: lee_sum => i _; apply: lee_wpmul2l; first by rewrite lee_fin.
    rewrite EFinD; apply: leeD; first exact: PV.
    rewrite hE hEm -EFinB -EFin_expe lee_fin.
    have -> : mxdot (Sig i)^T T - mxdot Sigma^T T = mxdot (Sig i - Sigma)^T T.
      by rewrite raddfB /= mxdotBl.
    by rewrite -[in X in X <= _]Tt mxdot_trmx.
  rewrite (eq_bigr (fun i => (w i * (tau ^+ 2 * frobenius T ^+ 2 +
      mxdot (Sig i - Sigma) T ^+ 2))%:E)); try
    by move=> i _; rewrite EFinM.
  have tc : 0 <= tau ^+ 2 + c ^+ 2 by rewrite addr_ge0 ?sqr_ge0.
  rewrite sumEFin lee_fin (sqr_sqrtr tc).
  have -> : \sum_i w i * (tau ^+ 2 * frobenius T ^+ 2 +
      mxdot (Sig i - Sigma) T ^+ 2) =
      tau ^+ 2 * frobenius T ^+ 2 * \sum_i w i +
      \sum_i w i * mxdot (Sig i - Sigma) T ^+ 2.
    rewrite mulr_sumr -big_split /=; apply: eq_bigr => i _; ring.
  by rewrite sum_w mulr1 mulrDl lerD2l; exact: spread.
Qed.

(* The hypothesis on the spread of the covariances of
   mixture_regular_feature_dot follows from a bound on
   sum_i w_i |Sig i - Sigma|_F^2, by Cauchy-Schwarz for the Frobenius
   product. *)
Theorem mixture_regular_feature :
  0 < opnorm Sigma -> \sum_i w i * frobenius (Sig i - Sigma) ^+ 2 <= c ^+ 2 ->
  A <= K ^+ 4 * opnorm Sigma ^+ 2 ->
  regular_feature K (Num.sqrt (tau ^+ 2 + c ^+ 2)) Sigma mu.
Proof.
move=> S0 spread AK; apply: mixture_regular_feature_dot => // T Ts.
apply: (@le_trans _ _
  ((\sum_i w i * frobenius (Sig i - Sigma) ^+ 2) * frobenius T ^+ 2)).
  rewrite mulr_suml; apply: ler_sum => i _; rewrite -mulrA.
  apply: ler_wpM2l; first exact: w0.
  by apply: le_trans (mxdot_cauchy_schwarz _ _) _; rewrite -!frobenius_sqr.
by apply: ler_wpM2r => //; exact: sqr_ge0.
Qed.

End mixture_regular.
