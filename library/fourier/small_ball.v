From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear interval archimedean.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval_inference topology.
From mathcomp Require Import normedtype sequences derive realfun exp numfun.
From mathcomp Require Import measure trigo.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.gaussian Require Import lebesgue_rV.
From GaussianAnalysis.matrix Require Import euclidean real_spectral whitening.
From GaussianAnalysis.comparison Require Import normal_linear.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.fourier Require Import charfun esseen gauss_factor.
From GaussianAnalysis.fourier Require Import charfun_rV.

(**md**************************************************************************)
(* # The vector small-ball estimate                                           *)
(*                                                                            *)
(* For independent real x_1, ..., x_n of laws mu_1, ..., mu_n (tuple_prod)    *)
(* and row vectors w_1, ..., w_n of 'rV[R]_m with |w_k| <= rho and            *)
(* sum_k <x, w_k>^2 >= |x|^2 for all x, the probability that sum_k x_k w_k    *)
(* lies in a closed ball of radius eta sqrt m is at most (C eta)^m for        *)
(* eta >= C rho (vector_small_ball). The constant C depends only on v,        *)
(* lambda and eps when E[x_k^2] <= v and conc_fun mu_k lambda <= 1 - eps;     *)
(* in the form of Koehler and Sohn (arXiv 2608.27372, Proposition 2.4),       *)
(* for laws of mean zero and variance one with E[x^2 1_{|x| <= M}] >= 1/2,    *)
(* it depends only on M (vector_small_ball_moments). The proof is             *)
(* Fourier-analytic, after Ball and Nazarov, and Rudelson and Vershynin:      *)
(*                                                                            *)
(* - Frames. If sum_k w_k^T w_k = I_m, then |theta|^2 = sum_k <theta, w_k>^2  *)
(*   (frame_mxdot) and sum_k |w_k|^2 = m (frame_trace). The regularized       *)
(*   modulus exp (- s^2 |theta|^2 / 2) |cf nu theta| of the law nu of         *)
(*   sum_k x_k w_k is then the product over k of                              *)
(*   |cf mu_k <w_k, theta>| exp (- s^2 <w_k, theta>^2 / 2)                    *)
(*   (cf_rV_norm_frame).                                                      *)
(* - Lemma 3.8 of the paper (cf_rV_regularized_le). If, for each k with       *)
(*   r = |w_k| > 0,                                                           *)
(*     \int |cf mu_k u|^(1 / r^2) exp (- s^2 u^2 / (2 r^2)) du <= r C,        *)
(*   then \int exp (- s^2 |theta|^2 / 2) |cf nu theta| dtheta <= C^m. This    *)
(*   is the Brascamp-Lieb inequality with u_k = w_k / |w_k| and               *)
(*   c_k = |w_k|^2 (brascamp_lieb_ge0 allows zero weights), after the         *)
(*   change of variables u = |w_k| t.                                         *)
(* - Removing the Gaussian. For G of law gauss m independent of Y and         *)
(*   2 m s^2 <= d^2, P(|Y - z| <= r) <= 2 P(|Y + s G - z| <= r + d)           *)
(*   (ball_le_add_gauss), and the latter is bounded by the regularized        *)
(*   integral and the volume of the ball (add_gauss_ball_le). If the          *)
(*   regularized integral is at most C^m and 2 s^2 <= eta^2, then             *)
(*   P(|Y - z| <= eta sqrt m) <= (sqrt (8 e / pi) C eta)^m                    *)
(*   (small_ball_of_cf_bound).                                                *)
(* - Whitening. A matrix W with W (sum_k w_k^T w_k) W^T = I_m and             *)
(*   |x W| <= |x| turns the w_k into a frame w_k W^T (frame_mulmx) and does   *)
(*   not shrink the balls (tuple_prod_ball_mulmx, contraction_trmx).          *)
(*                                                                            *)
(* vector_small_ball_fourier puts these together, with the constant           *)
(* max (2, sqrt (8 e / pi) C), for laws that satisfy the bound above for      *)
(* all 0 < r <= s <= 1/2 (Lemma 3.5 of the paper).                            *)
(*                                                                            *)
(* Status. The Brascamp-Lieb inequality (comparison/brascamp_lieb.v) is not   *)
(* in the library yet: until it is proved, the section small_ball takes its   *)
(* statement as the hypothesis brascamp_lieb, and every result of that        *)
(* section is proved from it. The bound of Lemma 3.5 and its first half       *)
(* are gauss_factor_exists and conc_fun_truncated_exists of                   *)
(* fourier/gauss_factor.v, and the whitening matrix is whitening_exists of    *)
(* matrix/whitening.v.                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section prod_power.
Context {R : realType}.

(* Products of nonnegative extended reals are monotone. *)
Lemma lee_prod I (r : seq I) (P : pred I) (f g : I -> \bar R) :
  (forall i, P i -> 0 <= f i)%E -> (forall i, P i -> f i <= g i)%E ->
  (\prod_(i <- r | P i) f i <= \prod_(i <- r | P i) g i)%E.
Proof.
move=> f0 fg; elim/(big_load (fun x : \bar R => 0 <= x)%E): _.
elim/big_rec2: _ => // i y x Pi [x0 xy]; split; first by rewrite mule_ge0 ?f0.
by rewrite lee_pmul ?f0 ?fg.
Qed.

(* x^(sum_i c_i) = prod_i x^(c_i) for x > 0. *)
Lemma powR_sum (x : R) I (r : seq I) (P : pred I) (c : I -> R) : 0 < x ->
  x `^ (\sum_(i <- r | P i) c i) = \prod_(i <- r | P i) x `^ c i.
Proof.
move=> x0; have xD a b : x `^ (a + b) = x `^ a * x `^ b.
  by rewrite powRD// (gt_eqF x0) /= implybT.
elim: r => [|i r IH]; first by rewrite !big_nil powRr0.
by rewrite !big_cons; case: ifP => // _; rewrite xD IH.
Qed.

End prod_power.

Section frame.
Context {R : realType} {m : nat}.

(* theta (w^T w) = <theta, w> w. *)
Lemma mulmx_outer_rV (theta w : 'rV[R]_m) :
  theta *m (w^T *m w) = mxdot theta w *: w.
Proof.
by rewrite mulmxA [theta *m w^T]mx11_scalar mul_scalar_mx -mxdot_rowE.
Qed.

(* A frame (sum_k w_k^T w_k = I_m) preserves the norm:
   |theta|^2 = sum_k <theta, w_k>^2. *)
Lemma frame_mxdot I (r : seq I) (P : pred I) (w : I -> 'rV[R]_m)
    (theta : 'rV[R]_m) :
  \sum_(k <- r | P k) (w k)^T *m w k = 1%:M ->
  mxdot theta theta = \sum_(k <- r | P k) mxdot theta (w k) ^+ 2.
Proof.
move=> hw; transitivity (mxdot theta (theta *m 1%:M)).
  by rewrite mulmx1.
rewrite -hw mulmx_sumr mxdot_sumr; apply: eq_bigr => k _.
by rewrite mulmx_outer_rV mxdotZr expr2.
Qed.

(* The trace of a frame: sum_k |w_k|^2 = m. *)
Lemma frame_trace I (r : seq I) (P : pred I) (w : I -> 'rV[R]_m) :
  \sum_(k <- r | P k) (w k)^T *m w k = 1%:M ->
  \sum_(k <- r | P k) mxdot (w k) (w k) = m%:R.
Proof.
move=> hw; transitivity (\tr (1%:M : 'M[R]_m)); last exact: mxtrace1.
rewrite -hw raddf_sum; apply: eq_bigr => k _.
by rewrite mxdot_trace mxtrace_mulC.
Qed.

End frame.

Section frame_cf.
Context {R : realType} {m : nat}.

(* For x of law tuple_prod mu n and a frame w, the regularized modulus
   exp (- s^2 |theta|^2 / 2) |cf nu theta| of the law nu of sum_k x_k w_k
   is a product of one-dimensional factors. *)
Lemma cf_rV_norm_frame (mu : nat -> probability (measurableTypeR R) R) n
    (w : nat -> 'rV[R]_m) (nu : probability 'rV[R]_m R) (s : R) :
  (forall A : set 'rV[R]_m, measurable A ->
     tuple_prod mu n ((fun x => \sum_(k < n) tnth x k *: w k) @^-1` A) =
     nu A) ->
  \sum_(k < n) (w k)^T *m w k = 1%:M ->
  forall theta,
    expR (- s ^+ 2 * mxdot theta theta / 2) * cf_rV_norm nu theta =
    \prod_(k < n) (cf_norm (mu k) (mxdot (w k) theta) *
                   expR (- s ^+ 2 * mxdot (w k) theta ^+ 2 / 2)).
Proof.
move=> numu hw theta; rewrite big_split /= -(cf_rV_norm_tuple_prod numu).
rewrite mulrC (frame_mxdot theta hw) mulr_sumr mulr_suml expR_sum.
by congr (_ * _); apply: eq_bigr => k _; rewrite mxdotC.
Qed.

End frame_cf.

Section remove_gauss.
Context {R : realType} {m : nat}.
Local Open Scope ereal_scope.

(* Removing the Gaussian: if 2 m s^2 <= d^2, P(|Y - z| <= r) is at most
   twice P(|Y + s G - z| <= r + d), for G of law gauss m independent of Y. *)
Lemma ball_le_add_gauss (nu : probability 'rV[R]_m R) (s r d : R)
    (z : 'rV[R]_m) :
  (0 < s)%R -> (0 <= r)%R -> (0 < d)%R ->
  (2 * m%:R * s ^+ 2 <= d ^+ 2)%R ->
  nu [set y | (frobenius (y - z) <= r)%R] <=
  2%:E * (nu \x gauss m) [set p | (frobenius (p.1 + s *: p.2 - z) <= r + d)%R].
Proof.
move=> s0 r0 d0 sd.
set B := [set y | _]; set E := [set p | _].
have mB : measurable B := measurable_ball_rV z r.
pose t : R := (d / s)%R.
have t0 : (0 < t)%R by rewrite divr_gt0.
pose S := [set g : 'rV[R]_m | (frobenius g <= t)%R].
have mS : measurable S.
  rewrite /S (_ : [set g | _] =
      [set g : 'rV[R]_m | (frobenius (g - 0) <= t)%R]).
    by apply/seteqP; split => g /=; rewrite subr0.
  exact: measurable_ball_rV.
have mE : measurable E.
  have mF : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
      (fun p : 'rV[R]_m * 'rV[R]_m => (p.1 + s *: p.2)%R).
    apply: measurable_addmx; first exact: measurable_fst.
    apply: measurable_scalemx; first exact: measurable_cst.
    exact: measurable_snd.
  rewrite -[X in measurable X]setTI.
  exact: (mF measurableT _ (measurable_ball_rV z (r + d))).
have hS : (2^-1)%:E <= gauss m S.
  apply: le_trans (gauss_frobenius_ge t0); rewrite lee_fin.
  have d20 : (0 < d ^+ 2)%R by rewrite exprn_gt0.
  have -> : (m%:R / t ^+ 2 = m%:R * s ^+ 2 / d ^+ 2)%R.
    by rewrite /t expr_div_n invf_div mulrA.
  have : (m%:R * s ^+ 2 / d ^+ 2 <= 2^-1)%R.
    rewrite ler_pdivrMr//; lra.
  lra.
have [x Px] : exists x : R, nu B = x%:E.
  exists (fine (nu B)); rewrite fineK// ge0_fin_numE//.
  by apply: le_lt_trans (probability_le1 _ mB) _; rewrite ltry.
have x0 : (0 <= x)%R by rewrite -lee_fin -Px measure_ge0.
have h1 : x%:E * gauss m S = (nu \x gauss m) (B `*` S).
  rewrite product_measure1E//; apply: (congr1 (fun X => X * gauss m S)).
  by rewrite -Px.
have h2 : (nu \x gauss m) (B `*` S) <= (nu \x gauss m) E.
  apply: le_measure; rewrite ?inE//; first exact: measurableX.
  move=> [y g] [/= yB gS]; rewrite /E /=.
  have -> : (y + s *: g - z = (y - z) + s *: g)%R by rewrite addrAC.
  apply: (le_trans (frobeniusD _ _)).
  rewrite frobeniusZ gtr0_norm//; apply: lerD; first exact: yB.
  apply: (le_trans (ler_wpM2l (ltW s0) gS)).
  by rewrite /t mulrC divfK// lt0r_neq0.
have key : x%:E * (2^-1)%:E <= (nu \x gauss m) E.
  apply: le_trans (lee_wpmul2l _ hS) _; first by rewrite lee_fin.
  by rewrite h1.
rewrite Px; have : (2%:E * (x%:E * (2^-1)%:E) <= 2%:E * (nu \x gauss m) E).
  by apply: lee_wpmul2l => //; rewrite lee_fin.
by rewrite -!EFinM mulrCA mulfV ?mulr1// pnatr_eq0.
Qed.

(* The regularized law on a ball: P(|Y + s G - z| <= r) is at most
   (2 pi)^-m (\int |cf nu| exp (- s^2 |theta|^2 / 2))
   (sqrt (2 pi e / m) r)^m. *)
Lemma add_gauss_ball_le (nu : probability 'rV[R]_m R) (s r : R)
    (z : 'rV[R]_m) : (0 < s)%R -> (0 < r)%R ->
  (nu \x gauss m) [set p | (frobenius (p.1 + s *: p.2 - z) <= r)%R] <=
  ((2 * pi) ^- m)%:E *
  \int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E *
  ((Num.sqrt (2 * pi * expR 1 / m%:R) * r) ^+ m)%:E.
Proof.
move=> s0 r0.
apply: le_trans (prod_gauss_le_cf_rV nu s0 (measurable_ball_rV z r)) _.
apply: lee_wpmul2l.
  rewrite mule_ge0// ?lee_fin ?invr_ge0 ?exprn_ge0// ?mulr_ge0// ?pi_ge0//.
  apply: integral_ge0 => th _.
  by rewrite lee_fin mulr_ge0 ?expR_ge0 ?cf_rV_norm_ge0.
exact: lebesgue_rV_ball_le.
Qed.

Let sqrt_const (eta : R) : (0 < m)%N -> (0 <= eta)%R ->
  (Num.sqrt (2 * pi * expR 1 / m%:R) *
    (eta * Num.sqrt m%:R + eta * Num.sqrt m%:R) / (2 * pi) =
   Num.sqrt (2 * expR 1 / pi) * eta)%R.
Proof.
move=> m0 eta0.
have pi0 : (0 < pi :> R)%R := pi_gt0 R.
have e0 : (0 < expR 1 :> R)%R := expR_gt0 1.
have mR0 : (0 < m%:R :> R)%R by rewrite ltr0n.
have L0 : (0 <= Num.sqrt (2 * pi * expR 1 / m%:R) *
    (eta * Num.sqrt m%:R + eta * Num.sqrt m%:R) / (2 * pi))%R.
  apply: divr_ge0; last by rewrite mulr_ge0// ltW.
  apply: mulr_ge0; first exact: sqrtr_ge0.
  by apply: addr_ge0; apply: mulr_ge0 => //; exact: sqrtr_ge0.
have R0 : (0 <= Num.sqrt (2 * expR 1 / pi) * eta)%R.
  by rewrite mulr_ge0// sqrtr_ge0.
have a0 : (0 <= 2 * pi * expR 1 / m%:R :> R)%R.
  by rewrite divr_ge0 ?mulr_ge0 ?ltW.
have d0 : (0 <= 2 * expR 1 / pi :> R)%R by rewrite divr_ge0 ?mulr_ge0 ?ltW.
have m0' : (0 <= m%:R :> R)%R by rewrite ler0n.
apply/eqP; rewrite -(eqrXn2 (n := 2) _ L0 R0)//; apply/eqP.
rewrite expr_div_n !exprMn (sqr_sqrtr a0) (sqr_sqrtr d0).
rewrite (_ : (eta * Num.sqrt m%:R + eta * Num.sqrt m%:R =
    2 * eta * Num.sqrt m%:R)%R); first by ring.
rewrite !exprMn (sqr_sqrtr m0').
have mn0 : (m%:R != 0 :> R)%R by rewrite gt_eqF.
have pn0 : (pi != 0 :> R)%R by rewrite gt_eqF.
move: mn0 pn0; move: (m%:R : R) (pi : R) => M p mn0 pn0.
by field.
Qed.

(* If the regularized integral is at most C^m and 2 s^2 <= eta^2, then
   P(|Y - z| <= eta sqrt m) <= (sqrt (8 e / pi) C eta)^m. *)
Lemma small_ball_of_cf_bound (nu : probability 'rV[R]_m R) (s C eta : R)
    (z : 'rV[R]_m) :
  (0 < m)%N -> (0 < s)%R -> (0 < eta)%R -> (2 * s ^+ 2 <= eta ^+ 2)%R ->
  (0 <= C)%R ->
  \int[lebesgue_rV m]_th
    (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E <= (C ^+ m)%:E ->
  nu [set y | (frobenius (y - z) <= eta * Num.sqrt m%:R)%R] <=
  ((Num.sqrt (8 * expR 1 / pi) * C * eta) ^+ m)%:E.
Proof.
move=> m0 s0 eta0 seta C0 hK.
have mR0 : (0 < m%:R :> R)%R by rewrite ltr0n.
have r0 : (0 < eta * Num.sqrt m%:R)%R by rewrite mulr_gt0// sqrtr_gt0.
have hsd : (2 * m%:R * s ^+ 2 <= (eta * Num.sqrt m%:R) ^+ 2)%R.
  by rewrite exprMn sqr_sqrtr ?ler0n// mulrAC ler_pM2r.
apply: le_trans (ball_le_add_gauss nu z s0 (ltW r0) r0 hsd) _.
have r20 : (0 < eta * Num.sqrt m%:R + eta * Num.sqrt m%:R)%R.
  by rewrite addr_gt0.
apply: le_trans (lee_wpmul2l _ (add_gauss_ball_le nu z s0 r20)) _.
  by rewrite lee_fin.
set K := \int[lebesgue_rV m]__ _.
set X := (Num.sqrt _ * _)%R.
have pi0 : (0 < pi :> R)%R := pi_gt0 R.
have X0 : (0 <= X)%R by rewrite /X mulr_ge0 ?sqrtr_ge0// addr_ge0// ltW.
apply: (@le_trans _ _
  (2%:E * (((2 * pi) ^- m)%:E * (C ^+ m)%:E * (X ^+ m)%:E))).
  apply: lee_wpmul2l; first by rewrite lee_fin.
  apply: lee_wpmul2r; first by rewrite lee_fin exprn_ge0.
  apply: lee_wpmul2l => //.
  by rewrite lee_fin invr_ge0 exprn_ge0// mulr_ge0// ltW.
rewrite -!EFinM lee_fin.
have e1 : ((2 * pi) ^- m * C ^+ m * X ^+ m =
    (C * (Num.sqrt (2 * expR 1 / pi) * eta)) ^+ m)%R.
  rewrite -(sqrt_const m0 (ltW eta0)) -/X [RHS]exprMn expr_div_n.
  by ring.
have e2 : (Num.sqrt (8 * expR 1 / pi) = 2 * Num.sqrt (2 * expR 1 / pi) :> R)%R.
  rewrite (_ : (8 * expR 1 / pi = 2 ^+ 2 * (2 * expR 1 / pi) :> R)%R).
    by ring.
  by rewrite sqrtrM ?sqr_ge0// sqrtr_sqr ger0_norm.
rewrite e1 e2 (_ : (2 * Num.sqrt (2 * expR 1 / pi) * C * eta =
    2 * (C * (Num.sqrt (2 * expR 1 / pi) * eta)) :> R)%R); first by ring.
rewrite [leRHS]exprMn; apply: ler_wpM2r.
  by rewrite exprn_ge0// mulr_ge0// mulr_ge0 ?sqrtr_ge0// ltW.
by rewrite ler_eXnr// ler1n.
Qed.

End remove_gauss.

Section whitening_reduction.
Context {R : realType} {m : nat}.

(* If x |-> x W does not increase the Euclidean norm, neither does
   y |-> y W^T. *)
Lemma contraction_trmx (W : 'M[R]_m) :
  (forall x : 'rV[R]_m, frobenius (x *m W) <= frobenius x) ->
  forall y : 'rV[R]_m, frobenius (y *m W^T) <= frobenius y.
Proof.
move=> hW y; set a := frobenius (y *m W^T).
have a0 : 0 <= a := frobenius_ge0 _.
have h : a ^+ 2 <= a * frobenius y.
  rewrite /a frobenius_sqr mxdot_mulmxr trmxK mxdotC.
  apply: le_trans (ler_mxdot _ _) _.
  by apply: ler_wpM2r; [exact: frobenius_ge0|exact: hW].
have [a00|an0] := eqVneq a 0; first by rewrite a00 frobenius_ge0.
have ap : 0 < a by rewrite lt0r an0 a0.
by rewrite -(ler_pM2l ap) -expr2.
Qed.

(* The map x |-> sum_k x_k w_k on n-tuples, and the events
   |sum_k x_k w_k - z| <= t, are measurable. *)
Lemma measurable_tuple_sum_rV n (w : nat -> 'rV[R]_m) :
  measurable_fun [set: n.-tuple (measurableTypeR R)]
    (fun x => \sum_(k < n) tnth x k *: w k).
Proof.
apply/measurable_fun_mxP => i j.
rewrite (_ : (fun x => _) = (fun x => \sum_(k < n) tnth x k * w k i j)).
  by apply/funext => x; rewrite summxE; apply: eq_bigr => k _; rewrite mxE.
apply: measurable_sum => k; apply: measurable_funM => //.
exact: measurable_tnth.
Qed.

Lemma measurable_tuple_ball_rV n (w : nat -> 'rV[R]_m) (z : 'rV[R]_m)
    (t : R) :
  measurable [set x : n.-tuple (measurableTypeR R) |
    frobenius (\sum_(k < n) tnth x k *: w k - z) <= t].
Proof.
rewrite -[X in measurable X]setTI.
exact: (@measurable_tuple_sum_rV n w measurableT _ (measurable_ball_rV z t)).
Qed.

(* Whitening: if y |-> y A does not increase the norm, the event
   |sum_k x_k w_k - z| <= t is contained in
   |sum_k x_k (w_k A) - z A| <= t. *)
Lemma tuple_prod_ball_mulmx (mu : nat -> probability (measurableTypeR R) R)
    n (w : nat -> 'rV[R]_m) (A : 'M[R]_m) (z : 'rV[R]_m) (t : R) :
  (forall y : 'rV[R]_m, frobenius (y *m A) <= frobenius y) ->
  (tuple_prod mu n
     [set x | (frobenius (\sum_(k < n) tnth x k *: w k - z) <= t)%R] <=
   tuple_prod mu n
     [set x |
       (frobenius (\sum_(k < n) tnth x k *: (w k *m A) - z *m A) <= t)%R])%E.
Proof.
move=> hA; apply: le_measure; rewrite ?inE.
- exact: (@measurable_tuple_ball_rV n w).
- exact: (@measurable_tuple_ball_rV n (fun k => w k *m A)).
move=> x /= hx; apply: le_trans hx.
have -> : \sum_(k < n) tnth x k *: (w k *m A) - z *m A =
    (\sum_(k < n) tnth x k *: w k - z) *m A.
  rewrite mulmxBl mulmx_suml; congr (_ - _).
  by apply: eq_bigr => k _; rewrite scalemxAl.
exact: hA.
Qed.

(* If W S W^T = I_m for S = sum_k w_k^T w_k, the w_k W^T form a frame. *)
Lemma frame_mulmx n (w : nat -> 'rV[R]_m) (W : 'M[R]_m) :
  W *m (\sum_(k < n) (w k)^T *m w k) *m W^T = 1%:M ->
  \sum_(k < n) (w k *m W^T)^T *m (w k *m W^T) = 1%:M.
Proof.
move=> <-; rewrite mulmx_sumr mulmx_suml; apply: eq_bigr => k _.
by rewrite trmx_mul trmxK !mulmxA.
Qed.

End whitening_reduction.

Section small_ball.
Context {R : realType}.

(* The Brascamp-Lieb inequality in Lebesgue form, as stated in the header
   of comparison/brascamp_lieb.v, until it is proved there. *)
Hypothesis brascamp_lieb : forall m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (F : 'I_n -> R -> \bar R),
  (forall i, mxdot (u i) (u i) = 1) -> (forall i, 0 < c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) -> (forall i t, 0 <= F i t)%E ->
  (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[lebesgue_measure]_t F i t) `^ c i)%E.

(* The Brascamp-Lieb inequality with nonnegative weights: the unit vectors
   are only required where the weight is positive. *)
Lemma brascamp_lieb_ge0 m n (u : 'I_n -> 'rV[R]_m) (c : 'I_n -> R)
    (F : 'I_n -> R -> \bar R) :
  (forall i, 0 < c i -> mxdot (u i) (u i) = 1) -> (forall i, 0 <= c i) ->
  \sum_i c i *: ((u i)^T *m u i) = 1%:M ->
  (forall i, measurable_fun [set: R] (F i)) -> (forall i t, 0 <= F i t)%E ->
  (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i <=
   \prod_i (\int[lebesgue_measure]_t F i t) `^ c i)%E.
Proof.
move=> hu hc hframe mF F0.
pose J := [seq i <- index_enum 'I_n | 0 < c i].
pose s := tnth (in_tuple J).
have Js j : 0 < c (s j).
  by have := mem_tnth j (in_tuple J); rewrite mem_filter => /andP[].
have reindex (T : Type) (idx : T) (op : Monoid.com_law idx) (G : 'I_n -> T) :
    (forall i, ~~ (0 < c i) -> G i = idx) ->
    \big[op/idx]_i G i = \big[op/idx]_(j < size J) G (s j).
  move=> G1; transitivity (\big[op/idx]_(i | 0 < c i) G i).
    rewrite [RHS]big_mkcond; apply: eq_bigr => i _.
    by case: ifPn => // /G1 ->.
  by rewrite -big_filter big_tnth.
have c0 i : ~~ (0 < c i) -> c i = 0.
  by move=> ci; apply/eqP; rewrite eq_le hc andbT leNgt.
rewrite (reindex _ _ _ (fun i => (\int[lebesgue_measure]_t F i t) `^ c i)%E).
  by move=> i /c0 ->; rewrite poweRe0.
have -> : (\int[lebesgue_rV m]_x \prod_i F i (mxdot x (u i)) `^ c i =
    \int[lebesgue_rV m]_x
      \prod_(j < size J) F (s j) (mxdot x (u (s j))) `^ c (s j))%E.
  apply: eq_integral => x _.
  rewrite (reindex _ _ _ (fun i => F i (mxdot x (u i)) `^ c i)%E) //.
  by move=> i /c0 ->; rewrite poweRe0.
apply: brascamp_lieb => //.
- by move=> j; exact: hu.
- rewrite -hframe (reindex _ _ _ (fun i => c i *: ((u i)^T *m u i)))//.
  by move=> i /c0 ->; rewrite scale0r.
Qed.

(* Lemma 3.8 of Koehler and Sohn: for the law nu of sum_k x_k w_k, x of law
   tuple_prod mu n and w a frame, if the one-dimensional factor of each
   nonzero w_k is at most r C, r = |w_k|, then the regularized integral of
   |cf nu| is at most C^m. *)
Lemma cf_rV_regularized_le m (mu : nat -> probability (measurableTypeR R) R) n
    (w : nat -> 'rV[R]_m) (nu : probability 'rV[R]_m R) (s C : R) :
  (forall A : set 'rV[R]_m, measurable A ->
     tuple_prod mu n ((fun x => \sum_(k < n) tnth x k *: w k) @^-1` A) =
     nu A) ->
  \sum_(k < n) (w k)^T *m w k = 1%:M -> 0 < C ->
  (forall k, (k < n)%N -> w k != 0 ->
     (\int[lebesgue_measure]_u
        (cf_norm (mu k) u `^ (frobenius (w k) ^- 2) *
         expR (- s ^+ 2 * u ^+ 2 / (2 * frobenius (w k) ^+ 2)))%:E <=
      (frobenius (w k) * C)%:E)%E) ->
  (\int[lebesgue_rV m]_th
     (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E <=
   (C ^+ m)%:E)%E.
Proof.
move=> numu hw C0 hfac.
pose r (k : 'I_n) := frobenius (w k).
pose c (k : 'I_n) := r k ^+ 2.
pose u (k : 'I_n) := (r k)^-1 *: w k.
pose F (k : 'I_n) (t : R) :=
  (cf_norm (mu k) (r k * t) `^ (c k)^-1 * expR (- s ^+ 2 * t ^+ 2 / 2))%:E.
have c0 k : 0 <= c k by rewrite /c sqr_ge0.
have rn0 (k : 'I_n) : w k != 0 -> r k != 0 by rewrite /r frobenius_eq0.
have cw0 (k : 'I_n) : w k = 0 -> c k = 0.
  by move=> w0; rewrite /c /r w0 frobenius0 expr2 mulr0.
have Fk (k : 'I_n) theta : (F k (mxdot theta (u k)) `^ c k)%E =
    (cf_norm (mu k) (mxdot (w k) theta) *
     expR (- s ^+ 2 * mxdot (w k) theta ^+ 2 / 2))%:E.
  have [w0|wn0] := eqVneq (w k) 0.
    rewrite (cw0 _ w0) poweRe0 w0 mxdot0l cf_norm0 mul1r.
    by rewrite [0 ^+ 2]expr2 !mulr0 mul0r expR0.
  have r0 := rn0 _ wn0.
  rewrite /F poweR_EFin; congr (_%:E).
  rewrite powRM ?powR_ge0 ?expR_ge0// -powRrM mulVf ?expf_neq0// powRr1.
    exact: cf_norm_ge0.
  rewrite -expRM /u mxdotZr mulrA mulfV// mul1r [mxdot theta _]mxdotC.
  congr (_ * expR _); rewrite /c.
  move: r0; move: (r k) => a a0.
  by field.
have hpt theta :
    (expR (- s ^+ 2 * mxdot theta theta / 2) * cf_rV_norm nu theta)%:E =
    (\prod_(k < n) F k (mxdot theta (u k)) `^ c k)%E.
  rewrite (cf_rV_norm_frame s numu hw) -prodEFin.
  by apply: eq_bigr => k _; rewrite Fk.
have F0 k t : (0 <= F k t)%E by rewrite lee_fin mulr_ge0 ?powR_ge0 ?expR_ge0.
apply: (@le_trans _ _
  (\prod_(k < n) (\int[lebesgue_measure]_t F k t) `^ c k)%E).
  have -> : (\int[lebesgue_rV m]_th
        (expR (- s ^+ 2 * mxdot th th / 2) * cf_rV_norm nu th)%:E =
      \int[lebesgue_rV m]_th \prod_(k < n) F k (mxdot th (u k)) `^ c k)%E.
    by apply: eq_integral => th _; exact: hpt.
  apply: brascamp_lieb_ge0.
  - move=> k ck; have wn0 : w k != 0.
      by apply: (contraTneq _ ck) => /cw0 ->; rewrite ltxx.
    have r0 := rn0 _ wn0.
    rewrite /u mxdotZl mxdotZr -(frobenius_sqr (w k)) -/(r k) mulrA -expr2.
    by rewrite exprVn mulVf// expf_neq0.
  - exact: c0.
  - rewrite -hw; apply: eq_bigr => k _.
    have [w0|wn0] := eqVneq (w k) 0.
      by rewrite /u w0 scaler0 trmx0 mul0mx scaler0.
    have r0 := rn0 _ wn0.
    rewrite /u linearZ /= [((r k)^-1 *: w k)^T]linearZ /= -scalemxAl !scalerA.
    have -> : c k * ((r k)^-1 * (r k)^-1) = 1.
      by rewrite /c; move: r0; move: (r k) => a a0; field.
    by rewrite scale1r.
  - move=> k; apply/measurable_EFinP; apply: measurable_funM.
      apply: (measurableT_comp (measurable_powR _)).
      have mcf : measurable_fun [set: R] (cf_norm (mu k)).
        by apply: continuous_measurable_fun; exact: continuous_cf_norm.
      apply: (measurableT_comp mcf).
      exact: mulrl_measurable.
    apply: measurableT_comp; first exact: measurable_expR.
    apply: measurable_funM; last exact: measurable_cst.
    apply: measurable_funM; first exact: measurable_cst.
    by apply: measurable_funX; exact: measurable_id.
  - exact: F0.
apply: (@le_trans _ _ (\prod_(k < n) (C%:E) `^ c k)%E).
  apply: lee_prod => k _; first exact: poweR_ge0.
  have [w0|wn0] := eqVneq (w k) 0; first by rewrite (cw0 _ w0) !poweRe0.
  have r0 := rn0 _ wn0.
  have rpos : 0 < r k by rewrite lt0r r0 frobenius_ge0.
  apply: gt0_ler_poweR.
  - exact: c0.
  - rewrite in_itv /= leey andbT.
    by apply: integral_ge0 => t _; exact: F0.
  - by rewrite in_itv /= leey andbT lee_fin ltW.
  pose g (v : R) := (cf_norm (mu k) v `^ (r k ^- 2) *
    expR (- s ^+ 2 * v ^+ 2 / (2 * r k ^+ 2)))%:E.
  have mg : measurable_fun [set: R] g.
    apply/measurable_EFinP; apply: measurable_funM.
      apply: (measurableT_comp (measurable_powR _)).
      by apply: continuous_measurable_fun; exact: continuous_cf_norm.
    apply: measurableT_comp; first exact: measurable_expR.
    apply: measurable_funM; last exact: measurable_cst.
    apply: measurable_funM; first exact: measurable_cst.
    by apply: measurable_funX; exact: measurable_id.
  have g0 v : (0 <= g v)%E by rewrite lee_fin mulr_ge0 ?powR_ge0 ?expR_ge0.
  have -> : (\int[lebesgue_measure]_t F k t =
      \int[lebesgue_measure]_t g (r k * t + 0)%R)%E.
    apply: eq_integral => t _; rewrite /F /g addr0 /c.
    congr (EFin (_ * expR _)).
    by move: r0; move: (r k) => a a0; field.
  rewrite (ge0_integral_lebesgue_affine _ r0 mg g0) (gtr0_norm rpos).
  apply: (@le_trans _ _ ((r k)^-1%:E * (r k * C)%:E)%E).
    apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 ltW.
    exact: (hfac k (ltn_ord k) wn0).
  by rewrite -EFinM mulrA (mulVf r0) mul1r; exact: lexx.
under eq_bigr => k _ do rewrite poweR_EFin.
rewrite prodEFin lee_fin -powR_sum//.
have -> : \sum_(k < n) c k = m%:R.
  rewrite -(frame_trace hw); apply: eq_bigr => k _.
  by rewrite /c /r frobenius_sqr.
by rewrite powR_mulrn ?lexx// ltW.
Qed.

(* The vector small-ball estimate, given a whitening matrix W and the bound
   r C on the one-dimensional factors of Lemma 3.8 at s = rho. *)
Let vector_small_ball_of m (mu : nat -> probability (measurableTypeR R) R)
    n (w : nat -> 'rV[R]_m) (W : 'M[R]_m) (z : 'rV[R]_m) (rho eta C : R) :
  (0 < m)%N ->
  W *m (\sum_(k < n) (w k)^T *m w k) *m W^T = 1%:M ->
  (forall x : 'rV[R]_m, frobenius (x *m W) <= frobenius x) ->
  0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) -> 0 < C ->
  (forall k r, (k < n)%N -> 0 < r <= rho ->
     (\int[lebesgue_measure]_u
        (cf_norm (mu k) u `^ (r ^- 2) *
         expR (- rho ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <= (r * C)%:E)%E) ->
  0 < eta -> 2 * rho ^+ 2 <= eta ^+ 2 ->
  (tuple_prod mu n [set x | (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
     eta * Num.sqrt m%:R)%R] <=
   ((Num.sqrt (8 * expR 1 / pi) * C * eta) ^+ m)%:E)%E.
Proof.
move=> m0 hW cW rho0 wrho C0 hfac eta0 hre.
have cWT := contraction_trmx cW.
apply: le_trans
  (@tuple_prod_ball_mulmx R m mu n w W^T z (eta * Num.sqrt m%:R) cWT) _.
pose g (x : n.-tuple (measurableTypeR R)) :=
  \sum_(k < n) tnth x k *: (w k *m W^T).
have mg : measurable_fun [set: n.-tuple (measurableTypeR R)] g :=
  @measurable_tuple_sum_rV R m n (fun k => w k *m W^T).
pose G : {mfun n.-tuple (measurableTypeR R) >-> 'rV[R]_m} :=
  HB.pack g (isMeasurableFun.Build _ _ _ _ _ mg).
pose nu := distribution (tuple_prod mu n) G.
have numu (A : set 'rV[R]_m) : measurable A ->
    tuple_prod mu n ((fun x => \sum_(k < n) tnth x k *: (w k *m W^T)) @^-1` A) =
    nu A.
  by move=> _.
change (nu [set y : 'rV[R]_m | (frobenius (y - z *m W^T) <=
  eta * Num.sqrt m%:R)%R] <=
  ((Num.sqrt (8 * expR 1 / pi) * C * eta) ^+ m)%:E)%E.
apply: (@small_ball_of_cf_bound R m nu rho C eta (z *m W^T) m0 rho0 eta0 hre
  (ltW C0)).
apply: (@cf_rV_regularized_le m mu n (fun k => w k *m W^T) nu rho C numu
  (frame_mulmx hW) C0).
move=> k kn wk0; apply: hfac => //.
by rewrite frobenius_gt0 wk0 /=; apply: le_trans (cWT _) (wrho k kn).
Qed.

(* The vector small-ball estimate with an explicit constant, for laws whose
   characteristic functions satisfy the one-dimensional bound of Lemma 3.5
   with constant C, given a whitening matrix W of the frame. *)
Theorem vector_small_ball_fourier m
    (mu : nat -> probability (measurableTypeR R) R) n (w : nat -> 'rV[R]_m)
    (W : 'M[R]_m) (z : 'rV[R]_m) (rho eta C : R) :
  W *m (\sum_(k < n) (w k)^T *m w k) *m W^T = 1%:M ->
  (forall x : 'rV[R]_m, frobenius (x *m W) <= frobenius x) ->
  0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) -> 0 < C ->
  (forall k r s, (k < n)%N -> 0 < r <= s -> s <= 2^-1 ->
     (\int[lebesgue_measure]_u
        (cf_norm (mu k) u `^ (r ^- 2) *
         expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <= (r * C)%:E)%E) ->
  maxr 2 (Num.sqrt (8 * expR 1 / pi) * C) * rho <= eta ->
  (tuple_prod mu n [set x | (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
     eta * Num.sqrt m%:R)%R] <=
   ((maxr 2 (Num.sqrt (8 * expR 1 / pi) * C) * eta) ^+ m)%:E)%E.
Proof.
move=> hW cW rho0 wrho C0 hfac hK.
set K := maxr 2 _ in hK *.
have K2 : 2 <= K by rewrite le_max lexx.
have KC : Num.sqrt (8 * expR 1 / pi) * C <= K by rewrite le_max lexx orbT.
have K0 : 0 < K by apply: lt_le_trans K2.
have eta0 : 0 < eta by apply: lt_le_trans hK; rewrite mulr_gt0.
have mB := @measurable_tuple_ball_rV R m n w z (eta * Num.sqrt m%:R).
have [m0|m0] := posnP m.
  subst m; rewrite expr0; exact: probability_le1.
have [Kbig|Ksmall] := leP 1 (K * eta).
  apply: le_trans (probability_le1 _ mB) _.
  by rewrite lee_fin exprn_ege1.
have h1 : 2 * rho <= eta := le_trans (ler_wpM2r (ltW rho0) K2) hK.
have h2 : 2 * eta < 1 := le_lt_trans (ler_wpM2r (ltW eta0) K2) Ksmall.
have rho_le : rho <= 2^-1 by lra.
have hre : 2 * rho ^+ 2 <= eta ^+ 2.
  apply: (@le_trans _ _ ((2 * rho) ^+ 2)).
    by rewrite exprMn ler_wpM2r ?sqr_ge0// expr2 ler_peMr// ler1n.
  by rewrite lerXn2r// nnegrE ?mulr_ge0// ltW.
apply: le_trans (@vector_small_ball_of m mu n w W z rho eta C m0 hW cW rho0
  wrho C0 _ eta0 hre) _.
  by move=> k r kn hr; exact: (hfac k r rho kn hr rho_le).
rewrite lee_fin; apply: lerXn2r.
- by rewrite nnegrE !mulr_ge0 ?sqrtr_ge0// ltW.
- by rewrite nnegrE mulr_ge0// ltW.
by rewrite ler_pM2r.
Qed.

(* The vector small-ball estimate. *)
Theorem vector_small_ball (v lambda eps : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  exists2 C : R, 0 < C &
  forall m n (mu : nat -> probability (measurableTypeR R) R)
      (w : nat -> 'rV[R]_m) (z : 'rV[R]_m) (rho eta : R),
    (forall k, (k < n)%N -> (\int[mu k]_x ((x ^+ 2)%R)%:E <= v%:E)%E) ->
    (forall k, (k < n)%N -> conc_fun (mu k) lambda <= 1 - eps) ->
    (forall x : 'rV[R]_m, mxdot x x <= \sum_(k < n) mxdot x (w k) ^+ 2) ->
    0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) ->
    C * rho <= eta ->
    (tuple_prod mu n [set x |
       (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
        eta * Num.sqrt m%:R)%R] <= ((C * eta) ^+ m)%:E)%E.
Proof.
move=> v0 l0 e0.
have [C C0 hC] := @gauss_factor_exists R v lambda eps v0 l0 e0.
exists (maxr 2 (Num.sqrt (8 * expR 1 / pi) * C)).
  by rewrite lt_max ltr0n.
move=> m n mu w z rho eta hv hl hS rho0 wrho hK.
pose S := \sum_(k < n) (w k)^T *m w k.
have Ssym : S \is symmetricmx.
  apply/symmetricmxP; rewrite /S linear_sum /=; apply: eq_bigr => k _.
  by rewrite trmx_mul trmxK.
have SI (x : 'rV[R]_m) : mxdot x x <= mxdot (x *m S) x.
  have -> : mxdot (x *m S) x = \sum_(k < n) mxdot x (w k) ^+ 2.
    rewrite /S mulmx_sumr mxdot_suml; apply: eq_bigr => k _.
    by rewrite mulmx_outer_rV mxdotZl mxdotC expr2.
  exact: hS.
have [W [hW cW]] := whitening_exists Ssym SI.
apply: (@vector_small_ball_fourier m mu n w W z rho eta C hW cW rho0 wrho
  C0 _ hK).
move=> k r s kn hr hs.
exact: (hC (mu k) r s (hv k kn) (hl k kn) hr hs).
Qed.

(* The vector small-ball estimate in the form of Proposition 2.4 of Koehler
   and Sohn: laws of mean zero and variance one with
   E[x^2 1_{|x| <= M}] >= 1/2. *)
Theorem vector_small_ball_moments (M : R) : 0 < M ->
  exists2 C : R, 0 < C &
  forall m n (mu : nat -> probability (measurableTypeR R) R)
      (w : nat -> 'rV[R]_m) (z : 'rV[R]_m) (rho eta : R),
    (forall k, (k < n)%N -> (\int[mu k]_x x%:E = 0)%E) ->
    (forall k, (k < n)%N -> (\int[mu k]_x ((x ^+ 2)%R)%:E = 1)%E) ->
    (forall k, (k < n)%N -> ((2^-1)%:E <=
       \int[mu k]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E)%E) ->
    (forall x : 'rV[R]_m, mxdot x x <= \sum_(k < n) mxdot x (w k) ^+ 2) ->
    0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) ->
    C * rho <= eta ->
    (tuple_prod mu n [set x |
       (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
        eta * Num.sqrt m%:R)%R] <= ((C * eta) ^+ m)%:E)%E.
Proof.
move=> M0; have [c c0 hc] := @conc_fun_truncated_exists R M M0.
have l0 : 0 < 8^-1 :> R by rewrite invr_gt0 ltr0n.
have [C C0 hC] := @vector_small_ball 1 (8^-1) c ltr01 l0 c0.
exists C => // m n mu w z rho eta h0 h1 h2 hS rho0 wrho hK.
apply: hC.
- by move=> k kn; rewrite (h1 k kn).
- by move=> k kn; exact: (hc (mu k) (h0 k kn) (h1 k kn) (h2 k kn)).
- exact: hS.
- exact: rho0.
- exact: wrho.
- exact: hK.
Qed.

End small_ball.
