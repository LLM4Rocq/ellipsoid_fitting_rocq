From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis.comparison Require Import normal_mgf chi_square.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.

(**md**************************************************************************)
(* # Subgaussian and subexponential random variables                          *)
(*                                                                            *)
(* A real random variable X on a probability space P is subgaussian with      *)
(* constant K > 0 when E exp (X^2 / K^2) <= 2, and subexponential with        *)
(* constant L > 0 when E exp (|X| / L) <= 2. The least such constants are     *)
(* the norms psi_2 and psi_1 of Vershynin, High-Dimensional Probability,      *)
(* sections 2.5 and 2.7. Independent variables are functions f_i (x_i) of     *)
(* the coordinates of a tuple x of law tuple_prod mu n (lindeberg.v).         *)
(*                                                                            *)
(* ```                                                                        *)
(*    subgaussian P X K == 0 < K, X is measurable and E exp (X^2 / K^2) <= 2  *)
(* subexponential P X L == 0 < L, X is measurable and E exp (|X| / L) <= 2    *)
(*        psi2_norm P X == the infimum of the K with subgaussian P X K        *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results, with explicit constants:                                     *)
(* - subgaussian_tail: P(|X| >= u) <= 2 exp (- u^2 / K^2) for u >= 0;         *)
(*   subexponential_tail: P(|Y| >= u) <= 2 exp (- u / L);                     *)
(* - subgaussian_moment: E X^(2k) <= 2 k! K^(2k), and every power of X is     *)
(*   integrable (integrable_subgaussian_exprn);                               *)
(* - subgaussian_mgf: if E X = 0, then E exp (l X) <= exp (3 l^2 K^2) for     *)
(*   every real l;                                                            *)
(* - subgaussian_of_mgf: conversely, if E exp (l X) <= exp (l^2 s^2) for      *)
(*   every l, then X is subgaussian with every constant L > 0 such that       *)
(*   16 s^2 <= 3 L^2, by integrating against a standard normal law;           *)
(* - Hoeffding's inequality, for x of law tuple_prod mu n and centered        *)
(*   f_i (x_i), subgaussian with constants K_i (subgaussian_sum_mgf,          *)
(*   subgaussian_sum): E exp (l \sum_i a_i f_i (x_i)) <=                      *)
(*   exp (3 l^2 \sum_i a_i^2 K_i^2), and the sum is subgaussian with constant *)
(*   4 (\sum_i a_i^2 K_i^2)^(1/2); for laws nu i of the line with mean 0,     *)
(*   subgaussian with a common constant K (subgaussian_lincomb),              *)
(*   E exp ((\sum_i a_i x_i)^2 / (16 K^2 \sum_i a_i^2)) <= 2 under            *)
(*   tuple_prod nu n;                                                         *)
(* - subexponential_sqr, subexponential_mul: X^2 is subexponential with       *)
(*   constant K^2, and X Y with constant K L, for X, Y subgaussian with       *)
(*   constants K, L; subexponential_center: Y - E Y is subexponential with    *)
(*   constant 3 L when Y is with constant L; a subexponential Y is            *)
(*   integrable (integrable_subexponential);                                  *)
(* - subexponential_mgf: if E Y = 0, then E exp (l Y) <= exp (16 l^2 L^2)     *)
(*   for |l| <= 1 / (2 L);                                                    *)
(* - Bernstein's inequality, for x of law tuple_prod mu n and centered        *)
(*   f_i (x_i), subexponential with constants L_i, and reals a_i              *)
(*   (subexponential_sum_mgf, bernstein_upper, bernstein):                    *)
(*   P(|\sum_i a_i f_i (x_i)| >= t) <= 2 exp (- min (t^2 / (64 s^2),          *)
(*   t / (4 M))), where s^2 = \sum_i a_i^2 L_i^2 and M = \max_i |a_i| L_i;    *)
(*   bernstein_sum: if every f_i has constant L,                              *)
(*   P(|\sum_(i < n) f_i (x_i)| >= t) <=                                      *)
(*   2 exp (- min (t^2 / (64 n L^2), t / (4 L))).                             *)
(* The scalar inequalities behind them: expR_le_quad                          *)
(* (e^y <= 1 + y + y^2 e^|y|), exprn_le_expR (u^k <= k! e^u for u >= 0),      *)
(* le_expR34, expR_mean_le and expR_third_le; lee_prod_ge0 is the             *)
(* monotonicity of products of nonnegative extended reals.                    *)
(*                                                                            *)
(* Planned result (phase 5, stage 3): the infimum psi2_norm is attained, so   *)
(* that subgaussian P X K holds for every K > 0 with psi2_norm P X <= K as    *)
(* soon as X is subgaussian with some constant (monotone convergence).        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section scalar.
Context {R : realType}.
Implicit Types (u y a : R).

(* e^y (1 - y) <= 1, from 1 - y <= e^(-y). *)
Lemma expR_mul1B_le1 y : expR y * (1 - y) <= 1.
Proof.
have h := expR_ge1Dx (- y); rewrite expRN in h.
have e0 := expR_gt0 y.
by rewrite -[leRHS](mulfV (lt0r_neq0 e0)) ler_pM2l.
Qed.

(* The remainder of the first-order Taylor expansion of exp. *)
Lemma expR_le_quad y : expR y <= 1 + y + y ^+ 2 * expR `|y|.
Proof.
have h := expR_mul1B_le1 y; have e0 := expR_gt0 y.
have [y0|y0] := leP 0 y.
  rewrite ger0_norm//.
  have h1 : expR y <= 1 + y * expR y by nra.
  nra.
have h1 : expR y <= 1 + y + y ^+ 2 by nra.
have : 1 <= expR `|y| by rewrite -expR0 ler_expR.
nra.
Qed.

Lemma exprn_le_expR u k : 0 <= u -> u ^+ k <= k`!%:R * expR u.
Proof.
move=> u0; case: k => [|k].
  by rewrite expr0 fact0 mul1r -expR0 ler_expR.
have := expR_ge1Dxn k u0; have := expR_gt0 u.
have : 0 < k.+1`!%:R :> R by rewrite ltr0n fact_gt0.
move=> f0 e0 h; rewrite -ler_pdivrMl//.
by apply: le_trans h; rewrite mulrC lerDr.
Qed.

Lemma sqr_le_expR u : 0 <= u -> u ^+ 2 <= 2 * expR u.
Proof. by move=> u0; have := exprn_le_expR 2 u0. Qed.

Lemma le_expR34 u : 0 <= u -> u <= expR (3 / 4 * u).
Proof.
move=> u0; have u34 : 0 <= 3 / 4 * u by rewrite mulr_ge0.
have := expR_ge1Dxn 1 u34; rewrite (_ : 2`!%:R = 2 :> R) // => h.
apply: le_trans h; have := sqr_ge0 (3 / 4 * u - 4 / 3).
nra.
Qed.

Lemma expR_mean_le a b : expR ((a + b) / 2) <= (expR a + expR b) / 2.
Proof.
have ea := expR_gt0 (a / 2); have eb := expR_gt0 (b / 2).
have -> : expR ((a + b) / 2) = expR (a / 2) * expR (b / 2).
  by rewrite -expRD mulrDl.
have -> : expR a = expR (a / 2) ^+ 2.
  by rewrite -expRM_natl mulrC -mulrA mulVf ?mulr1.
have -> : expR b = expR (b / 2) ^+ 2.
  by rewrite -expRM_natl mulrC -mulrA mulVf ?mulr1.
have := sqr_ge0 (expR (a / 2) - expR (b / 2)).
nra.
Qed.

Lemma expR_third_le y : expR (y / 3) <= (expR y + 2) / 3.
Proof.
have e := expR_gt0 (y / 3).
have -> : expR y = expR (y / 3) ^+ 3.
  by rewrite -expRM_natl mulrC -mulrA mulVf ?mulr1.
have := mulr_ge0 (sqr_ge0 (expR (y / 3) - 1)) (ltW e).
nra.
Qed.

End scalar.

Section subgaussian.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition subgaussian (X : T -> R) (K : R) : Prop :=
  [/\ 0 < K, measurable_fun [set: T] X &
      (\int[P]_t (expR (X t ^+ 2 / K ^+ 2))%:E <= 2%:E)%E].

Definition subexponential (Y : T -> R) (L : R) : Prop :=
  [/\ 0 < L, measurable_fun [set: T] Y &
      (\int[P]_t (expR (`|Y t| / L))%:E <= 2%:E)%E].

Definition psi2_norm (X : T -> R) : R := inf [set K | subgaussian X K].

End subgaussian.

Section subgaussian_props.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.
Implicit Types (X Y : T -> R) (K L : R).

Lemma measurable_expR_sqr X K : measurable_fun [set: T] X ->
  measurable_fun [set: T] (fun t => expR (X t ^+ 2 / K ^+ 2)).
Proof.
move=> mX; apply: measurableT_comp => //; apply: measurable_funM => //.
exact: measurable_funX.
Qed.

Lemma integrable_subgaussian_expR X K : subgaussian P X K ->
  P.-integrable [set: T] (fun t => (expR (X t ^+ 2 / K ^+ 2))%:E).
Proof.
case=> K0 mX h; apply/integrableP; split.
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
under eq_integral do rewrite gee0_abs ?lee_fin ?expR_ge0//.
by apply: le_lt_trans h _; rewrite ltry.
Qed.

Lemma subgaussian_exprn_le X K k t : (0 < K)%R ->
  (X t ^+ (2 * k) <= K ^+ (2 * k) * k`!%:R * expR (X t ^+ 2 / K ^+ 2))%R.
Proof.
move=> K0; have u0 : (0 <= X t ^+ 2 / K ^+ 2)%R by rewrite divr_ge0 ?sqr_ge0.
have := exprn_le_expR k u0; rewrite expr_div_n -!exprM.
have K2 : (0 < K ^+ (2 * k))%R by rewrite exprn_gt0.
by rewrite ler_pdivrMr // mulrC mulrA.
Qed.

Lemma subgaussian_moment X K k : subgaussian P X K ->
  \int[P]_t (X t ^+ (2 * k))%:E <= (2 * k`!%:R * K ^+ (2 * k))%:E.
Proof.
move=> sX; have [K0 mX h] := sX.
have me := measurable_expR_sqr K mX.
apply: (@le_trans _ _
  (\int[P]_t ((K ^+ (2 * k) * k`!%:R) * expR (X t ^+ 2 / K ^+ 2))%:E)).
  apply: ge0_le_integral => //.
  - by move=> t _; rewrite lee_fin exprM exprn_ge0 ?sqr_ge0.
  - by apply/measurable_EFinP; apply: measurable_funX.
  - by apply/measurable_EFinP; apply: measurable_funM.
  - by move=> t _; rewrite lee_fin; exact: subgaussian_exprn_le.
have c0 : (0 <= K ^+ (2 * k) * k`!%:R)%R by rewrite mulr_ge0 ?exprn_ge0 ?ltW.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //; first by apply/measurable_EFinP.
apply: le_trans (lee_wpmul2l _ h) _; first by rewrite lee_fin.
by rewrite -EFinM lee_fin [in leLHS]mulrC mulrA [in leRHS]mulrAC.
Qed.

Lemma integrable_subgaussian_exprn X K k : subgaussian P X K ->
  P.-integrable [set: T] (fun t => (X t ^+ k)%:E).
Proof.
move=> sX; have [K0 mX h] := sX.
have m2 : measurable_fun [set: T] (fun t => X t ^+ (2 * k))%R.
  exact: measurable_funX.
have i2 : P.-integrable [set: T] (fun t => (X t ^+ (2 * k))%:E).
  apply/integrableP; split; first exact/measurable_EFinP.
  have e t : `|(X t ^+ (2 * k))%:E| = (X t ^+ (2 * k))%:E.
    by rewrite gee0_abs // lee_fin exprM exprn_ge0 // sqr_ge0.
  under eq_integral do rewrite e.
  by apply: le_lt_trans (subgaussian_moment k sX) _; rewrite ltry.
have i1 : P.-integrable [set: T] (fun t => (1 + X t ^+ (2 * k))%:E)%R.
  under eq_fun do rewrite EFinD.
  apply: integrableD => //; exact: finite_measure_integrable_cst.
apply: le_integrable i1 => //.
  by apply/measurable_EFinP; exact: measurable_funX.
move=> t _; rewrite !abse_EFin lee_fin normrX.
have e0 : (0 <= X t ^+ (2 * k))%R by rewrite exprM exprn_ge0 // sqr_ge0.
rewrite [`|1 + _|%R]ger0_norm; first exact: (addr_ge0 ler01 e0).
have [x1|x1] := (leP `|X t| 1)%R.
  by apply: le_trans (exprn_ile1 _ _ _) _ => //; rewrite lerDl.
apply: (@le_trans _ _ (`|X t| ^+ (2 * k))%R).
  by rewrite ler_eXn2l // leq_pmull.
by rewrite -normrX ger0_norm // lerDr.
Qed.

Lemma subgaussian_tail X K (u : R) : subgaussian P X K -> (0 <= u)%R ->
  P [set t | u <= `|X t|]%R <= (2 * expR (- (u ^+ 2 / K ^+ 2)))%:E.
Proof.
move=> sX u0; have [K0 mX h] := sX.
have K2 : (0 < K ^+ 2)%R by rewrite exprn_gt0.
have -> : [set t | (u <= `|X t|)%R] =
    [set t | (u ^+ 2 / K ^+ 2 <= X t ^+ 2 / K ^+ 2)%R].
  apply/seteqP; split => t /=.
    move=> ux; rewrite ler_pM2r ?invr_gt0 // -(real_normK (num_real (X t))).
    by have := normr_ge0 (X t); nra.
  rewrite ler_pM2r ?invr_gt0 // -(real_normK (num_real (X t))) => h2.
  by have := normr_ge0 (X t); nra.
have mf : measurable_fun [set: T] (fun t => X t ^+ 2 / K ^+ 2)%R.
  by apply: measurable_funM => //; exact: measurable_funX.
apply: le_trans (measure_ge_expR P (u ^+ 2 / K ^+ 2)%R mf ler01) _.
under eq_integral do rewrite mul1r expRD EFinM.
rewrite ge0_integralZr //.
  by apply/measurable_EFinP; exact: measurable_expR_sqr.
by rewrite EFinM lee_wpmul2r // lee_fin expR_ge0.
Qed.

Lemma subexponential_tail Y L (u : R) : subexponential P Y L ->
  P [set t | u <= `|Y t|]%R <= (2 * expR (- (u / L)))%:E.
Proof.
move=> [L0 mY h].
have mf : measurable_fun [set: T] (fun t => `|Y t| / L)%R.
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurableT_comp (@normr_measurable _ _) mY.
have -> : [set t | (u <= `|Y t|)%R] = [set t | (u / L <= `|Y t| / L)%R].
  by apply/seteqP; split => t /=; rewrite ler_pM2r ?invr_gt0.
apply: le_trans (measure_ge_expR P (u / L)%R mf ler01) _.
under eq_integral do rewrite mul1r expRD EFinM.
rewrite ge0_integralZr //.
  by apply/measurable_EFinP; apply: measurableT_comp.
by rewrite EFinM lee_wpmul2r // lee_fin expR_ge0.
Qed.

Lemma subgaussian_mgf_pointwise (x K l : R) : (0 < K)%R ->
  (expR (l * x) <= 1 + l * x +
     l ^+ 2 * K ^+ 2 * expR (l ^+ 2 * K ^+ 2) * expR (x ^+ 2 / K ^+ 2))%R.
Proof.
move=> K0; have K2 : (0 < K ^+ 2)%R by rewrite exprn_gt0.
have Kn : K != 0%R by rewrite gt_eqF.
have u0 : (0 <= x ^+ 2 / K ^+ 2)%R by rewrite divr_ge0 ?sqr_ge0 ?ltW.
have h1 := expR_le_quad (l * x).
have h2 : (`|l * x| <= l ^+ 2 * K ^+ 2 + x ^+ 2 / K ^+ 2 / 4)%R.
  have e : (l ^+ 2 * K ^+ 2 + x ^+ 2 / K ^+ 2 / 4 - `|l| * `|x| =
      (`|l| * K - `|x| / K / 2) ^+ 2)%R.
    rewrite sqrrB !exprMn -!(real_normK (num_real l)).
    by rewrite -!(real_normK (num_real x)); field.
  by rewrite normrM -subr_ge0 e sqr_ge0.
have h3 : (expR `|l * x| <=
    expR (l ^+ 2 * K ^+ 2) * expR (x ^+ 2 / K ^+ 2 / 4))%R.
  by rewrite -expRD ler_expR.
have h4 : ((l * x) ^+ 2 <=
    l ^+ 2 * K ^+ 2 * expR (3 / 4 * (x ^+ 2 / K ^+ 2)))%R.
  have -> : ((l * x) ^+ 2 = l ^+ 2 * K ^+ 2 * (x ^+ 2 / K ^+ 2))%R.
    by field.
  by rewrite ler_wpM2l ?le_expR34 // mulr_ge0 ?sqr_ge0.
have h5 : ((l * x) ^+ 2 * expR `|l * x| <=
    l ^+ 2 * K ^+ 2 * expR (3 / 4 * (x ^+ 2 / K ^+ 2)) *
    (expR (l ^+ 2 * K ^+ 2) * expR (x ^+ 2 / K ^+ 2 / 4)))%R.
  by apply: ler_pM => //; rewrite ?sqr_ge0 ?expR_ge0.
have e : (l ^+ 2 * K ^+ 2 * expR (3 / 4 * (x ^+ 2 / K ^+ 2)) *
    (expR (l ^+ 2 * K ^+ 2) * expR (x ^+ 2 / K ^+ 2 / 4)) =
    l ^+ 2 * K ^+ 2 * expR (l ^+ 2 * K ^+ 2) * expR (x ^+ 2 / K ^+ 2))%R.
  have -> : (expR (x ^+ 2 / K ^+ 2) = expR (3 / 4 * (x ^+ 2 / K ^+ 2)) *
      expR (x ^+ 2 / K ^+ 2 / 4))%R.
    by rewrite -expRD; congr expR; lra.
  ring.
rewrite -e; lra.
Qed.

Lemma subgaussian_mgf X K (l : R) :
  subgaussian P X K -> (\int[P]_t X t = 0)%R ->
  \int[P]_t (expR (l * X t))%:E <= (expR (3 * l ^+ 2 * K ^+ 2))%:E.
Proof.
move=> sX X0; have [K0 mX h] := sX.
set c := (l ^+ 2 * K ^+ 2 * expR (l ^+ 2 * K ^+ 2))%R.
have c0 : (0 <= c)%R by rewrite /c mulr_ge0 ?expR_ge0 // mulr_ge0 ?sqr_ge0.
have iX : P.-integrable [set: T] (EFin \o X).
  have := integrable_subgaussian_exprn 1 sX.
  by apply: eq_integrable => // t _; rewrite /= expr1.
have ie := integrable_subgaussian_expR sX.
have i1 : P.-integrable [set: T] (EFin \o (fun _ : T => 1%R)).
  exact: finite_measure_integrable_cst.
have iXl : P.-integrable [set: T] (EFin \o (fun t => l * X t)%R).
  have := integrableZl measurableT l iX.
  by apply: eq_integrable => // t _; rewrite /= EFinM.
have iec : P.-integrable [set: T]
    (EFin \o (fun t => c * expR (X t ^+ 2 / K ^+ 2))%R).
  have := integrableZl measurableT c ie.
  by apply: eq_integrable => // t _; rewrite /= EFinM.
have i1X : P.-integrable [set: T] (EFin \o (fun t => 1 + l * X t)%R).
  have := integrableD measurableT i1 iXl.
  by apply: eq_integrable => // t _; rewrite /= EFinD.
have iF : P.-integrable [set: T]
    (EFin \o (fun t => 1 + l * X t + c * expR (X t ^+ 2 / K ^+ 2))%R).
  have := integrableD measurableT i1X iec.
  by apply: eq_integrable => // t _; rewrite /= EFinD.
apply: (@le_trans _ _
  (\int[P]_t (1 + l * X t + c * expR (X t ^+ 2 / K ^+ 2))%:E)).
  apply: ge0_le_integral => //.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    exact: measurable_funM.
  - exact: (measurable_int _ iF).
  - by move=> t _; rewrite lee_fin /c; exact: subgaussian_mgf_pointwise.
have -> : \int[P]_t (1 + l * X t + c * expR (X t ^+ 2 / K ^+ 2))%:E =
    (\int[P]_t (1 + l * X t + c * expR (X t ^+ 2 / K ^+ 2)))%:E.
  by rewrite fineK // integrable_fin_num.
rewrite RintegralD // RintegralD // RintegralZl // RintegralZl //.
rewrite Rintegral_cst //.
have -> : fine (P [set: T]) = 1%R by rewrite probability_setT.
rewrite X0 mulr0 mul1r addr0 lee_fin.
have he : (\int[P]_x expR (X x ^+ 2 / K ^+ 2) <= 2)%R.
  by rewrite -lee_fin fineK // integrable_fin_num.
apply: (@le_trans _ _ (1 + 2 * c)%R).
  by rewrite lerD2l mulrC ler_wpM2r.
have e3 : (3 * l ^+ 2 * K ^+ 2 =
    l ^+ 2 * K ^+ 2 + 2 * (l ^+ 2 * K ^+ 2))%R by ring.
rewrite /c e3 expRD.
have := expR_ge1Dx (2 * (l ^+ 2 * K ^+ 2)).
have : (1 <= expR (l ^+ 2 * K ^+ 2))%R.
  by rewrite -expR0 ler_expR mulr_ge0 ?sqr_ge0.
have := expR_ge0 (l ^+ 2 * K ^+ 2).
nra.
Qed.

End subgaussian_props.

Section subexponential_props.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.
Implicit Types (X Y : T -> R) (K L : R).

Lemma subexponential_sqr X K : subgaussian P X K ->
  subexponential P (fun t => X t ^+ 2)%R (K ^+ 2).
Proof.
case=> K0 mX h; split.
- by rewrite exprn_gt0.
- exact: measurable_funX.
- have e t : (`|X t ^+ 2| = X t ^+ 2)%R by rewrite ger0_norm ?sqr_ge0.
  by under eq_integral do rewrite e.
Qed.

Lemma subexponential_mul X Y K L : subgaussian P X K -> subgaussian P Y L ->
  subexponential P (fun t => X t * Y t)%R (K * L).
Proof.
move=> sX sY; have [K0 mX hX] := sX; have [L0 mY hY] := sY.
have Kn : K != 0%R by rewrite gt_eqF.
have Ln : L != 0%R by rewrite gt_eqF.
split; first by rewrite mulr_gt0.
  exact: measurable_funM.
have pw t : (expR (`|X t * Y t| / (K * L)) <=
    (expR (X t ^+ 2 / K ^+ 2) + expR (Y t ^+ 2 / L ^+ 2)) / 2)%R.
  apply: le_trans (expR_mean_le _ _); rewrite ler_expR.
  have -> : (`|X t * Y t| / (K * L) = (`|X t| / K) * (`|Y t| / L))%R.
    by rewrite normrM; field.
  have -> : (X t ^+ 2 / K ^+ 2 = (`|X t| / K) ^+ 2)%R.
    by rewrite expr_div_n real_normK ?num_real.
  have -> : (Y t ^+ 2 / L ^+ 2 = (`|Y t| / L) ^+ 2)%R.
    by rewrite expr_div_n real_normK ?num_real.
  by have := sqr_ge0 (`|X t| / K - `|Y t| / L)%R; nra.
have mx := measurable_expR_sqr K mX; have my := measurable_expR_sqr L mY.
apply: (@le_trans _ _ (\int[P]_t ((2^-1 * expR (X t ^+ 2 / K ^+ 2))%:E +
    (2^-1 * expR (Y t ^+ 2 / L ^+ 2))%:E))).
  apply: ge0_le_integral => //.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    apply: measurable_funM => //; apply: measurableT_comp => //.
    exact: measurable_funM.
  - by apply: emeasurable_funD; apply/measurable_EFinP; exact: measurable_funM.
  - by move=> t _; rewrite -EFinD lee_fin; have := pw t; lra.
rewrite ge0_integralD //.
- by apply/measurable_EFinP; exact: measurable_funM.
- by apply/measurable_EFinP; exact: measurable_funM.
- under eq_integral do rewrite EFinM.
  under [X in _ + X]eq_integral do rewrite EFinM.
  rewrite !ge0_integralZl_EFin //; try by apply/measurable_EFinP.
    all: try by move=> t _; rewrite lee_fin expR_ge0.
  have h2 : (0 <= (2^-1)%:E :> \bar R) by rewrite lee_fin invr_ge0.
  apply: le_trans (leeD (lee_wpmul2l h2 hX) (lee_wpmul2l h2 hY)) _.
  by rewrite -!EFinM -EFinD lee_fin; lra.
Qed.

Lemma integrable_subexponential_expR Y L : subexponential P Y L ->
  P.-integrable [set: T] (fun t => (expR (`|Y t| / L))%:E).
Proof.
case=> L0 mY h; apply/integrableP; split.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; apply: measurableT_comp.
have e t : `|(expR (`|Y t| / L))%:E| = (expR (`|Y t| / L))%:E.
  by rewrite gee0_abs // lee_fin expR_ge0.
under eq_integral do rewrite e.
by apply: le_lt_trans h _; rewrite ltry.
Qed.

Lemma integrable_subexponential Y L : subexponential P Y L ->
  P.-integrable [set: T] (EFin \o Y).
Proof.
move=> sY; have [L0 mY h] := sY.
have ie := integrable_subexponential_expR sY.
have iL : P.-integrable [set: T] (fun t => (L * expR (`|Y t| / L))%:E).
  have := integrableZl measurableT L ie.
  by apply: eq_integrable => // t _; rewrite EFinM.
apply: le_integrable iL => //; first exact/measurable_EFinP.
move=> t _; rewrite !abse_EFin lee_fin.
have eL : (0 <= L * expR (`|Y t| / L))%R by rewrite mulr_ge0 ?expR_ge0 // ltW.
rewrite [X in (_ <= X)%R]ger0_norm //.
have h1 := expR_ge1Dx (`|Y t| / L).
have hu : (`|Y t| / L * L = `|Y t|)%R by rewrite mulfVK ?gt_eqF.
nra.
Qed.

Lemma subexponential_center Y L : subexponential P Y L ->
  subexponential P (fun t => Y t - \int[P]_s Y s)%R (3 * L).
Proof.
move=> sY; have [L0 mY h] := sY.
have Ln : L != 0%R by rewrite gt_eqF.
have ie := integrable_subexponential_expR sY.
have iY := integrable_subexponential sY.
have ie' : P.-integrable [set: T] (EFin \o (fun t => expR (`|Y t| / L))%R).
  by [].
have i1 := finite_measure_integrable_cst P 1%R measurableT.
set m := (\int[P]_s Y s)%R.
have hR : (\int[P]_t expR (`|Y t| / L) <= 2)%R.
  by rewrite -lee_fin fineK // integrable_fin_num.
have m1 : (`|m| <= L)%R.
  apply: le_trans (le_normr_Rintegral measurableT iY) _.
  have iabs : P.-integrable [set: T] (EFin \o (fun t => `|Y t|)%R).
    exact: (integrable_norm iY).
  have iB : P.-integrable [set: T]
      (EFin \o (fun t => expR (`|Y t| / L) - 1)%R).
    have := integrableB measurableT ie' i1.
    by apply: eq_integrable => // t _; rewrite /= -EFinB.
  apply: (@le_trans _ _ (\int[P]_t (L * (expR (`|Y t| / L) - 1)))%R).
    apply: le_Rintegral => //.
    - have := integrableZl measurableT L iB.
      by apply: eq_integrable => // t _; rewrite /= -EFinM.
    - move=> t _; have := expR_ge1Dx (`|Y t| / L).
      rewrite -(ler_pM2l L0) mulrDr mulr1 mulrCA mulfV // mulr1 => h1.
      by rewrite mulrBr mulr1; lra.
  rewrite RintegralZl // RintegralB // Rintegral_cst //.
  have -> : fine (P [set: T]) = 1%R by rewrite probability_setT.
  by rewrite mulr1 -[leRHS]mulr1 ler_pM2l //; lra.
split; first by rewrite mulr_gt0.
  by apply: measurable_funB.
have e13 : (expR (3^-1) <= 3 / 2 :> R)%R.
  have := expR_mul1B_le1 (3^-1 : R); have := expR_gt0 (3^-1 : R).
  move=> e0 h1; have h3 : (0 < 1 - 3^-1 :> R)%R by lra.
  by rewrite -(ler_pM2r h3); lra.
have pw t : (expR (`|Y t - m| / (3 * L)) <=
    2^-1 * expR (`|Y t| / L) + 1)%R.
  have h1 : (`|Y t - m| / (3 * L) <= (`|Y t| / L) / 3 + 3^-1)%R.
    rewrite ler_pdivrMr ?mulr_gt0 //.
    have -> : ((`|Y t| / L / 3 + 3^-1) * (3 * L) = `|Y t| + L)%R by field.
    by apply: le_trans (ler_normB _ _) _; rewrite lerD2l.
  apply: le_trans (_ : expR ((`|Y t| / L) / 3 + 3^-1) <= _)%R.
    by rewrite ler_expR.
  rewrite expRD.
  have := expR_third_le (`|Y t| / L); have := expR_gt0 (`|Y t| / L / 3).
  have := expR_gt0 (3^-1 : R); have := expR_ge0 (`|Y t| / L).
  by nra.
have iZ : P.-integrable [set: T]
    (EFin \o (fun t => 2^-1 * expR (`|Y t| / L))%R).
  have := integrableZl measurableT 2^-1 ie'.
  by apply: eq_integrable => // t _; rewrite /= EFinM.
have iF : P.-integrable [set: T]
    (EFin \o (fun t => 2^-1 * expR (`|Y t| / L) + 1)%R).
  have := integrableD measurableT iZ i1.
  by apply: eq_integrable => // t _; rewrite /= EFinD.
apply: (@le_trans _ _ (\int[P]_t (2^-1 * expR (`|Y t| / L) + 1)%:E)).
  apply: ge0_le_integral => //.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    apply: measurable_funM => //; apply: measurableT_comp => //.
    exact: measurable_funB.
  - exact: (measurable_int _ iF).
  - by move=> t _; rewrite lee_fin; exact: pw.
have -> : \int[P]_t (2^-1 * expR (`|Y t| / L) + 1)%:E =
    (\int[P]_t (2^-1 * expR (`|Y t| / L) + 1))%:E.
  by rewrite fineK // integrable_fin_num.
rewrite RintegralD // RintegralZl // Rintegral_cst //.
have -> : fine (P [set: T]) = 1%R by rewrite probability_setT.
by rewrite lee_fin; lra.
Qed.

Lemma subexponential_mgf Y L (l : R) :
  subexponential P Y L -> (\int[P]_t Y t = 0)%R -> (`|l| <= (2 * L)^-1)%R ->
  \int[P]_t (expR (l * Y t))%:E <= (expR (16 * l ^+ 2 * L ^+ 2))%:E.
Proof.
move=> sY Y0 hl; have [L0 mY h] := sY.
have Ln : L != 0%R by rewrite gt_eqF.
set c := (8 * l ^+ 2 * L ^+ 2)%R.
have c0 : (0 <= c)%R.
  by rewrite /c; have := sqr_ge0 l; have := sqr_ge0 L; nra.
have pw t : (expR (l * Y t) <= 1 + l * Y t + c * expR (`|Y t| / L))%R.
  have h1 := expR_le_quad (l * Y t).
  have L2 : (0 < 2 * L)%R by rewrite mulr_gt0.
  have u0 : (0 <= `|Y t| / (2 * L))%R by rewrite divr_ge0 // ltW.
  have h2 : (expR `|l * Y t| <= expR (`|Y t| / (2 * L)))%R.
    rewrite ler_expR normrM [X in (_ <= X)%R]mulrC.
    by rewrite ler_wpM2r.
  have h3 : ((l * Y t) ^+ 2 <=
      l ^+ 2 * (8 * L ^+ 2 * expR (`|Y t| / (2 * L))))%R.
    rewrite exprMn ler_wpM2l ?sqr_ge0 //.
    have := sqr_le_expR u0.
    have -> : ((`|Y t| / (2 * L)) ^+ 2 = Y t ^+ 2 / (4 * L ^+ 2))%R.
      by rewrite expr_div_n real_normK ?num_real; field.
    rewrite ler_pdivrMr ?mulr_gt0 ?exprn_gt0 //.
    by move=> h4; nra.
  have e2 : (expR (`|Y t| / (2 * L)) * expR (`|Y t| / (2 * L)) =
      expR (`|Y t| / L))%R.
    by rewrite -expRD; congr expR; field.
  have h5 : ((l * Y t) ^+ 2 * expR `|l * Y t| <=
      l ^+ 2 * (8 * L ^+ 2 * expR (`|Y t| / (2 * L))) *
      expR (`|Y t| / (2 * L)))%R.
    by apply: ler_pM => //; rewrite ?sqr_ge0 ?expR_ge0.
  have e3 : (l ^+ 2 * (8 * L ^+ 2 * expR (`|Y t| / (2 * L))) *
      expR (`|Y t| / (2 * L)) = c * expR (`|Y t| / L))%R.
    by rewrite /c -e2; ring.
  lra.
have iY := integrable_subexponential sY.
have ie' : P.-integrable [set: T] (EFin \o (fun t => expR (`|Y t| / L))%R).
  exact: integrable_subexponential_expR sY.
have i1 := finite_measure_integrable_cst P 1%R measurableT.
have iYl : P.-integrable [set: T] (EFin \o (fun t => l * Y t)%R).
  have := integrableZl measurableT l iY.
  by apply: eq_integrable => // t _; rewrite /= EFinM.
have iec : P.-integrable [set: T]
    (EFin \o (fun t => c * expR (`|Y t| / L))%R).
  have := integrableZl measurableT c ie'.
  by apply: eq_integrable => // t _; rewrite /= EFinM.
have i1Y : P.-integrable [set: T] (EFin \o (fun t => 1 + l * Y t)%R).
  have := integrableD measurableT i1 iYl.
  by apply: eq_integrable => // t _; rewrite /= EFinD.
have iF : P.-integrable [set: T]
    (EFin \o (fun t => 1 + l * Y t + c * expR (`|Y t| / L))%R).
  have := integrableD measurableT i1Y iec.
  by apply: eq_integrable => // t _; rewrite /= EFinD.
apply: (@le_trans _ _ (\int[P]_t (1 + l * Y t + c * expR (`|Y t| / L))%:E)).
  apply: ge0_le_integral => //.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    exact: measurable_funM.
  - exact: (measurable_int _ iF).
  - by move=> t _; rewrite lee_fin; exact: pw.
have -> : \int[P]_t (1 + l * Y t + c * expR (`|Y t| / L))%:E =
    (\int[P]_t (1 + l * Y t + c * expR (`|Y t| / L)))%:E.
  by rewrite fineK // integrable_fin_num.
rewrite RintegralD // RintegralD // RintegralZl // RintegralZl //.
rewrite Rintegral_cst //.
have -> : fine (P [set: T]) = 1%R by rewrite probability_setT.
rewrite Y0 mulr0 mul1r addr0 lee_fin.
have he : (\int[P]_x expR (`|Y x| / L) <= 2)%R.
  by rewrite -lee_fin fineK // integrable_fin_num.
apply: (@le_trans _ _ (1 + 2 * c)%R).
  by rewrite lerD2l mulrC ler_wpM2r.
by have := expR_ge1Dx (16 * l ^+ 2 * L ^+ 2); rewrite /c; lra.
Qed.

End subexponential_props.

Section subgaussian_mgf_converse.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.
Local Notation N := (@normal_prob R 0 1).

Lemma subgaussian_of_mgf (X : T -> R) (s L : R) :
  measurable_fun [set: T] X -> (0 < L)%R -> (16 * s ^+ 2 <= 3 * L ^+ 2)%R ->
  (forall l : R,
    \int[P]_t (expR (l * X t))%:E <= (expR (l ^+ 2 * s ^+ 2))%:E) ->
  subgaussian P X L.
Proof.
move=> mX L0 sL hm; split => //.
have Ln : L != 0%R by rewrite gt_eqF.
set a := (Num.sqrt 2 / L)%R.
have a2 : (a ^+ 2 = 2 / L ^+ 2)%R by rewrite /a expr_div_n sqr_sqrtr.
have E1 t : (expR (X t ^+ 2 / L ^+ 2))%:E =
    \int[N]_g (expR ((a * X t) * g))%:E.
  rewrite integral_normal_expR ?oner_neq0 // mulr0 add0r expr1n mulr1.
  by congr (expR _)%:E; rewrite exprMn a2; field.
under eq_integral do rewrite E1.
pose g := fun p : T * measurableTypeR R => (expR (a * X p.1 * p.2))%:E.
have mg : measurable_fun [set: T * measurableTypeR R] g.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  apply: measurable_funM => //; apply: measurable_funM => //.
  exact: measurableT_comp mX measurable_fst.
have g0 p : 0 <= g p by rewrite /g lee_fin expR_ge0.
have FT := fubini_tonelli1 (m1 := P) (m2 := N) g mg g0.
have GT := fubini_tonelli2 (m1 := P) (m2 := N) g mg g0.
rewrite FT /fubini_F /fubini_G /g /= in GT; rewrite GT.
apply: (@le_trans _ _ (\int[N]_y (expR ((a ^+ 2 * s ^+ 2) * y ^+ 2))%:E)).
  apply: ge0_le_integral => //.
  - by move=> y _; apply: integral_ge0 => x _; rewrite lee_fin expR_ge0.
  - exact: (measurable_fun_fubini_tonelli_G (m1 := P) g mg g0).
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_funX.
  - move=> y _; have := hm (a * y)%R.
    have -> : ((a * y) ^+ 2 * s ^+ 2 = a ^+ 2 * s ^+ 2 * y ^+ 2)%R by ring.
    by under eq_integral do rewrite mulrAC.
have L2 : (0 < L ^+ 2)%R by rewrite exprn_gt0.
have hc : (2 * (a ^+ 2 * s ^+ 2) * 1 ^+ 2 <= 3 / 4)%R.
  have -> : (2 * (a ^+ 2 * s ^+ 2) * 1 ^+ 2 = 4 * s ^+ 2 / L ^+ 2)%R.
    by rewrite a2 expr1n; field.
  by rewrite ler_pdivrMr //; lra.
have h1 : (2 * (a ^+ 2 * s ^+ 2) * 1 ^+ 2 < 1)%R by lra.
rewrite integral_normal_expR_sqr ?oner_neq0 //.
rewrite lee_fin invf_ple ?posrE ?ltr0Sn ?sqrtr_gt0.
- lra.
- by [].
- have -> : (2^-1 = Num.sqrt (2^-1 ^+ 2) :> R)%R.
    by rewrite sqrtr_sqr ger0_norm // invr_ge0.
  by rewrite ler_sqrt ?expr2; lra.
Qed.

End subgaussian_mgf_converse.

Section hoeffding.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* Products of nonnegative extended reals are monotone (as lee_prod of
   fourier/small_ball.v). *)
Lemma lee_prod_ge0 I (r : seq I) (P : pred I) (f g : I -> \bar R) :
  (forall i, P i -> 0 <= f i) -> (forall i, P i -> f i <= g i) ->
  \prod_(i <- r | P i) f i <= \prod_(i <- r | P i) g i.
Proof.
move=> f0 fg; elim/(big_load (fun x : \bar R => 0 <= x)): _.
elim/big_rec2: _ => // i y x Pi [x0 xy]; split; first by rewrite mule_ge0 ?f0.
by rewrite lee_pmul ?f0 ?fg.
Qed.

(* Hoeffding: the moment generating function of a weighted sum of
   independent centered subgaussian variables. *)
Lemma subgaussian_sum_mgf (mu : nat -> probability T R) n (f : nat -> T -> R)
    (K a : nat -> R) (l : R) :
  (forall i, (i < n)%N -> subgaussian (mu i) (f i) (K i)) ->
  (forall i, (i < n)%N -> \int[mu i]_t f i t = 0)%R ->
  \int[tuple_prod mu n]_x (expR (l * \sum_(i < n) a i * f i (tnth x i)))%:E <=
  (expR (3 * l ^+ 2 * \sum_(i < n) a i ^+ 2 * K i ^+ 2))%:E.
Proof.
move=> sf f0.
pose g i t := if (i < n)%N then expR (l * a i * f i t) else 1%R.
have mg i : measurable_fun [set: T] (g i).
  case: (boolP (i < n)%N) => [ilt|ige].
  - have [_ mfi _] := sf i ilt.
    have -> : g i = (fun t => expR (l * a i * f i t)).
      by apply/funext => t; rewrite /g ilt.
    by apply: measurableT_comp => //; apply: measurable_funM.
  - have -> : g i = (fun=> 1%R) by apply/funext => t; rewrite /g (negbTE ige).
    exact: measurable_cst.
have g0 i t : (0 <= g i t)%R.
  by rewrite /g; case: ifP => _; rewrite ?expR_ge0 ?ler01.
have E x : (expR (l * \sum_(i < n) a i * f i (tnth x i)) =
    \prod_(i < n) g i (tnth x i))%R.
  rewrite mulr_sumr expR_sum; apply: eq_bigr => i _.
  by rewrite /g ltn_ord mulrA.
under eq_integral do rewrite E.
rewrite ge0_integral_tuple_prod_prod //.
have -> : (3 * l ^+ 2 * \sum_(i < n) a i ^+ 2 * K i ^+ 2 =
    \sum_(i < n) 3 * (l * a i) ^+ 2 * K i ^+ 2)%R.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite exprMn; ring.
rewrite expR_sum -prodEFin.
apply: lee_prod_ge0 => i _.
  by apply: integral_ge0 => t _; rewrite lee_fin.
have ilt := ltn_ord i.
have -> : \int[mu i]_t (g i t)%:E = \int[mu i]_t (expR ((l * a i) * f i t))%:E.
  by apply: eq_integral => t _; rewrite /g ilt.
exact: subgaussian_mgf (sf i ilt) (f0 i ilt).
Qed.

Lemma subgaussian_sum (mu : nat -> probability T R) n (f : nat -> T -> R)
    (K a : nat -> R) :
  (forall i, (i < n)%N -> subgaussian (mu i) (f i) (K i)) ->
  (forall i, (i < n)%N -> \int[mu i]_t f i t = 0)%R ->
  (0 < \sum_(i < n) a i ^+ 2 * K i ^+ 2)%R ->
  subgaussian (tuple_prod mu n) (fun x => \sum_(i < n) a i * f i (tnth x i))%R
    (4 * Num.sqrt (\sum_(i < n) a i ^+ 2 * K i ^+ 2))%R.
Proof.
move=> sf f0 S0; set S := (\sum_(i < n) a i ^+ 2 * K i ^+ 2)%R.
have S0' : (0 <= S)%R by rewrite ltW.
apply: (@subgaussian_of_mgf _ _ _ _ _ (Num.sqrt (3 * S))).
- apply: measurable_sum => i; apply: measurable_funM => //.
  have [_ mfi _] := sf i (ltn_ord i).
  exact: measurableT_comp mfi (measurable_tnth i).
- by rewrite mulr_gt0 // sqrtr_gt0.
- by rewrite exprMn !sqr_sqrtr ?mulr_ge0 //; lra.
- move=> l; have S3 : (0 <= 3 * S)%R by rewrite mulr_ge0.
  rewrite sqr_sqrtr //.
  have -> : (l ^+ 2 * (3 * S) = 3 * l ^+ 2 * S)%R by ring.
  exact: subgaussian_sum_mgf.
Qed.

End hoeffding.

Section lincomb.
Context (R : realType).
Local Open Scope ereal_scope.

(* Linear combinations of independent centered coordinates of the line,
   subgaussian with a common constant K. *)
Lemma subgaussian_lincomb (nu : nat -> probability (measurableTypeR R) R) n
    (K : R) (a : nat -> R) :
  (forall i, (i < n)%N -> subgaussian (nu i) (fun x => x) K) ->
  (forall i, (i < n)%N -> \int[nu i]_x x = 0)%R ->
  \int[tuple_prod nu n]_x (expR ((\sum_(i < n) a i * tnth x i) ^+ 2 /
     (16 * K ^+ 2 * \sum_(i < n) a i ^+ 2)))%:E <= 2%:E.
Proof.
move=> sf f0.
have [A0|A0] := eqVneq (\sum_(i < n) a i ^+ 2)%R 0%R.
  under eq_integral do rewrite A0 mulr0 invr0 mulr0 expR0.
  by rewrite integral_cst //= probability_setT mul1e lee_fin ler1n.
have Apos : (0 < \sum_(i < n) a i ^+ 2)%R.
  by rewrite lt_def A0 /=; apply: sumr_ge0 => i _; exact: sqr_ge0.
have n0 : (0 < n)%N.
  by case: n {sf f0} A0 Apos => //; rewrite big_ord0 eqxx.
have [K0 _ _] := sf 0%N n0.
have SK : (0 < \sum_(i < n) a i ^+ 2 * K ^+ 2)%R.
  by rewrite -mulr_suml mulr_gt0 // exprn_gt0.
have [_ _ h] := subgaussian_sum (K := fun=> K) sf f0 SK.
have e : ((4 * Num.sqrt (\sum_(i < n) a i ^+ 2 * K ^+ 2)) ^+ 2 =
    16 * K ^+ 2 * \sum_(i < n) a i ^+ 2)%R.
  by rewrite exprMn sqr_sqrtr ?ltW // -mulr_suml; ring.
by rewrite e in h.
Qed.

End lincomb.

Section bernstein.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma subexponential_sum_mgf (mu : nat -> probability T R) n
    (f : nat -> T -> R) (L a : nat -> R) (l : R) :
  (forall i, (i < n)%N -> subexponential (mu i) (f i) (L i)) ->
  (forall i, (i < n)%N -> \int[mu i]_t f i t = 0)%R ->
  (forall i, (i < n)%N -> `|l * a i| <= (2 * L i)^-1)%R ->
  \int[tuple_prod mu n]_x (expR (l * \sum_(i < n) a i * f i (tnth x i)))%:E <=
  (expR (16 * l ^+ 2 * \sum_(i < n) a i ^+ 2 * L i ^+ 2))%:E.
Proof.
move=> sf f0 hl.
pose g i t := if (i < n)%N then expR (l * a i * f i t) else 1%R.
have mg i : measurable_fun [set: T] (g i).
  case: (boolP (i < n)%N) => [ilt|ige].
  - have [_ mfi _] := sf i ilt.
    have -> : g i = (fun t => expR (l * a i * f i t)).
      by apply/funext => t; rewrite /g ilt.
    by apply: measurableT_comp => //; apply: measurable_funM.
  - have -> : g i = (fun=> 1%R) by apply/funext => t; rewrite /g (negbTE ige).
    exact: measurable_cst.
have g0 i t : (0 <= g i t)%R.
  by rewrite /g; case: ifP => _; rewrite ?expR_ge0 ?ler01.
have E x : (expR (l * \sum_(i < n) a i * f i (tnth x i)) =
    \prod_(i < n) g i (tnth x i))%R.
  rewrite mulr_sumr expR_sum; apply: eq_bigr => i _.
  by rewrite /g ltn_ord mulrA.
under eq_integral do rewrite E.
rewrite ge0_integral_tuple_prod_prod //.
have -> : (16 * l ^+ 2 * \sum_(i < n) a i ^+ 2 * L i ^+ 2 =
    \sum_(i < n) 16 * (l * a i) ^+ 2 * L i ^+ 2)%R.
  by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite exprMn; ring.
rewrite expR_sum -prodEFin.
apply: lee_prod_ge0 => i _.
  by apply: integral_ge0 => t _; rewrite lee_fin.
have ilt := ltn_ord i.
have -> : \int[mu i]_t (g i t)%:E = \int[mu i]_t (expR ((l * a i) * f i t))%:E.
  by apply: eq_integral => t _; rewrite /g ilt.
exact: subexponential_mgf (sf i ilt) (f0 i ilt) (hl i ilt).
Qed.

(* Bernstein's inequality, upper tail. *)
Lemma bernstein_upper (mu : nat -> probability T R) n (f : nat -> T -> R)
    (L a : nat -> R) (t : R) :
  (forall i, (i < n)%N -> subexponential (mu i) (f i) (L i)) ->
  (forall i, (i < n)%N -> \int[mu i]_s f i s = 0)%R -> (0 <= t)%R ->
  tuple_prod mu n [set x | t <= \sum_(i < n) a i * f i (tnth x i)]%R <=
  (expR (- Num.min (t ^+ 2 / (64 * \sum_(i < n) a i ^+ 2 * L i ^+ 2))
                   (t / (4 * \big[Num.max/0%R]_(i < n) (`|a i| * L i)))))%:E.
Proof.
move=> sf f0 t0.
set s2 := (\sum_(i < n) a i ^+ 2 * L i ^+ 2)%R.
set M := (\big[Num.max/0%R]_(i < n) (`|a i| * L i))%R.
set A := (t ^+ 2 / (64 * s2))%R; set B := (t / (4 * M))%R.
have s20 : (0 <= s2)%R by apply: sumr_ge0 => i _; rewrite mulr_ge0 ?sqr_ge0.
have M0 : (0 <= M)%R.
  rewrite /M; elim/big_ind: _ => //.
    by move=> x y x0 y0; rewrite le_max x0.
  by move=> i _; rewrite mulr_ge0 // ltW //; have [] := sf i (ltn_ord i).
have aLM i : (i < n)%N -> (`|a i| * L i <= M)%R.
  move=> ilt.
  have := le_bigmax 0%R (fun j : 'I_n => (`|a j| * L j)%R) (Ordinal ilt).
  by rewrite -/M.
have mS : measurable_fun [set: n.-tuple T]
    (fun x => \sum_(i < n) a i * f i (tnth x i))%R.
  apply: measurable_sum => i; apply: measurable_funM => //.
  have [_ mfi _] := sf i (ltn_ord i).
  exact: measurableT_comp mfi (measurable_tnth i).
have P1 : tuple_prod mu n
    [set x | t <= \sum_(i < n) a i * f i (tnth x i)]%R <= 1.
  apply: le_trans (measure_ge_expR _ t mS (lexx 0%R)) _.
  under eq_integral do rewrite mul0r expR0.
  by rewrite integral_cst //= probability_setT mul1e.
have B0 : (0 <= B)%R by rewrite /B divr_ge0 // mulr_ge0.
have [s2e|s2n] := eqVneq s2 0%R.
  apply: le_trans P1 _; rewrite lee_fin -expR0 ler_expR oppr_ge0.
  by rewrite /A s2e mulr0 invr0 mulr0 ge_min lexx.
have [Me|Mn] := eqVneq M 0%R.
  apply: le_trans P1 _; rewrite lee_fin -expR0 ler_expR oppr_ge0.
  by rewrite /B Me mulr0 invr0 mulr0 ge_min lexx orbT.
have s2p : (0 < s2)%R by rewrite lt_def s2n.
have Mp : (0 < M)%R by rewrite lt_def Mn.
set lam := (Num.min (t / (32 * s2)) (2 * M)^-1)%R.
have lam0 : (0 <= lam)%R.
  rewrite /lam le_min; apply/andP; split.
    by rewrite divr_ge0 // mulr_ge0.
  by rewrite invr_ge0 mulr_ge0 // ltW.
have lamM : (lam <= (2 * M)^-1)%R by rewrite /lam ge_min lexx orbT.
apply: le_trans (measure_ge_expR _ t mS lam0) _.
have E x : (expR (lam * (\sum_(i < n) a i * f i (tnth x i) - t)) =
    expR (lam * \sum_(i < n) a i * f i (tnth x i)) * expR (- (lam * t)))%R.
  by rewrite -expRD mulrBr.
under eq_integral do rewrite E EFinM.
rewrite ge0_integralZr //; last first.
  have hl i : (i < n)%N -> (`|lam * a i| <= (2 * L i)^-1)%R.
    move=> ilt; have [Li _ _] := sf i ilt.
    rewrite normrM ger0_norm // -div1r ler_pdivlMr ?mulr_gt0 //.
    have h2 : (lam * (2 * M) <= 1)%R.
      by rewrite -ler_pdivlMr ?mulr_gt0 // div1r.
    have h1 := aLM i ilt; have := normr_ge0 (a i).
    nra.
  have h0 : (0 <= (expR (- (lam * t)))%:E :> \bar R).
    by rewrite lee_fin expR_ge0.
  apply: le_trans (lee_wpmul2r h0 (subexponential_sum_mgf sf f0 hl)) _.
  rewrite -/s2 -EFinM lee_fin -expRD ler_expR.
  have [h|h] := (leP (t / (32 * s2)) (2 * M)^-1)%R.
    have -> : lam = (t / (32 * s2))%R by rewrite /lam; apply/min_idPl.
    have -> : (16 * (t / (32 * s2)) ^+ 2 * s2 - t / (32 * s2) * t = - A)%R.
      by rewrite /A; field.
    by rewrite lerN2 ge_min lexx.
  have -> : lam = ((2 * M)^-1)%R by rewrite /lam; apply/min_idPr; rewrite ltW.
  apply: le_trans (_ : - B <= _)%R; last by rewrite lerN2 ge_min lexx orbT.
  have e1 : (t / (32 * s2) - (2 * M)^-1 =
      (M * t - 16 * s2) / (32 * M * s2))%R by field.
  have hs : (0 < M * t - 16 * s2)%R.
    by have := h; rewrite -subr_gt0 e1 pmulr_lgt0 // invr_gt0 !mulr_gt0.
  have e2 : (16 * (2 * M)^-1 ^+ 2 * s2 - (2 * M)^-1 * t + B =
      - (M * t - 16 * s2) / (4 * M ^+ 2))%R.
    by rewrite /B; field.
  have : (16 * (2 * M)^-1 ^+ 2 * s2 - (2 * M)^-1 * t + B <= 0)%R.
    by rewrite e2 mulNr oppr_le0 divr_ge0 ?ltW // mulr_gt0 // exprn_gt0.
  lra.
apply/measurable_EFinP; apply: measurableT_comp => //.
exact: measurable_funM.
Qed.

(* Bernstein's inequality. *)
Lemma bernstein (mu : nat -> probability T R) n (f : nat -> T -> R)
    (L a : nat -> R) (t : R) :
  (forall i, (i < n)%N -> subexponential (mu i) (f i) (L i)) ->
  (forall i, (i < n)%N -> \int[mu i]_s f i s = 0)%R -> (0 <= t)%R ->
  tuple_prod mu n [set x | t <= `|\sum_(i < n) a i * f i (tnth x i)|]%R <=
  (2 * expR (- Num.min (t ^+ 2 / (64 * \sum_(i < n) a i ^+ 2 * L i ^+ 2))
      (t / (4 * \big[Num.max/0%R]_(i < n) (`|a i| * L i)))))%:E.
Proof.
move=> sf f0 t0.
have h1 := bernstein_upper a sf f0 t0.
have h2 := bernstein_upper (fun i => - a i)%R sf f0 t0.
have e1 : (\sum_(i < n) (- a i) ^+ 2 * L i ^+ 2 =
    \sum_(i < n) a i ^+ 2 * L i ^+ 2)%R.
  by apply: eq_bigr => i _; rewrite sqrrN.
have e2 : (\big[Num.max/0%R]_(i < n) (`|- a i| * L i) =
    \big[Num.max/0%R]_(i < n) (`|a i| * L i))%R.
  by apply: eq_bigr => i _; rewrite normrN.
rewrite e1 e2 in h2.
have mS (b : nat -> R) : measurable_fun [set: n.-tuple T]
    (fun x => \sum_(i < n) b i * f i (tnth x i))%R.
  apply: measurable_sum => i; apply: measurable_funM => //.
  have [_ mfi _] := sf i (ltn_ord i).
  exact: measurableT_comp mfi (measurable_tnth i).
have mE (b : nat -> R) :
    measurable [set x | t <= \sum_(i < n) b i * f i (tnth x i)]%R.
  rewrite -(preimage_itvcy (fun x => \sum_(i < n) b i * f i (tnth x i))%R).
  rewrite -[X in measurable X]setTI.
  by apply: (mS b) => //; exact: measurable_itv.
have eN x : (\sum_(i < n) - a i * f i (tnth x i) =
    - \sum_(i < n) a i * f i (tnth x i))%R.
  by rewrite -sumrN; apply: eq_bigr => i _; rewrite mulNr.
have -> : [set x | t <= `|\sum_(i < n) a i * f i (tnth x i)|]%R =
    [set x | t <= \sum_(i < n) a i * f i (tnth x i)]%R `|`
    [set x | t <= \sum_(i < n) - a i * f i (tnth x i)]%R.
  apply/seteqP; split => x /=; rewrite eN.
    by rewrite ler_normr => /orP[h|h]; [left|right].
  by rewrite ler_normr => -[] ->; rewrite ?orbT.
apply: le_trans (measureU2 _ (mE a) (mE (fun i => - a i)%R)) _.
rewrite EFinM (_ : 2%:E = 1 + 1) // muleDl // !mul1e.
exact: leeD.
Qed.

(* Bernstein's inequality for a sum of independent centered variables
   subexponential with a common constant L. *)
Lemma bernstein_sum (mu : nat -> probability T R) n (f : nat -> T -> R)
    (L t : R) :
  (forall i, (i < n)%N -> subexponential (mu i) (f i) L) ->
  (forall i, (i < n)%N -> \int[mu i]_s f i s = 0)%R -> (0 <= t)%R ->
  tuple_prod mu n [set x | t <= `|\sum_(i < n) f i (tnth x i)|]%R <=
  (2 * expR (- Num.min (t ^+ 2 / (64 * n%:R * L ^+ 2)) (t / (4 * L))))%:E.
Proof.
move=> sf f0 t0.
have := bernstein (L := fun=> L) (fun=> 1%R) sf f0 t0.
have -> : [set x | t <= `|\sum_(i < n) (fun=> 1%R) i * f i (tnth x i)|]%R =
    [set x | t <= `|\sum_(i < n) f i (tnth x i)|]%R.
  have e x : (\sum_(i < n) 1 * f i (tnth x i) = \sum_(i < n) f i (tnth x i))%R.
    by apply: eq_bigr => i _; rewrite mul1r.
  by apply/seteqP; split => x /=; rewrite e.
have -> : (\sum_(i < n) 1 ^+ 2 * L ^+ 2 = n%:R * L ^+ 2)%R.
  rewrite (eq_bigr (fun=> L ^+ 2)%R) ?sumr_const ?card_ord ?mulr_natl //.
  by move=> i _; rewrite expr1n mul1r.
rewrite mulrA.
case: n sf f0 => [|n] sf f0 h.
  apply: le_trans h _; rewrite lee_fin ler_pM2l // ler_expR lerN2.
  rewrite big_ord0 !mulr0 !mul0r invr0 !mulr0.
  by rewrite ge_min le_min lexx /= ?ge_min ?lexx.
have [L0 _ _] := sf 0%N (ltn0Sn n).
have hM : (\big[Num.max/0%R]_(i < n.+1) (`|1| * L) = L)%R.
  rewrite normr1 mul1r big_const_ord.
  have hi k : (iter k (Num.max L) 0%R <= L)%R.
    elim: k => [|k IH] /=; first exact: ltW.
    by rewrite ge_max lexx.
  by rewrite iterS; apply/max_idPl; exact: hi.
by rewrite hM in h.
Qed.

End bernstein.
