From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp realfun.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From GaussianAnalysis.comparison Require Import normal_mgf gauss_smoothing.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.

(**md**************************************************************************)
(* # Norms of random vectors and matrices with subgaussian coordinates        *)
(*                                                                            *)
(* Independent coordinates are functions f_i (x_i) of the coordinates of a    *)
(* tuple x of law tuple_prod mu n (lindeberg.v), subgaussian with a common    *)
(* constant K (subgaussian.v). The results are Theorems 3.1.1 and 4.4.5 of    *)
(* Vershynin, High-Dimensional Probability, with explicit constants.          *)
(*                                                                            *)
(* Main results:                                                              *)
(* - subgaussian_unit_ge1: a subgaussian constant K of a variable X with      *)
(*   E X^2 = 1 is at least 1;                                                 *)
(* - norm_concentration: if E f_i (x_i)^2 = 1 for every i, the Euclidean norm *)
(*   |x| = (\sum_i f_i (x_i)^2)^(1/2) satisfies, for t >= 0,                  *)
(*     P(| |x| - sqrt n | >= t) <= 2 exp (- t^2 / (576 K^4)),                 *)
(*   from Bernstein's inequality (bernstein_sum) for the centered             *)
(*   subexponential variables f_i (x_i)^2 - 1; the f_i need not be centered;  *)
(* - mgf_tail: P(|X| >= r) <= 2 exp (- r^2 / (4 s^2)) for r >= 0 when         *)
(*   E exp (l X) <= exp (s^2 l^2) for every real l;                           *)
(* - opnorm_tail_mgf: for a random m x n matrix A with measurable entries     *)
(*   whose bilinear forms u^T A v, |u|, |v| <= 1, satisfy                     *)
(*   E exp (l u^T A v) <= exp (s^2 l^2) for every real l, and t >= 0,         *)
(*     P(opnorm A > 12 s (sqrt m + sqrt n + t)) <= 2 exp (- t^2),             *)
(*   by 1/4-nets of the unit balls (unit_ball_net and opnorm_net_bilinear of  *)
(*   nets.v) and the union bound;                                             *)
(* - subgaussian_opnorm_tail: for the m x n matrix A = vec_mx (f_k (x_k))_k   *)
(*   of independent centered entries, subgaussian with constant K, and t >= 0,*)
(*     P(opnorm A > 21 K (sqrt m + sqrt n + t)) <= 2 exp (- t^2),             *)
(*   from Hoeffding's inequality (subgaussian_sum_mgf) with s = sqrt 3 K.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section unit_variance.
Context d (T : measurableType d) (R : realType) (P : probability T R).

(* X^2 <= K^2 (exp (X^2 / K^2) - 1), integrated: 1 <= K^2 (2 - 1). *)
Lemma subgaussian_unit_ge1 (X : T -> R) (K : R) :
  subgaussian P X K -> \int[P]_t X t ^+ 2 = 1 -> 1 <= K.
Proof.
move=> sX hX; have [K0 mX h] := sX.
have Kn : K != 0 by rewrite gt_eqF.
have ie := integrable_subgaussian_expR sX.
have i2 := integrable_subgaussian_exprn 2 sX.
have i1 := finite_measure_integrable_cst P 1 measurableT.
have hR : \int[P]_t expR (X t ^+ 2 / K ^+ 2) <= 2.
  by rewrite -lee_fin fineK // integrable_fin_num.
have ie' : P.-integrable [set: T] (EFin \o (fun t => expR (X t ^+ 2 / K ^+ 2))).
  by [].
have iB : P.-integrable [set: T]
    (EFin \o (fun t => expR (X t ^+ 2 / K ^+ 2) - 1)).
  have := integrableB measurableT ie' i1.
  by apply: eq_integrable => // t _; rewrite /= -EFinB.
have hle : \int[P]_t X t ^+ 2 <=
    \int[P]_t (K ^+ 2 * (expR (X t ^+ 2 / K ^+ 2) - 1)).
  apply: le_Rintegral => //.
  - have := integrableZl measurableT (K ^+ 2) iB.
    by apply: eq_integrable => // t _; rewrite /= -EFinM.
  - move=> t _; have := expR_ge1Dx (X t ^+ 2 / K ^+ 2).
    rewrite -(ler_pM2l (exprn_gt0 2 K0)) mulrDr mulr1.
    have -> : K ^+ 2 * (X t ^+ 2 / K ^+ 2) = X t ^+ 2 by field.
    by rewrite mulrBr mulr1 lerBrDr addrC.
move: hle; rewrite hX RintegralZl // RintegralB // Rintegral_cst //.
have -> : fine (P [set: T]) = 1 by rewrite probability_setT.
rewrite mulr1 => h1.
have K2 : 0 <= K ^+ 2 by exact: sqr_ge0.
have K21 : 1 <= K ^+ 2 by nra.
nra.
Qed.

End unit_variance.

Section arithmetic.
Context {R : realType}.

(* |a^2 - b^2| = |a - b| (a + b) >= t max (t, b) when |a - b| >= t. *)
Local Lemma sqr_gap (a b t : R) : 0 <= a -> 0 <= b -> 0 <= t ->
  t <= `|a - b| -> Num.max (t ^+ 2) (t * b) <= `|a ^+ 2 - b ^+ 2|.
Proof.
move=> a0 b0 t0 hab.
have -> : a ^+ 2 - b ^+ 2 = (a - b) * (a + b) by ring.
rewrite normrM (ger0_norm (addr_ge0 a0 b0)).
have hs : `|a - b| <= a + b.
  by rewrite ler_norml; apply/andP; split; lra.
have u0 := normr_ge0 (a - b).
by rewrite ge_max; apply/andP; split; nra.
Qed.

(* The exponent of Bernstein's inequality for the norm. *)
Local Lemma norm_conc_arith (K t N : R) : 1 <= K -> 0 <= t -> 0 < N ->
  t ^+ 2 / (576 * K ^+ 4) <=
  Num.min (Num.max (t ^+ 2) (t * Num.sqrt N) ^+ 2 / (64 * N * (3 * K ^+ 2) ^+ 2))
    (Num.max (t ^+ 2) (t * Num.sqrt N) / (4 * (3 * K ^+ 2))).
Proof.
move=> K1 t0 N0.
have hs1 : t * Num.sqrt N <= Num.max (t ^+ 2) (t * Num.sqrt N).
  by rewrite le_max lexx orbT.
have hs2 : t ^+ 2 <= Num.max (t ^+ 2) (t * Num.sqrt N) by rewrite le_max lexx.
have a0 : 0 <= t * Num.sqrt N by rewrite mulr_ge0 ?sqrtr_ge0.
have eN : (t * Num.sqrt N) ^+ 2 = t ^+ 2 * N.
  by rewrite exprMn sqr_sqrtr // ltW.
move: hs1 hs2 a0 eN; move: (Num.max (t ^+ 2) (t * Num.sqrt N)) => s.
move: (t * Num.sqrt N) => a hs1 hs2 a0 eN.
have K0 : 0 < K by apply: lt_le_trans K1.
have Kn : K != 0 by rewrite gt_eqF.
have Nn : N != 0 by rewrite gt_eqF.
have c0 : 0 < 576 * K ^+ 4 by rewrite mulr_gt0 // exprn_gt0.
have s0 : 0 <= s by apply: le_trans hs2; exact: sqr_ge0.
have hs : t ^+ 2 * N <= s ^+ 2 by rewrite -eN; nra.
rewrite le_min; apply/andP; split.
  have -> : s ^+ 2 / (64 * N * (3 * K ^+ 2) ^+ 2) = s ^+ 2 / N / (576 * K ^+ 4).
    by field.
  apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
  by rewrite ler_pdivlMr.
apply: (@le_trans _ _ (s / (576 * K ^+ 4))).
  by apply: ler_wpM2r => //; rewrite invr_ge0 ltW.
apply: ler_wpM2l => //.
rewrite lef_pV2 ?posrE ?mulr_gt0 ?exprn_gt0 //.
have K2 : 1 <= K ^+ 2 by nra.
have -> : K ^+ 4 = K ^+ 2 * K ^+ 2 by rewrite -exprD.
nra.
Qed.

(* sqrt (m + n) <= sqrt m + sqrt n, squared. *)
Local Lemma sqrt_add_sqr (m n : nat) :
  m%:R + n%:R <= (Num.sqrt m%:R + Num.sqrt n%:R) ^+ 2 :> R.
Proof.
rewrite sqrrD !sqr_sqrtr ?ler0n // -addrA lerD2l lerDr.
by rewrite mulrn_wge0 // mulr_ge0 ?sqrtr_ge0.
Qed.

(* The count of the union bound over two 1/4-nets. *)
Local Lemma net_count_arith (m n : nat) (s t NU NV : R) : 0 < s -> 0 <= t ->
  0 <= NU -> NU <= (2 * expR 1 * (1 + 2 / 4^-1)) ^+ m ->
  0 <= NV -> NV <= (2 * expR 1 * (1 + 2 / 4^-1)) ^+ n ->
  NU * (NV * (2 * expR (- ((2 * s * (3 * (Num.sqrt m%:R + Num.sqrt n%:R) + t))
    ^+ 2 / (4 * s ^+ 2))))) <= 2 * expR (- t ^+ 2).
Proof.
move=> s0 t0 U0 hU V0 hV.
have sn : s != 0 by rewrite gt_eqF.
set a := Num.sqrt m%:R + Num.sqrt n%:R.
have a0 : 0 <= a by rewrite addr_ge0 ?sqrtr_ge0.
have ha : m%:R + n%:R <= a ^+ 2 by exact: sqrt_add_sqr.
have -> : (2 * s * (3 * a + t)) ^+ 2 / (4 * s ^+ 2) = (3 * a + t) ^+ 2 by field.
have eq18 : 2 * expR 1 * (1 + 2 / 4^-1) = 18 * expR 1 :> R by field.
rewrite eq18 in hU hV.
have q0 : 0 <= 18 * expR 1 :> R by rewrite mulr_ge0 ?expR_ge0.
have q9 : 18 * expR 1 <= expR 9 :> R.
  have -> : (9 : R) = 8 + 1 by rewrite natr1.
  rewrite expRD ler_pM2r ?expR_gt0 //.
  have := exprn_le_expR 2 (ler0n R 8).
  have -> : (2`!)%:R = 2 :> R by [].
  have -> : 8 ^+ 2 = 64 :> R by rewrite expr2 -natrM.
  move=> h8; lra.
have hUV : NU * NV <= expR (9 * (m%:R + n%:R)).
  apply: (@le_trans _ _ ((18 * expR 1) ^+ m * (18 * expR 1) ^+ n)).
    exact: ler_pM.
  rewrite -exprD -natrD [9 * _]mulrC expRM_natl.
  by apply: lerXn2r; rewrite ?nnegrE ?expR_ge0.
have hE : expR (- (3 * a + t) ^+ 2) <= expR (- (9 * (m%:R + n%:R))) * expR (- t ^+ 2).
  rewrite -expRD ler_expR; nra.
rewrite mulrA mulrCA.
apply: ler_wpM2l; first by rewrite ler0n.
apply: le_trans (ler_wpM2l (mulr_ge0 U0 V0) hE) _.
rewrite mulrA; apply: (@le_trans _ _ (expR (9 * (m%:R + n%:R)) *
  expR (- (9 * (m%:R + n%:R))) * expR (- t ^+ 2))).
  by apply: ler_wpM2r; [exact: expR_ge0 | apply: ler_wpM2r => //; exact: expR_ge0].
by rewrite -expRD subrr expR0 mul1r lexx.
Qed.

End arithmetic.

Section norm_concentration.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Theorem norm_concentration (mu : nat -> probability T R) n (f : nat -> T -> R)
    (K t : R) :
  (forall i, (i < n)%N -> subgaussian (mu i) (f i) K) ->
  (forall i, (i < n)%N -> \int[mu i]_s f i s ^+ 2 = 1)%R -> (0 <= t)%R ->
  tuple_prod mu n [set x | t <=
    `|Num.sqrt (\sum_(i < n) f i (tnth x i) ^+ 2) - Num.sqrt n%:R|]%R <=
  (2 * expR (- (t ^+ 2 / (576 * K ^+ 4))))%:E.
Proof.
move=> sf f1 t0.
have mS : measurable_fun [set: n.-tuple T]
    (fun x => \sum_(i < n) f i (tnth x i) ^+ 2)%R.
  apply: measurable_sum => i; apply: measurable_funX.
  have [_ mfi _] := sf i (ltn_ord i).
  exact: measurableT_comp mfi (measurable_tnth i).
have mN : measurable_fun [set: n.-tuple T] (fun x =>
    `|Num.sqrt (\sum_(i < n) f i (tnth x i) ^+ 2) - Num.sqrt n%:R|)%R.
  apply: measurableT_comp; first exact: normr_measurable.
  apply: measurable_funB => //.
  exact: measurableT_comp (continuous_measurable_fun (@sqrt_continuous R)) mS.
have mE : measurable [set x | t <=
    `|Num.sqrt (\sum_(i < n) f i (tnth x i) ^+ 2) - Num.sqrt n%:R|]%R.
  rewrite -(preimage_itvcy (fun x =>
    `|Num.sqrt (\sum_(i < n) f i (tnth x i) ^+ 2) - Num.sqrt n%:R|)%R).
  by rewrite -[X in measurable X]setTI; apply: mN => //; exact: measurable_itv.
case: n sf f1 mS mN mE => [|n] sf f1 mS mN mE.
  have [t00|tp] := eqVneq t 0%R.
    apply: le_trans (probability_le1 _ mE) _.
    by rewrite t00 expr2 !mul0r oppr0 expR0 mulr1 lee_fin ler1n.
  have -> : [set x : 0.-tuple T | t <=
      `|Num.sqrt (\sum_(i < 0) f i (tnth x i) ^+ 2) - Num.sqrt 0%:R|]%R = set0.
    apply/seteqP; split => // x /=.
    rewrite big_ord0 mulr0n sqrtr0 subr0 normr0 => h.
    by move: tp; rewrite eq_le h t0.
  by rewrite measure0 lee_fin mulr_ge0 ?expR_ge0 ?ler0n.
have K1 : (1 <= K)%R := subgaussian_unit_ge1 (sf 0%N (ltn0Sn n)) (f1 0%N (ltn0Sn n)).
pose g i s := (f i s ^+ 2 - 1)%R.
have sg i : (i < n.+1)%N -> subexponential (mu i) (g i) (3 * K ^+ 2).
  move=> ilt; have := subexponential_center (subexponential_sqr (sf i ilt)).
  by rewrite /= (f1 i ilt).
have g0 i : (i < n.+1)%N -> (\int[mu i]_s g i s = 0)%R.
  move=> ilt.
  have i2' := integrable_subgaussian_exprn 2 (sf i ilt).
  have i2 : (mu i).-integrable [set: T] (EFin \o (fun s => f i s ^+ 2)%R).
    by [].
  have i1 := finite_measure_integrable_cst (mu i) 1%R measurableT.
  rewrite /g RintegralB // (f1 i ilt) Rintegral_cst //.
  have -> : fine (mu i [set: T]) = 1%R by rewrite probability_setT.
  by rewrite mulr1 subrr.
have s0 : (0 <= Num.max (t ^+ 2) (t * Num.sqrt n.+1%:R))%R.
  by rewrite le_max sqr_ge0.
have hB := bernstein_sum sg g0 s0.
have mGf : measurable_fun [set: n.+1.-tuple T]
    (fun x => `|\sum_(i < n.+1) g i (tnth x i)|)%R.
  apply: measurableT_comp; first exact: normr_measurable.
  apply: measurable_sum => i; rewrite /g.
  apply: measurable_funB => //; apply: measurable_funX.
  have [_ mfi _] := sf i (ltn_ord i).
  exact: measurableT_comp mfi (measurable_tnth i).
have mG : measurable [set x : n.+1.-tuple T |
    Num.max (t ^+ 2) (t * Num.sqrt n.+1%:R) <= `|\sum_(i < n.+1) g i (tnth x i)|]%R.
  rewrite -(preimage_itvcy (fun x => `|\sum_(i < n.+1) g i (tnth x i)|)%R).
  by rewrite -[X in measurable X]setTI; apply: mGf => //; exact: measurable_itv.
apply: (@le_trans _ _ (tuple_prod mu n.+1 [set x | Num.max (t ^+ 2)
    (t * Num.sqrt n.+1%:R) <= `|\sum_(i < n.+1) g i (tnth x i)|]%R)).
  apply: le_measure; rewrite ?inE //.
  move=> x /= hx.
  have S0 : (0 <= \sum_(i < n.+1) f i (tnth x i) ^+ 2)%R.
    by apply: sumr_ge0 => i _; exact: sqr_ge0.
  have -> : (\sum_(i < n.+1) g i (tnth x i) =
      Num.sqrt (\sum_(i < n.+1) f i (tnth x i) ^+ 2) ^+ 2 -
      Num.sqrt n.+1%:R ^+ 2)%R.
    rewrite !sqr_sqrtr ?ler0n // /g sumrB; congr (_ - _)%R.
    by rewrite sumr_const card_ord.
  exact: sqr_gap (sqrtr_ge0 _) (sqrtr_ge0 _) t0 hx.
apply: le_trans hB _.
rewrite lee_fin; apply: ler_wpM2l; first by rewrite ler0n.
rewrite ler_expR lerN2.
exact: norm_conc_arith K1 t0 (ltr0Sn _ _).
Qed.

End norm_concentration.

Section union_bound.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Local Lemma measure_bigsetU_seq (I : Type) (s : seq I) (F : I -> set T) :
  (forall i, measurable (F i)) ->
  P (\big[setU/set0]_(i <- s) F i) <= \sum_(i <- s) P (F i).
Proof.
move=> mF; elim: s => [|i s IH]; first by rewrite !big_nil measure0.
rewrite !big_cons; apply: le_trans (measureU2 _ (mF i) _) _.
  by apply: bigsetU_measurable => j _; exact: mF.
exact: leeD.
Qed.

Local Lemma in_bigsetU (I : eqType) (s : seq I) (F : I -> set T) i x :
  i \in s -> F i x -> (\big[setU/set0]_(j <- s) F j) x.
Proof.
elim: s => [//|j s IH]; rewrite inE big_cons => /orP[/eqP <-|iS] Fx.
  by left.
by right; exact: IH.
Qed.

End union_bound.

Section opnorm_measurable.
Context d (T : measurableType d) (R : realType).

Local Lemma opnorm_lip m n (A B : 'M[R]_(m, n)) :
  `|opnorm A - opnorm B| <= frobenius (A - B).
Proof.
have h (X Y : 'M[R]_(m, n)) : opnorm X <= opnorm Y + frobenius (X - Y).
  have -> : opnorm X = opnorm (Y + (X - Y)) by rewrite addrC subrK.
  by rewrite (le_trans (opnormD _ _)) // lerD2l opnorm_le_frobenius.
rewrite ler_norml; have := h A B; have := h B A.
rewrite -frobeniusN opprB; lra.
Qed.

Local Lemma mxdot_mxvec m n (A B : 'M[R]_(m, n)) :
  mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 (reindex _ (curry_mxvec_bij m n)) /=.
rewrite pair_big /=; apply: eq_bigr => -[i j] _ /=.
by rewrite !mxvecE.
Qed.

(* The operator norm of a random matrix with measurable entries is
   measurable: it is 1-Lipschitz for the Frobenius norm. *)
Lemma measurable_opnorm m n (A : T -> 'M[R]_(m, n)) :
  (forall i j, measurable_fun [set: T] (fun x => A x i j)) ->
  measurable_fun [set: T] (fun x => opnorm (A x)).
Proof.
move=> mA.
have FL (a b : 'rV[R]_(m * n)) : `|opnorm (vec_mx a : 'M[R]_(m, n)) -
    opnorm (vec_mx b : 'M[R]_(m, n))| <= 1 * frobenius (a - b).
  rewrite mul1r (le_trans (opnorm_lip _ _)) // -linearB /=.
  by rewrite /frobenius -mxdot_mxvec vec_mxK.
have mF := continuous_measurable_mx (lipschitz_frobenius_continuous FL).
have -> : (fun x => opnorm (A x)) =
    (fun a => opnorm (vec_mx a : 'M[R]_(m, n))) \o (fun x => mxvec (A x)).
  by apply/funext => x /=; rewrite mxvecK.
apply: measurableT_comp mF _; apply/measurable_fun_mxP => i k.
case/mxvec_indexP: k => j k.
have -> : (fun x => mxvec (A x) i (mxvec_index j k)) = (fun x => A x j k).
  by apply/funext => x; rewrite (ord1 i) mxvecE.
exact: mA.
Qed.

End opnorm_measurable.

Section opnorm_tail.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

(* Chernoff's bound for a variable with a subgaussian moment generating
   function. *)
Lemma mgf_upper_tail (X : T -> R) (s r : R) :
  measurable_fun [set: T] X -> (0 < s)%R -> (0 <= r)%R ->
  (forall l : R, \int[P]_x (expR (l * X x))%:E <= (expR (s ^+ 2 * l ^+ 2))%:E) ->
  P [set x | r <= X x]%R <= (expR (- (r ^+ 2 / (4 * s ^+ 2))))%:E.
Proof.
move=> mX s0 r0 hm.
have sn : s != 0%R by rewrite gt_eqF.
pose l := (r / (2 * s ^+ 2))%R.
have l0 : (0 <= l)%R by rewrite divr_ge0 // mulr_ge0 // sqr_ge0.
apply: le_trans (measure_ge_expR P r mX l0) _.
have E x : (expR (l * (X x - r)) = expR (l * X x) * expR (- (l * r)))%R.
  by rewrite -expRD mulrBr.
under eq_integral do rewrite E EFinM.
rewrite ge0_integralZr //; last first.
  apply: le_trans (lee_wpmul2r _ (hm l)) _; first by rewrite lee_fin expR_ge0.
  rewrite -EFinM lee_fin -expRD ler_expR.
  have -> : (s ^+ 2 * l ^+ 2 - l * r = - (r ^+ 2 / (4 * s ^+ 2)))%R.
    by rewrite /l; field.
  exact: lexx.
apply/measurable_EFinP; apply: measurableT_comp => //.
exact: measurable_funM.
Qed.

Lemma mgf_tail (X : T -> R) (s r : R) :
  measurable_fun [set: T] X -> (0 < s)%R -> (0 <= r)%R ->
  (forall l : R, \int[P]_x (expR (l * X x))%:E <= (expR (s ^+ 2 * l ^+ 2))%:E) ->
  P [set x | r <= `|X x|]%R <= (2 * expR (- (r ^+ 2 / (4 * s ^+ 2))))%:E.
Proof.
move=> mX s0 r0 hm.
have mN : measurable_fun [set: T] (fun x => - X x)%R.
  exact: measurableT_comp mX.
have hmN (l : R) :
    \int[P]_x (expR (l * - X x))%:E <= (expR (s ^+ 2 * l ^+ 2))%:E.
  have -> : (fun x => (expR (l * - X x))%:E) = (fun x => (expR (- l * X x))%:E).
    by apply/funext => x; rewrite mulrN mulNr.
  by rewrite -[X in expR (s ^+ 2 * X)]sqrrN; exact: hm.
have h1 := mgf_upper_tail mX s0 r0 hm.
have h2 := mgf_upper_tail mN s0 r0 hmN.
have mE (Y : T -> R) : measurable_fun [set: T] Y -> measurable [set x | r <= Y x]%R.
  move=> mY; rewrite -(preimage_itvcy Y) -[X in measurable X]setTI.
  by apply: mY => //; exact: measurable_itv.
have -> : [set x | r <= `|X x|]%R = [set x | r <= X x]%R `|` [set x | r <= - X x]%R.
  apply/seteqP; split => x /=.
    by rewrite ler_normr => /orP[h|h]; [left|right].
  by rewrite ler_normr => -[] ->; rewrite ?orbT.
apply: le_trans (measureU2 _ (mE _ mX) (mE _ mN)) _.
rewrite EFinM (_ : 2%:E = 1 + 1) // muleDl // !mul1e.
exact: leeD.
Qed.

Theorem opnorm_tail_mgf m n (A : T -> 'M[R]_(m, n)) (s t : R) :
  (forall i j, measurable_fun [set: T] (fun x => A x i j)) -> (0 < s)%R ->
  (0 <= t)%R ->
  (forall (u : 'cV[R]_m) (v : 'cV[R]_n) (l : R),
    (frobenius u <= 1)%R -> (frobenius v <= 1)%R ->
    \int[P]_x (expR (l * mxdot u (A x *m v)))%:E <=
      (expR (s ^+ 2 * l ^+ 2))%:E) ->
  P [set x | 12 * s * (Num.sqrt m%:R + Num.sqrt n%:R + t) < opnorm (A x)]%R <=
  (2 * expR (- t ^+ 2))%:E.
Proof.
move=> mA s0 t0 hm.
have q0 : (0 < 4^-1 :> R)%R by rewrite invr_gt0.
have [U [U1 UN Us]] := unit_ball_net m q0.
have [V [V1 VN Vs]] := unit_ball_net n q0.
set a := (Num.sqrt m%:R + Num.sqrt n%:R)%R.
have a0 : (0 <= a)%R by rewrite addr_ge0 ?sqrtr_ge0.
set r := (2 * s * (3 * a + t))%R.
have r0 : (0 <= r)%R.
  by rewrite mulr_ge0 ?addr_ge0 ?mulr_ge0 // ltW.
have mB (u : 'cV[R]_m) (v : 'cV[R]_n) :
    measurable_fun [set: T] (fun x => mxdot u (A x *m v)).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  apply: measurable_funM => //.
  have -> : (fun x => (A x *m v) i j) = (fun x => \sum_k A x i k * v k j)%R.
    by apply/funext => x; rewrite mxE.
  apply: measurable_sum => k; apply: measurable_funM => //; exact: mA.
have mE (u : 'cV[R]_m) (v : 'cV[R]_n) :
    measurable [set x | r <= `|mxdot u (A x *m v)|]%R.
  have mBn : measurable_fun [set: T] (fun x => `|mxdot u (A x *m v)|)%R.
    by apply: measurableT_comp; [exact: normr_measurable | exact: mB].
  rewrite -(preimage_itvcy (fun x => `|mxdot u (A x *m v)|)%R).
  by rewrite -[X in measurable X]setTI; apply: mBn => //; exact: measurable_itv.
have mO : measurable [set x | 12 * s * (a + t) < opnorm (A x)]%R.
  rewrite -(preimage_itvoy (fun x => opnorm (A x))) -[X in measurable X]setTI.
  by apply: (measurable_opnorm mA) => //; exact: measurable_itv.
have e1 : (2 * 4^-1 < 1 :> R)%R.
  by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr_nat.
have sub : [set x | 12 * s * (a + t) < opnorm (A x)]%R `<=`
    \big[setU/set0]_(u <- U) \big[setU/set0]_(v <- V)
      [set x | r <= `|mxdot u (A x *m v)|]%R.
  move=> x /= hx; apply: contrapT => hno.
  have hb u v : u \in U -> v \in V -> (`|mxdot u (A x *m v)| <= r)%R.
    move=> uU vV; rewrite leNgt; apply/negP => hlt; apply: hno.
    apply: (in_bigsetU uU); apply: (in_bigsetU vV); exact: ltW.
  have hop := opnorm_net_bilinear (ltW q0) e1 UN U1 VN hb.
  have h4 : (r / (1 - 2 * 4^-1) <= 12 * s * (a + t))%R.
    have -> : (r / (1 - 2 * 4^-1) = 4 * s * (3 * a + t))%R by rewrite /r; field.
    by rewrite -subr_ge0; have := mulr_ge0 (ltW s0) t0; nra.
  by have := lt_le_trans hx (le_trans hop h4); rewrite ltxx.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  by apply: bigsetU_measurable => u _; apply: bigsetU_measurable => v _.
set c := (2 * expR (- (r ^+ 2 / (4 * s ^+ 2))))%R.
apply: (@le_trans _ _ (\sum_(u <- U) \sum_(v <- V) c%:E)).
  apply: le_trans (measure_bigsetU_seq _ _ _) _.
    by move=> u; apply: bigsetU_measurable => v _.
  rewrite big_seq [X in _ <= X]big_seq; apply: lee_sum => u uU.
  apply: le_trans (measure_bigsetU_seq _ _ _) _; first by move=> v.
  rewrite big_seq [X in _ <= X]big_seq; apply: lee_sum => v vV.
  exact: mgf_tail (mB u v) s0 r0 (fun l => hm u v l (U1 u uU) (V1 v vV)).
have sc (I : Type) (z : seq I) (y : R) : (\sum_(i <- z) y = (size z)%:R * y)%R.
  elim: z => [|i z IH]; first by rewrite big_nil mul0r.
  by rewrite big_cons IH /= -add1n natrD mulrDl mul1r.
under eq_bigr do rewrite sumEFin sc.
rewrite sumEFin sc lee_fin.
exact: net_count_arith s0 t0 (ler0n _ _) Us (ler0n _ _) Vs.
Qed.

End opnorm_tail.

Section subgaussian_opnorm.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Theorem subgaussian_opnorm_tail (mu : nat -> probability T R) m n
    (f : nat -> T -> R) (K t : R) :
  (forall k, (k < m * n)%N -> subgaussian (mu k) (f k) K) ->
  (forall k, (k < m * n)%N -> \int[mu k]_s f k s = 0)%R ->
  (0 < K)%R -> (0 <= t)%R ->
  tuple_prod mu (m * n) [set x | 21 * K * (Num.sqrt m%:R + Num.sqrt n%:R + t) <
    opnorm (vec_mx (\row_k f k (tnth x k)) : 'M[R]_(m, n))]%R <=
  (2 * expR (- t ^+ 2))%:E.
Proof.
move=> sf f0 K0 t0.
pose A x : 'M[R]_(m, n) := vec_mx (\row_k f k (tnth x k)).
have mA i j : measurable_fun [set: (m * n).-tuple T] (fun x => A x i j).
  have -> : (fun x => A x i j) =
      (fun x => f (mxvec_index i j) (tnth x (mxvec_index i j))).
    by apply/funext => x; rewrite /A !mxE.
  have [_ mfk _] := sf _ (ltn_ord (mxvec_index i j)).
  exact: measurableT_comp mfk (measurable_tnth _).
have s0 : (0 < Num.sqrt 3 * K)%R by rewrite mulr_gt0 // sqrtr_gt0.
have hm (u : 'cV[R]_m) (v : 'cV[R]_n) (l : R) :
    (frobenius u <= 1)%R -> (frobenius v <= 1)%R ->
    \int[tuple_prod mu (m * n)]_x (expR (l * mxdot u (A x *m v)))%:E <=
      (expR ((Num.sqrt 3 * K) ^+ 2 * l ^+ 2))%:E.
  move=> u1 v1.
  pose w := mxvec (u *m v^T).
  pose b (k : nat) : R :=
    if (insub k : option 'I_(m * n)) is Some j then w ord0 j else 0%R.
  have eB x : mxdot u (A x *m v) =
      (\sum_(k < m * n) b k * f k (tnth x k))%R.
    rewrite mxdot_colE mulmxA -mxdot_outer mxdotC -mxdot_mxvec /A vec_mxK.
    rewrite /mxdot big_ord1; apply: eq_bigr => k _.
    by rewrite /b valK mxE.
  under eq_integral do rewrite eB.
  apply: le_trans (subgaussian_sum_mgf b l sf f0) _.
  rewrite lee_fin ler_expR exprMn sqr_sqrtr // -mulr_suml.
  have hw : (\sum_(k < m * n) b k ^+ 2 <= 1)%R.
    have -> : (\sum_(k < m * n) b k ^+ 2 = mxdot w w)%R.
      rewrite /mxdot big_ord1; apply: eq_bigr => k _.
      by rewrite /b valK expr2.
    rewrite /w mxdot_mxvec mxdot_outer2 -!frobenius_sqr.
    have fu := frobenius_ge0 u; have fv := frobenius_ge0 v.
    have hu : (frobenius u ^+ 2 <= 1)%R by nra.
    have hv : (frobenius v ^+ 2 <= 1)%R by nra.
    have hv0 : (0 <= frobenius v ^+ 2)%R by exact: sqr_ge0.
    nra.
  have hlk : (0 <= l ^+ 2 * K ^+ 2)%R by rewrite mulr_ge0 ?sqr_ge0.
  nra.
apply: le_trans _ (opnorm_tail_mgf mA s0 t0 hm).
apply: le_measure; rewrite ?inE.
- rewrite -(preimage_itvoy (fun x => opnorm (A x))) -[X in measurable X]setTI.
  by apply: (measurable_opnorm mA) => //; exact: measurable_itv.
- rewrite -(preimage_itvoy (fun x => opnorm (A x))) -[X in measurable X]setTI.
  by apply: (measurable_opnorm mA) => //; exact: measurable_itv.
move=> x /= hx; apply: le_lt_trans hx.
have at0 : (0 <= Num.sqrt m%:R + Num.sqrt n%:R + t)%R.
  by apply: addr_ge0 => //; apply: addr_ge0; exact: sqrtr_ge0.
apply: ler_wpM2r => //.
have h74 : (0 <= 7 / 4 :> R)%R by rewrite divr_ge0.
have h3 : (Num.sqrt 3 <= 7 / 4 :> R)%R.
  rewrite -[X in (_ <= X)%R](ger0_norm h74) -sqrtr_sqr; apply: ler_wsqrtr.
  lra.
nra.
Qed.

End subgaussian_opnorm.
