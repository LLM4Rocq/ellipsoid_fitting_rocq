From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral hoelder probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows moments.

(**md**************************************************************************)
(* # The Efron-Stein inequality and moment bounds for product laws            *)
(*                                                                            *)
(* For x of law tuple_prod mu n (lindeberg.v), x^(i) is x with its coordinate *)
(* i replaced by an independent t of law mu i: tuple_set x i t. Variances are *)
(* those of probability.v, with values in [0, +oo]: 'V_P[X] is +oo when X is  *)
(* measurable and not square integrable (varianceT, sqr_dev_variance).        *)
(*                                                                            *)
(* - Fubini at one coordinate, for F measurable and nonnegative               *)
(*   (ge0_integral_tuple_prod_set) and for F integrable                       *)
(*   (integral_tuple_prod_set): \int[tuple_prod mu n]_x F x is                *)
(*   \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t). The inner      *)
(*   integral is a measurable function of x (measurable_tuple_set_integral,   *)
(*   measurable_integral_tuple_set), and for F integrable,                    *)
(*   t |-> F (tuple_set x i t) is integrable for almost every x               *)
(*   (ae_integrable_tuple_set).                                               *)
(* - sqr_dev_variance: E (X - c)^2 = Var X + (E X - c)^2 for X measurable and *)
(*   c real; variance_le_sqr_dev: Var X <= E (X - c)^2;                       *)
(*   variance_resample: E (X - X')^2 = 2 Var X for an independent copy X'.    *)
(* - efron_stein_pair: for F integrable on a product of two probabilities,    *)
(*   Var F <= E_y Var_x F (x, y) + E_x Var_y F (x, y).                        *)
(* - efron_stein_integrable (F integrable) and efron_stein (F in L^2):        *)
(*   'V_(tuple_prod mu n)[F] <= \sum_(i < n) \int[tuple_prod mu n]_x V i x,   *)
(*   where V i x = 'V_(mu i)[fun t => F (tuple_set x i t)].                   *)
(* - efron_stein_resample: Var F <= 1/2 \sum_i E (F (x) - F (x^(i)))^2, since *)
(*   E (F (x) - F (x^(i)))^2 = 2 E V i (integral_resample_tuple_set).         *)
(* - One coordinate and the others: the coordinate i of tuple_prod mu n has   *)
(*   law mu i (ge0_integral_tuple_prod_coord, integral_tuple_prod_coord), and *)
(*   E [f (x_i) H (x)] = E [f] E [H] when H does not depend on x_i            *)
(*   (ge0_integral_tuple_prod_coordM, integral_tuple_prod_coordM, with the    *)
(*   integrability of the product).                                           *)
(* - cauchy_schwarz: (int |f g|)^2 <= int f^2 int g^2, from Hoelder.          *)
(* - Moments from Efron-Stein (the L^p recursion of Koehler and Sohn, in the  *)
(*   proof of their Proposition 2.6, at p = 4): efron_stein_fourth, if        *)
(*   E (F (x) - F (x^(i)))^4 <= D_i^2 for every i, then                       *)
(*   E (F - E F)^4 <= 9/2 (sum_i D_i)^2; by Efron-Stein for (F - E F)^2,      *)
(*   Cauchy-Schwarz and the two estimates resample_sqr_le and                 *)
(*   resample_sqr_sqr_le of one resampled coordinate.                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma tuple_set_set (U : Type) n (x : n.-tuple U) (i : 'I_n) (s t : U) :
  tuple_set (tuple_set x i s) i t = tuple_set x i t.
Proof. by apply: eq_from_tnth => j; rewrite !tnth_mktuple; case: eqP. Qed.

Section resample.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma measurable_tuple_set_pair n (i : 'I_n) :
  measurable_fun [set: n.-tuple T * T] (fun p => tuple_set p.1 i p.2).
Proof.
apply/measurable_fun_tnthP => j /=.
apply: (eq_measurable_fun
  (fun p : n.-tuple T * T => if j == i then p.2 else tnth p.1 j)).
  by move=> p _; rewrite /= tnth_mktuple.
case: (j == i); first exact: measurable_snd.
exact: measurableT_comp (measurable_tnth j) measurable_fst.
Qed.

(* The integral over one coordinate is a measurable function of the
   others. *)
Lemma measurable_tuple_set_integral (nu : nat -> probability T R) n (i : 'I_n)
    (H : n.-tuple T -> \bar R) :
  measurable_fun [set: n.-tuple T] H -> (forall x, 0 <= H x) ->
  measurable_fun [set: n.-tuple T] (fun x => \int[nu i]_t H (tuple_set x i t)).
Proof.
move=> mH H0.
have mHs : measurable_fun [set: n.-tuple T * T]
    (fun p => H (tuple_set p.1 i p.2)).
  exact: measurableT_comp mH (measurable_tuple_set_pair i).
exact: (measurable_fun_fubini_tonelli_F (m2 := nu i) _ mHs (fun p => H0 _)).
Qed.

(* Fubini at one coordinate: resampling coordinate i does not change the
   integral of a nonnegative function. *)
Lemma ge0_integral_tuple_prod_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> \bar R) :
  measurable_fun [set: n.-tuple T] F -> (forall x, 0 <= F x) ->
  \int[tuple_prod mu n]_x F x =
  \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t).
Proof.
elim: n mu i F => [|n IH] mu i F mF F0; first by case: i.
have mG m (nu : nat -> probability T R) (k : 'I_m) (H : m.-tuple T -> \bar R) :
    measurable_fun [set: m.-tuple T] H -> (forall x, 0 <= H x) ->
    measurable_fun [set: m.-tuple T]
      (fun x => \int[nu k]_t H (tuple_set x k t)).
  move=> mH H0.
  have mHs : measurable_fun [set: m.-tuple T * T]
      (fun p => H (tuple_set p.1 k p.2)).
    exact: measurableT_comp mH (measurable_tuple_set_pair k).
  exact: (measurable_fun_fubini_tonelli_F (m2 := nu k) _ mHs (fun p => H0 _)).
have G0 x : 0 <= \int[mu i]_t F (tuple_set x i t) by apply: integral_ge0.
have mGi := mG _ mu i F mF F0.
rewrite [RHS]ge0_integral_tuple_prodS // [LHS]ge0_integral_tuple_prodS //.
case: (unliftP ord0 i) => [j ->|->].
  apply: eq_integral => t0 _.
  have mF' : measurable_fun [set: n.-tuple T]
      (fun ts => F (tuple_cons (t0, ts))).
    exact: measurableT_comp mF (measurable_tuple_cons_l t0).
  rewrite (IH (fun k => mu k.+1) j _ mF' (fun _ => F0 _)).
  apply: eq_integral => ts _; rewrite lift0.
  by apply: eq_integral => s _; rewrite /tuple_cons /= tuple_set_consS.
have e t ts s : tuple_set (tuple_cons (t, ts)) ord0 s = tuple_cons (s, ts).
  by rewrite /tuple_cons /= tuple_set_cons0.
under [RHS]eq_integral do under eq_integral do under eq_integral do rewrite e.
set C := \int[tuple_prod (fun i0 : nat => mu i0.+1) n]_x
  \int[mu ord0]_x0 F (tuple_cons (x0, x)).
rewrite [RHS](@integral_cst _ _ _ (mu 0%N) _ measurableT C).
match goal with |- _ = _ * ?X => have hM : X = 1 by apply: probability_setT end.
rewrite hM mule1 /C.
have mg : measurable_fun [set: T * n.-tuple T] (fun p => F (tuple_cons p)).
  exact: measurableT_comp mF (@measurable_tuple_cons _ T n).
have FT := fubini_tonelli1 (m1 := mu 0%N)
  (m2 := tuple_prod (fun k => mu k.+1) n) _ mg (fun p => F0 _).
have GT := fubini_tonelli2 (m1 := mu 0%N)
  (m2 := tuple_prod (fun k => mu k.+1) n) _ mg (fun p => F0 _).
by rewrite FT /fubini_F /fubini_G in GT.
Qed.

Lemma integrable_tuple_prod_set_pair (mu : nat -> probability T R) n
    (i : 'I_n) (F : n.-tuple T -> \bar R) :
  (tuple_prod mu n).-integrable [set: n.-tuple T] F ->
  (tuple_prod mu n \x mu i).-integrable [set: n.-tuple T * T]
    (fun p => F (tuple_set p.1 i p.2)).
Proof.
move=> Fi; have mF := measurable_int _ Fi.
have mFs : measurable_fun [set: n.-tuple T * T]
    (fun p => F (tuple_set p.1 i p.2)).
  exact: measurableT_comp mF (measurable_tuple_set_pair i).
apply/integrableP; split => //.
have mA : measurable_fun [set: n.-tuple T * T]
    (fun p => `|F (tuple_set p.1 i p.2)|).
  exact: measurableT_comp mFs.
rewrite (fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ mA
  (fun p => abse_ge0 _)).
rewrite /fubini_F -(ge0_integral_tuple_prod_set mu i (F := fun x => `|F x|)) //.
- exact: measurableT_comp mF.
- by have /integrableP[] := Fi.
Qed.

(* For F integrable, its restriction to the coordinate i is integrable for
   almost every value of the other coordinates. *)
Lemma ae_integrable_tuple_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> \bar R) :
  (tuple_prod mu n).-integrable [set: n.-tuple T] F ->
  {ae tuple_prod mu n, forall x,
    (mu i).-integrable [set: T] (fun t => F (tuple_set x i t))}.
Proof.
by move=> Fi; exact: ae_integrable1 (integrable_tuple_prod_set_pair i Fi).
Qed.

Lemma measurable_integral_tuple_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> \bar R) :
  (tuple_prod mu n).-integrable [set: n.-tuple T] F ->
  measurable_fun [set: n.-tuple T] (fun x => \int[mu i]_t F (tuple_set x i t)).
Proof.
by move=> Fi; exact: measurable_fubini_F (integrable_tuple_prod_set_pair i Fi).
Qed.

(* Fubini at one coordinate, for integrable functions. *)
Lemma integral_tuple_prod_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> \bar R) :
  (tuple_prod mu n).-integrable [set: n.-tuple T] F ->
  \int[tuple_prod mu n]_x F x =
  \int[tuple_prod mu n]_x \int[mu i]_t F (tuple_set x i t).
Proof.
move=> Fi; have mF := measurable_int _ Fi.
have Fi2 := integrable_tuple_prod_set_pair i Fi.
rewrite [RHS](integral12_prod_meas1 Fi2).
have E (G : n.-tuple T -> \bar R) : measurable_fun [set: n.-tuple T] G ->
    (forall x, 0 <= G x) ->
    \int[tuple_prod mu n \x mu i]_p G (tuple_set p.1 i p.2) =
    \int[tuple_prod mu n]_x G x.
  move=> mG G0.
  have mGs : measurable_fun [set: n.-tuple T * T]
      (fun p => G (tuple_set p.1 i p.2)).
    exact: measurableT_comp mG (measurable_tuple_set_pair i).
  rewrite (fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ mGs
    (fun p => G0 _)).
  by rewrite /fubini_F -ge0_integral_tuple_prod_set.
have mFp := measurable_funepos mF; have mFn := measurable_funeneg mF.
rewrite [LHS]integralE [RHS]integralE.
rewrite -(E _ mFp (fun x => funepos_ge0 F x)).
rewrite -(E _ mFn (fun x => funeneg_ge0 F x)).
congr (_ - _).
  by apply: eq_integral => p _; rewrite !funeposE.
by apply: eq_integral => p _; rewrite !funenegE.
Qed.

(* The law of the coordinate i of tuple_prod mu n is mu i. *)
Lemma ge0_integral_tuple_prod_coord (mu : nat -> probability T R) n (i : 'I_n)
    (f : T -> \bar R) :
  measurable_fun setT f -> (forall t, 0 <= f t) ->
  \int[tuple_prod mu n]_x f (tnth x i) = \int[mu i]_t f t.
Proof.
move=> mf f0.
rewrite (ge0_integral_tuple_prod_set mu i (F := fun x => f (tnth x i))).
- exact: measurableT_comp mf (measurable_tnth i).
- by move=> x; exact: f0.
under eq_integral do under eq_integral do
  rewrite /tuple_set tnth_mktuple eqxx.
rewrite (@integral_cst _ _ _ (tuple_prod mu n) _ measurableT
  (\int[mu i]_t f t)).
by rewrite [X in _ * X]probability_setT mule1.
Qed.

Lemma integral_tuple_prod_coord (mu : nat -> probability T R) n (i : 'I_n)
    (f : T -> \bar R) : measurable_fun setT f ->
  \int[tuple_prod mu n]_x f (tnth x i) = \int[mu i]_t f t.
Proof.
move=> mf; rewrite integralE [RHS]integralE.
rewrite -(ge0_integral_tuple_prod_coord mu i (measurable_funepos mf)) //.
rewrite -(ge0_integral_tuple_prod_coord mu i (measurable_funeneg mf)) //.
by congr (_ - _)%E; apply: eq_integral => x _; rewrite ?funeposE ?funenegE.
Qed.

(* Independence of the coordinate i from the others: for H that does not
   depend on the coordinate i, E [f (x_i) H (x)] = E [f (x_i)] E [H (x)]. *)
Lemma ge0_integral_tuple_prod_coordM (mu : nat -> probability T R) n
    (i : 'I_n) (f : T -> \bar R) (H : n.-tuple T -> \bar R) :
  measurable_fun setT f -> (forall t, 0 <= f t) ->
  measurable_fun setT H -> (forall x, 0 <= H x) ->
  (forall x t, H (tuple_set x i t) = H x) ->
  \int[tuple_prod mu n]_x (f (tnth x i) * H x) =
  \int[mu i]_t f t * \int[tuple_prod mu n]_x H x.
Proof.
move=> mf f0 mH H0 Hi.
have mfi : measurable_fun setT (fun x : n.-tuple T => f (tnth x i)).
  exact: measurableT_comp mf (measurable_tnth i).
rewrite (ge0_integral_tuple_prod_set mu i (F := fun x => f (tnth x i) * H x)).
- exact: emeasurable_funM.
- by move=> x; exact: mule_ge0.
under eq_integral do under eq_integral do
  rewrite Hi /tuple_set tnth_mktuple eqxx.
transitivity (\int[tuple_prod mu n]_x (\int[mu i]_t f t * H x)).
  by apply: eq_integral => x _; rewrite ge0_integralZr.
by rewrite ge0_integralZl //; exact: integral_ge0.
Qed.

Lemma integral_tuple_prod_coordM (mu : nat -> probability T R) n (i : 'I_n)
    (f : T -> R) (H : n.-tuple T -> R) :
  (mu i).-integrable setT (EFin \o f) ->
  (tuple_prod mu n).-integrable setT (EFin \o H) ->
  (forall x t, H (tuple_set x i t) = H x) ->
  (tuple_prod mu n).-integrable setT (fun x => (f (tnth x i) * H x)%:E) /\
  \int[tuple_prod mu n]_x (f (tnth x i) * H x)%:E =
  \int[mu i]_t (f t)%:E * \int[tuple_prod mu n]_x (H x)%:E.
Proof.
move=> fi iH Hind.
have mf : measurable_fun setT f.
  by apply/measurable_EFinP; exact: measurable_int fi.
have mH : measurable_fun setT H.
  by apply/measurable_EFinP; exact: measurable_int iH.
have mP : measurable_fun setT (fun x : n.-tuple T => f (tnth x i) * H x)%R.
  apply: measurable_funM => //.
  exact: measurableT_comp mf (measurable_tnth i).
have /integrableP[_ fl] := fi; have /integrableP[_ Hl] := iH.
have iP : (tuple_prod mu n).-integrable setT
    (fun x => (f (tnth x i) * H x)%:E).
  apply/integrableP; split; first exact/measurable_EFinP.
  under eq_integral do rewrite abse_EFin normrM EFinM.
  rewrite (@ge0_integral_tuple_prod_coordM mu n i (fun t => `|f t|%:E)
    (fun x => `|H x|%:E)).
  - by apply/measurable_EFinP; exact: measurableT_comp.
  - by move=> t; rewrite lee_fin.
  - by apply/measurable_EFinP; exact: measurableT_comp.
  - by move=> x; rewrite lee_fin.
  - by move=> x t; rewrite Hind.
  apply: lte_mul_pinfty.
  - by apply: integral_ge0 => t _; rewrite lee_fin.
  - rewrite ge0_fin_numE; first by apply: integral_ge0 => t _; rewrite lee_fin.
    suff -> : \int[mu i]_t `|f t|%:E = \int[mu i]_x `|(EFin \o f) x| by [].
    by apply: eq_integral => t _.
  suff -> : \int[tuple_prod mu n]_x `|H x|%:E =
    \int[tuple_prod mu n]_x `|(EFin \o H) x| by [].
  by apply: eq_integral => t _.
split => //; rewrite (integral_tuple_prod_set i iP).
under eq_integral do under eq_integral do
  rewrite Hind /tuple_set tnth_mktuple eqxx EFinM.
under eq_integral do rewrite integralZr //.
have ff : \int[mu i]_t (f t)%:E \is a fin_num by apply: integrable_fin_num.
by rewrite -(fineK ff) integralZl.
Qed.

End resample.

Section variance_facts.
Context d (U : measurableType d) (R : realType) (P : probability U R).
Local Open Scope ereal_scope.

(* The variance as an integral, with no integrability condition. *)
Lemma varianceT (X : U -> R) :
  'V_P[X] = \int[P]_x ((X x - fine (\int[P]_y (X y)%:E)) ^+ 2)%:E.
Proof.
by rewrite /variance !unlock; apply: eq_integral => x _; rewrite /= expr2.
Qed.

Lemma sqr_dev_Lfun2 (X : U -> R) (c : R) : measurable_fun setT X ->
  \int[P]_x ((X x - c) ^+ 2)%:E < +oo -> X \in Lfun P 2%:E.
Proof.
move=> mX lt; have mXc : measurable_fun setT (fun x => X x - c)%R.
  exact: measurable_funB.
have Xc2 : (fun x => X x - c)%R \in Lfun P 2%:E.
  apply: integrable_sqr_Lfun2 => //; apply/integrableP; split.
    by apply/measurable_EFinP; exact: measurable_funX.
  apply: le_lt_trans lt; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => x _ /=; rewrite ger0_norm // sqr_ge0.
have -> : X = ((fun x => X x - c) \+ cst c)%R.
  by apply/funext => x /=; rewrite subrK.
by rewrite rpredD // ?lee1n // => ?; exact: Lfun_cst.
Qed.

(* The second moment about c is the variance plus the square of the
   distance from c to the mean, in [0, +oo] and for every measurable X. *)
Lemma sqr_dev_variance (X : U -> R) (c : R) : measurable_fun setT X ->
  \int[P]_x ((X x - c) ^+ 2)%:E = 'V_P[X] + ((fine 'E_P[X] - c) ^+ 2)%:E.
Proof.
move=> mX; have [X2|X2] := boolP (X \in Lfun P 2%:E).
  have X1 := Lfun_subset12 (fin_num_measure P _ measurableT) X2.
  have Y2 : (X \- cst c)%R \in Lfun P 2%:E.
    by rewrite rpredB // ?lee1n // => ?; exact: Lfun_cst.
  have EY : 'E_P[X \- cst c] = (fine 'E_P[X] - c)%:E.
    rewrite expectationB //; first exact: (@Lfun_cst _ _ _ P c 1).
    rewrite (@expectation_cst _ _ _ P c).
    by rewrite -{1}(fineK (expectation_fin_num X1)).
  have := varianceE Y2; rewrite varianceB_cst_r // EY => ->.
  rewrite -EFin_expe subeK //.
  by rewrite unlock; apply: eq_integral => x _; rewrite /= expr2.
have Xoo c' : \int[P]_x ((X x - c') ^+ 2)%:E = +oo.
  apply/eqP; rewrite eq_le leey /= leNgt; apply/negP.
  by move=> /(sqr_dev_Lfun2 mX) X2'; rewrite X2' in X2.
by rewrite Xoo varianceT Xoo addye.
Qed.

(* The variance is at most the second moment about any point. *)
Lemma variance_le_sqr_dev (X : U -> R) (c : R) : measurable_fun setT X ->
  'V_P[X] <= \int[P]_x ((X x - c) ^+ 2)%:E.
Proof.
by move=> mX; rewrite (sqr_dev_variance c mX) leeDl // lee_fin sqr_ge0.
Qed.

Lemma sqr_fine_expectation_le (X : U -> R) : measurable_fun setT X ->
  ((fine 'E_P[X]) ^+ 2)%:E <= \int[P]_x ((X x) ^+ 2)%:E.
Proof.
move=> mX; have := sqr_dev_variance 0 mX; rewrite subr0.
under eq_integral do rewrite subr0.
by move=> ->; rewrite leeDr // variance_ge0.
Qed.

(* For an independent copy X' of X, E (X - X')^2 = 2 Var X. *)
Lemma variance_resample (X : U -> R) : measurable_fun setT X ->
  \int[P]_s \int[P]_t ((X s - X t) ^+ 2)%:E = 'V_P[X] *+ 2.
Proof.
move=> mX; transitivity (\int[P]_s ('V_P[X] + ((X s - fine 'E_P[X]) ^+ 2)%:E)).
  apply: eq_integral => s _; under eq_integral do rewrite -opprB sqrrN.
  by rewrite (sqr_dev_variance (X s) mX) -opprB sqrrN.
rewrite ge0_integralD //.
- by move=> s _; exact: variance_ge0.
- by move=> s _; rewrite lee_fin sqr_ge0.
- by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
rewrite (@integral_cst _ _ _ P _ measurableT ('V_P[X])).
rewrite [X in _ * X]probability_setT mule1 mule2n; congr (_ + _).
by rewrite varianceT unlock.
Qed.

End variance_facts.

Section cauchy_schwarz.
Context d (U : measurableType d) (R : realType).
Variable mu : {measure set U -> \bar R}.
Local Open Scope ereal_scope.

Lemma poweR2 (y : \bar R) : 0 <= y -> y `^ 2 = y ^+ 2.
Proof.
case: y => [r| |] //= r0; last by rewrite pnatr_eq0 mulyy.
by rewrite -EFinM; congr EFin; rewrite -expr2 (powR_mulrn 2) // -lee_fin.
Qed.

(* The Cauchy-Schwarz inequality, in [0, +oo]. *)
Lemma cauchy_schwarz (f g : U -> R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (\int[mu]_x `|f x * g x|%:E) ^+ 2 <=
  \int[mu]_x (f x ^+ 2)%:E * \int[mu]_x (g x ^+ 2)%:E.
Proof.
move=> mf mg.
have two0 : (0 < 2 :> R)%R by [].
have half : (2^-1 + 2^-1 = 1 :> R)%R by field.
have H := @hoelder _ _ _ mu f g 2 2 mf mg two0 two0 half.
rewrite Lnorm1 in H.
have H' : \int[mu]_x `|f x * g x|%:E <=
    'N[mu]_2[EFin \o f] * 'N[mu]_2[EFin \o g] by exact: H.
have N2 (h : U -> R) : measurable_fun setT h ->
    'N[mu]_2[EFin \o h] ^+ 2 = \int[mu]_x (h x ^+ 2)%:E.
  move=> mh; rewrite -poweR2 ?Lnorm_ge0 // powR_Lnorm ?gt_eqF //.
  apply: eq_integral => x _; rewrite poweR2 ?abse_ge0 //.
  rewrite (_ : `|(EFin \o h) x| = `|h x|%:E) // -EFin_expe.
  by rewrite real_normK ?num_real.
rewrite -(N2 f mf) -(N2 g mg) !expe2 muleACA.
have I0 : 0 <= \int[mu]_x `|f x * g x|%:E.
  by apply: integral_ge0 => x _; rewrite lee_fin.
by apply: lee_pmul.
Qed.

End cauchy_schwarz.

Section efron_stein_pair.
Context d1 d2 (U1 : measurableType d1) (U2 : measurableType d2) (R : realType).
Variables (m1 : probability U1 R) (m2 : probability U2 R).
Local Open Scope ereal_scope.

(* Integrating a measurable function in one coordinate gives a measurable
   function of the other one. *)
Lemma measurable_integral1 (f : U1 * U2 -> \bar R) : measurable_fun setT f ->
  measurable_fun setT (fun y => \int[m1]_x f (x, y)).
Proof.
move=> mf; apply: (eq_measurable_fun
    (fun y => \int[m1]_x f^\+ (x, y) - \int[m1]_x f^\- (x, y))).
  move=> y _; rewrite [RHS]integralE.
  by congr (_ - _)%E; apply: eq_integral => x _; rewrite ?funeposE ?funenegE.
apply: emeasurable_funB.
- exact: (measurable_fun_fubini_tonelli_G _ (measurable_funepos mf)
    (fun p => funepos_ge0 _ _)).
- exact: (measurable_fun_fubini_tonelli_G _ (measurable_funeneg mf)
    (fun p => funeneg_ge0 _ _)).
Qed.

Lemma measurable_integral2 (f : U1 * U2 -> \bar R) : measurable_fun setT f ->
  measurable_fun setT (fun x => \int[m2]_y f (x, y)).
Proof.
move=> mf; apply: (eq_measurable_fun
    (fun x => \int[m2]_y f^\+ (x, y) - \int[m2]_y f^\- (x, y))).
  move=> x _; rewrite [RHS]integralE.
  by congr (_ - _)%E; apply: eq_integral => y _; rewrite ?funeposE ?funenegE.
apply: emeasurable_funB.
- exact: (measurable_fun_fubini_tonelli_F _ (measurable_funepos mf)
    (fun p => funepos_ge0 _ _)).
- exact: (measurable_fun_fubini_tonelli_F _ (measurable_funeneg mf)
    (fun p => funeneg_ge0 _ _)).
Qed.

(* The variance in one coordinate is a measurable function of the other
   one. *)
Lemma measurable_variance1 (F : U1 * U2 -> R) : measurable_fun setT F ->
  measurable_fun setT (fun y => 'V_m1[fun x => F (x, y)]).
Proof.
move=> mF.
have mG : measurable_fun setT (fun y => fine (\int[m1]_x (F (x, y))%:E)).
  apply: measurableT_comp => //.
  by apply: (measurable_integral1 (f := EFin \o F)); exact/measurable_EFinP.
apply: (eq_measurable_fun (fun y => \int[m1]_x
    ((F (x, y) - fine (\int[m1]_x' (F (x', y))%:E)) ^+ 2)%:E)).
  by move=> y _; rewrite varianceT.
apply: (measurable_fun_fubini_tonelli_G
  (fun p => ((F p - fine (\int[m1]_x (F (x, p.2))%:E)) ^+ 2)%:E)).
- apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB => //.
  exact: measurableT_comp mG measurable_snd.
- by move=> p; rewrite lee_fin sqr_ge0.
Qed.

Lemma measurable_variance2 (F : U1 * U2 -> R) : measurable_fun setT F ->
  measurable_fun setT (fun x => 'V_m2[fun y => F (x, y)]).
Proof.
move=> mF.
have mK : measurable_fun setT (fun x => fine (\int[m2]_y (F (x, y))%:E)).
  apply: measurableT_comp => //.
  by apply: (measurable_integral2 (f := EFin \o F)); exact/measurable_EFinP.
apply: (eq_measurable_fun (fun x => \int[m2]_y
    ((F (x, y) - fine (\int[m2]_y' (F (x, y'))%:E)) ^+ 2)%:E)).
  by move=> x _; rewrite varianceT.
apply: (measurable_fun_fubini_tonelli_F
  (fun p => ((F p - fine (\int[m2]_y (F (p.1, y))%:E)) ^+ 2)%:E)).
- apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB => //.
  exact: measurableT_comp mK measurable_fst.
- by move=> p; rewrite lee_fin sqr_ge0.
Qed.

(* The Efron-Stein inequality for two independent blocks. *)
Theorem efron_stein_pair (F : U1 * U2 -> R) :
  (m1 \x m2).-integrable setT (EFin \o F) ->
  'V_(m1 \x m2)[F] <=
    \int[m2]_y 'V_m1[fun x => F (x, y)] + \int[m1]_x 'V_m2[fun y => F (x, y)].
Proof.
move=> iF; have mF : measurable_fun setT F.
  by apply/measurable_EFinP; exact: measurable_int iF.
set c := fine (\int[m1 \x m2]_z (F z)%:E).
pose G y := fine (\int[m1]_x (F (x, y))%:E).
pose K x := fine (\int[m2]_y (F (x, y))%:E).
have mG : measurable_fun setT G.
  exact: measurableT_comp (measurable_fubini_G iF).
have mK : measurable_fun setT K.
  exact: measurableT_comp (measurable_fubini_F iF).
have sq0 (r : R) : 0 <= (r ^+ 2)%:E by rewrite lee_fin sqr_ge0.
have mFc : measurable_fun setT (fun z => ((F z - c) ^+ 2)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
(* The law of total variance. *)
have -> : 'V_(m1 \x m2)[F] =
    \int[m2]_y 'V_m1[fun x => F (x, y)] + \int[m2]_y ((G y - c) ^+ 2)%:E.
  rewrite varianceT -/c (fubini_tonelli2 _ mFc (fun z => sq0 _)).
  rewrite -ge0_integralD //.
  - by move=> y _; exact: variance_ge0.
  - exact: measurable_variance1 mF.
  - by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
  apply: eq_integral => y _; rewrite /fubini_G /=.
  have mFy : measurable_fun setT (fun x => F (x, y)).
    exact: measurableT_comp mF (pair2_measurable y).
  by rewrite (sqr_dev_variance m1 c mFy) /G unlock.
apply: leeD2l.
(* The variance of the conditional mean G is at most the mean of the
   conditional variances in y, by Jensen's inequality. *)
have iF1 := integrable_fubini_F iF.
have iK : m1.-integrable setT (EFin \o K).
  apply/integrableP; split; first exact/measurable_EFinP.
  have /integrableP[_ iF1lt] := iF1.
  have afine (e : \bar R) : `|(fine e)%:E| <= `|e|.
    by case: e => [r| |] /=; rewrite ?normr0 ?abse0 ?leey.
  apply: le_lt_trans iF1lt; apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; exact/measurable_EFinP.
  - by apply: measurableT_comp => //; exact: measurable_fubini_F iF.
  by move=> x _; exact: afine.
have IK : \int[m1]_x (K x)%:E = c%:E.
  rewrite /c fineK; first exact: (integrable_fin_num measurableT iF).
  rewrite -(integral12_prod_meas1 iF); apply: ae_eq_integral => //.
  - exact/measurable_EFinP.
  - exact: measurable_fubini_F iF.
  apply: filterS (integrable_ae measurableT iF1) => x /(_ I) fx _.
  by rewrite /K fineK.
have mH : measurable_fun setT (fun p : U1 * U2 => ((F p - K p.1) ^+ 2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB => //.
  exact: measurableT_comp mK measurable_fst.
have FT := fubini_tonelli (m1 := m1) (m2 := m2) _ mH (fun p => sq0 _).
apply: (@le_trans _ _
    (\int[m2]_y \int[m1]_x ((F (x, y) - K (x, y).1) ^+ 2)%:E)); last first.
  rewrite -FT; apply: ge0_le_integral => //.
  - by move=> x _; apply: integral_ge0 => y _; exact: sq0.
  - exact: (measurable_fun_fubini_tonelli_F _ mH (fun p => sq0 _)).
  - exact: measurable_variance2 mF.
  by move=> x _; rewrite varianceT.
apply: ae_ge0_le_integral => //.
- by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
- by move=> y _; apply: integral_ge0 => x _; exact: sq0.
- exact: (measurable_fun_fubini_tonelli_G _ mH (fun p => sq0 _)).
apply: filterS (ae_integrable2 iF) => y iy _.
have mFy : measurable_fun setT (fun x => F (x, y) - K x)%R.
  apply: measurable_funB => //.
  exact: measurableT_comp mF (pair2_measurable y).
have := sqr_fine_expectation_le m1 mFy.
suff -> : fine 'E_m1[fun x => F (x, y) - K x]%R = (G y - c)%R by [].
rewrite unlock; under eq_integral do rewrite EFinB.
by rewrite integralB_EFin // IK fineB // integrable_fin_num.
Qed.

End efron_stein_pair.

Section variance_distribution.
Context d1 d2 (V : measurableType d1) (W : measurableType d2) (R : realType).
Local Open Scope ereal_scope.

Lemma integral_distribution_measurable (P : probability V R)
    (X : {mfun V >-> W}) (f : W -> \bar R) : measurable_fun setT f ->
  \int[distribution P X]_y f y = \int[P]_x f (X x).
Proof.
move=> mf; rewrite integralE [RHS]integralE.
rewrite !ge0_integral_distribution //.
- exact: measurable_funepos.
- exact: measurable_funeneg.
by congr (_ - _)%E; apply: eq_integral => x _; rewrite /= ?funeposE ?funenegE.
Qed.

Lemma variance_distribution (P : probability V R) (X : {mfun V >-> W})
    (F : W -> R) : measurable_fun setT F ->
  'V_(distribution P X)[F] = 'V_P[F \o X].
Proof.
move=> mF; rewrite !varianceT integral_distribution_measurable //.
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_funB.
by rewrite integral_distribution_measurable //; exact/measurable_EFinP.
Qed.

End variance_distribution.

Section efron_stein.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma measurable_variance_tuple_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> R) : measurable_fun setT F ->
  measurable_fun setT (fun x => 'V_(mu i)[fun t => F (tuple_set x i t)]).
Proof.
move=> mF; exact: (measurable_variance2 (mu i)
  (measurableT_comp mF (measurable_tuple_set_pair i))).
Qed.

(* The Efron-Stein inequality: the variance of an integrable function of
   independent coordinates is at most the sum over i of the mean of its
   variance in the coordinate i, the others being fixed. The variances are
   in [0, +oo]. *)
Theorem efron_stein_integrable (mu : nat -> probability T R) n
    (F : n.-tuple T -> R) :
  (tuple_prod mu n).-integrable setT (EFin \o F) ->
  'V_(tuple_prod mu n)[F] <=
    \sum_(i < n) \int[tuple_prod mu n]_x
      'V_(mu i)[fun t => F (tuple_set x i t)].
Proof.
elim: n mu F => [|n IH] mu F iF.
  have -> : F = cst (F [tuple]) by apply/funext => x; rewrite (tuple0 x).
  by rewrite variance_cst big_ord0.
have mF : measurable_fun setT F.
  by apply/measurable_EFinP; exact: measurable_int iF.
set Q := tuple_prod (fun i => mu i.+1) n.
have iFc : (mu 0%N \x Q).-integrable setT (EFin \o (F \o @tuple_cons _ T n)).
  have mEF : measurable_fun setT (EFin \o F) by exact/measurable_EFinP.
  exact: (integrable_tuple_prodS mu mEF).1 iF.
have -> : 'V_(tuple_prod mu n.+1)[F] = 'V_(mu 0%N \x Q)[F \o @tuple_cons _ T n].
  exact: variance_distribution.
apply: le_trans (efron_stein_pair iFc) _.
rewrite big_ord_recl; apply: leeD.
  (* The coordinate 0. *)
  rewrite [X in _ <= X]ge0_integral_tuple_prodS.
  - exact: measurable_variance_tuple_set.
  - by move=> x; exact: variance_ge0.
  have W0E t ts :
      'V_(mu ord0)[fun s => F (tuple_set (tuple_cons (t, ts)) ord0 s)] =
      'V_(mu 0%N)[fun s => F (tuple_cons (s, ts))].
    by apply: congr1; apply/funext => s; rewrite /tuple_cons /= tuple_set_cons0.
  under [X in _ <= X]eq_integral do under eq_integral do rewrite W0E.
  set C := \int[tuple_prod (fun i : nat => mu i.+1) n]_x
    'V_(mu 0%N)[(fun s : T => F (tuple_cons (s, x)))].
  rewrite (@integral_cst _ _ _ (mu 0%N) _ measurableT C).
  by rewrite [X in _ * X]probability_setT mule1.
(* The other coordinates, by the induction hypothesis for almost every
   value of the coordinate 0. *)
have WjE t ts (j : 'I_n) :
    'V_(mu (lift ord0 j))
      [fun s => F (tuple_set (tuple_cons (t, ts)) (lift ord0 j) s)] =
    'V_(mu j.+1)[fun s => F (tuple_cons (t, tuple_set ts j s))].
  rewrite lift0; apply: congr1; apply/funext => s.
  by rewrite /tuple_cons /= tuple_set_consS.
have mWc (j : 'I_n) : measurable_fun setT (fun p : T * n.-tuple T =>
    'V_(mu j.+1)[fun s => F (tuple_cons (p.1, tuple_set p.2 j s))]).
  apply: (eq_measurable_fun (fun p =>
    'V_(mu (lift ord0 j))
      [fun s => F (tuple_set (tuple_cons p) (lift ord0 j) s)])).
    by move=> [t ts] _; exact: WjE.
  exact: measurableT_comp (measurable_variance_tuple_set mu (lift ord0 j) mF)
    (@measurable_tuple_cons _ T n).
rewrite (_ : (\sum_(j < n) _)%R = \int[mu 0%N]_t (\sum_(j < n)
    (\int[Q]_ts
      'V_(mu j.+1)[fun s => F (tuple_cons (t, tuple_set ts j s))])%E)%R);
  last first.
  apply: ae_ge0_le_integral => //.
  - by move=> t _; exact: variance_ge0.
  - apply: measurable_variance2.
    exact: measurableT_comp mF (@measurable_tuple_cons _ T n).
  - move=> t _; apply: sume_ge0 => j _; apply: integral_ge0 => ts _.
    exact: variance_ge0.
  - apply: emeasurable_sum => j.
    exact: (measurable_fun_fubini_tonelli_F _ (mWc j)
      (fun p => variance_ge0 _ _)).
  apply: filterS (ae_integrable1 iFc) => t it _.
  exact: (IH (fun i => mu i.+1) (fun ts => F (tuple_cons (t, ts))) it).
rewrite ge0_integral_sum //.
- move=> j.
  exact: (measurable_fun_fubini_tonelli_F _ (mWc j)
    (fun p => variance_ge0 _ _)).
- by move=> j t _; apply: integral_ge0 => ts _; exact: variance_ge0.
apply: eq_bigr => j _; rewrite ge0_integral_tuple_prodS.
- exact: measurable_variance_tuple_set.
- by move=> x; exact: variance_ge0.
by apply: eq_integral => t _; apply: eq_integral => ts _; exact: WjE.
Qed.

(* The Efron-Stein inequality for a square integrable F. *)
Theorem efron_stein (mu : nat -> probability T R) n (F : n.-tuple T -> R) :
  F \in Lfun (tuple_prod mu n) 2%:E ->
  'V_(tuple_prod mu n)[F] <=
    \sum_(i < n) \int[tuple_prod mu n]_x
      'V_(mu i)[fun t => F (tuple_set x i t)].
Proof.
move=> F2; apply: efron_stein_integrable; apply/Lfun1_integrable.
exact: (Lfun_subset12 (fin_num_measure (tuple_prod mu n) _ measurableT) F2).
Qed.

(* Resampling the coordinate i: for x' equal to x with its coordinate i
   replaced by an independent copy, E (F x - F x')^2 is twice the mean of the
   variance in the coordinate i. *)
Lemma integral_resample_tuple_set (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> R) : measurable_fun setT F ->
  \int[tuple_prod mu n]_x \int[mu i]_t ((F x - F (tuple_set x i t)) ^+ 2)%:E =
  (\int[tuple_prod mu n]_x 'V_(mu i)[fun t => F (tuple_set x i t)]) *+ 2.
Proof.
move=> mF; have sq0 (r : R) : 0 <= (r ^+ 2)%:E by rewrite lee_fin sqr_ge0.
have mH : measurable_fun setT (fun p : n.-tuple T * T =>
    ((F p.1 - F (tuple_set p.1 i p.2)) ^+ 2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurableT_comp mF measurable_fst.
  exact: measurableT_comp mF (measurable_tuple_set_pair i).
rewrite (ge0_integral_tuple_prod_set mu i).
- exact: (measurable_fun_fubini_tonelli_F (m2 := mu i) _ mH (fun p => sq0 _)).
- by move=> x; apply: integral_ge0 => t _; exact: sq0.
transitivity (\int[tuple_prod mu n]_x
    ('V_(mu i)[fun t => F (tuple_set x i t)] *+ 2)).
  apply: eq_integral => x _.
  under eq_integral do under eq_integral do rewrite tuple_set_set.
  exact: (variance_resample (mu i)
    (measurableT_comp mF (measurable_tuple_set x i))).
under eq_integral do rewrite mule2n.
have mV := measurable_variance_tuple_set mu i mF.
by rewrite ge0_integralD // ?mule2n // => x _; exact: variance_ge0.
Qed.

(* The Efron-Stein inequality with resampled coordinates:
   Var F <= 1/2 sum_i E (F x - F x^(i))^2. *)
Theorem efron_stein_resample (mu : nat -> probability T R) n
    (F : n.-tuple T -> R) :
  (tuple_prod mu n).-integrable setT (EFin \o F) ->
  'V_(tuple_prod mu n)[F] <= 2^-1%:E * \sum_(i < n)
    \int[tuple_prod mu n]_x \int[mu i]_t ((F x - F (tuple_set x i t)) ^+ 2)%:E.
Proof.
move=> iF; have mF : measurable_fun setT F.
  by apply/measurable_EFinP; exact: measurable_int iF.
under eq_bigr => i _ do rewrite (integral_resample_tuple_set mu i mF) mule2n.
have half (S : \bar R) : 2^-1%:E * (S + S) = S.
  case: S => [r| |] /=.
  - by rewrite -EFinD -EFinM; congr EFin; field.
  - by rewrite mulry gtr0_sg ?invr_gt0 // mul1e.
  - by rewrite mulrNy gtr0_sg ?invr_gt0 // mul1e.
by rewrite big_split /= half; exact: efron_stein_integrable.
Qed.

(* The two estimates of one resampled coordinate that the fourth moment
   bound uses, for F with E F^4 < +oo and m = E F. *)
Lemma resample_sqr_le (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> R) (Di : R) :
  measurable_fun setT F -> (0 <= Di)%R ->
  \int[tuple_prod mu n]_x \int[mu i]_t
    ((F x - F (tuple_set x i t)) ^+ 4)%:E <= (Di ^+ 2)%:E ->
  \int[tuple_prod mu n]_x \int[mu i]_t
    ((F x - F (tuple_set x i t)) ^+ 2)%:E <= Di%:E.
Proof.
move=> mF D0 H4.
pose h (p : n.-tuple T * T) := (F p.1 - F (tuple_set p.1 i p.2))%R.
have mh : measurable_fun setT h.
  apply: measurable_funB; first exact: measurableT_comp mF measurable_fst.
  exact: measurableT_comp mF (measurable_tuple_set_pair i).
have mhk k : measurable_fun setT (fun p => ((h p) ^+ k)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have hk0 k p : 0 <= ((h p) ^+ (2 * k))%:E.
  by rewrite lee_fin exprM exprn_ge0 // sqr_ge0.
have I2 := fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ (mhk 2%N)
  (fun p => hk0 1%N p).
have I4 := fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ (mhk 4%N)
  (fun p => hk0 2%N p).
rewrite /fubini_F in I2 I4; rewrite -[X in X <= _]I2.
rewrite -[X in X <= _]I4 in H4.
have mh2 : measurable_fun setT (fun p => h p ^+ 2)%R by exact: measurable_funX.
have m1 : measurable_fun setT (fun _ : n.-tuple T * T => 1%R : R).
  exact: measurable_cst.
have CS := cauchy_schwarz (tuple_prod mu n \x mu i) mh2 m1.
have e1 : \int[tuple_prod mu n \x mu i]_x `|h x ^+ 2 * 1|%:E =
    \int[tuple_prod mu n \x mu i]_x (h x ^+ 2)%:E.
  by apply: eq_integral => x _; rewrite mulr1 ger0_norm // sqr_ge0.
have e2 : \int[tuple_prod mu n \x mu i]_x (h x ^+ 2 ^+ 2)%:E =
    \int[tuple_prod mu n \x mu i]_x (h x ^+ 4)%:E.
  by apply: eq_integral => x _; rewrite -exprM.
have e3 : \int[tuple_prod mu n \x mu i]__ ((1 : R) ^+ 2)%:E = 1.
  by rewrite expr1n integral_cst // mul1e [LHS]probability_setT.
rewrite e1 e2 e3 mule1 in CS; have {CS}C2 := le_trans CS H4.
set a := \int[tuple_prod mu n \x mu i]_z (h z ^+ 2)%:E in C2 *.
have a0 : 0 <= a by apply: integral_ge0 => z _; exact: (hk0 1%N).
clearbody a; move: a0 C2; case: a => [r| |] // r0 C2.
rewrite -EFin_expe lee_fin in C2; rewrite lee_fin.
have r0' : (0 <= r)%R by rewrite -lee_fin.
by rewrite -(ler_pXn2r (_ : (0 < 2)%N)) ?nnegrE.
Qed.

Lemma resample_sqr_sqr_le (mu : nat -> probability T R) n (i : 'I_n)
    (F : n.-tuple T -> R) (m Di : R) :
  measurable_fun setT F -> (0 <= Di)%R ->
  \int[tuple_prod mu n]_x ((F x - m) ^+ 4)%:E < +oo ->
  \int[tuple_prod mu n]_x \int[mu i]_t
    ((F x - F (tuple_set x i t)) ^+ 4)%:E <= (Di ^+ 2)%:E ->
  \int[tuple_prod mu n]_x \int[mu i]_t
    (((F x - m) ^+ 2 - (F (tuple_set x i t) - m) ^+ 2) ^+ 2)%:E <=
  (4 * Di * Num.sqrt (fine (\int[tuple_prod mu n]_x ((F x - m) ^+ 4)%:E)))%:E.
Proof.
move=> mF D0 M4 H4.
pose Z x := (F x - m)%R.
pose a (p : n.-tuple T * T) := (F p.1 - F (tuple_set p.1 i p.2))%R.
pose b (p : n.-tuple T * T) := (Z p.1 + Z (tuple_set p.1 i p.2))%R.
have mZ : measurable_fun setT Z by apply: measurable_funB.
have mZ1 : measurable_fun setT (fun p : n.-tuple T * T => Z p.1).
  exact: measurableT_comp mZ measurable_fst.
have mZ' : measurable_fun setT
    (fun p : n.-tuple T * T => Z (tuple_set p.1 i p.2)).
  exact: measurableT_comp mZ (measurable_tuple_set_pair i).
have ma : measurable_fun setT a.
  apply: measurable_funB; first exact: measurableT_comp mF measurable_fst.
  exact: measurableT_comp mF (measurable_tuple_set_pair i).
have mb : measurable_fun setT b by exact: measurable_funD.
have sq0 (r : R) : 0 <= (r ^+ 2)%:E by rewrite lee_fin sqr_ge0.
have z40 (r : R) : 0 <= (r ^+ 4)%:E.
  by rewrite lee_fin (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
have mG : measurable_fun setT (fun p : n.-tuple T * T =>
    (((F p.1 - m) ^+ 2 - (F (tuple_set p.1 i p.2) - m) ^+ 2) ^+ 2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; apply: measurable_funB.
    exact: measurable_funX mZ1.
  exact: measurable_funX mZ'.
rewrite -(fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ mG
  (fun p => sq0 _)).
have -> : \int[tuple_prod mu n \x mu i]_z
    (((F z.1 - m) ^+ 2 - (F (tuple_set z.1 i z.2) - m) ^+ 2) ^+ 2)%:E =
    \int[tuple_prod mu n \x mu i]_z `|a z ^+ 2 * b z ^+ 2|%:E.
  apply: eq_integral => z _.
  have ab0 : (0 <= a z ^+ 2 * b z ^+ 2)%R by rewrite mulr_ge0 // sqr_ge0.
  by rewrite (ger0_norm ab0) /a /b /Z; congr (EFin _); ring.
have ma2 : measurable_fun setT (fun z => a z ^+ 2)%R by exact: measurable_funX.
have mb2 : measurable_fun setT (fun z => b z ^+ 2)%R by exact: measurable_funX.
have CS := cauchy_schwarz (tuple_prod mu n \x mu i) ma2 mb2.
have Ia : \int[tuple_prod mu n \x mu i]_x (a x ^+ 2 ^+ 2)%:E <= (Di ^+ 2)%:E.
  apply: le_trans H4; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  under eq_integral do rewrite -exprM.
  have ma4 : measurable_fun setT (fun z => (a z ^+ 4)%:E).
    by apply/measurable_EFinP; exact: measurable_funX.
  by rewrite (fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ ma4).
set M := \int[tuple_prod mu n]_x ((F x - m) ^+ 4)%:E in M4 *.
have M0 : 0 <= M by apply: integral_ge0 => x _; exact: z40.
have mZ4 : measurable_fun setT (fun x => (Z x ^+ 4)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have mZ1' : measurable_fun setT (fun p : n.-tuple T * T => (Z p.1 ^+ 4)%:E).
  exact: measurableT_comp mZ4 measurable_fst.
have mZ2' : measurable_fun setT
    (fun p : n.-tuple T * T => (Z (tuple_set p.1 i p.2) ^+ 4)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have Q1 : \int[tuple_prod mu n \x mu i]_p (Z p.1 ^+ 4)%:E = M.
  rewrite (fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ mZ1'
    (fun p => z40 _)) /fubini_F /=.
  apply: eq_integral => x _; rewrite integral_cst //.
  by rewrite [X in _ * X]probability_setT mule1.
have Q2 : \int[tuple_prod mu n \x mu i]_p
    (Z (tuple_set p.1 i p.2) ^+ 4)%:E = M.
  rewrite (fubini_tonelli1 (m1 := tuple_prod mu n) (m2 := mu i) _ mZ2'
    (fun p => z40 _)) /fubini_F /=.
  by rewrite -(ge0_integral_tuple_prod_set mu i mZ4 (fun x => z40 _)).
have pw (u v : R) : ((u + v) ^+ 2 ^+ 2 <= 8 * (u ^+ 4 + v ^+ 4))%R.
  have h1 := sqr_ge0 ((u - v) * (u + v)).
  have h2 := sqr_ge0 ((u - v) ^+ 2).
  nra.
have Mf : M \is a fin_num by rewrite ge0_fin_numE.
have Ib : \int[tuple_prod mu n \x mu i]_x (b x ^+ 2 ^+ 2)%:E <=
    (16 * fine M)%:E.
  apply: (@le_trans _ _ (\int[tuple_prod mu n \x mu i]_p
    (8%:E * ((Z p.1 ^+ 4)%:E + (Z (tuple_set p.1 i p.2) ^+ 4)%:E)))).
    apply: ge0_le_integral => //.
    - by apply/measurable_EFinP; do 2 apply: measurable_funX.
    - by apply: emeasurable_funM => //; exact: emeasurable_funD.
    - by move=> x _; rewrite -EFinD -EFinM lee_fin; exact: pw.
  rewrite ge0_integralZl //.
  - exact: emeasurable_funD.
  - by move=> x _; rewrite adde_ge0.
  rewrite ge0_integralD // Q1 Q2.
  by rewrite -(fineK Mf) -EFinD -EFinM lee_fin; lra.
have fM0 : (0 <= fine M)%R by rewrite fine_ge0.
set c := \int[tuple_prod mu n \x mu i]_z `|a z ^+ 2 * b z ^+ 2|%:E in CS *.
have c0 : 0 <= c by apply: integral_ge0 => z _; rewrite lee_fin.
have C2 : c ^+ 2 <= (Di ^+ 2 * (16 * fine M))%:E.
  apply: le_trans CS _; rewrite EFinM; apply: lee_pmul => //.
  - by apply: integral_ge0 => z _; rewrite lee_fin exprn_ge0 // sqr_ge0.
  - by apply: integral_ge0 => z _; rewrite lee_fin exprn_ge0 // sqr_ge0.
clear CS; clearbody c; move: c0 C2; case: c => [r| |] // r0 C2.
rewrite -EFin_expe lee_fin in C2; rewrite lee_fin.
have r0' : (0 <= r)%R by rewrite -lee_fin.
have X0 : (0 <= 4 * Di * Num.sqrt (fine M))%R.
  by rewrite !mulr_ge0 // sqrtr_ge0.
rewrite -(ler_pXn2r (_ : (0 < 2)%N)) ?nnegrE // !exprMn sqr_sqrtr //.
lra.
Qed.

(* Moments from Efron-Stein: if E (F (x) - F (x^(i)))^4 <= D_i^2 for every
   i, then E (F - E F)^4 <= 9/2 (sum_i D_i)^2. *)
Theorem efron_stein_fourth (mu : nat -> probability T R) n
    (F : n.-tuple T -> R) (D : nat -> R) :
  measurable_fun setT F ->
  \int[tuple_prod mu n]_x ((F x) ^+ 4)%:E < +oo ->
  (forall i, 0 <= D i)%R ->
  (forall i : 'I_n, \int[tuple_prod mu n]_x \int[mu i]_t
    ((F x - F (tuple_set x i t)) ^+ 4)%:E <= ((D i) ^+ 2)%:E) ->
  \int[tuple_prod mu n]_x
    ((F x - fine (\int[tuple_prod mu n]_y (F y)%:E)) ^+ 4)%:E <=
  (9 / 2 * (\sum_(i < n) D i) ^+ 2)%:E.
Proof.
move=> mF F4 D0 HD.
set P := tuple_prod mu n; set m := fine (\int[P]_y (F y)%:E).
have e4 (r : R) : (0 <= r ^+ 4)%R by rewrite (_ : 4 = 2 * 2)%N // exprM sqr_ge0.
have z40 (r : R) : 0 <= (r ^+ 4)%:E by rewrite lee_fin.
have iF4 : P.-integrable setT (fun x => (F x ^+ 4)%:E).
  apply/integrableP; split.
    by apply/measurable_EFinP; exact: measurable_funX.
  apply: le_lt_trans F4; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => x _; rewrite gee0_abs.
have i1F4 : P.-integrable setT (fun x => (1 + F x ^+ 4)%:E).
  under eq_fun do rewrite EFinD.
  by apply: integrableD => //; exact: finite_measure_integrable_cst.
(* F and (F - m)^2 are square integrable. *)
have F2i : P.-integrable setT (EFin \o (fun x => F x ^+ 2)%R).
  apply: le_integrable i1F4 => //.
    by apply/measurable_EFinP; exact: measurable_funX.
  move=> x _; change (`|(F x ^+ 2)%:E| <= `|(1 + F x ^+ 4)%:E|).
  rewrite !abse_EFin lee_fin; have h := sqr_ge0 (F x ^+ 2 - 1)%R.
  rewrite !ger0_norm ?sqr_ge0 ?addr_ge0 ?exprn_even_ge0 //; nra.
have F2 : F \in Lfun P 2%:E by exact: integrable_sqr_Lfun2.
have F1 : P.-integrable setT (EFin \o F).
  apply/Lfun1_integrable.
  exact: (Lfun_subset12 (fin_num_measure P _ measurableT) F2).
have pw (u v : R) : ((u - v) ^+ 4 <= 8 * (u ^+ 4 + v ^+ 4))%R.
  have h1 := sqr_ge0 ((u + v) * (u - v)).
  have h2 := sqr_ge0 ((u + v) ^+ 2).
  nra.
have iZ4 : P.-integrable setT (fun x => ((F x - m) ^+ 4)%:E).
  apply: le_integrable (_ : P.-integrable setT
    (fun x => (8 * (F x ^+ 4 + m ^+ 4))%:E)) => //.
  - apply/measurable_EFinP; apply: measurable_funX.
    exact: measurable_funB.
  - move=> x _; rewrite !abse_EFin lee_fin.
    have h8 : (0 <= 8 * (F x ^+ 4 + m ^+ 4))%R by rewrite mulr_ge0 // addr_ge0.
    by rewrite (ger0_norm (e4 _)) (ger0_norm h8); exact: pw.
  under eq_fun do rewrite EFinM EFinD.
  apply: integrableZl => //; under eq_fun do rewrite EFinD.
  by apply: integrableD => //; exact: finite_measure_integrable_cst.
have M4 : \int[P]_x ((F x - m) ^+ 4)%:E < +oo.
  have /integrableP[_ h] := iZ4.
  apply: le_lt_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => x _; rewrite gee0_abs.
have mG : measurable_fun setT (fun x => (F x - m) ^+ 2)%R.
  by apply: measurable_funX; exact: measurable_funB.
have G2 : (fun x => (F x - m) ^+ 2)%R \in Lfun P 2%:E.
  apply: integrable_sqr_Lfun2 => //.
  apply: (@eq_integrable _ _ _ P setT measurableT
    (fun x => ((F x - m) ^+ 4)%:E)) => // x _.
  by rewrite /= -exprM.
have G1 : P.-integrable setT (EFin \o (fun x => (F x - m) ^+ 2)%R).
  apply/Lfun1_integrable.
  exact: (Lfun_subset12 (fin_num_measure P _ measurableT) G2).
(* Efron-Stein for F and for (F - m)^2. *)
set S := (\sum_(i < n) D i)%R.
have S0 : (0 <= S)%R by apply: sumr_ge0 => i _; exact: D0.
have VF : 'V_P[F] <= (2^-1 * S)%:E.
  apply: le_trans (efron_stein_resample F1) _.
  rewrite EFinM; apply: lee_wpmul2l => //.
  rewrite /S -sumEFin; apply: lee_sum => i _.
  exact: (resample_sqr_le mF (D0 i) (HD i)).
set M := \int[P]_x ((F x - m) ^+ 4)%:E in M4 iZ4 *.
have VG : 'V_P[(fun x => (F x - m) ^+ 2)%R] <=
    (2^-1 * \sum_(i < n) (4 * D i * Num.sqrt (fine M)))%:E.
  apply: le_trans (efron_stein_resample G1) _.
  rewrite EFinM; apply: lee_wpmul2l => //.
  rewrite -sumEFin; apply: lee_sum => i _.
  exact: (resample_sqr_sqr_le mF (D0 i) M4 (HD i)).
(* E (F - m)^4 = Var ((F - m)^2) + (Var F)^2. *)
have EG2 : 'E_P[((fun x => (F x - m) ^+ 2) ^+ 2)%R] = M.
  rewrite unlock /M; apply: eq_integral => x _.
  by rewrite exprfctE -exprM.
have EG : 'E_P[(fun x => (F x - m) ^+ 2)%R] = 'V_P[F].
  by rewrite varianceT unlock.
have := varianceE G2; rewrite EG2 EG => VGE.
have M0 : 0 <= M by apply: integral_ge0 => x _; exact: z40.
have Mf : M \is a fin_num by rewrite ge0_fin_numE.
have VFf : 'V_P[F] \is a fin_num by exact: variance_fin_num.
have VF0 : 0 <= 'V_P[F] by exact: variance_ge0.
rewrite VGE in VG; clear VGE EG EG2; move: VG VF => VG VF.
have eM : M = (fine M)%:E by rewrite fineK.
have eV : 'V_P[F] = (fine 'V_P[F])%:E by rewrite fineK.
rewrite eV in VG VF VF0; rewrite [X in X - _ <= _]eM in VG.
rewrite eM; rewrite eM in M0.
rewrite -EFin_expe -EFinB !lee_fin in VG VF M0 VF0 *.
rewrite -mulr_suml -mulr_sumr -/S in VG.
move: VG VF M0 VF0.
set mu4 := fine M; set v := fine 'V_P[F] => VG VF M0 VF0.
have es := sqr_sqrtr M0; have s0 := sqrtr_ge0 mu4.
set s := Num.sqrt mu4 in VG es s0 *; rewrite -es in VG *.
have h1 : (4 * S * s <= s ^+ 2 + 4 * S ^+ 2)%R.
  by have := sqr_ge0 (s - 2 * S)%R; nra.
have h2 : (v ^+ 2 <= S ^+ 2 / 4)%R.
  have h3 : (v * v <= (2^-1 * S) * (2^-1 * S))%R by apply: ler_pM.
  nra.
lra.
Qed.

End efron_stein.
