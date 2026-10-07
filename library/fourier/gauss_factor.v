From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import archimedean ring_tactic field_tactic.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp trigo measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral ftc.
From mathcomp Require Import probability gauss_integral.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.gaussian Require Import normal_integral gauss_ibp.
From GaussianAnalysis.comparison Require Import normal_linear.
From GaussianAnalysis.fourier Require Import charfun esseen.

(**md**************************************************************************)
(* # Gaussian factors of characteristic functions                             *)
(*                                                                            *)
(* The bound of Lemma 3.5 of Koehler and Sohn's vector small-ball estimate:   *)
(* for a law mu on the line with E[X^2] <= v and Q(mu, lambda) <= 1 - eps,    *)
(* and for 0 < r <= 1/2 and r <= s,                                           *)
(*   \int |cf mu u|^(1/r^2) exp (- s^2 u^2 / (2 r^2)) du <= r C,              *)
(*   C = 16 pi^3 sqrt pi e^(1/8) (1 + sqrt (4 v / eps)) / (lambda sqrt eps)   *)
(* (gauss_factor_le; gauss_factor_scaled_le after the substitution u = r t;   *)
(* gauss_factor_exists with the constant uniform in mu). The same holds with  *)
(* E[(X - a)^2] <= v for any a, the variance when a is the mean               *)
(* (gauss_factor_center_le, gauss_factor_center_exists). With                 *)
(* N = floor (1 / (2 r^2)), |cf mu u|^(1/r^2) <= |cf mu u|^(2 N), the         *)
(* characteristic function of the sum S of N independent copies of the        *)
(* symmetrized law (cf_re_sum_sym). The Gaussian Fubini identity              *)
(*   \int cf_re nu u exp (- u^2 / 2) du = sqrt (2 pi) E[exp (- X^2 / 2)]      *)
(* (Rintegral_cf_re_gauss_weight), the bound                                  *)
(*   E[exp (- X^2 / 2)] <= 2 e^(1/8) sqrt (2 pi) Q(nu, 1)                     *)
(* for X of law nu (gauss_weight_conc_fun), and the concentration of sums     *)
(* of esseen.v, Q(S, 1) <= C' / sqrt N <= 2 C' r, conclude.                   *)
(*                                                                            *)
(* The first half of the same lemma, for any truncation level c: a law with   *)
(* mean 0, variance 1 and E[X^2 1_{|X| <= M}] >= c has, for every L > 0,      *)
(*   Q(mu, L) <= 1 - min ((c - 4 L^2) / M^2, L^2 / (2 L^2 + 1))               *)
(* (conc_fun_truncated_level, conc_fun_truncated_level_exists). For c = 1/2   *)
(* and L = 1/8 this gives the paper's Q(mu, 1/8) <= 1 - min (7 / (16 M^2),    *)
(* 1/100) (conc_fun_truncated, conc_fun_truncated_exists). The length must    *)
(* depend on c: if c < 1/256, a law with mass close to 1 at +-1/16 and a      *)
(* small mass far away has Q(mu, 1/8) close to 1.                             *)
(*                                                                            *)
(* Laws on the line are probabilities on measurableTypeR R, as in charfun.v.  *)
(*                                                                            *)
(* ```                                                                        *)
(*       sym_diff p == p.1 - p.2, as a measurable function on pairs           *)
(*       sym_law mu == the law of X - X' for independent X and X' of law mu   *)
(*      tuple_sum x == the sum of the coordinates of the tuple x              *)
(*     sum_law mu n == the law of X_0 + ... + X_(n-1) for independent X_k     *)
(*                     of laws mu k                                           *)
(* gauss_factor_const v lambda eps == the constant C of gauss_factor_le       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


Section laws.
Context {R : realType}.

Definition sym_diff (p : measurableTypeR R * measurableTypeR R) :
  measurableTypeR R := (p.1 : R) - p.2.

Lemma measurable_sym_diff : measurable_fun [set: _] sym_diff.
Proof.
apply: measurable_funB.
  exact: measurableT_comp (@measurable_idR R) measurable_fst.
exact: measurableT_comp (@measurable_idR R) measurable_snd.
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ sym_diff measurable_sym_diff.

(* The law of X - X' for X and X' independent of law mu. *)
Definition sym_law (mu : probability (measurableTypeR R) R) :
  probability (measurableTypeR R) R := distribution (mu \x mu)%E sym_diff.

Lemma sym_lawE (mu : probability (measurableTypeR R) R)
    (A : set (measurableTypeR R)) : measurable A ->
  (mu \x mu)%E ((fun p => p.1 - p.2 : R) @^-1` A) = sym_law mu A.
Proof. by []. Qed.

Definition tuple_sum n (x : n.-tuple (measurableTypeR R)) : measurableTypeR R :=
  \sum_(k < n) (tnth x k : R).

Lemma measurable_tuple_sum n : measurable_fun [set: _] (@tuple_sum n).
Proof.
apply: measurable_sum => k.
exact: measurableT_comp (@measurable_idR R) (measurable_tnth k).
Qed.

HB.instance Definition _ n :=
  isMeasurableFun.Build _ _ _ _ (@tuple_sum n) (@measurable_tuple_sum n).

(* The law of X_1 + ... + X_n for independent X_k of laws mu k. *)
Definition sum_law (mu : nat -> probability (measurableTypeR R) R) n :
  probability (measurableTypeR R) R :=
  distribution (tuple_prod mu n) (@tuple_sum n).

Lemma sum_lawE (mu : nat -> probability (measurableTypeR R) R) n
    (A : set (measurableTypeR R)) : measurable A ->
  tuple_prod mu n ((fun x => \sum_(k < n) tnth x k) @^-1` A) = sum_law mu n A.
Proof. by []. Qed.

End laws.

(* The first half of Lemma 3.5 of Koehler and Sohn, for any truncation
   level c: a law of mean 0 and variance 1 with E[X^2 1_{|X| <= M}] >= c puts
   mass at most 1 - min ((c - 4 L^2) / M^2, L^2 / (2 L^2 + 1)) on every
   interval of length L > 0. *)
Section truncated_moment.
Context {R : realType} (mu : probability (measurableTypeR R) R) (M c : R).
Hypothesis M0 : 0 < M.
Hypothesis mean0 : (\int[mu]_x (x : R)%:E = 0)%E.
Hypothesis var1 : (\int[mu]_x (((x : R) ^+ 2)%R)%:E = 1)%E.
Hypothesis trunc : (c%:E <=
  \int[mu]_x (((x : R) ^+ 2 * \1_[set y : R | `|y| <= M] x)%R)%:E)%E.

Local Notation S := [set y : R | `|y| <= M].

Let mx : measurable_fun [set: measurableTypeR R] (fun x => x : R).
Proof. exact: measurable_idR. Qed.

Let mx2 : measurable_fun [set: measurableTypeR R] (fun x => (x : R) ^+ 2).
Proof. exact: measurable_funX. Qed.

Let mS : measurable S.
Proof.
have -> : S = `[(- M)%R, M]%classic.
  by apply/seteqP; split => y; rewrite /= in_itv /= ler_norml.
exact: measurable_itv.
Qed.

Let ix2 : mu.-integrable [set: _] (EFin \o (fun x => (x : R) ^+ 2)).
Proof.
apply/integrableP; split; first exact/measurable_EFinP.
under eq_integral do rewrite /= ger0_norm ?sqr_ge0//.
by rewrite var1 ltry.
Qed.

Let ix : mu.-integrable [set: _] (EFin \o (fun x => x : R)).
Proof.
have i1 : mu.-integrable [set: _] (EFin \o (fun x => 1 + (x : R) ^+ 2)).
  have := integrableD measurableT
    (finite_measure_integrable_cst mu 1 measurableT) ix2.
  by apply: eq_integrable => // x _; rewrite /= EFinD.
apply: (le_integrable measurableT _ _ i1); first exact/measurable_EFinP.
move=> x _; rewrite /comp !abse_EFin lee_fin.
rewrite [`|1 + _|]ger0_norm ?addr_ge0 ?sqr_ge0//.
rewrite -[(x : R) ^+ 2]real_normK; first exact: num_real.
by have := normr_ge0 (x : R); nra.
Qed.

Let Ex2 : \int[mu]_x ((x : R) ^+ 2) = 1.
Proof. by rewrite /Rintegral var1. Qed.

Let Ex : \int[mu]_x (x : R) = 0.
Proof. by rewrite /Rintegral mean0. Qed.

Let prob_fine (A : set (measurableTypeR R)) : measurable A ->
  mu A = (fine (mu A))%:E.
Proof.
move=> mA; rewrite fineK// ge0_fin_numE ?measure_ge0//.
by rewrite (le_lt_trans (probability_le1 mu mA)) ?ltry.
Qed.

Let iI (A : set (measurableTypeR R)) : measurable A ->
  mu.-integrable [set: _] (EFin \o \1_A).
Proof.
move=> mA; apply: (bounded_integrable mu (C := 1)) => [|x].
  exact: measurable_indic.
by rewrite indicE; case: (x \in A); rewrite /= ?normr1 ?normr0.
Qed.

Let RI (A : set (measurableTypeR R)) : measurable A ->
  \int[mu]_x \1_A x = fine (mu A).
Proof. by move=> mA; rewrite /Rintegral integral_indic// setIT. Qed.

Let ix2A (A : set (measurableTypeR R)) : measurable A ->
  mu.-integrable [set: _] (EFin \o (fun x => (x : R) ^+ 2 * \1_A x)).
Proof.
move=> mA; apply: (le_integrable measurableT _ _ ix2).
  apply/measurable_EFinP.
  by apply: measurable_funM => //; exact: measurable_indic.
move=> x _; rewrite /comp !abse_EFin lee_fin normrM indicE.
by case: (x \in A); rewrite /= ?normr1 ?normr0 ?mulr1 ?mulr0.
Qed.

Let ixA (A : set (measurableTypeR R)) (sg : R) : measurable A -> sg ^+ 2 = 1 ->
  mu.-integrable [set: _] (EFin \o (fun x => sg * (x : R) * \1_A x)).
Proof.
move=> mA sg1; apply: (le_integrable measurableT _ _ ix).
  apply/measurable_EFinP; apply: measurable_funM; last exact: measurable_indic.
  exact: measurable_funM.
move=> x _; rewrite /comp !abse_EFin lee_fin !normrM indicE.
have -> : `|sg| = 1.
  apply/eqP; rewrite -(@eqrXn2 _ 2 _ _ erefl (normr_ge0 sg) ler01) expr1n.
  by rewrite real_normK ?num_real// sg1.
by case: (x \in A); rewrite /= ?normr1 ?normr0 ?mulr1 ?mulr0 ?mul1r.
Qed.

Let dl_eq (I : set (measurableTypeR R)) : measurable I ->
  \int[mu]_x \1_(~` I) x = 1 - fine (mu I).
Proof.
move=> mI; have mnI : measurable (~` I) by exact: measurableC.
rewrite RI//; apply/EFin_inj; rewrite EFinB -!prob_fine//.
exact: probability_setC.
Qed.

(* If an interval I lies in [-2 L, 2 L], mu misses it with probability at
   least (c - 4 L^2) / M^2. *)
Let case_small (I : set (measurableTypeR R)) (L : R) : measurable I ->
  (forall x, I x -> `|x : R| <= 2 * L) ->
  (c - 4 * L ^+ 2) / M ^+ 2 <= 1 - fine (mu I).
Proof.
move=> mI hI; have mnI : measurable (~` I) by exact: measurableC.
have mnS : measurable (~` S) by exact: measurableC.
have dl := dl_eq mI.
have hL : 0 <= 4 * L ^+ 2 by rewrite mulr_ge0// sqr_ge0.
have pw x : (x : R) ^+ 2 <=
    4 * L ^+ 2 + M ^+ 2 * \1_(~` I) x + (x : R) ^+ 2 * \1_(~` S) x.
  rewrite !indicE; case: (x \in ~` S) / boolP => xS.
    by rewrite /= mulr1 lerDr addr_ge0// mulr_ge0// ?sqr_ge0//; case: (_ \in _).
  move: xS; rewrite in_setC negbK => /set_mem xS.
  case: (x \in ~` I) / boolP => xI.
    rewrite /= mulr1 mulr0 addr0; rewrite /= in xS.
    have : (x : R) ^+ 2 <= M ^+ 2.
      by rewrite -real_normK ?num_real// ler_pXn2r ?nnegrE ?normr_ge0// ltW.
    lra.
  move: xI; rewrite in_setC negbK => /set_mem/hI xI.
  rewrite /= !mulr0 !addr0 -real_normK ?num_real//.
  by have := normr_ge0 (x : R); nra.
have split x : (x : R) ^+ 2 =
    (x : R) ^+ 2 * \1_S x + (x : R) ^+ 2 * \1_(~` S) x.
  rewrite -mulrDr !indicE in_setC.
  by case: (x \in S); rewrite /= ?addr0 ?add0r mulr1.
have iC : mu.-integrable [set: _] (EFin \o cst (4 * L ^+ 2 : R)).
  exact: finite_measure_integrable_cst.
have iMI : mu.-integrable [set: _] (EFin \o (fun x => M ^+ 2 * \1_(~` I) x)).
  have := integrableZl measurableT (M ^+ 2) (iI mnI).
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have iCMI : mu.-integrable [set: _]
    (EFin \o (fun x => 4 * L ^+ 2 + M ^+ 2 * \1_(~` I) x)).
  have := integrableD measurableT iC iMI.
  by apply: eq_integrable => // x _; rewrite /= EFinD.
have iall : mu.-integrable [set: _] (EFin \o (fun x =>
    4 * L ^+ 2 + M ^+ 2 * \1_(~` I) x + (x : R) ^+ 2 * \1_(~` S) x)).
  have := integrableD measurableT iCMI (ix2A mnS).
  by apply: eq_integrable => // x _; rewrite /= EFinD.
have h1 : \int[mu]_x ((x : R) ^+ 2) <= \int[mu]_x
    (4 * L ^+ 2 + M ^+ 2 * \1_(~` I) x + (x : R) ^+ 2 * \1_(~` S) x).
  exact: (le_Rintegral measurableT ix2 iall (fun x _ => pw x)).
rewrite Ex2 (@RintegralD _ _ _ mu setT
  (fun x => 4 * L ^+ 2 + M ^+ 2 * \1_(~` I) x)
  (fun x => (x : R) ^+ 2 * \1_(~` S) x) measurableT iCMI (ix2A mnS)) in h1.
rewrite (@RintegralD _ _ _ mu setT (cst (4 * L ^+ 2))
  (fun x => M ^+ 2 * \1_(~` I) x) measurableT iC iMI) in h1.
rewrite Rintegral_cst//= in h1.
rewrite [X in _ * fine X]probability_setT /= mulr1 in h1.
rewrite (RintegralZl (M ^+ 2) measurableT (iI mnI)) dl in h1.
have h2 : \int[mu]_x ((x : R) ^+ 2 * \1_(~` S) x) =
    1 - \int[mu]_x ((x : R) ^+ 2 * \1_S x).
  have e : \int[mu]_x ((x : R) ^+ 2) = \int[mu]_x
      ((x : R) ^+ 2 * \1_S x + (x : R) ^+ 2 * \1_(~` S) x).
    by apply: eq_Rintegral => x _; exact: split.
  rewrite (@RintegralD _ _ _ mu setT (fun x => (x : R) ^+ 2 * \1_S x)
    (fun x => (x : R) ^+ 2 * \1_(~` S) x) measurableT (ix2A mS)
    (ix2A mnS)) Ex2 in e.
  by rewrite e; lra.
have h3 : c <= \int[mu]_x ((x : R) ^+ 2 * \1_S x).
  have fin : (\int[mu]_x ((x : R) ^+ 2 * \1_S x)%:E)%E \is a fin_num.
    by have := integrable_fin_num measurableT (ix2A mS).
  by rewrite -lee_fin /Rintegral fineK.
rewrite ler_pdivrMr ?exprn_gt0//.
by rewrite h2 in h1; lra.
Qed.

(* If sg x >= L on I, with sg = 1 or sg = -1, then mu misses I with
   probability at least L^2 / (2 L^2 + 1), because E[X] = 0 and E[X^2] = 1. *)
Let case_far (I : set (measurableTypeR R)) (sg L : R) : measurable I ->
  0 < L -> sg ^+ 2 = 1 -> (forall x, I x -> L <= sg * x) ->
  L ^+ 2 / (2 * L ^+ 2 + 1) <= 1 - fine (mu I).
Proof.
move=> mI L0 sg1 hI; have mnI : measurable (~` I) by exact: measurableC.
have dlE := dl_eq mI.
have nsg : `|sg| = 1.
  apply/eqP; rewrite -(@eqrXn2 _ 2 _ _ erefl (normr_ge0 sg) ler01) expr1n.
  by rewrite real_normK ?num_real// sg1.
have i8 : mu.-integrable [set: _] (EFin \o (fun x => L * \1_I x)).
  have := integrableZl measurableT L (iI mI).
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have low : L * fine (mu I) <= \int[mu]_x (sg * x * \1_I x).
  rewrite -RI// -(RintegralZl L measurableT (iI mI)).
  apply: (le_Rintegral measurableT i8 (ixA mI sg1)) => x _.
  rewrite indicE; case: (x \in I) / boolP => xI; last by rewrite /= !mulr0.
  by rewrite /= !mulr1; apply: hI; exact: set_mem.
have isg : mu.-integrable [set: _] (EFin \o (fun x => sg * (x : R))).
  have := integrableZl measurableT sg ix.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have sum0 : \int[mu]_x (sg * x * \1_I x) +
    \int[mu]_x (sg * x * \1_(~` I) x) = 0.
  rewrite -(@RintegralD _ _ _ mu setT (fun x => sg * x * \1_I x)
    (fun x => sg * x * \1_(~` I) x) measurableT (ixA mI sg1) (ixA mnI sg1)).
  transitivity (\int[mu]_x (sg * (x : R))).
    apply: eq_Rintegral => x _; rewrite -mulrDr !indicE in_setC.
    by case: (x \in I); rewrite /= ?addr0 ?add0r mulr1.
  have E1 : \int[mu]_x (sg * (x : R)) = sg * \int[mu]_x (x : R).
    exact: (RintegralZl sg measurableT ix).
  by rewrite E1 Ex mulr0.
(* |x| <= L / 2 x^2 + 1 / (2 L) *)
have key (y : R) : y <= L / 2 * y ^+ 2 + (2 * L)^-1.
  have Ln0 : L != 0 by rewrite gt_eqF.
  have -> : L / 2 * y ^+ 2 + (2 * L)^-1 = y + L / 2 * (y - L^-1) ^+ 2.
    by field.
  rewrite lerDl; apply: mulr_ge0; last exact: sqr_ge0.
  by rewrite divr_ge0// ltW.
have i20 : mu.-integrable [set: _]
    (EFin \o (fun x => L / 2 * (x : R) ^+ 2 + (2 * L)^-1 * \1_(~` I) x)).
  have i1 := integrableZl measurableT (L / 2) ix2.
  have i2 := integrableZl measurableT (2 * L)^-1 (iI mnI).
  have := integrableD measurableT i1 i2.
  by apply: eq_integrable => // x _; rewrite /= EFinD !EFinM.
have iN : mu.-integrable [set: _]
    (EFin \o (fun x => - (sg * x * \1_(~` I) x))).
  have := integrableZl measurableT (-1) (ixA mnI sg1).
  by apply: eq_integrable => // x _; rewrite /= -EFinM mulN1r.
have up : - (\int[mu]_x (sg * x * \1_(~` I) x)) <=
    L / 2 + (2 * L)^-1 * (1 - fine (mu I)).
  have NE : \int[mu]_x (- (sg * x * \1_(~` I) x)) =
      - \int[mu]_x (sg * x * \1_(~` I) x).
    exact: (RintegralN (ixA mnI sg1)).
  rewrite -NE.
  apply: le_trans (le_Rintegral measurableT iN i20 _) _.
    move=> x _; rewrite indicE; case: (x \in ~` I) => /=; last first.
      rewrite !mulr0 oppr0 addr0; apply: mulr_ge0; last exact: sqr_ge0.
      by rewrite divr_ge0// ltW.
    rewrite !mulr1; apply: le_trans (ler_norm _) _.
    rewrite normrN normrM nsg mul1r -real_normK ?num_real//.
  rewrite (@RintegralD _ _ _ mu setT (fun x => L / 2 * (x : R) ^+ 2)
    (fun x => (2 * L)^-1 * \1_(~` I) x) measurableT _ _).
  - have := integrableZl measurableT (L / 2) ix2.
    by apply: eq_integrable => // x _; rewrite /= EFinM.
  - have := integrableZl measurableT (2 * L)^-1 (iI mnI).
    by apply: eq_integrable => // x _; rewrite /= EFinM.
  have E1 : \int[mu]_x (L / 2 * (x : R) ^+ 2) =
      L / 2 * \int[mu]_x ((x : R) ^+ 2).
    exact: (RintegralZl (L / 2) measurableT ix2).
  by rewrite E1 Ex2 (RintegralZl (2 * L)^-1 measurableT (iI mnI)) dlE mulr1.
have h : L * fine (mu I) <= L / 2 + (2 * L)^-1 * (1 - fine (mu I)) by lra.
set p := fine (mu I) in h *.
have Ln0 : L != 0 by rewrite gt_eqF.
have h2 : 2 * L ^+ 2 * p <= L ^+ 2 + (1 - p).
  have := ler_wpM2l (_ : 0 <= 2 * L) h.
  have -> : 2 * L * (L * p) = 2 * L ^+ 2 * p by ring.
  have -> : 2 * L * (L / 2 + (2 * L)^-1 * (1 - p)) = L ^+ 2 + (1 - p).
    by field.
  by apply; rewrite mulr_ge0// ltW.
have d0 : 0 < 2 * L ^+ 2 + 1 by have := sqr_ge0 L; lra.
rewrite ler_pdivrMr//.
lra.
Qed.

Lemma conc_fun_truncated_level (L : R) : 0 < L ->
  conc_fun mu L <=
  1 - minr ((c - 4 * L ^+ 2) / M ^+ 2) (L ^+ 2 / (2 * L ^+ 2 + 1)).
Proof.
move=> L0; apply: conc_fun_le => a.
set I := `[a, (a + L)%R]%classic.
have mI : measurable I by exact: measurable_itv.
rewrite (prob_fine mI) lee_fin.
suff : minr ((c - 4 * L ^+ 2) / M ^+ 2) (L ^+ 2 / (2 * L ^+ 2 + 1)) <=
    1 - fine (mu I) by lra.
have [ha|ha] := ltP L a.
  rewrite ge_min; apply/orP; right; apply: (@case_far I 1 L) => //.
    by rewrite expr1n.
  by move=> x; rewrite /I /= in_itv /= mul1r => /andP[h _]; lra.
have [hb|hb] := ltP a (- (2 * L)).
  rewrite ge_min; apply/orP; right; apply: (@case_far I (-1) L) => //.
    by rewrite sqrrN expr1n.
  by move=> x; rewrite /I /= in_itv /= mulN1r => /andP[_ h]; lra.
rewrite ge_min; apply/orP; left; apply: (@case_small I L) => // x.
rewrite /I /= in_itv /= => /andP[h1 h2].
by rewrite ler_norml; apply/andP; split; lra.
Qed.

End truncated_moment.

(* The first half of Lemma 3.5 as stated in the paper: level 1/2 and
   intervals of length 1/8. *)
Section truncated_moment_half.
Context {R : realType} (mu : probability (measurableTypeR R) R) (M : R).
Hypothesis M0 : 0 < M.
Hypothesis mean0 : (\int[mu]_x (x : R)%:E = 0)%E.
Hypothesis var1 : (\int[mu]_x (((x : R) ^+ 2)%R)%:E = 1)%E.
Hypothesis trunc : ((2^-1)%:E <=
  \int[mu]_x (((x : R) ^+ 2 * \1_[set y : R | `|y| <= M] x)%R)%:E)%E.

Lemma conc_fun_truncated :
  conc_fun mu 8^-1 <= 1 - minr (7 / (16 * M ^+ 2)) 100^-1.
Proof.
have L0 : 0 < 8^-1 :> R by rewrite invr_gt0 ltr0n.
apply: le_trans (conc_fun_truncated_level M0 mean0 var1 trunc L0) _.
have Mn0 : M != 0 by rewrite gt_eqF.
have -> : (2^-1 - 4 * 8^-1 ^+ 2) / M ^+ 2 = 7 / (16 * M ^+ 2) :> R.
  by field.
have -> : 8^-1 ^+ 2 / (2 * 8^-1 ^+ 2 + 1) = 66^-1 :> R by field.
rewrite lerD2l lerN2 le_min !ge_min lexx /=.
by apply/orP; right; lra.
Qed.

End truncated_moment_half.

(* The Gaussian weight exp (- y^2 / 2), of integral sqrt (2 pi). *)
Section gauss_weight.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

Lemma normal_peak1V : (normal_peak (1 : R))^-1 = Num.sqrt (2 * pi).
Proof. by rewrite /normal_peak invrK expr1n mul1r mulr_natl. Qed.

Let peak0 : 0 < normal_peak (1 : R).
Proof. by rewrite normal_peak_gt0// oner_neq0. Qed.

Let gwE (y : R) : expR (- y ^+ 2 / 2) = (normal_peak 1)^-1 * normal_pdf 0 1 y.
Proof. by rewrite normal_pdf01E mulrA mulVf ?mul1r// gt_eqF. Qed.

Lemma measurable_gauss_weight :
  measurable_fun [set: R] (fun y => expR (- y ^+ 2 / 2)).
Proof.
have -> : (fun y : R => expR (- y ^+ 2 / 2)) =
    fun y => (normal_peak 1)^-1 * normal_pdf 0 1 y.
  by apply/funext => y; exact: gwE.
by apply: measurable_funM => //; exact: measurable_normal_pdf.
Qed.

Lemma integrable_gauss_weight :
  leb.-integrable [set: R] (EFin \o (fun y => expR (- y ^+ 2 / 2))).
Proof.
have := integrableZl measurableT (normal_peak (1 : R))^-1
  (integrable_normal_pdf 0 (1 : R)).
by apply: eq_integrable => // y _; rewrite /= gwE EFinM.
Qed.

Lemma Rintegral_gauss_weight :
  \int[leb]_y expR (- y ^+ 2 / 2) = Num.sqrt (2 * pi) :> R.
Proof.
transitivity (\int[leb]_y ((normal_peak (1 : R))^-1 * normal_pdf 0 1 y)).
  by apply: eq_Rintegral => y _; exact: gwE.
rewrite RintegralZl//; first exact: integrable_normal_pdf.
by rewrite /Rintegral integral_normal_pdf /= mulr1 normal_peak1V.
Qed.

End gauss_weight.

Section gauss_conc.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

Let leb_itv (a b : R) : a <= b -> leb `[a, b]%classic = (b - a)%:E.
Proof.
move=> ab; have := @lebesgue_measure_itv R `[a, b].
rewrite /= lte_fin; have [ab'|ba] := ltP a b.
  by rewrite EFinB => h; exact: h.
have ea : a = b by apply/eqP; rewrite eq_le ab ba.
by rewrite ea subrr => h; exact: h.
Qed.

(* The integral of exp (- y^2 / 2) over [x - 1/2, x + 1/2] is at least
   exp (- 1/8) exp (- x^2 / 2) / 2: on the half of the window that is closer
   to 0, y^2 <= x^2 + 1/4. *)
Let window (x : measurableTypeR R) :
  expR (- 8^-1) / 2 * expR (- (x : R) ^+ 2 / 2) <=
  \int[leb]_y (\1_`[(x : R) - 2^-1, (x : R) + 2^-1]%classic y *
    expR (- (y : R) ^+ 2 / 2)).
Proof.
pose c := expR (- 8^-1) * expR (- (x : R) ^+ 2 / 2).
pose J : set (measurableTypeR R) := if 0 <= (x : R) then
  `[(x : R) - 2^-1, (x : R)]%classic else `[(x : R), (x : R) + 2^-1]%classic.
have mJ : measurable J by rewrite /J; case: ifP => _; exact: measurable_itv.
have legJ : leb J = (2^-1)%:E.
  rewrite /J; case: ifP => _; rewrite leb_itv.
  - by rewrite gerBl.
  - by congr EFin; ring.
  - by rewrite lerDl.
  - by congr EFin; ring.
set W : set (measurableTypeR R) :=
  `[(x : R) - 2^-1, (x : R) + 2^-1]%classic.
have mW : measurable W by exact: measurable_itv.
have c0 : 0 <= c by rewrite mulr_ge0// expR_ge0.
have E1 : (\int[leb]_y (c * \1_J y)%:E = (c / 2)%:E)%E.
  under eq_integral do rewrite EFinM.
  rewrite ge0_integralZl//.
  - exact/measurable_EFinP/measurable_indic.
  - rewrite integral_indic// setIT.
    transitivity (c%:E * (2^-1)%:E)%E; first by congr (_ * _)%E; exact: legJ.
    by rewrite -EFinM.
have iW : leb.-integrable [set: _]
    (EFin \o (fun y => \1_W y * expR (- (y : R) ^+ 2 / 2))).
  apply: (le_integrable measurableT _ _ (@integrable_gauss_weight R)).
    apply/measurable_EFinP; apply: measurable_funM.
      exact: measurable_indic.
    exact: (@measurable_gauss_weight R).
  move=> y _; rewrite /comp !abse_EFin lee_fin normrM indicE.
  by case: (y \in W); rewrite /= ?normr1 ?normr0 ?mul1r ?mul0r// normr_ge0.
have pw (y : measurableTypeR R) : ((c * \1_J y)%:E <=
    (\1_W y * expR (- (y : R) ^+ 2 / 2))%:E)%E.
  rewrite lee_fin !indicE; case: (y \in J) / boolP => yJ; last first.
    by rewrite /= mulr0 mulr_ge0 ?expR_ge0//; case: (_ \in _).
  have yW : y \in W.
    move: yJ; rewrite /J /W; case: ifP => x0; rewrite !inE /= !in_itv /=;
      move=> /andP[h1 h2]; apply/andP; split; lra.
  rewrite yW /= !mulr1 mul1r /c -expRD ler_expR.
  move: yJ; rewrite /J; case: ifP => x0; rewrite inE /= in_itv /=;
    move=> /andP[h1 h2].
  - have : (y : R) ^+ 2 <= (x : R) ^+ 2 + 4^-1.
      have : 0 <= (x : R) - y by lra.
      have : 0 <= (y : R) - ((x : R) - 2^-1) by lra.
      nra.
    lra.
  - have : (y : R) ^+ 2 <= (x : R) ^+ 2 + 4^-1.
      have : 0 <= (y : R) - x by lra.
      have : 0 <= ((x : R) + 2^-1) - y by lra.
      have x0' : (x : R) < 0 by rewrite ltNge x0.
      nra.
    lra.
have le : (\int[leb]_y (c * \1_J y)%:E <=
    \int[leb]_y (\1_W y * expR (- (y : R) ^+ 2 / 2))%:E)%E.
  apply: ge0_le_integral.
  - exact: measurableT.
  - by move=> y _; rewrite lee_fin mulr_ge0// indicE; case: (y \in J).
  - by apply/measurable_EFinP; apply: measurable_funM => //;
      exact: measurable_indic.
  - exact: measurable_int iW.
  - by move=> y _; exact: pw.
rewrite E1 in le; rewrite /Rintegral.
have fin : (\int[leb]_y (\1_W y * expR (- (y : R) ^+ 2 / 2))%:E)%E
    \is a fin_num by exact: integrable_fin_num iW.
rewrite -lee_fin fineK//; apply: le_trans le.
by rewrite lee_fin /c; lra.
Qed.

(* E[exp (- X^2 / 2)] <= 2 e^(1/8) sqrt (2 pi) Q(X, 1). *)
Lemma gauss_weight_conc_fun (nu : probability (measurableTypeR R) R) :
  \int[nu]_x expR (- (x : R) ^+ 2 / 2) <=
  2 * expR 8^-1 * Num.sqrt (2 * pi) * conc_fun nu 1.
Proof.
set B := [set p : measurableTypeR R * measurableTypeR R |
  (`|p.1 - p.2| <= 2^-1)%R].
have mB : measurable B.
  have -> : B = sym_diff @^-1` `[(- 2^-1)%R, 2^-1]%classic.
    by apply/seteqP; split => p; rewrite /B /= in_itv /= ler_norml.
  rewrite -[X in measurable X]setTI.
  by apply: measurable_sym_diff => //; exact: measurable_itv.
pose F (p : measurableTypeR R * measurableTypeR R) : R :=
  \1_B p * expR (- (p.2 : R) ^+ 2 / 2).
have mF : measurable_fun [set: _] F.
  apply: measurable_funM; first exact: measurable_indic.
  exact: measurableT_comp (@measurable_gauss_weight R) measurable_snd.
have Fg x y : `|F (x, y)| <= expR (- (y : R) ^+ 2 / 2).
  rewrite /F normrM [`|expR _|]ger0_norm ?expR_ge0// indicE.
  by case: ((x, y) \in B); rewrite /= ?normr1 ?normr0 ?mul1r ?mul0r// expR_ge0.
have ig := @integrable_gauss_weight R.
have low x : expR (- 8^-1) / 2 * expR (- (x : R) ^+ 2 / 2) <=
    \int[lebesgue_measure]_y F (x, y).
  apply: le_trans (window x) _; rewrite le_eqVlt; apply/orP; left.
  apply/eqP; apply: eq_Rintegral => y _; rewrite /F !indicE.
  congr (_ * _); congr ((_ : bool)%:R).
  apply/idP/idP; rewrite !in_setE /B /= ?in_itv /= ?ler_norml;
    by move=> /andP[h1 h2]; apply/andP; split; lra.
have iFx x : (@lebesgue_measure R).-integrable [set: _]
    (EFin \o (fun y => F (x, y))).
  apply: (le_integrable measurableT _ _ ig).
    by apply/measurable_EFinP; exact: measurableT_comp.
  move=> y _; rewrite /comp !abse_EFin lee_fin (le_trans (Fg x y))//.
  exact: ler_norm.
have K x : `|\int[lebesgue_measure]_y F (x, y)| <= Num.sqrt (2 * pi).
  rewrite -Rintegral_gauss_weight.
  apply: le_trans (le_normr_Rintegral measurableT (iFx x)) _.
  have iA : (@lebesgue_measure R).-integrable [set: _]
      (EFin \o (fun y => `|F (x, y)|)).
    apply: (le_integrable measurableT _ _ (iFx x)).
      by apply/measurable_EFinP; apply: measurableT_comp => //;
        exact: measurableT_comp.
    by move=> y _; rewrite /comp !abse_EFin lee_fin normr_id.
  exact: (le_Rintegral measurableT iA ig (fun y _ => Fg x y)).
have mK : measurable_fun [set: _] (fun x => \int[lebesgue_measure]_y F (x, y)).
  exact: (measurable_Rintegral1 nu mF ig Fg).
have iK : nu.-integrable [set: _]
    (EFin \o (fun x => \int[lebesgue_measure]_y F (x, y))).
  exact: (bounded_integrable nu mK K).
set c := 2 * expR (8^-1 : R).
have c0 : 0 < c by rewrite mulr_gt0// expR_gt0.
have iL : nu.-integrable [set: _]
    (EFin \o (fun x => expR (- (x : R) ^+ 2 / 2))).
  apply: (bounded_integrable nu (C := 1)).
    exact: measurableT_comp (@measurable_gauss_weight R) (@measurable_idR R).
  move=> x; rewrite ger0_norm ?expR_ge0// -expR0 ler_expR.
  by rewrite mulNr oppr_le0 divr_ge0// sqr_ge0.
have icK : nu.-integrable [set: _]
    (EFin \o (fun x => c * \int[lebesgue_measure]_y F (x, y))).
  have := integrableZl measurableT c iK.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
have step1 : \int[nu]_x expR (- (x : R) ^+ 2 / 2) <=
    c * \int[nu]_x \int[lebesgue_measure]_y F (x, y).
  rewrite -(RintegralZl c measurableT iK).
  apply: (le_Rintegral measurableT iL icK) => x _.
  have h := low x.
  have e1 : expR (8^-1 : R) * expR (- 8^-1) = 1 by rewrite -expRD addrN expR0.
  have h' := ler_wpM2l (ltW c0) h.
  have eq : c * (expR (- 8^-1) / 2 * expR (- (x : R) ^+ 2 / 2)) =
      expR (- (x : R) ^+ 2 / 2).
    have e2 : 2 * expR (8^-1 : R) * (expR (- 8^-1) / 2) =
        (2 / 2) * (expR (8^-1 : R) * expR (- 8^-1)) by ring.
    by rewrite /c mulrA e2 divff ?pnatr_eq0// e1 !mul1r.
  by rewrite eq in h'.
rewrite (Rintegral_fubini nu mF ig Fg) in step1.
have step2 : \int[lebesgue_measure]_y \int[nu]_x F (x, y) <=
    \int[lebesgue_measure]_y (expR (- (y : R) ^+ 2 / 2) * conc_fun nu 1).
  apply: le_Rintegral => //.
  - apply: (le_integrable measurableT _ _ ig).
      by apply/measurable_EFinP; exact: (measurable_Rintegral2 nu mF ig Fg).
    move=> y _; rewrite /comp !abse_EFin lee_fin.
    rewrite [`|expR _|]ger0_norm ?expR_ge0//.
    by apply: Rintegral_bounded => [|x]; [exact: measurableT_comp|exact: Fg].
  - have := integrableZr measurableT (conc_fun nu 1) ig.
    by apply: eq_integrable => // y _; rewrite /= EFinM.
  - move=> y _.
    have mI : measurable (`[(y : R) - 2^-1, (y : R) - 2^-1 + 1]%classic : set
        (measurableTypeR R)) by exact: measurable_itv.
    have E : \int[nu]_x F (x, y) =
        \int[nu]_x \1_(`[(y : R) - 2^-1, (y : R) - 2^-1 + 1]%classic) x *
        expR (- (y : R) ^+ 2 / 2).
      have iI : nu.-integrable [set: _]
          (EFin \o \1_(`[(y : R) - 2^-1, (y : R) - 2^-1 + 1]%classic)).
        by apply: (bounded_integrable nu (C := 1)) => [|x];
          [exact: measurable_indic|rewrite indicE; case: (_ \in _);
           rewrite /= ?normr1 ?normr0].
      transitivity (\int[nu]_x
        (\1_(`[(y : R) - 2^-1, (y : R) - 2^-1 + 1]%classic) x *
         expR (- (y : R) ^+ 2 / 2))); last exact: RintegralZr.
      apply: eq_Rintegral => x _; rewrite /F !indicE; congr (_ * _).
      congr ((_ : bool)%:R); apply/idP/idP;
        rewrite !in_setE /B /= ?in_itv /= ?ler_norml;
        by move=> /andP[h1 h2]; apply/andP; split; lra.
    rewrite E mulrC ler_wpM2l ?expR_ge0//.
    rewrite /Rintegral integral_indic// setIT.
    exact: conc_fun_ub.
rewrite RintegralZr// Rintegral_gauss_weight in step2.
by apply: le_trans step1 _; rewrite -mulrA -/c ler_pM2l.
Qed.

End gauss_conc.

Section gauss_fubini.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).
Local Notation N := (@normal_prob R 0 1).

(* For f bounded and measurable, E[f (G)] = \int f (x) phi (x) dx, with G
   standard normal and phi its density. *)
Lemma Rintegral_normal01 (f : R -> R) (C : R) :
  measurable_fun [set: R] f -> (forall x, `|f x| <= C) ->
  \int[N]_x f x = \int[leb]_x (f x * normal_pdf 0 1 x).
Proof.
move=> mf fC; rewrite /Rintegral integral_normal_prob.
  exact: (bounded_integrable N mf fC).
by congr fine; apply: eq_integral => x _; rewrite /= EFinM.
Qed.

(* The Gaussian Fubini identity: the integral of cf_re nu against the
   Gaussian weight is sqrt (2 pi) E[exp (- X^2 / 2)] for X of law nu. *)
Lemma Rintegral_cf_re_gauss_weight (nu : probability (measurableTypeR R) R) :
  \int[leb]_u (cf_re nu u * expR (- (u : R) ^+ 2 / 2)) =
  Num.sqrt (2 * pi) * \int[nu]_x expR (- (x : R) ^+ 2 / 2).
Proof.
have peak0 : 0 < normal_peak (1 : R) by rewrite normal_peak_gt0// oner_neq0.
rewrite -normal_peak1V.
pose F (p : measurableTypeR R * measurableTypeR R) : R :=
  cos ((p.2 : R) * p.1) * expR (- (p.2 : R) ^+ 2 / 2).
have m1 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => p.1 : R).
  exact: measurableT_comp (@measurable_idR R) measurable_fst.
have m2 : measurable_fun [set: measurableTypeR R * measurableTypeR R]
    (fun p => p.2 : R).
  exact: measurableT_comp (@measurable_idR R) measurable_snd.
have mF : measurable_fun [set: _] F.
  apply: measurable_funM.
    by apply: measurable_cos_comp; exact: measurable_funM.
  exact: measurableT_comp (@measurable_gauss_weight R) m2.
have Fg x u : `|F (x, u)| <= expR (- (u : R) ^+ 2 / 2).
  rewrite /F normrM [`|expR _|]ger0_norm ?expR_ge0//.
  by have := cos_max ((u : R) * x); have := expR_ge0 (- (u : R) ^+ 2 / 2); nra.
have ig := @integrable_gauss_weight R.
have L : \int[leb]_u (cf_re nu u * expR (- (u : R) ^+ 2 / 2)) =
    \int[leb]_u \int[nu]_x F (x, u).
  apply: eq_Rintegral => u _; rewrite /cf_re /F /=; symmetry.
  exact: (RintegralZr _ measurableT
    (integrable_cos_mul nu u (@measurable_idR R))).
rewrite L -(Rintegral_fubini nu mF ig Fg).
transitivity (\int[nu]_x ((normal_peak 1)^-1 * expR (- (x : R) ^+ 2 / 2))).
  apply: eq_Rintegral => x _.
  have -> : expR (- (x : R) ^+ 2 / 2) = cf_re N x by rewrite cf_re_normal01.
  rewrite /cf_re (@Rintegral_normal01 (fun u => cos (x * u)) 1).
  - exact: (measurable_cos_mul x (@measurable_id _ R setT)).
  - by move=> u; exact: cos_max.
  rewrite -RintegralZl//.
    apply: (le_integrable measurableT _ _ (integrable_normal_pdf 0 1)).
      apply/measurable_EFinP; apply: measurable_funM.
        exact: (measurable_cos_mul x (@measurable_id _ R setT)).
      exact: measurable_normal_pdf.
    move=> u _; rewrite /comp !abse_EFin lee_fin normrM.
    by have := cos_max (x * u); have := normr_ge0 (normal_pdf 0 1 u); nra.
  apply: eq_Rintegral => u _; rewrite /F normal_pdf01E /=.
  by rewrite [in RHS]mulrCA mulKf ?gt_eqF// [(u : R) * _]mulrC.
apply: RintegralZl => //.
apply: (bounded_integrable nu (C := 1)).
  exact: measurableT_comp (@measurable_gauss_weight R) (@measurable_idR R).
move=> x; rewrite ger0_norm ?expR_ge0// -expR0 ler_expR.
by rewrite mulNr oppr_le0 divr_ge0// sqr_ge0.
Qed.

End gauss_fubini.

(* The symmetrized law, and sums of independent copies of it. *)
Section sym_sum_facts.
Context {R : realType}.
Implicit Types mu : probability (measurableTypeR R) R.

Lemma cf_sym_law mu t : cf (sym_law mu) t = (cf_norm mu t ^+ 2, 0).
Proof. by apply: cf_sym => A mA; exact: sym_lawE. Qed.

Lemma conc_fun_sym_law mu (L : R) : conc_fun (sym_law mu) L <= conc_fun mu L.
Proof.
have n1 : (-1 : R) != 0 by rewrite oppr_eq0 oner_neq0.
have := @conc_fun_add R _ (measurableTypeR R) mu (fun x => x : R) mu
  (sym_law mu) (-1) L (@measurable_idR R) n1.
rewrite normrN normr1 mul1r; apply => A mA; rewrite -sym_lawE//.
by congr ((mu \x mu)%E (_ @^-1` A)); apply/funext => p; rewrite mulN1r.
Qed.

(* E[(X - X')^2] <= 4 E[X^2]. *)
Lemma sym_law_second_moment mu (v : R) :
  (\int[mu]_x (((x : R) ^+ 2)%R)%:E <= v%:E)%E ->
  (\int[sym_law mu]_x (((x : R) ^+ 2)%R)%:E <= (4 * v)%:E)%E.
Proof.
move=> mu2.
have m2 : measurable_fun [set: measurableTypeR R]
    (fun y : measurableTypeR R => (((y : R) ^+ 2)%R)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_idR.
have h0 (y : measurableTypeR R) : (0 <= (((y : R) ^+ 2)%R)%:E)%E.
  by rewrite lee_fin sqr_ge0.
rewrite (@ge0_integral_distribution _ _ _ _ _ (mu \x mu)%E sym_diff _ m2 h0).
exact: (sym_second_moment mu2).
Qed.

(* E[(X - X')^2] <= 4 E[(X - a)^2] for every a. *)
Lemma sym_law_second_moment_center mu (a v : R) :
  (\int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E <= v%:E)%E ->
  (\int[sym_law mu]_x (((x : R) ^+ 2)%R)%:E <= (4 * v)%:E)%E.
Proof.
move=> mu2.
have m2 : measurable_fun [set: measurableTypeR R]
    (fun y : measurableTypeR R => (((y : R) ^+ 2)%R)%:E).
  by apply/measurable_EFinP; apply: measurable_funX; exact: measurable_idR.
have h0 (y : measurableTypeR R) : (0 <= (((y : R) ^+ 2)%R)%:E)%E.
  by rewrite lee_fin sqr_ge0.
rewrite (@ge0_integral_distribution _ _ _ _ _ (mu \x mu)%E sym_diff _ m2 h0).
exact: (sym_second_moment_center mu2).
Qed.

(* A complex product of real numbers is real. *)
Lemma cmul_real_big (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  \big[cmul/(1, 0)]_(i <- r | P i) (F i, 0) = (\prod_(i <- r | P i) F i, 0).
Proof.
apply: (big_ind2 (fun (z : R * R) (x : R) => z = (x, 0))) => //.
by move=> y1 y z1 z -> ->; rewrite cmulE !mul0r !mulr0 subr0 addr0.
Qed.

(* The sum of n independent copies of X - X' has the characteristic
   function |cf mu t|^(2 n). *)
Lemma cf_re_sum_sym mu n t :
  cf_re (sum_law (fun=> sym_law mu) n) t = cf_norm mu t ^+ (2 * n).
Proof.
have numu (A : set (measurableTypeR R)) : measurable A ->
    tuple_prod (fun=> sym_law mu) n
      ((fun x => \sum_(k < n) (fun=> 1) k * tnth x k) @^-1` A) =
    sum_law (fun=> sym_law mu) n A.
  move=> mA; rewrite -sum_lawE//; congr (tuple_prod _ n (_ @^-1` A)).
  by apply/funext => x; apply: eq_bigr => k _; rewrite mul1r.
have := @cf_tuple_prod R (fun=> sym_law mu) n (fun=> 1)
  (sum_law (fun=> sym_law mu) n) numu t.
under eq_bigr do rewrite mul1r cf_sym_law.
rewrite (cmul_real_big _ _ (fun=> cf_norm mu t ^+ 2)) prodr_const card_ord.
case=> ->.
by rewrite exprM.
Qed.

End sym_sum_facts.

Section gauss_factor_bound.
Context {R : realType}.
Local Notation leb := (@lebesgue_measure R).

Definition gauss_factor_const (v lambda eps : R) : R :=
  16 * pi ^+ 3 * Num.sqrt pi * expR 8^-1 * (1 + Num.sqrt (4 * v / eps)) /
  (lambda * Num.sqrt eps).

Lemma gauss_factor_const_gt0 (v lambda eps : R) :
  0 < v -> 0 < lambda -> 0 < eps -> 0 < gauss_factor_const v lambda eps.
Proof.
move=> v0 l0 e0; have pi0 : 0 < pi :> R := pi_gt0 R.
have A0 : 0 < 1 + Num.sqrt (4 * v / eps) by rewrite ltr_pwDl ?sqrtr_ge0.
apply: divr_gt0; last by rewrite mulr_gt0// sqrtr_gt0.
by rewrite !mulr_gt0// ?exprn_gt0// ?sqrtr_gt0// expR_gt0.
Qed.

Let measurable_integrand (mu : probability (measurableTypeR R) R) (p a b : R) :
  measurable_fun [set: R]
    (fun u => cf_norm mu u `^ p * expR (- a * u ^+ 2 / b)).
Proof.
apply: measurable_funM.
  apply: measurableT_comp (@measurable_powR R _) _.
  exact: continuous_measurable_fun (@continuous_cf_norm R mu).
apply: measurableT_comp (@measurable_expR R) _.
apply: measurable_funM => //.
by apply: measurable_funM => //; exact: measurable_funX.
Qed.

(* Lemma 3.5 of Koehler and Sohn: for a law mu on the line with
   E[(X - a)^2] <= v for some a and Q(mu, lambda) <= 1 - eps, and for
   0 < r <= 1/2 and r <= s, \int |cf mu u|^(1/r^2) exp (- s^2 u^2 / (2 r^2)) du
   <= r C, with C depending only on v, lambda and eps. *)
Theorem gauss_factor_center_le (mu : probability (measurableTypeR R) R)
    (a v lambda eps r s : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  (\int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E <= v%:E)%E ->
  conc_fun mu lambda <= 1 - eps ->
  0 < r -> r <= 2^-1 -> r <= s ->
  (\int[leb]_u (cf_norm mu u `^ (r ^- 2) *
     expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <=
   (r * gauss_factor_const v lambda eps)%:E)%E.
Proof.
move=> v0 l0 e0 mu2 Q r0 r12 rs.
have pi0 : 0 < pi :> R := pi_gt0 R.
have rn0 : r != 0 by rewrite gt_eqF.
pose x := (2 * r ^+ 2)^-1.
have x2 : 2 <= x.
  rewrite /x -[(2 * r ^+ 2)^-1]mul1r ler_pdivlMr.
    by rewrite mulr_gt0// exprn_gt0.
  have : r ^+ 2 <= 4^-1 by rewrite expr2; nra.
  lra.
pose N := Num.truncn x.
have /andP[Nx xN] : N%:R <= x < N.+1%:R by apply: truncn_itv; lra.
have N0 : (0 < N)%N by rewrite truncn_gt0; lra.
have xE : r ^- 2 = 2 * x by rewrite /x; field.
have N2 : (2 * N)%:R <= r ^- 2 by rewrite natrM xE ler_pM2l.
have N4 : (4 * r ^+ 2)^-1 <= N%:R.
  have -> : (4 * r ^+ 2)^-1 = x / 2 by rewrite /x; field.
  by move: xN; rewrite mulrSr; lra.
(* the sum of N independent copies of the symmetrized law *)
pose S := sum_law (fun=> sym_law mu) N.
have QS : conc_fun S 1 <= 2 * pi ^+ 2 * Num.sqrt pi *
    (1 + Num.sqrt (4 * v / eps)) / (lambda * Num.sqrt (eps * N%:R)).
  apply: (@conc_fun_sum R (fun=> sym_law mu) N S (4 * v) lambda eps 1) => //.
  - by rewrite mulr_gt0.
  - by move=> k _; exact: (sym_law_second_moment_center mu2).
  - by move=> k _; exact: le_trans (conc_fun_sym_law mu lambda) Q.
have ES := gauss_weight_conc_fun S.
have FS := Rintegral_cf_re_gauss_weight S.
have cfS u : cf_re S u = cf_norm mu u ^+ (2 * N) := cf_re_sum_sym mu N u.
have p0 : r ^- 2 != 0 by rewrite invr_eq0 sqrf_eq0.
have pw u : cf_norm mu u `^ (r ^- 2) * expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2))
    <= cf_re S u * expR (- u ^+ 2 / 2).
  rewrite cfS; apply: ler_pM.
  - exact: powR_ge0.
  - exact: expR_ge0.
  - have [c0|c0] := eqVneq (cf_norm mu u) 0.
      by rewrite c0 (powR0 p0) exprn_ge0.
    have cpos : 0 < cf_norm mu u by rewrite lt0r c0 cf_norm_ge0.
    have c1 : 0 < cf_norm mu u <= 1 by rewrite cpos cf_norm_le1.
    rewrite -(@powR_mulrn _ (cf_norm mu u)) ?cf_norm_ge0//.
    exact: (ger_powR c1 N2).
  - rewrite ler_expR !mulNr lerN2.
    have -> : s ^+ 2 * u ^+ 2 / (2 * r ^+ 2) = u ^+ 2 / 2 * (s / r) ^+ 2.
      by field.
    apply: ler_peMr; first by rewrite divr_ge0// sqr_ge0.
    by apply: exprn_ege1; rewrite ler_pdivlMr// mul1r.
have cfS0 u : 0 <= cf_re S u by rewrite cfS exprn_ge0// cf_norm_ge0.
have cfS1 u : cf_re S u <= 1.
  by rewrite cfS exprn_ile1// ?cf_norm_ge0// cf_norm_le1.
have mf := measurable_integrand mu (r ^- 2) (s ^+ 2) (2 * r ^+ 2).
have mg : measurable_fun [set: R] (fun u => cf_re S u * expR (- u ^+ 2 / 2)).
  apply: measurable_funM.
    exact: continuous_measurable_fun (@continuous_cf_re R S).
  exact: measurable_gauss_weight.
have gS u : cf_re S u * expR (- u ^+ 2 / 2) <= expR (- u ^+ 2 / 2).
  by rewrite ler_piMl ?expR_ge0.
have ig := @integrable_gauss_weight R.
have iR : leb.-integrable [set: R]
    (EFin \o (fun u => cf_re S u * expR (- u ^+ 2 / 2))).
  apply: (le_integrable measurableT _ _ ig).
    exact/measurable_EFinP.
  move=> u _; rewrite /comp !abse_EFin lee_fin ger0_norm ?mulr_ge0 ?expR_ge0//.
  by rewrite ger0_norm ?expR_ge0.
have iL : leb.-integrable [set: R]
    (EFin \o (fun u => cf_norm mu u `^ (r ^- 2) *
       expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))).
  apply: (le_integrable measurableT _ _ ig).
    exact/measurable_EFinP.
  move=> u _; rewrite /comp !abse_EFin lee_fin.
  rewrite ger0_norm ?mulr_ge0 ?powR_ge0 ?expR_ge0// ger0_norm ?expR_ge0//.
  exact: le_trans (pw u) (gS u).
have I1 : \int[leb]_u (cf_norm mu u `^ (r ^- 2) *
    expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2))) <=
    Num.sqrt (2 * pi) * \int[S]_y expR (- (y : R) ^+ 2 / 2).
  by rewrite -FS; apply: le_Rintegral => //; move=> u _; exact: pw.
have main : r^-1 * \int[leb]_u (cf_norm mu u `^ (r ^- 2) *
    expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2))) <=
    gauss_factor_const v lambda eps.
  have ri0 : 0 <= r^-1 by rewrite invr_ge0 ltW.
  have pi1 : 0 <= Num.sqrt (2 * pi : R) by exact: sqrtr_ge0.
  have c2 : 0 <= 2 * expR 8^-1 * Num.sqrt (2 * pi : R).
    by rewrite mulr_ge0 ?mulr_ge0 ?expR_ge0 ?sqrtr_ge0.
  apply: le_trans (ler_wpM2l ri0 I1) _.
  apply: le_trans (ler_wpM2l ri0 (ler_wpM2l pi1
    (le_trans ES (ler_wpM2l c2 QS)))) _.
  set A := 1 + Num.sqrt (4 * v / eps).
  have A0 : 0 < A by rewrite /A ltr_pwDl ?sqrtr_ge0.
  pose w : R := Num.sqrt N%:R.
  have w0 : 0 < w by rewrite sqrtr_gt0 ltr0n.
  (* 1 / sqrt N <= 2 r *)
  have r2 : r^-1 / w <= 2.
    have r4 : 0 <= 4 * r ^+ 2 by rewrite mulr_ge0// sqr_ge0.
    have e2 : Num.sqrt ((4 * r ^+ 2)^-1) = (2 * r)^-1.
      have -> : 4 * r ^+ 2 = (2 * r) ^+ 2 by ring.
      by rewrite sqrtrV ?sqr_ge0// sqrtr_sqr ger0_norm// mulr_ge0// ltW.
    have h : (2 * r)^-1 <= w by rewrite -e2 /w ler_sqrt// ler0n.
    rewrite ler_pdivrMr//.
    have -> : r^-1 = 2 * (2 * r)^-1 by field.
    by rewrite ler_pM2l.
  have pk : Num.sqrt (2 * pi) * Num.sqrt (2 * pi) = 2 * pi :> R.
    by rewrite -expr2 sqr_sqrtr// mulr_ge0// ltW.
  have sn0 : Num.sqrt eps != 0 by rewrite gt_eqF// sqrtr_gt0.
  have ln0 : lambda != 0 by rewrite gt_eqF.
  have wn0 : w != 0 by rewrite gt_eqF.
  rewrite [Num.sqrt (eps * _)]sqrtrM; first exact: ltW.
  rewrite -/w.
  have -> : r^-1 * (Num.sqrt (2 * pi) * (2 * expR 8^-1 * Num.sqrt (2 * pi) *
      (2 * pi ^+ 2 * Num.sqrt pi * A / (lambda * (Num.sqrt eps * w))))) =
      (4 * expR 8^-1 * pi ^+ 2 * Num.sqrt pi * A / (lambda * Num.sqrt eps)) *
      (Num.sqrt (2 * pi) * Num.sqrt (2 * pi)) * (r^-1 / w).
    by move: (Num.sqrt (2 * pi)) => sq; move: (Num.sqrt pi) => sp;
      move: (pi) => p; field.
  rewrite pk.
  have -> : gauss_factor_const v lambda eps =
      (4 * expR 8^-1 * pi ^+ 2 * Num.sqrt pi * A / (lambda * Num.sqrt eps)) *
      (2 * pi) * 2.
    by rewrite /gauss_factor_const -/A; move: (Num.sqrt pi) => sp;
      move: (pi) => p; field.
  apply: ler_wpM2l => //.
  by rewrite !mulr_ge0 ?expR_ge0 ?sqrtr_ge0 ?invr_ge0 ?mulr_ge0 ?sqrtr_ge0//
    ?ltW// exprn_ge0// ltW.
have fin : (\int[leb]_u (cf_norm mu u `^ (r ^- 2) *
    expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E)%E \is a fin_num.
  exact: integrable_fin_num iL.
by rewrite -(fineK fin) lee_fin -ler_pdivrMl.
Qed.

(* The case a = 0: E[X^2] <= v. *)
Theorem gauss_factor_le (mu : probability (measurableTypeR R) R)
    (v lambda eps r s : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  (\int[mu]_x (((x : R) ^+ 2)%R)%:E <= v%:E)%E ->
  conc_fun mu lambda <= 1 - eps ->
  0 < r -> r <= 2^-1 -> r <= s ->
  (\int[leb]_u (cf_norm mu u `^ (r ^- 2) *
     expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <=
   (r * gauss_factor_const v lambda eps)%:E)%E.
Proof.
move=> v0 l0 e0 mu2 Q r0 r12 rs.
apply: (@gauss_factor_center_le mu 0 v lambda eps r s) => //.
by under eq_integral do rewrite subr0.
Qed.

(* The same bound after the substitution u = r t:
   \int |cf mu (r t)|^(1/r^2) exp (- s^2 t^2 / 2) dt <= C. *)
Corollary gauss_factor_scaled_le (mu : probability (measurableTypeR R) R)
    (v lambda eps r s : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  (\int[mu]_x (((x : R) ^+ 2)%R)%:E <= v%:E)%E ->
  conc_fun mu lambda <= 1 - eps ->
  0 < r -> r <= 2^-1 -> r <= s ->
  (\int[leb]_t (cf_norm mu (r * t) `^ (r ^- 2) *
     expR (- s ^+ 2 * t ^+ 2 / 2))%:E <=
   (gauss_factor_const v lambda eps)%:E)%E.
Proof.
move=> v0 l0 e0 mu2 Q r0 r12 rs.
have rn0 : r != 0 by rewrite gt_eqF.
pose f u := cf_norm mu u `^ (r ^- 2) * expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)).
have mEf : measurable_fun [set: R] (EFin \o f).
  by apply/measurable_EFinP; exact: measurable_integrand.
have f0 u : (0 <= (EFin \o f) u)%E.
  by rewrite lee_fin mulr_ge0 ?powR_ge0 ?expR_ge0.
have := @ge0_integral_lebesgue_affine R r 0 (EFin \o f) rn0 mEf f0.
rewrite gtr0_norm// => E.
have -> : (\int[leb]_t (cf_norm mu (r * t) `^ (r ^- 2) *
    expR (- s ^+ 2 * t ^+ 2 / 2))%:E =
    \int[leb]_t (EFin \o f) (r * t + 0)%R)%E.
  apply: eq_integral => t _; rewrite /= addr0 /f.
  by congr (_ * expR _)%:E; field.
rewrite E; apply: le_trans (lee_wpmul2l _
  (gauss_factor_le v0 l0 e0 mu2 Q r0 r12 rs)) _.
  by rewrite lee_fin invr_ge0 ltW.
by rewrite -EFinM mulrA mulVf// mul1r.
Qed.

(* The form with a constant uniform in the law. *)
Corollary gauss_factor_exists (v lambda eps : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  exists2 C : R, 0 < C &
  forall (mu : probability (measurableTypeR R) R) (r s : R),
    (\int[mu]_x (((x : R) ^+ 2)%R)%:E <= v%:E)%E ->
    conc_fun mu lambda <= 1 - eps ->
    0 < r <= s -> s <= 2^-1 ->
    (\int[leb]_u (cf_norm mu u `^ (r ^- 2) *
       expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <= (r * C)%:E)%E.
Proof.
move=> v0 l0 e0; exists (gauss_factor_const v lambda eps).
  exact: gauss_factor_const_gt0.
move=> mu r s mu2 Q /andP[r0 rs] s12.
exact: (gauss_factor_le v0 l0 e0 mu2 Q r0 (le_trans rs s12) rs).
Qed.

(* The same with a centered second moment, E[(X - a)^2] <= v for some a: the
   variance when a is the mean. *)
Corollary gauss_factor_center_exists (v lambda eps : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  exists2 C : R, 0 < C &
  forall (mu : probability (measurableTypeR R) R) (a r s : R),
    (\int[mu]_x ((((x : R) - a) ^+ 2)%R)%:E <= v%:E)%E ->
    conc_fun mu lambda <= 1 - eps ->
    0 < r <= s -> s <= 2^-1 ->
    (\int[leb]_u (cf_norm mu u `^ (r ^- 2) *
       expR (- s ^+ 2 * u ^+ 2 / (2 * r ^+ 2)))%:E <= (r * C)%:E)%E.
Proof.
move=> v0 l0 e0; exists (gauss_factor_const v lambda eps).
  exact: gauss_factor_const_gt0.
move=> mu a r s mu2 Q /andP[r0 rs] s12.
exact: (gauss_factor_center_le v0 l0 e0 mu2 Q r0 (le_trans rs s12) rs).
Qed.

End gauss_factor_bound.

(* The first half of Lemma 3.5 with a constant uniform in the law. *)
Corollary conc_fun_truncated_exists {R : realType} (M : R) : 0 < M ->
  exists2 c : R, 0 < c &
  forall mu : probability (measurableTypeR R) R,
    (\int[mu]_x (x : R)%:E = 0)%E ->
    (\int[mu]_x (((x : R) ^+ 2)%R)%:E = 1)%E ->
    ((2^-1)%:E <=
      \int[mu]_x (((x : R) ^+ 2 * \1_[set y : R | `|y| <= M] x)%R)%:E)%E ->
    conc_fun mu 8^-1 <= 1 - c.
Proof.
move=> M0; exists (minr (7 / (16 * M ^+ 2)) 100^-1).
  have c0 : 0 < 7 / (16 * M ^+ 2) by rewrite divr_gt0// mulr_gt0// exprn_gt0.
  by rewrite lt_min c0 invr_gt0 ltr0n.
by move=> mu m0 v1 t; exact: conc_fun_truncated.
Qed.

(* The same for any truncation level c, on intervals of any length L with
   4 L^2 < c (for instance L = sqrt c / 4). *)
Corollary conc_fun_truncated_level_exists {R : realType} (M c L : R) :
  0 < M -> 0 < L -> 4 * L ^+ 2 < c ->
  exists2 k : R, 0 < k &
  forall mu : probability (measurableTypeR R) R,
    (\int[mu]_x (x : R)%:E = 0)%E ->
    (\int[mu]_x (((x : R) ^+ 2)%R)%:E = 1)%E ->
    (c%:E <=
      \int[mu]_x (((x : R) ^+ 2 * \1_[set y : R | `|y| <= M] x)%R)%:E)%E ->
    conc_fun mu L <= 1 - k.
Proof.
move=> M0 L0 Lc.
exists (minr ((c - 4 * L ^+ 2) / M ^+ 2) (L ^+ 2 / (2 * L ^+ 2 + 1))).
  have k1 : 0 < (c - 4 * L ^+ 2) / M ^+ 2.
    by rewrite divr_gt0 ?subr_gt0// exprn_gt0.
  have d0 : 0 < 2 * L ^+ 2 + 1 by have := sqr_ge0 L; lra.
  have k2 : 0 < L ^+ 2 / (2 * L ^+ 2 + 1) by rewrite divr_gt0// exprn_gt0.
  by rewrite lt_min k1 k2.
by move=> mu m0 v1 t; exact: (conc_fun_truncated_level M0 m0 v1 t L0).
Qed.
