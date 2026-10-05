(* Bounded-row concentration under the Gaussian product law.

   For F continuous and bounded on N rows of p standard Gaussian
   coordinates, with every whole-row change at most c:
   1. the mean of F under gaussian_product_law (N p) is the iterated
      expectation, and the exponential moment bound of
      PaperMainLossConcentrationRow holds for the product-law integral;
   2. the measurable lower tail: for c, t > 0 and N >= 1,
      P (F <= E F - t) <= exp (- t^2 / (2 N c^2)),
      from the indicator bound 1 <= exp (lambda (E F - F) - lambda t) on the
      event and lambda = t / (N c^2); the upper tail is the same argument
      for - F. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinateWeightDefinitions
  GaussianCoordinateMarginals GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure GaussianProbabilityProductIntegrals
  GaussianProbabilityProductContinuity PaperMainHeadSectionMeasurable
  PaperMainLossConcentrationRow.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. Product-law forms. *)

Lemma paper_main_concentration_mean_law d (F : list R -> R) (C : R) :
  finite_joint_continuous d F ->
  (forall xs, length xs = d -> (Rabs (F xs) <= C)%Rcoq) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> HF HB.
apply: gpp_all_sections.
- apply/measurable_EFinP; exact: gpp_joint_measurable.
- exact: (paper_main_concentration_integrable d F C HF HB).
- apply: (gaussian_iterated_polynomial_absolutely_integrable d F C 0 HF).
  exact: paper_main_concentration_poly0.
Qed.

Theorem paper_main_concentration_rows_law N p (F : list R -> R) (C c lam : R) :
  (0 <= c)%Rcoq -> finite_joint_continuous (N * p) F ->
  (forall xs, length xs = (N * p)%nat -> (Rabs (F xs) <= C)%Rcoq) ->
  paper_main_row_oscillation N p c F ->
  (\int[gaussian_product_law (N * p)]_x
     ((exp (lam * (F (tval x) - gaussian_iterated_expectation (N * p) F)))%Rcoq)%:E <=
   ((exp (lam ^ 2 * INR N * c ^ 2 / 2))%Rcoq)%:E)%E.
Proof.
move=> Hc HF HB Hosc.
set m := gaussian_iterated_expectation (N * p) F.
have HGc : finite_joint_continuous (N * p) (fun xs => exp (lam * (F xs - m))).
  exact: (paper_main_concentration_comp _ F _ (paper_main_concentration_exp_continuous lam m) HF).
have HGb : forall xs, length xs = (N * p)%nat ->
    (Rabs (exp (lam * (F xs - m))) <= exp (Rabs lam * (C + Rabs m)))%Rcoq.
  move=> xs Hxs; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := Rle_abs (lam * (F xs - m)); rewrite Rabs_mult in H1.
  have H2 := HB xs Hxs; have H3 := Rabs_pos lam.
  have H4 : (Rabs (F xs - m) <= C + Rabs m)%Rcoq.
    have := Rabs_triang (F xs) (- m); rewrite Rabs_Ropp /Rminus; lra.
  apply: Rle_trans H1 _; by apply: Rmult_le_compat_l.
rewrite (gpp_nonnegative (N * p) (fun xs => exp (lam * (F xs - m)))).
- apply/measurable_EFinP; exact: (gpp_joint_measurable (N * p) _ HGc).
- by move=> xs; apply/RleP; apply: Rlt_le; apply: exp_pos.
- exact: (paper_main_concentration_integrable _ _ _ HGc HGb).
- rewrite lee_fin; apply/RleP.
  exact: (paper_main_concentration_rows N p F C c lam Hc HF HB Hosc).
Qed.

(* 2. The measurable lower tail. *)

Theorem paper_main_concentration_lower_tail N p (F : list R -> R) (C c t : R) :
  (0 < N)%N -> (0 < c)%Rcoq -> (0 < t)%Rcoq ->
  finite_joint_continuous (N * p) F ->
  (forall xs, length xs = (N * p)%nat -> (Rabs (F xs) <= C)%Rcoq) ->
  paper_main_row_oscillation N p c F ->
  measurable [set x : (N * p).-tuple (measurableTypeR R) |
    (F (tval x) <= gaussian_iterated_expectation (N * p) F - t)%R] /\
  (gaussian_product_law (N * p)
     [set x | (F (tval x) <= gaussian_iterated_expectation (N * p) F - t)%R] <=
   ((exp (- (t ^ 2) / (2 * INR N * c ^ 2)))%Rcoq)%:E)%E.
Proof.
move=> HN Hc Ht HF HB Hosc.
set m := gaussian_iterated_expectation (N * p) F.
have mF : measurable_fun [set: (N * p).-tuple (measurableTypeR R)]
    ((fun x => F (tval x)) : _ -> measurableTypeR R).
  exact: gpp_joint_measurable.
have mE : measurable [set x : (N * p).-tuple (measurableTypeR R) | (F (tval x) <= m - t)%R].
  by apply: paper_main_head_section_le_measurable => //; exact: measurable_cst.
split => //.
have HNR : (0 < INR N)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
set lam := (t / (INR N * c ^ 2))%Rcoq.
have Hc2 : (0 < c ^ 2)%Rcoq by apply: pow_lt.
have Hlam : (0 < lam)%Rcoq by apply: Rdiv_lt_0_compat => //; apply: Rmult_lt_0_compat.
set G := fun xs => exp (lam * (m - F xs) - lam * t).
have HGc : finite_joint_continuous (N * p) G.
  apply: (paper_main_concentration_comp _ F (fun y => exp (lam * (m - y) - lam * t))) => //.
  by move=> y; reg.
have HGb : forall xs, length xs = (N * p)%nat ->
    (Rabs (G xs) <= exp (lam * (Rabs m + C)))%Rcoq.
  move=> xs Hxs; rewrite /G Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := HB xs Hxs.
  have H2 := Rle_abs m; have H3 := Rle_abs (- F xs); rewrite Rabs_Ropp in H3.
  have : (lam * (m - F xs) <= lam * (Rabs m + C))%Rcoq.
    by apply: Rmult_le_compat_l; lra.
  have : (0 <= lam * t)%Rcoq by apply: Rmult_le_pos; lra.
  lra.
have HGi := paper_main_concentration_integrable _ _ _ HGc HGb.
have Hint : (\int[gaussian_product_law (N * p)]_x (G (tval x))%:E =
    (gaussian_iterated_expectation (N * p) G)%:E)%E.
  apply: gpp_nonnegative.
  - apply/measurable_EFinP; exact: (gpp_joint_measurable (N * p) _ HGc).
  - by move=> xs; apply/RleP; apply: Rlt_le; apply: exp_pos.
  - exact: HGi.
have HP : (gaussian_product_law (N * p) [set x | (F (tval x) <= m - t)%R] <=
    \int[gaussian_product_law (N * p)]_x (G (tval x))%:E)%E.
  rewrite -(setIT [set x : (N * p).-tuple (measurableTypeR R) | (F (tval x) <= m - t)%R]).
  rewrite -integral_indic //.
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin /numfun.indic; case: (_ \in _).
  - apply/measurable_EFinP; exact: measurable_indic.
  - apply/measurable_EFinP; exact: (gpp_joint_measurable (N * p) _ HGc).
  - move=> x _; rewrite lee_fin /numfun.indic.
    case: (boolP (x \in _)) => Hx /=.
      rewrite in_setE /= in Hx.
      move/RleP: Hx => Hx.
      rewrite -RminusE in Hx.
      have H1 : (exp 0 <= G (tval x))%Rcoq.
        apply: paper_main_concentration_exp_le.
        have key : forall y : R, (y <= m - t)%Rcoq -> (0 <= lam * (m - y) - lam * t)%Rcoq.
          move=> y Hy.
          have := Rmult_le_compat_l lam t (m - y) (Rlt_le _ _ Hlam) ltac:(lra).
          lra.
        exact: key _ Hx.
      by rewrite exp_0 in H1; apply/RleP.
    by apply/RleP; apply: Rlt_le; apply: exp_pos.
apply: le_trans HP _.
rewrite Hint lee_fin; apply/RleP.
have Hrows := paper_main_concentration_rows N p F C c (- lam) (Rlt_le _ _ Hc) HF HB Hosc.
rewrite -/m in Hrows.
have HEc : finite_joint_continuous (N * p) (fun xs => exp ((- lam) * (F xs - m))).
  exact: (paper_main_concentration_comp _ F _ (paper_main_concentration_exp_continuous (- lam) m) HF).
have HEb : forall xs, length xs = (N * p)%nat ->
    (Rabs (exp ((- lam) * (F xs - m))) <= exp (Rabs (- lam) * (C + Rabs m)))%Rcoq.
  move=> xs Hxs; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := Rle_abs ((- lam) * (F xs - m)); rewrite Rabs_mult in H1.
  have H2 := HB xs Hxs; have H3 := Rabs_pos (- lam).
  have H4 : (Rabs (F xs - m) <= C + Rabs m)%Rcoq.
    have := Rabs_triang (F xs) (- m); rewrite Rabs_Ropp /Rminus; lra.
  apply: Rle_trans H1 _; by apply: Rmult_le_compat_l.
have HEi := paper_main_concentration_integrable _ _ _ HEc HEb.
rewrite (gaussian_iterated_expectation_ext _ G
  (fun xs => (exp (- (lam * t)) * exp ((- lam) * (F xs - m)))%Rcoq)).
  by move=> xs _; rewrite /G -exp_plus; congr exp; ring.
rewrite (proj2 (gaussian_iterated_scale _ _ _ HEi)).
apply: Rle_trans (Rmult_le_compat_l _ _ _ (Rlt_le _ _ (exp_pos _)) Hrows) _.
rewrite -exp_plus; apply: paper_main_concentration_exp_le.
right; rewrite /lam; field; split; lra.
Qed.

(* The upper tail, from the lower tail of - F. *)

Corollary paper_main_concentration_upper_tail N p (F : list R -> R) (C c t : R) :
  (0 < N)%N -> (0 < c)%Rcoq -> (0 < t)%Rcoq ->
  finite_joint_continuous (N * p) F ->
  (forall xs, length xs = (N * p)%nat -> (Rabs (F xs) <= C)%Rcoq) ->
  paper_main_row_oscillation N p c F ->
  measurable [set x : (N * p).-tuple (measurableTypeR R) |
    (gaussian_iterated_expectation (N * p) F + t <= F (tval x))%R] /\
  (gaussian_product_law (N * p)
     [set x | (gaussian_iterated_expectation (N * p) F + t <= F (tval x))%R] <=
   ((exp (- (t ^ 2) / (2 * INR N * c ^ 2)))%Rcoq)%:E)%E.
Proof.
move=> HN Hc Ht HF HB Hosc.
set G := fun xs => (- F xs)%Rcoq.
have HGc : finite_joint_continuous (N * p) G.
  apply: (paper_main_concentration_comp _ F (fun y => (- y)%Rcoq)) => //.
  by move=> y; reg.
have HGb : forall xs, length xs = (N * p)%nat -> (Rabs (G xs) <= C)%Rcoq.
  by move=> xs Hxs; rewrite /G Rabs_Ropp; exact: HB.
have HGo : paper_main_row_oscillation N p c G.
  move=> k a z z' b Hk Ha Hz Hz' Hb; rewrite /G.
  have -> : (- F (a ++ z ++ b) - - F (a ++ z' ++ b) =
      - (F (a ++ z ++ b) - F (a ++ z' ++ b)))%Rcoq by ring.
  by rewrite Rabs_Ropp; exact: (Hosc k a z z' b Hk Ha Hz Hz' Hb).
have HFi := paper_main_concentration_integrable _ F C HF HB.
have HEG : gaussian_iterated_expectation (N * p) G =
    (- gaussian_iterated_expectation (N * p) F)%Rcoq.
  rewrite (gaussian_iterated_expectation_ext _ G (fun xs => (-1 * F xs)%Rcoq)).
    by move=> xs _; rewrite /G; ring.
  by rewrite (proj2 (gaussian_iterated_scale _ _ (-1) HFi)); ring.
have [mE PE] := paper_main_concentration_lower_tail N p G C c t HN Hc Ht HGc HGb HGo.
rewrite HEG in mE PE.
have Hset : [set x : (N * p).-tuple (measurableTypeR R) |
    (G (tval x) <= - gaussian_iterated_expectation (N * p) F - t)%R] =
  [set x | (gaussian_iterated_expectation (N * p) F + t <= F (tval x))%R].
  apply/seteqP; split => x /= /RleP H; apply/RleP; rewrite /G in H *;
    move: H; rewrite -?RminusE -?RplusE -?RoppE; lra.
rewrite Hset in mE PE.
by split.
Qed.
