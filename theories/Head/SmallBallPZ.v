(* The small-ball probability of the translated quadratic form under the
   actual Gaussian law. For a real symmetric H of size r and real b let
     Y(x) = x^T H x - Tr H - b,   sigma2 = 2 |H|_F^2 + b^2,
   with x distributed by gaussian_product_law r (MathComp Lebesgue integrals).
   - Joint measurability: on any measurable space, for measurable maps
     x |-> g x (an r-tuple), entrywise measurable x |-> H x and measurable
     x |-> b x, the value Y and the event {t x <= Y^2} are measurable.
   - Law: Y^2 and Y^4 are integrable, E Y^2 = sigma2 and E Y^4 <= 19 sigma2^2
     (from Head.SmallBallFourth through the orthogonal law transport
     of the rotated smooth test).
   - Paley-Zygmund for any probability measure: if Z is measurable,
     E Z = m, E Z^2 = M and 0 <= theta < m, then M > 0 and
     P(theta <= Z) >= (m - theta)^2 / M
     (paper_main_head_small_ball_paley_zygmund,
     from paley_zygmund of GaussianAnalysis.probability.moments).
   - Hence P(sigma2 / 2 <= Y^2) >= 1 / 76 = 1 / (4 * 19). For sigma2 = 0
     (H = 0, b = 0) the event is everything; r = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability numfun hoelder.
From GaussianAnalysis.probability Require Import moments.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gaussian.CovarianceDefinitions PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Gaussian.WeightedSquare Gaussian.SmoothCovariance
  Gaussian.Orthogonal Gaussian.OrthogonalLaw Spectral.DiagonalizationLists
  Gaussian.QuadraticTail Measurability.Coordinates Head.SectionMeasurable
  Head.SmallBall Head.SmallBallFourth.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* Paley-Zygmund, from the library (paley_zygmund of moments.v). *)

Theorem paper_main_head_small_ball_paley_zygmund {dX : measure_display}
    {X : measurableType dX} (P : probability X R) (Z : X -> R) (m M theta : R) :
  measurable_fun [set: X] (Z : X -> T) ->
  P.-integrable [set: X] (fun x => (Z x)%:E) -> (\int[P]_x (Z x)%:E = m%:E)%E ->
  P.-integrable [set: X] (fun x => (Z x ^ 2)%:E) -> (\int[P]_x (Z x ^ 2)%:E = M%:E)%E ->
  0 <= theta -> theta < m ->
  0 < M /\ ((((m - theta) ^ 2 / M)%Rcoq)%:E <= P [set x | Rle theta (Z x)])%E.
Proof.
move=> mZ _ HE1 HI2 HE2 Hth Hm.
have Hm' : (theta < m)%R by apply/RltP.
have Hth' : (0 <= theta)%R by apply/RleP.
have sqrE : (fun x => (Z x ^ 2)%:E) = EFin \o (fun x => (Z x ^+ 2)%R).
  by apply/funext => x; rewrite RpowE.
have Z2 : Z \in Lfun P 2%:E by apply: integrable_sqr_Lfun2 => //; rewrite -sqrE.
have Em : ('E_P[Z] = m%:E)%E by rewrite unlock.
have EM : ('E_P[(Z ^+ 2)%R] = M%:E)%E.
  by rewrite unlock -HE2; apply: eq_integral => x _; rewrite RpowE expr2.
split.
  have := expectation_sqr_le Z2; rewrite Em EM /= => mM.
  by apply/RltP; apply: lt_le_trans mM; rewrite exprn_gt0 // (le_lt_trans Hth').
have := paley_zygmund Z2 Hth'; rewrite Em EM /= lte_fin => /(_ Hm').
have -> : [set x | Rle theta (Z x)] = [set x | (theta <= Z x)%R].
  by apply/seteqP; split => x /= /RleP.
by rewrite Rmult_1_r expr2.
Qed.

(* Measurability, jointly in the sample and the parameters. *)

Lemma paper_main_head_small_ball_coord_measurable r (k : nat) :
  measurable_fun [set: r.-tuple T] ((fun x => List.nth k (tval x) 0) : r.-tuple T -> T).
Proof.
have [kn|kn] := ltnP k r.
- have -> : (fun x : r.-tuple T => List.nth k (tval x) 0) = (fun x => tnth x (Ordinal kn)).
    by apply/funext => x; rewrite pm_List_nth_nth (tnth_nth 0).
  exact: measurable_tnth.
- have -> : (fun x : r.-tuple T => List.nth k (tval x) 0) = (fun _ => (0 : T)).
    by apply/funext => x; rewrite pm_List_nth_nth nth_default // size_tuple.
  exact: measurable_cst.
Qed.

Theorem paper_main_head_small_ball_joint_measurable {dX : measure_display}
    {X : measurableType dX} r (g : X -> r.-tuple T) (H : X -> 'M[R]_r) (b : X -> R) :
  measurable_fun [set: X] g ->
  (forall i j, measurable_fun [set: X] ((fun x => H x i j) : X -> T)) ->
  measurable_fun [set: X] (b : X -> T) ->
  measurable_fun [set: X]
    ((fun x => paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) : X -> T).
Proof.
move=> mg mH mb.
have mc : forall k, measurable_fun [set: X] ((fun x => List.nth k (tval (g x)) 0) : X -> T).
  by move=> k; exact: (measurableT_comp (paper_main_head_small_ball_coord_measurable r k) mg).
have -> : (fun x => paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) =
    (fun x => ((\sum_(i < r) \sum_(j < r)
      List.nth i (tval (g x)) 0 * H x i j * List.nth j (tval (g x)) 0) -
      \sum_(i < r) H x i i - b x)%R).
  apply/funext => x.
  rewrite /paper_main_gaussian_quadratic_statistic /paper_main_quadratic_form
    /paper_main_trace /paper_main_symmetric_column !RminusE.
  congr (_ - _ - _)%R.
  by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite !mxE.
apply: measurable_funB; last exact: mb.
apply: measurable_funB.
- apply: measurable_sum => i; apply: measurable_sum => j.
  by apply: measurable_funM; [apply: measurable_funM; [exact: mc | exact: mH] | exact: mc].
- by apply: measurable_sum => i; exact: mH.
Qed.

Corollary paper_main_head_small_ball_joint_event {dX : measure_display}
    {X : measurableType dX} r (g : X -> r.-tuple T) (H : X -> 'M[R]_r) (b t : X -> R) :
  measurable_fun [set: X] g ->
  (forall i j, measurable_fun [set: X] ((fun x => H x i j) : X -> T)) ->
  measurable_fun [set: X] (b : X -> T) -> measurable_fun [set: X] (t : X -> T) ->
  measurable [set x | Rle (t x)
    ((paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) ^ 2)].
Proof.
move=> mg mH mb mt.
have mY := paper_main_head_small_ball_joint_measurable r g H b mg mH mb.
have mY2 : measurable_fun [set: X]
    ((fun x => (paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) ^ 2) :
      X -> T).
  have -> : (fun x => (paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) ^ 2) =
      (fun x => (paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) *
        (paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x)).
    by apply/funext => x; rewrite /= Rmult_1_r.
  exact: (measurable_funM mY mY).
have H0 := paper_main_head_section_le_measurable t _ mt mY2.
have -> : [set x | Rle (t x)
    ((paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) ^ 2)] =
  [set x | (t x <= (paper_main_gaussian_quadratic_statistic (H x) (tval (g x)) - b x) ^ 2)%R].
  by apply/seteqP; split => x /=; [move/RleP | move/RleP].
exact: H0.
Qed.

(* The law of Y^(k+2) under the actual Gaussian law. *)

Theorem paper_main_head_small_ball_law r (H : 'M[R]_r) (b : R) (k : nat) :
  paper_main_symmetric H ->
  (gaussian_product_law r).-integrable setT
    (fun x => ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ S (S k))%:E) /\
  (\int[gaussian_product_law r]_x
    ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ S (S k))%:E =
  (gaussian_iterated_expectation r
    (fun xs => (paper_main_gaussian_quadratic_statistic H xs - b) ^ S (S k)))%:E)%E.
Proof.
move=> HH.
have [O [c [HO [Hid [Hfr [Hc Hrot]]]]]] := paper_main_head_small_ball_rotation r H HH.
set Lc := finite_sum (fun j => Rabs (c j)) (List.seq 0 r).
have HL : 0 <= Lc by apply: finite_sum_nonnegative => j _; exact: Rabs_pos.
have Hs := paper_main_head_small_ball_test_smooth r c b Lc k HL Hc.
have [HI HE] := paper_main_gaussian_orthogonal_law_transport r O _ _ _
  (pmgs_continuous _ _ _ _ _ _ Hs) (pmgs_bound _ _ _ _ _ _ Hs).
have Hf : (fun x : r.-tuple T =>
    ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ S (S k))%:E) =
  (fun x => (paper_main_head_small_ball_test r c b k
    (gaussian_covariance_image r r O (tval x)))%:E).
  by apply/funext => x; rewrite /paper_main_head_small_ball_test -Hid.
rewrite Hf; split; first exact: HI.
rewrite HE; congr (_%:E).
apply: gaussian_iterated_expectation_ext => xs _.
by rewrite /paper_main_head_small_ball_test Hid.
Qed.

Theorem paper_main_head_small_ball_law_moments r (H : 'M[R]_r) (b : R) :
  paper_main_symmetric H ->
  (gaussian_product_law r).-integrable setT
    (fun x => ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 2)%:E) /\
  (\int[gaussian_product_law r]_x
    ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 2)%:E =
    ((2 * paper_main_pairing H H + b ^ 2)%Rcoq)%:E)%E /\
  (gaussian_product_law r).-integrable setT
    (fun x => ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 4)%:E) /\
  (\int[gaussian_product_law r]_x
    ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 4)%:E <=
    ((19 * (2 * paper_main_pairing H H + b ^ 2) ^ 2)%Rcoq)%:E)%E.
Proof.
move=> HH.
have [I2 E2] := paper_main_head_small_ball_law r H b 0 HH.
have [I4 E4] := paper_main_head_small_ball_law r H b 2 HH.
have [M2 M4] := paper_main_head_small_ball_moments r H b HH.
split; first exact: I2.
split; first by rewrite E2 M2.
split; first exact: I4.
by rewrite E4 lee_fin; apply/RleP.
Qed.

(* The small-ball probability: 1 / 76 = 1 / (4 * 19). *)

Theorem paper_main_head_small_ball_probability r (H : 'M[R]_r) (b : R) :
  paper_main_symmetric H ->
  (((1 / 76)%Rcoq)%:E <= gaussian_product_law r
    [set x | Rle ((2 * paper_main_pairing H H + b ^ 2) / 2)
      ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 2)])%E.
Proof.
move=> HH.
have Hp0 : 0 <= paper_main_pairing H H by apply/RleP; exact: paper_main_pairing_self_ge0.
set s2 := 2 * paper_main_pairing H H + b ^ 2.
have Hs0 : 0 <= s2 by rewrite /s2; have := pow2_ge_0 b; lra.
case: (Rle_lt_or_eq_dec 0 s2 Hs0) => Hs; last first.
  (* Zero variance: the event is everything. *)
  have -> : [set x : r.-tuple T | Rle (s2 / 2)
      ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 2)] = setT.
    apply/seteqP; split => x // _ /=.
    rewrite -Hs.
    have := pow2_ge_0 (paper_main_gaussian_quadratic_statistic H x - b).
    rewrite /= Rmult_1_r; lra.
  rewrite probability_setT lee_fin; apply/RleP.
  have : (1 / 76 <= 1)%Rcoq by lra.
  by [].
set Z := fun x : r.-tuple T => (paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 2.
have mY := paper_main_head_small_ball_joint_measurable r (fun x => x) (fun _ => H) (fun _ => b)
  (@measurable_id _ _ setT) (fun i j => measurable_cst _) (measurable_cst _).
have mZ : measurable_fun [set: r.-tuple T] (Z : _ -> T).
  have -> : Z = (fun x => (paper_main_gaussian_quadratic_statistic H (tval x) - b) *
      (paper_main_gaussian_quadratic_statistic H (tval x) - b)).
    by apply/funext => x; rewrite /Z /= Rmult_1_r.
  exact: (measurable_funM mY mY).
have [I2 [E2 [I4 E4]]] := paper_main_head_small_ball_law_moments r H b HH.
have [I4' E4'] := paper_main_head_small_ball_law r H b 2 HH.
have [_ M4] := paper_main_head_small_ball_moments r H b HH.
set M := gaussian_iterated_expectation r
  (fun xs => (paper_main_gaussian_quadratic_statistic H xs - b) ^ 4) in E4' M4.
have HZ2 : (fun x => (Z x ^ 2)%:E) =
    (fun x => ((paper_main_gaussian_quadratic_statistic H (tval x) - b) ^ 4)%:E).
  by apply/funext => x; rewrite /Z -pow_mult.
have I4Z : (gaussian_product_law r).-integrable setT (fun x => (Z x ^ 2)%:E).
  by rewrite HZ2; exact: I4'.
have E4Z : (\int[gaussian_product_law r]_x (Z x ^ 2)%:E = M%:E)%E.
  by rewrite HZ2; exact: E4'.
have Hth : 0 <= s2 / 2 by lra.
have Hlt : s2 / 2 < s2 by lra.
have [HM HP] := paper_main_head_small_ball_paley_zygmund (gaussian_product_law r) Z s2 M
  (s2 / 2) mZ I2 E2 I4Z E4Z Hth Hlt.
apply: le_trans HP.
rewrite lee_fin; apply/RleP.
have E : (s2 - s2 / 2) ^ 2 / M - 1 / 76 = (19 * s2 ^ 2 - M) / (76 * M).
  by field; lra.
have Hq : 0 <= (19 * s2 ^ 2 - M) / (76 * M).
  have M4' : M <= 19 * s2 ^ 2 by exact: M4.
  apply: Rmult_le_pos; first lra.
  by apply/Rlt_le/Rinv_0_lt_compat; lra.
have : (1 / 76 <= (s2 - s2 / 2) ^ 2 / M)%Rcoq by lra.
by [].
Qed.
