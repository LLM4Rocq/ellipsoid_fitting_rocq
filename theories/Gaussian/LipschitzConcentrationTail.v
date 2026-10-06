(* Chernoff closure for a continuous Gaussian test from its actual centered
   exponential moment bound. This helper is independent of smoothness. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences exp measurable_realfun.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.IteratedExpectationDefinitions GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gaussian.SmoothLaw Gaussian.SmoothTail.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_gaussian_mgf_upper_tail d f L u :
  finite_joint_continuous d f -> 0 < L -> 0 < u ->
  (\int[gaussian_product_law d]_x
     (exp ((u / L ^ 2) * (f (tval x) - gaussian_iterated_expectation d f)))%:E <=
     (exp ((u / L ^ 2) ^ 2 * L ^ 2 / 2))%:E)%E ->
  (gaussian_product_law d
     [set x | Rle (gaussian_iterated_expectation d f + u) (f (tval x))] <=
   (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
Proof.
move=> Hc HL Hu HB.
have HL2 : 0 < L ^ 2 by apply pow_lt.
have Hq : 0 < u / L ^ 2 by apply Rdiv_lt_0_compat.
have Hq' : (0 < (u / L ^ 2)%Rcoq)%R by apply/RltP.
pose X : {RV gaussian_product_law d >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType) (paper_main_gaussian_smooth_centered d f)
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (paper_main_gaussian_smooth_centered_measurable d f Hc))).
have H := chernoff X (r := u / L ^ 2) u Hq'.
have HM : (@mmt_gen_fun _ _ _ (gaussian_product_law d) X (u / L ^ 2) =
  \int[gaussian_product_law d]_x
    (exp ((u / L ^ 2) * (f (tval x) - gaussian_iterated_expectation d f)))%:E)%E.
{ rewrite /mmt_gen_fun unlock; apply: eq_integral => x _ /=.
  by rewrite RexpE /paper_main_gaussian_smooth_centered mulrC. }
have HS : [set x | (u <= X x)%R] =
  [set x : d.-tuple (measurableTypeR R) |
    Rle (gaussian_iterated_expectation d f + u) (f (tval x))].
{ apply/seteqP; split=> x /=.
  - move/RleP; rewrite /paper_main_gaussian_smooth_centered => Hx.
    change (Rle u (f (tval x) - gaussian_iterated_expectation d f)) in Hx.
    change (Rle (gaussian_iterated_expectation d f + u) (f (tval x))); lra.
  - move=> Hx; apply/RleP; rewrite /paper_main_gaussian_smooth_centered.
    change (Rle (gaussian_iterated_expectation d f + u) (f (tval x))) in Hx.
    change (Rle u (f (tval x) - gaussian_iterated_expectation d f)); lra. }
rewrite -HS; apply: (le_trans H).
rewrite HM.
have HE : ((exp ((u / L ^ 2) ^ 2 * L ^ 2 / 2))%:E *
  (expR (- ((u / L ^ 2)%Rcoq * u)%R))%:E =
  (exp (- u ^ 2 / (2 * L ^ 2)))%:E)%E.
{ rewrite -RexpE -EFinM.
  apply f_equal; exact (paper_main_gaussian_chernoff_exponent L u HL). }
rewrite -HE; apply: lee_wpmul2r HB.
by rewrite lee_fin expR_ge0.
Qed.
