(* Finite-sample Gaussian matrix bounds in the frozen flat sample layout.
   The matrix is tuple_mx (sample_row_tuple x); its row i is point i transposed.
   The exact row-law identity transports the arbitrary-realType library
   expectation bound and positive-threshold Markov bounds, including zero
   dimensions and a zero scaling coefficient. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.probability Require Import lindeberg.
From GaussianAnalysis.random_matrix Require Import restricted_isometry isotropic_rows.
From GaussianAnalysis.random_matrix Require Import gaussian_rows_bounds.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidUniversality.Shifted Require Import GaussianRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section sample_matrix_bounds.
Variables n d : nat.
Local Notation H := (fun x : paper_main_sample n d =>
  restricted_isometry.tuple_mx (sample_row_tuple x)).
Local Notation P := (gaussian_product_law (n*d)).

Lemma ge0_integral_gaussian_sample_rows
    (f : n.-tuple 'rV[RR]_d -> \bar RR) :
  measurable_fun setT f -> (forall y, (0 <= f y)%E) ->
  (\int[P]_x f (sample_row_tuple x) =
    \int[tuple_prod (fun=> gauss d) n]_y f y)%E.
Proof.
move=> mf f0.
have ms := @measurable_sample_row_tuple n d.
have h := @ge0_integral_pushforward _ _ _ _ RR _ ms P setT f measurableT mf.
move: h => /(_ (fun y _ => f0 y)); rewrite preimage_setT => <-.
apply: (eq_measure_integral (tuple_prod (fun=> gauss d) n)) => A mA _.
exact: gaussian_sample_row_tuple_law.
Qed.

Lemma measurable_gaussian_sample_matrix_square :
  measurable_fun setT (fun x => opnorm (H x) ^+ 2).
Proof.
have mf := @measurable_gaussian_rows_opnorm_square RR n d.
have ms := @measurable_sample_row_tuple n d.
exact: measurableT_comp mf ms.
Qed.

Theorem gaussian_sample_matrix_second_moment :
  (\int[P]_x (opnorm (H x) ^+ 2)%:E <= (@gaussian_rows_bound RR n d)%:E)%E.
Proof.
rewrite (ge0_integral_gaussian_sample_rows
  (f := fun y : n.-tuple 'rV[RR]_d => (opnorm (restricted_isometry.tuple_mx y) ^+ 2)%:E)).
- by apply/measurable_EFinP; exact: measurable_gaussian_rows_opnorm_square.
- by move=> y; rewrite lee_fin sqr_ge0.
- exact: gaussian_rows_opnorm_second_moment.
Qed.

Theorem gaussian_sample_matrix_integrable :
  P.-integrable setT (fun x => (opnorm (H x) ^+ 2)%:E).
Proof.
apply/integrableP; split.
- by apply/measurable_EFinP; exact: measurable_gaussian_sample_matrix_square.
- under eq_integral do rewrite gee0_abs ?lee_fin ?sqr_ge0 //.
  exact: le_lt_trans gaussian_sample_matrix_second_moment (ltry _).
Qed.

Theorem gaussian_sample_matrix_tail (t : R) : 0 < t ->
  (P [set x | (t <= opnorm (H x) ^+ 2)%R] <=
    (@gaussian_rows_bound RR n d / t)%:E)%E.
Proof.
move=> t0.
have h := probability_markov_ge P t0 measurable_gaussian_sample_matrix_square
  (fun x => sqr_ge0 (opnorm (H x))).
apply: le_trans h _.
rewrite mulrC EFinM; apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 ltW.
exact: gaussian_sample_matrix_second_moment.
Qed.

Theorem gaussian_sample_matrix_scaled_tail (a t : R) : 0 <= a -> 0 < t ->
  (P [set x | (t <= a * opnorm (H x) ^+ 2)%R] <=
    (a * @gaussian_rows_bound RR n d / t)%:E)%E.
Proof.
move=> a0 t0.
have mf : measurable_fun setT (fun x : paper_main_sample n d =>
    (a * opnorm (H x) ^+ 2 : measurableTypeR RR)).
  by apply: measurable_funM => //; exact: measurable_gaussian_sample_matrix_square.
have f0 x : 0 <= a * opnorm (H x) ^+ 2 by rewrite mulr_ge0 ?sqr_ge0.
have h := probability_markov_ge P t0 mf f0.
apply: le_trans h _.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin //.
- by move=> x _; rewrite lee_fin sqr_ge0.
- by apply/measurable_EFinP; exact: measurable_gaussian_sample_matrix_square.
- have aE0 : (0 <= a%:E)%E by rewrite lee_fin.
  have h2 := lee_wpmul2l aE0 gaussian_sample_matrix_second_moment.
  have ti0 : (0 <= (t^-1)%:E)%E by rewrite lee_fin invr_ge0 ltW.
  apply: le_trans (lee_wpmul2l ti0 h2) _.
  by rewrite -!EFinM lee_fin [t^-1 * _]mulrC.
Qed.

End sample_matrix_bounds.
