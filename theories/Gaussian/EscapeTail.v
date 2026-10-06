(* Gaussian concentration for the genuine escape-through-a-mesh statistic,
   keeping the actual set width and exact norm mean. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import Gaussian.IteratedExpectationDefinitions
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gordon.ProcessCovariance Gordon.SetWidth Gaussian.Norm
  Gaussian.NormConcentration Gaussian.GordonTail Gordon.Escape
  Gordon.EscapeExpectation.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_gaussian_escape_sqrt_tail N M T u :
  Nat.lt 0 N -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) -> 0 < u ->
  (gaussian_product_law (Nat.mul N M) [set x |
    Rle (paper_main_gordon_escape N M T (tval x))
      (sqrt (INR N-1) - paper_main_gordon_set_width M T - u)] <=
    (exp(-u^2/2))%:E)%E.
Proof.
move=> HN HT HU Hu.
have HB : sqrt (INR N-1)-paper_main_gordon_set_width M T <=
  gaussian_iterated_expectation (Nat.mul N M) (paper_main_gordon_escape N M T).
  have H1 := paper_main_gaussian_norm_mean_lower N.
  have H2 := paper_main_gordon_escape_expectation N M T HN HT HU; lra.
have H := paper_main_gaussian_lipschitz_lower_margin (Nat.mul N M)
  (paper_main_gordon_escape N M T) 1
  (sqrt (INR N-1)-paper_main_gordon_set_width M T) u Rlt_0_1
  (paper_main_gordon_escape_lipschitz N M T HN HT HU) HB Hu.
replace (2*1^2) with 2 in H by ring; exact H.
Qed.
