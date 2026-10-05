(* Concentration of the finite-prior data soft loss on full data rows.

   Z_data (PaperMainHybridFiniteArray) is the entropy-shifted normalized
   finite soft minimum of continuous row losses with values in [0, 1] on N
   full data rows (g, y) of r + (mi + 1) coordinates. The A25 tails apply
   with row oscillation 1/N:
     P (Z_data <= E Z_data - t) <= exp (- N t^2 / 2),
   and the same for the upper tail. With the mean bound of
   PaperMainHybridFiniteMean this gives, for t > 0, the measurable event
     Z_data <= e (1 - exp (- c d^2)) - (2 eta + C eps S) - t
   of probability at most exp (- N t^2 / 2). The constants do not depend on
   the prior, its size, the offsets or the dimensions; C depends only on
   beta and eta, and kappa, e, c, d0 only on gamma. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainHeadSectionMeasurable
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates
  PaperMainDataFeatureMomentsCoordinates PaperMainLossNormalizedArray
  PaperMainLossConcentrationRow PaperMainLossConcentrationTail PaperMainLossConcentrationSoftMin
  PaperMainHybridFiniteArray PaperMainHybridFiniteMean.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* 1. The A25 tails for Z_data on full data rows. *)

Theorem paper_main_hybrid_finite_data_lower_tail N r mi beta (I : list nat) Hs bs
    (Bs : nat -> 'M[R]_(S mi)) (t : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq -> (0 < t)%Rcoq ->
  measurable [set x : (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R) |
    (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
     gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
       (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) - t)%R] /\
  (gaussian_product_law (N * (r + S mi)%coq_nat)
     [set x | (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
       gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
         (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) - t)%R] <=
   ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> HN HI Hb Ht.
exact: (paper_main_softmin_lower_tail (r + S mi)%coq_nat N beta I
  (paper_main_hybrid_finite_data_loss r mi Hs bs Bs) t HN HI Hb Ht
  (fun i j _ _ => paper_main_hybrid_finite_data_loss_continuous r mi Hs bs Bs i j)
  (fun i j xs _ _ _ => paper_main_hybrid_finite_data_loss_bounds r mi Hs bs Bs i j xs)).
Qed.

(* 2. The finite-prior data tail below the mean bound. *)
