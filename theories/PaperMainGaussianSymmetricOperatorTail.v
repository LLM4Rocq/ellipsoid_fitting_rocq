(* A measurable exceptional set for the actual isotropic symmetric
   Gaussian operator bound. The constants are deliberately coarse and fixed:
   outside a set of probability at most 2 exp(-10d), the bilinear operator
   norm is at most 20 sqrt(d), where d=n+1. *)
From Stdlib Require Import Reals List Lia Lra Psatz Classical_Prop.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions
  PaperMainGordonProcessCovariance PaperMainGaussianFeatureCoordinates
  PaperMainGaussianSymmetricLawPublic PaperMainConeConditionOperator
  PaperMainSymmetricBilinear PaperMainSymmetricOperatorNet
  PaperMainGaussianLinearTailSymmetric.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem paper_main_symmetric_gaussian_operator_good_set n :
  exists A : set ((paper_main_symmetric_dimension n).-tuple (measurableTypeR R)),
    measurable A /\
    (gaussian_product_law (paper_main_symmetric_dimension n) A <=
      (2*exp(-10*INR (S n)))%:E)%E /\
    (forall x, ~ A x -> paper_main_cone_opnorm_le
      (paper_main_public_symmetric_gaussian n (tval x)) (20*sqrt (INR (S n)))).
Proof.
have [s [v [Hs HV Hln HW]]] := paper_main_symmetric_operator_net_quarter_stdlib n.
have [HM HP] := paper_main_public_symmetric_net_tail_exponential n v s Hs HV Hln.
exists (paper_main_public_symmetric_net_event n v s (10*sqrt (INR (S n)))).
split; first exact HM.
split; first exact HP.
move=> x Hx; apply NNPP => Hnot.
have HE : 20*sqrt (INR (S n)) = 2*(10*sqrt (INR (S n))) by ring.
have [i [j [Hi Hj Hij]]] := HW (paper_main_public_symmetric_gaussian n (tval x))
  (10*sqrt (INR (S n))) (20*sqrt (INR (S n))) HE Hnot.
apply Hx; apply/paper_main_public_symmetric_net_eventE.
exists i,j; by repeat split.
Qed.
