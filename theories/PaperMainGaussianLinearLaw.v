(* The linear form <a, x> = paper_main_gordon_dot d a x of a tuple x, as a
   measurable function for the product law (paper_main_gaussian_linear_random).
   Its tails are in PaperMainGaussianTails. *)
From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCovarianceDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductIntegrals
  GaussianProbabilityProductContinuity PaperMainGordonProcessCovariance
  PaperMainGordonWidth.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_gaussian_linear_random d a
    (x : d.-tuple (measurableTypeR R)) : measurableTypeR R :=
  paper_main_gordon_dot d a (fun i => List.nth i (tval x) 0).

Lemma paper_main_gaussian_linear_random_measurable d a :
  measurable_fun [set: d.-tuple (measurableTypeR R)] (paper_main_gaussian_linear_random d a).
Proof.
exact: (gpp_joint_measurable d _ (paper_main_gordon_dot_continuous d a)).
Qed.

HB.instance Definition _ d a :=
  isMeasurableFun.Build _ _ _ _ (paper_main_gaussian_linear_random d a)
    (paper_main_gaussian_linear_random_measurable d a).
