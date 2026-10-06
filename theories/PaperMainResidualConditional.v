(* Conditional residual exceptions of the data sample. Let P be a map
   from Gaussian coordinates z to matrices. The joint
   residual set (paper_main_gaussian_residual_joint_set) contains the
   pairs (z, x) for which some point i < N of x has head feature W_i with
   |<W_i, P(z)>| >= r. A sample x is in the conditional event
   paper_main_residual_conditional_event when its section
   {z | (z, x) in the residual set} has probability at least tau.
   - paper_main_residual_conditional_good: outside the conditional event,
     the section has probability below tau.
   - paper_main_cone_selector_conditional: for kappa >= 1 and eps, r,
     tau > 0, the selector P of paper_main_cone_selector_residual takes
     values in the cone sphere K_kappa \cap S_F and satisfies
     support(Z(z)) - eps |Z(z)|_F <= <Z(z), P(z)> for the symmetric
     Gaussian matrix Z(z). Its conditional event is measurable, with
     probability at most tau^-1 N 2 exp(-d r^2 / (4 + 4 kappa r)) for
     d = n + 1, by Markov's inequality applied to the probability of the
     section, whose mean is the joint probability. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From EllipsoidFitting Require Import AnalysisBridge PaperMainDefinitions PaperMainAsymptotics
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainClippingLimits PaperMainResidualRates PaperMainGaussianConditionalException
  PaperMainGaussianResidualJoint PaperMainConeConditionOperator PaperMainGeometryPsd
  PaperMainConeApproxSelectorResidual PaperMainGeometryHeadWidth PaperMainGeometryHomogeneous
  PaperMainGaussianSymmetricLawPublic PaperMainGaussianFeatureCoordinates.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation T := (measurableTypeR R).

Definition paper_main_residual_conditional_event D N d
    (P : D.-tuple T -> 'M[R]_d) r tau : set (paper_main_sample N d) :=
  paper_main_conditional_exception_reverse D (N*d)%N
    (paper_main_gaussian_residual_joint_set D N d P r) tau.

Lemma paper_main_residual_conditional_good D N d
    (P : D.-tuple T -> 'M[R]_d) r tau (x : paper_main_sample N d) :
  ~ paper_main_residual_conditional_event D N d P r tau x ->
  (gaussian_product_law D (ysection (paper_main_gaussian_residual_joint_set D N d P r) x) < tau%:E)%E.
Proof.
move=> H; rewrite ltNge; apply/negP => Hge; exact: H Hge.
Qed.

Theorem paper_main_cone_selector_conditional N n (kappa eps r tau : R) :
  1 <= kappa -> 0 < eps -> 0 < r -> 0 < tau ->
  exists P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n),
    (forall a b, measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
      ((fun z => P z a b) : _ -> T)) /\
    (forall z, paper_main_head_cone_sphere kappa (P z) /\
      paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
        (paper_main_head_cone_sphere kappa) -
        eps*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
      paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z)) /\
    measurable (paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r tau) /\
    (paper_main_probability N (S n)
      (paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r tau) <=
      tau^-1%:E * (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
        (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> Hk He Hr Htau.
have [P [mP [HP [mE HB]]]] := paper_main_cone_selector_residual N n kappa eps r Hk He Hr.
exists P; split; first exact mP.
split; first by move=> z; case: (HP z) => H1 H2 H3; split.
have mS := paper_main_gaussian_residual_joint_set_measurable _ N (S n) P r mP.
split; first exact: paper_main_conditional_exception_reverse_measurable.
exact: paper_main_conditional_exception_reverse_bound mS Htau HB.
Qed.
