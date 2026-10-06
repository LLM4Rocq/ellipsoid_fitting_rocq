(* The joint residual bound for the approximate cone selector, with no
   measurable-selector premise. Let D = paper_main_symmetric_dimension n,
   z a D-tuple of Gaussian coordinates with symmetric Gaussian matrix Z(z),
   and x an N-point data sample of R^(S n) under the joint law
   gaussian_product_law (D + N (S n)). For 1 <= kappa, eps > 0 and r > 0, the
   selector P(z) of PaperMainConeApproxSelector has measurable entries, lies
   in paper_main_head_cone_sphere kappa, satisfies
     support(Z(z), K) - eps |Z(z)|_F <= <Z(z), P(z)> <= support(Z(z), K),
   and the joint residual event "exists i < N, r <= |<W_i(x), P(z)>|" of
   PaperMainGaussianResidualJoint is measurable with probability at most
     N 2 exp (- (S n) r^2 / (4 + 4 kappa r)).
   No bad set is needed, since every value of the selector is in the cone
   sphere. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability exp.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainConeConditionOperator PaperMainGaussianFeatureCoordinates
  PaperMainGaussianSymmetricLawPublic PaperMainHeadLaw
  PaperMainGaussianResidualRows PaperMainGaussianResidualJoint
  PaperMainConeApproxSelector.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

Theorem paper_main_cone_selector_residual N n (kappa eps r : R) :
  1 <= kappa -> 0 < eps -> 0 < r ->
  exists P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n),
    (forall a b : 'I_(S n), measurable_fun [set: _] ((fun z => P z a b) : _ -> T)) /\
    (forall z : (paper_main_symmetric_dimension n).-tuple T,
      [/\ paper_main_head_cone_sphere kappa (P z),
        paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
            (paper_main_head_cone_sphere kappa) -
          eps * paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
          paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z) &
        paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z) <=
          paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
            (paper_main_head_cone_sphere kappa)]) /\
    measurable (paper_main_gaussian_residual_joint_event
      (paper_main_symmetric_dimension n) N (S n) P r) /\
    (gaussian_product_law (Nat.add (paper_main_symmetric_dimension n) (N * S n)%N)
      (paper_main_gaussian_residual_joint_event (paper_main_symmetric_dimension n) N (S n) P r)
      <= (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
        (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> Hk He Hr.
have [P [mP HP]] := paper_main_cone_selector_gaussian n kappa eps Hk He.
exists P; split; first exact: mP.
split.
  by move=> z; case: (HP z) => HK _ _ _ [Hlo Hup]; split.
have Hk0 : 0 <= kappa by apply: le_trans Hk; exact: ler01.
have HPz : forall z, [/\ paper_main_symmetric (P z), paper_main_pairing (P z) (P z) = 1 &
    paper_main_cone_opnorm_le (P z) (kappa / Num.sqrt (S n)%:R)].
  move=> z; case: (HP z) => _ Hs H1 Hb _; split=> //.
  by rewrite -pmh_frobenius_sqr H1 expr1n.
exact: (paper_main_gaussian_residual_joint_tail_all _ N n P kappa r mP HPz Hk0 Hr).
Qed.
