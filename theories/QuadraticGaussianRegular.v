From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  TensorDefinitions SecondChaosDefinitions CoefficientBounds QuadraticDefinitions
  FiniteGibbsContinuity QuadraticGrowthProofs.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity QuadraticGrowthProofs.QuadraticGrowth.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of the inner module QuadraticGaussianRegular of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/QuadraticGaussianProofs.v) from Coquelicot to MathComp-Analysis.
   The source is build/agent2/unbundled/QuadraticGaussianRegular.v. The
   bundle's reference QuadraticGrowthProofs.QuadraticGrowthContinuity and
   QuadraticGrowthProofs.QuadraticGrowth now names the inner modules of
   analysis/QuadraticGrowthProofs.v.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. The statements change form in the ways of the
   ports of MatrixCoordinates and QuadraticGrowthProofs.

   1. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. On
      vector n this is the norm of the port of OperatorDefinitions, which
      nests euclidean_product of MatrixEuclideanProduct and so keeps
      Coquelicot's Euclidean norm, not MathComp's max norm
      (analysis/README.md, difference 1). The bounds therefore mean the same,
      constants included. They are stated with Stdlib's order, sum, product
      and power around MathComp's norm, and Rabs stays Stdlib's.

   2. Pointwise continuity. Coquelicot's continuous f x, continuity of f at
      the point x, becomes MathComp's {for x, continuous f}
      (README difference 5). The topology of vector n is the one of the port
      of MatrixDefinitions, whose neighbourhoods are those of the product
      topology, as Coquelicot's were.

   3. Order on indices. With ssreflect loaded, (a <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statement writes (a <= n)%coq_nat, which is Stdlib's le.

   The test Nat.eqb a b is a boolean in both libraries, so the if of the
   original is unchanged.

   In the proofs, Coquelicot's norm_ge_0 becomes normr_ge0 through RleP,
   continuous_minus and continuous_mult become continuous_Rminus_fct and
   continuous_Rmult_fct of FiniteGibbsContinuity, continuous_const becomes
   cst_continuous, and the continuity of a coordinate comes from
   growth_linear_continuous with tuple_entry_linear, at the codomain R^o. *)

Lemma gaussian_centered_coordinate_product_bound n (x : vector n) a b :
  Rabs (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0)
    <= (1 + (`|x|)%R)^2.
Proof.
  assert (Hn : 0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
  assert (Ha : Rabs (vector_entry n x a) <= (`|x|)%R).
  { unfold vector_entry; rewrite RabsE; exact (tuple_entry_norm_bound R^o n a x). }
  assert (Hb : Rabs (vector_entry n x b) <= (`|x|)%R).
  { unfold vector_entry; rewrite RabsE; exact (tuple_entry_norm_bound R^o n b x). }
  assert (Hab : Rabs (vector_entry n x a * vector_entry n x b) <= (`|x|)%R^2).
  { rewrite Rabs_mult; replace ((`|x|)%R^2) with ((`|x|)%R*(`|x|)%R) by ring.
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (Nat.eqb a b).
  - pose proof (Rabs_triang (vector_entry n x a * vector_entry n x b) (-1)) as H.
    replace (vector_entry n x a * vector_entry n x b - 1) with
      (vector_entry n x a * vector_entry n x b + -1) by ring.
    eapply Rle_trans; [exact H|].
    rewrite (Rabs_left (-1) ltac:(lra)); nra.
  - rewrite Rminus_0_r; nra.
Qed.

Lemma gaussian_centered_coordinate_product_continuous n a b (x : vector n) :
  {for x, continuous (fun z : vector n =>
    vector_entry n z a * vector_entry n z b - if Nat.eqb a b then 1 else 0)}.
Proof.
  apply: continuous_Rminus_fct.
  - apply: continuous_Rmult_fct.
    + exact (@growth_linear_continuous (vector_NormedModule n) R^o
        (fun z => vector_entry n z a) x (tuple_entry_linear R^o n a)).
    + exact (@growth_linear_continuous (vector_NormedModule n) R^o
        (fun z => vector_entry n z b) x (tuple_entry_linear R^o n b)).
  - apply: cst_continuous.
Qed.

Theorem quadratic_gaussian_weighted_entry_regular n beta gamma offset coeff Y S lambda C a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  (forall x : vector n, {for x, continuous
    (fun z : vector n => (vector_entry n z a * vector_entry n z b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C z) a b)}) /\
  exists K : R, 0 <= K /\ forall x : vector n,
    Rabs ((vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)
      <= K * (1 + (`|x|)%R)^2.
Proof.
  intros Hb Hg HY HS Ha Hbb.
  destruct (quadratic_gradient_entry_polynomial_regular n beta gamma offset coeff Y S lambda C
    (chaos_basis n a) (chaos_basis n b) a b Hb Hg HY HS Ha Hbb)
    as [K0 [K1 [K2 [H0 [H1 [H2 Hregular]]]]]].
  split.
  - intro x; apply: continuous_Rmult_fct.
    + apply gaussian_centered_coordinate_product_continuous.
    + destruct (Hregular x) as [_ [_ [HC _]]]; exact HC.
  - exists K0; split; [exact H0|]; intro x.
    assert (HF : Rabs (matrix_entry n
        (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b) <= K0).
    { destruct (Hregular x) as [_ [_ [_ [_ [_ [H _]]]]]].
      simpl in H; lra. }
    rewrite Rabs_mult Rmult_comm; apply Rmult_le_compat; try apply Rabs_pos.
    + exact HF.
    + apply gaussian_centered_coordinate_product_bound.
Qed.
