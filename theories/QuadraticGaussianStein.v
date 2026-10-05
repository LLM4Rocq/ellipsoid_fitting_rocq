From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions
  SecondChaosDefinitions QuadraticDefinitions QuadraticGrowthProofs
  GaussianVectorDefinitions GaussianVectorStein.
Import QuadraticGrowthProofs.QuadraticGrowth.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of the inner module QuadraticGaussianStein of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/QuadraticGaussianProofs.v), extracted to
   build/agent2/unbundled/QuadraticGaussianStein.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundles QuadraticGrowthProofs and
   GaussianVectorProofs, and named their inner modules
   QuadraticGrowthProofs.QuadraticGrowth and
   GaussianVectorProofs.GaussianVectorStein. The port imports
   analysis/QuadraticGrowthProofs.v, whose inner module QuadraticGrowth
   keeps that name, and the standalone ported module GaussianVectorStein.

   The theorem keeps its name, its arguments in the same order and its
   hypotheses. No item is added. Its statement changes form in one way,
   which does not change its meaning.

   1. Indices. With ssreflect loaded, (a <= n)%nat would mean ssrnat's
      boolean leq. The statement writes (a <= n)%coq_nat and
      (b <= n)%coq_nat, which are Stdlib's Peano order le, as in the
      original and in the ported gaussian_vector_second_stein and
      quadratic_gradient_entry_polynomial_regular.

   The test Nat.eqb a b is a boolean in both libraries, so the if of the
   original is unchanged. The meaning of gaussian_vector_domain and
   gaussian_vector_expectation follows the ported GaussianVectorDefinitions
   (difference 4 of analysis/README.md): Lebesgue integrability against the
   Gaussian kernel at each level of the iterated expectation, and Lebesgue
   integrals. The four functions of the statement are continuous and bounded
   by a polynomial in the Euclidean norm of the vector, so they are
   absolutely integrable against the kernel and the Lebesgue and improper
   Riemann values agree. The statement is the text of the clause
   "Concrete entrywise Gaussian identity" of the restated challenge
   ellipsoid_gaussian_matrix.

   The proof is the original one. The ported
   quadratic_gradient_entry_polynomial_regular states the derivatives with
   is_diff at the codomain R^o and the continuity with {for x, continuous _},
   which are the forms of the hypotheses of the ported
   gaussian_vector_second_stein. *)

Theorem quadratic_gaussian_entry_stein n beta gamma offset coeff Y S lambda C a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  List.Forall (gaussian_vector_domain n)
    [(fun x => matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b);
     (fun x => matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x
       (chaos_basis n a)) a b);
     (fun x => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
       (chaos_basis n a) (chaos_basis n b)) a b);
     (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
       matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)] /\
  gaussian_vector_expectation n
    (fun x => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x
      (chaos_basis n a) (chaos_basis n b)) a b) =
  gaussian_vector_expectation n
    (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) *
      matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b).
Proof.
  intros Hb Hg HY HS Ha Hbb.
  destruct (quadratic_gradient_entry_polynomial_regular n beta gamma offset coeff Y S lambda C
    (chaos_basis n a) (chaos_basis n b) a b Hb Hg HY HS Ha Hbb)
    as [K0 [K1 [K2 [H0 [H1 [H2 Hregular]]]]]].
  apply (gaussian_vector_second_stein n a b
    (fun x => matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)
    (fun x u => matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b)
    (fun x u v => matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u v) a b)
    K0 O K1 (Datatypes.S O) K2 (Datatypes.S (Datatypes.S O))); try assumption;
    intro x; specialize (Hregular x); tauto.
Qed.
