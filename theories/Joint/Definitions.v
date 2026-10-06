From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.VectorListDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.VectorDefinitions
  Goe.Definitions Gibbs.NestedGradientDefinitions
  Gibbs.MatrixThirdDerivativeDefinitions Chaos.SecondOrderDefinitions
  Quadratic.Definitions Matrix.SymmetricBasisDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Gaussian expectations of functions of a pair of vectors, and the joint
   interpolation between a quadratic matrix and a GOE matrix.
   - gaussian_list_domain d F: F is integrable and absolutely integrable
     at every level of the iterated Gaussian expectation over d
     coordinates, and F and |F| have expectations, equal to
     gaussian_iterated_expectation of F and of |F|. Each level asks for
     Lebesgue integrability over the line against the kernel.
   - A pair (x, z) of vectors has S m + S n coordinates;
     joint_vector_to_list and joint_vector_of_list convert between such
     pairs and lists, and gaussian_pair_expectation and
     gaussian_pair_domain are the iterated expectation and
     gaussian_list_domain of F x z read on lists.
   - joint_matrix n C t x z is C + sqrt (t / (n + 1)) (x x^T - I)
     + sqrt (1 - t) goe_matrix n z, and joint_quadratic_input n x is
     (x x^T - I) / sqrt (n + 1). At joint_matrix, the four joint
     observables are the nested gradient paired with joint_quadratic_input
     (joint_quadratic_trace) and with goe_matrix n z (joint_goe_trace), the
     symmetric divergence of the derivative of the gradient
     (joint_divergence), and the chaos contraction of the third derivative
     with x (joint_remainder).

   A joint vector has the type euclidean_product (vector_NormedModule m)
   (vector_NormedModule n) of Matrix.EuclideanProduct: a pair with the
   Euclidean norm of its S m + S n coordinates and the product topology.
   A bound variable for a joint vector should be given this type; an
   untyped pair gets MathComp's max norm on vector m * vector n. No
   MathComp module is imported here, so the lists, the scope and the
   arithmetic are Stdlib's. *)

Definition gaussian_list_domain d (F : list R -> R) : Prop :=
  gaussian_iterated_integrable d F /\ gaussian_iterated_absolutely_integrable d F /\
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (F xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (F xs))).

Definition joint_vector_to_list m n
    (xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n)) : list R :=
  vector_to_list m (fst xz) ++ vector_to_list n (snd xz).

Definition joint_vector_of_list m n (xs : list R) :
    euclidean_product (vector_NormedModule m) (vector_NormedModule n) :=
  (vector_of_list m (firstn (S m) xs), vector_of_list n (skipn (S m) xs)).

Definition gaussian_pair_pullback m n (F : vector m -> vector n -> R) (xs : list R) : R :=
  F (fst (joint_vector_of_list m n xs)) (snd (joint_vector_of_list m n xs)).

Definition gaussian_pair_expectation m n (F : vector m -> vector n -> R) : R :=
  gaussian_iterated_expectation (S m + S n) (gaussian_pair_pullback m n F).

Definition gaussian_pair_domain m n (F : vector m -> vector n -> R) : Prop :=
  gaussian_list_domain (S m + S n) (gaussian_pair_pullback m n F).

Definition joint_quadratic_input n (x : vector n) : matrix n :=
  quadratic_matrix n (/sqrt (INR (S n))) (matrix_zero n) x.

Definition joint_matrix n (C : matrix n) (t : R)
    (x : vector n) (z : vector (goe_vector_index n)) : matrix n :=
  matrix_add n (quadratic_matrix n (sqrt (t / INR (S n))) C x)
    (matrix_scale n (sqrt (1-t)) (goe_matrix n z)).

Definition joint_quadratic_trace n beta gamma offset coeff Y S C t x z : R :=
  trace_pair n (joint_quadratic_input n x)
    (matrix_nested_gradient n beta gamma offset coeff Y S (joint_matrix n C t x z)).

Definition joint_goe_trace n beta gamma offset coeff Y S C t x z : R :=
  trace_pair n (goe_matrix n z)
    (matrix_nested_gradient n beta gamma offset coeff Y S (joint_matrix n C t x z)).

Definition joint_divergence n beta gamma offset coeff Y S C t x z : R :=
  symmetric_divergence n
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S (joint_matrix n C t x z)).

Definition joint_remainder n beta gamma offset coeff Y S C t x z : R :=
  chaos_contraction n
    (matrix_nested_third_derivative n beta gamma offset coeff Y S (joint_matrix n C t x z)) x.
