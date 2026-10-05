From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions VectorCoordinateDefinitions
  GaussianProductDefinitions GaussianVectorDefinitions GoeDefinitions
  GradientDefinitions MatrixThirdDefinitions SecondChaosDefinitions QuadraticDefinitions SymmetricDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Port of theories/JointDefinitions.v from Coquelicot to MathComp-Analysis.

   Every definition keeps its name, its arguments and its text, with one
   change: the type of the joint vector. Coquelicot's
     prod_NormedModule R_AbsRing (vector_NormedModule m) (vector_NormedModule n)
   becomes
     euclidean_product (vector_NormedModule m) (vector_NormedModule n)
   of MatrixEuclideanProduct, which MatrixDefinitions re-exports. This is the
   product that the ports of MatrixDefinitions and OperatorDefinitions nest
   to build vectors and matrices. It is a copy of the type
   vector m * vector n, with the componentwise operations and Coquelicot's
   product norm sqrt (norm (fst xz) ^ 2 + norm (snd xz) ^ 2), so the norm of
   a joint vector is still the Euclidean norm of its S m + S n coordinates.
   MathComp's own product vector m * vector n would carry the max norm
   (difference 1 of analysis/README.md), which would change the polynomial
   bounds (1 + norm xz) ^ p that the challenges state on joint vectors. The
   topology of euclidean_product is the product topology
   (euclidean_product_nbhsE), so continuity on joint vectors means the same
   as before. The elements are still pairs: fst, snd, the pair constructor
   and destruct xz as [x z] behave as in the original. A statement about
   joint vectors should give its bound variables this type, as in
   fun yz : euclidean_product (vector_NormedModule m) (vector_NormedModule n)
   => F (fst yz) (snd yz). A pair variable left untyped gets MathComp's
   structures on vector m * vector n instead, with the same topology but the
   max norm.

   The Coquelicot import is dropped and no MathComp module is imported here,
   so the lists (firstn, skipn, ++), the scope and the arithmetic, including
   sqrt, /, INR, 1 - t and Rabs, are Stdlib's, as before.

   The other definitions are unchanged in text, and their meaning is
   inherited from the ported definitions they use. gaussian_list_domain d F
   has the text of gaussian_vector_domain of GaussianVectorDefinitions, and
   changes in the same way by difference 4 of analysis/README.md: each level
   of gaussian_iterated_integrable asks, through gaussian_integral_exists,
   that the integrand times the Gaussian kernel be measurable and Lebesgue
   integrable over the line, and gaussian_iterated_has_expectation uses
   whole_line_has_integral, Lebesgue integrability over the line with the
   given value, in place of Coquelicot's improper Riemann integral. The two
   readings agree on integrands that are continuous with an integrable
   majorant, which is how the challenges use gaussian_list_domain and
   gaussian_pair_domain. joint_matrix, joint_quadratic_input and the four
   joint observables are built from matrix_add, matrix_scale,
   quadratic_matrix, goe_matrix, trace_pair, the nested Gibbs derivatives,
   symmetric_divergence and chaos_contraction, whose ports keep their names,
   arguments and values. *)

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
