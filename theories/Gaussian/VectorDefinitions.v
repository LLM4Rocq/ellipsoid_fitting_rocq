(* Gaussian expectations of functions of a vector. A vector n has S n
   coordinates (Matrix.OperatorDefinitions). gaussian_vector_expectation n f is
   the iterated Gaussian expectation over S n coordinates of
   xs |-> f (vector_of_list n xs); the other definitions are the
   corresponding conditions of Gaussian.IteratedExpectationDefinitions, and
   gaussian_vector_domain n f collects them for f and |f|. Each level of
   the iterated expectation is a Lebesgue integral over the line, so
   gaussian_vector_domain n f says that the integrand of each level, for f
   and for |f|, is measurable and absolutely integrable. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.VectorListDefinitions
  Gaussian.IteratedExpectationDefinitions.
Open Scope R_scope.

Definition gaussian_vector_expectation n (f : vector n -> R) : R :=
  gaussian_iterated_expectation (S n) (fun xs => f (vector_of_list n xs)).

Definition gaussian_vector_integrable n (f : vector n -> R) : Prop :=
  gaussian_iterated_integrable (S n) (fun xs => f (vector_of_list n xs)).

Definition gaussian_vector_absolutely_integrable n (f : vector n -> R) : Prop :=
  gaussian_iterated_absolutely_integrable (S n) (fun xs => f (vector_of_list n xs)).

Definition gaussian_vector_has_expectation n (f : vector n -> R) (v : R) : Prop :=
  gaussian_iterated_has_expectation (S n) (fun xs => f (vector_of_list n xs)) v.

Definition gaussian_vector_domain n (f : vector n -> R) : Prop :=
  gaussian_vector_integrable n f /\ gaussian_vector_absolutely_integrable n f /\
  gaussian_vector_has_expectation n f (gaussian_vector_expectation n f) /\
  gaussian_vector_has_expectation n (fun x => Rabs (f x))
    (gaussian_vector_expectation n (fun x => Rabs (f x))).
