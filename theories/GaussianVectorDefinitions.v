(* Port of theories/GaussianVectorDefinitions.v from Coquelicot to
   MathComp-Analysis. The original used nothing from Coquelicot directly.
   Its Coquelicot content came only through the type vector n of
   OperatorDefinitions, through vector_of_list of VectorCoordinateDefinitions,
   and through the iterated Gaussian operators of GaussianProductDefinitions.
   Their ports keep the same names and arguments. So the import of Coquelicot
   is dropped and the text of every definition below is unchanged. MathComp is
   not imported here, so Rabs, the conjunctions and the scope are Stdlib's, as
   before.

   The meaning is inherited from the ported definitions. A vector is still a
   nested tuple of S n reals, read from and written to a list by
   vector_of_list. gaussian_iterated_expectation is the same iterated
   expectation, each level being gaussian_expectation of GaussianDefinitions.
   Two things change there, by difference 4 of analysis/README.md.
   gaussian_integral_exists, used at every level of
   gaussian_iterated_integrable, now says that the integrand times the
   Gaussian kernel is measurable and Lebesgue integrable over the line. In
   gaussian_iterated_has_expectation, Coquelicot's improper Riemann integral
   is_RInt_gen becomes whole_line_has_integral, Lebesgue integrability over
   the line together with the value of the integral. The two readings agree
   on integrands that are Riemann integrable on every segment and absolutely
   integrable over the line, such as continuous integrands with an integrable
   majorant. Elsewhere they differ: with the Lebesgue reading,
   gaussian_vector_domain n f says that the integrand of each level of the
   iterated expectation of f, and of Rabs o f, is measurable and absolutely
   integrable, while the original asked for Riemann integrability on
   segments and convergence of the improper integrals. The challenges assert
   gaussian_vector_domain for continuous functions with a polynomial bound,
   where the two readings are meant to coincide; the ports of the lemmas
   that prove it must establish the Lebesgue reading. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions
  VectorCoordinateDefinitions GaussianProductDefinitions.
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
