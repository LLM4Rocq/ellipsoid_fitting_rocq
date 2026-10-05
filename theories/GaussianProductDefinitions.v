(* Port of theories/GaussianProductDefinitions.v from Coquelicot to
   MathComp-Analysis. Every definition keeps its name, its arguments and its
   text, with one change: in gaussian_iterated_has_expectation, Coquelicot's
     is_RInt_gen (fun x => ... * gaussian_density x)
       (Rbar_locally m_infty) (Rbar_locally p_infty) v
   becomes
     whole_line_has_integral (fun x => ... * gaussian_density x) v
   of AnalysisIntegralDefinitions, that is, Lebesgue integrability of the
   integrand over the real line together with the value v of its integral.
   This is difference 4 of analysis/README.md: the improper Riemann integral
   of the original is replaced by the Lebesgue integral, and the two agree on
   absolutely integrable integrands. The Coquelicot import is dropped. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
Import ListNotations.
Open Scope R_scope.

(* The first list coordinate is integrated last. Only lists of length d
   are observed by the d-dimensional operator. No product measure is used. *)
Fixpoint gaussian_iterated_expectation (d : nat) (F : list R -> R) : R :=
  match d with
  | O => F []
  | S n => gaussian_expectation
      (fun x => gaussian_iterated_expectation n (fun xs => F (x :: xs)))
  end.

Fixpoint gaussian_iterated_integrable (d : nat) (F : list R -> R) : Prop :=
  match d with
  | O => True
  | S n =>
      (forall x, gaussian_iterated_integrable n (fun xs => F (x :: xs))) /\
      gaussian_integral_exists
        (fun x => gaussian_iterated_expectation n (fun xs => F (x :: xs)))
  end.

Definition gaussian_iterated_absolutely_integrable d (F : list R -> R) : Prop :=
  gaussian_iterated_integrable d (fun xs => Rabs (F xs)).

(* This companion relation exhibits actual normalized-density integrals
   at every level, including the final scalar value. *)
Fixpoint gaussian_iterated_has_expectation (d : nat) (F : list R -> R) (v : R) : Prop :=
  match d with
  | O => v = F []
  | S n =>
      (forall x, gaussian_iterated_has_expectation n (fun xs => F (x :: xs))
        (gaussian_iterated_expectation n (fun xs => F (x :: xs)))) /\
      whole_line_has_integral
        (fun x => gaussian_iterated_expectation n (fun xs => F (x :: xs)) * gaussian_density x)
        v
  end.

Fixpoint gaussian_separable_product (fs : list (R -> R)) (xs : list R) : R :=
  match fs with
  | [] => 1
  | f :: gs => match xs with
      | [] => 0
      | x :: ys => f x * gaussian_separable_product gs ys
      end
  end.

Fixpoint gaussian_product_expectations (fs : list (R -> R)) : R :=
  match fs with
  | [] => 1
  | f :: gs => gaussian_expectation f * gaussian_product_expectations gs
  end.

Fixpoint gaussian_sum_squares (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: ys => x*x + gaussian_sum_squares ys
  end.
