(* Definitions for the Gaussian interpolation between two covariances.

   Centered Gaussian vectors of R^K are written as linear images of
   independent standard Gaussian coordinates: X = P xi with xi in R^p and
   Y = Q eta with eta in R^q, for real K x p and K x q matrices P and Q
   given by their entries P a k (row a < K, column k < p). Every centered
   Gaussian vector of R^K has this form, with P a square root of its
   covariance matrix, and the covariance of P xi is P P^T. Vectors are
   lists; List.nth with default 0 reads an entry, so an index at or beyond
   the length reads 0.

   - gaussian_covariance_row p P a xs = sum_{k<p} P a k * xs_k, entry a of
     P xs.
   - gaussian_covariance_image K p P xs is the list of the K entries of
     P xs, in order.
   - gaussian_covariance_entry p P a b = sum_{k<p} P a k * P b k, entry
     (a, b) of P P^T.
   - gaussian_covariance_path K p q P Q t zs is the list of the K entries
     sqrt t (P xs)_a + sqrt (1-t) (Q ys)_a, where xs is the first p entries
     of zs and ys the others. For zs a list of p + q independent standard
     Gaussian coordinates it is the Gaussian interpolation
     Z(t) = sqrt t X + sqrt (1-t) Y between the independent vectors X and
     Y, as in the proofs of Slepian's and Gordon's comparison theorems.
   - gaussian_covariance_pairing K p q P Q H is
     sum_{a<K} sum_{b<K} ((P P^T)_{ab} - (Q Q^T)_{ab}) H a b, the pairing
     of the covariance difference with an array H, such as the second
     partial derivatives of a test function.
   - gaussian_covariance_domain d G has the body of gaussian_list_domain of
     JointDefinitions, which this module does not import: G is integrable
     and absolutely integrable at every level of the iterated Gaussian
     expectation over d coordinates, with actual normalized-density
     integrals for G and for its absolute value.

   sqrt, *, + and - are Stdlib's, and sqrt of a negative number is 0. The
   module contains definitions only. *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions.
Import ListNotations.
Open Scope R_scope.

Definition gaussian_covariance_row (p : nat) (P : nat -> nat -> R) (a : nat)
    (xs : list R) : R :=
  finite_sum (fun k => P a k * List.nth k xs 0) (List.seq 0 p).

Definition gaussian_covariance_image (K p : nat) (P : nat -> nat -> R)
    (xs : list R) : list R :=
  List.map (fun a => gaussian_covariance_row p P a xs) (List.seq 0 K).

Definition gaussian_covariance_entry (p : nat) (P : nat -> nat -> R) (a b : nat) : R :=
  finite_sum (fun k => P a k * P b k) (List.seq 0 p).

Definition gaussian_covariance_path (K p q : nat) (P Q : nat -> nat -> R) (t : R)
    (zs : list R) : list R :=
  List.map (fun a =>
    sqrt t * gaussian_covariance_row p P a (List.firstn p zs) +
    sqrt (1 - t) * gaussian_covariance_row q Q a (List.skipn p zs))
    (List.seq 0 K).

Definition gaussian_covariance_domain (d : nat) (G : list R -> R) : Prop :=
  gaussian_iterated_integrable d G /\ gaussian_iterated_absolutely_integrable d G /\
  gaussian_iterated_has_expectation d G (gaussian_iterated_expectation d G) /\
  gaussian_iterated_has_expectation d (fun xs => Rabs (G xs))
    (gaussian_iterated_expectation d (fun xs => Rabs (G xs))).
