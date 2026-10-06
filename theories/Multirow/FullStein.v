(* The Stein identity for the multirow observables, row by row and summed
   over the rows (paper_multirow_full_stein_results), for symmetric
   matrices B s and 0 < t < 1. For each row i, the row velocity and the row
   remainder have a Gaussian domain under the law of all the coordinates,
   and E[velocity of row i] = sqrt t / (2 d sqrt d) * E[remainder of row i],
   with d = S n. Summed over the rows, both sums have a domain, the
   expectation of each sum is the sum of the expectations, and the identity
   holds for the sums. No bound on the score data y and B is assumed: the
   regularity of the row observables for any y and B comes from
   Multirow.ObservableBounds, the identity of one row from
   gaussian_row_full_stein_of_regular (Row.ConditionalStein), and the sums from
   gaussian_finite_polynomial_sum (Gaussian.Iterated.FiniteSums). *)
From Stdlib Require Import Reals List.
From EllipsoidFitting Require Import Matrix.Definitions Soft.Definitions
  Tensor.Definitions Goe.Definitions Gaussian.Iterated.Definitions
  Joint.Definitions Row.ObservableDefinitions.
From Stdlib Require Import Lia.
From EllipsoidFitting Require Import Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Multirow.ObservableBounds
  Row.ConditionalStein Gaussian.Iterated.FiniteSums.
Import ListNotations.
Open Scope R_scope.

Theorem paper_multirow_full_stein_results :
(* Row by row: domains of the row velocity and of the row remainder under
   the law of all the rows, and the Stein identity of row i. *)
(forall (n m : nat) (beta gamma : R) (y : nat -> nat -> R) (B : nat -> matrix n)
    (Y S : list nat) (t : R) (i : nat),
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  0 < t < 1 -> (i <= m)%nat ->
  gaussian_list_domain (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => gaussian_row_velocity n m beta gamma y B Y S t i xs) /\
  gaussian_list_domain (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => gaussian_row_remainder n m beta gamma y B Y S t i xs) /\
  gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => gaussian_row_velocity n m beta gamma y B Y S t i xs) =
  sqrt t / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n))) *
    gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
      (fun xs => gaussian_row_remainder n m beta gamma y B Y S t i xs)) /\
(* Summed over the rows: domains of both sums, expectation of each sum as
   the sum of the expectations, and the summed Stein identity. *)
(forall (n m : nat) (beta gamma : R) (y : nat -> nat -> R) (B : nat -> matrix n)
    (Y S : list nat) (t : R),
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  0 < t < 1 ->
  gaussian_list_domain (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))) /\
  gaussian_list_domain (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => finite_sum (fun i => gaussian_row_remainder n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))) /\
  gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))) =
  finite_sum (fun i =>
    gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
      (fun xs => gaussian_row_velocity n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) /\
  gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => finite_sum (fun i => gaussian_row_remainder n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))) =
  finite_sum (fun i =>
    gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
      (fun xs => gaussian_row_remainder n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) /\
  gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
    (fun xs => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S t i xs)
      (List.seq 0 (Datatypes.S m))) =
  sqrt t / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n))) *
    finite_sum (fun i =>
      gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
        (fun xs => gaussian_row_remainder n m beta gamma y B Y S t i xs))
      (List.seq 0 (Datatypes.S m))).
Proof.
  split.
  - intros n m beta gamma y B Y S t i Hb Hg HY HS Hsym Ht Hi.
    destruct (multirow_row_observables_regular n m beta gamma y B Y S t i Hb Hg HY HS Hi)
      as [HCV [HCR [CV [CR [HBV HBR]]]]].
    exact (gaussian_row_full_stein_of_regular n m beta gamma y B Y S t i CV CR
      Hi Hb Hg HY HS Ht Hsym HCV HBV HCR HBR).
  - intros n m beta gamma y B Y S t Hb Hg HY HS Hsym Ht.
    assert (Hrow : forall i, In i (List.seq 0 (Datatypes.S m)) -> (i <= m)%nat).
    { intros i Hi; apply in_seq in Hi; lia. }
    assert (HV : forall i, In i (List.seq 0 (Datatypes.S m)) -> exists C,
      finite_joint_continuous (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) (gaussian_row_velocity n m beta gamma y B Y S t i) /\
      finite_polynomial_bound (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) C 2 (gaussian_row_velocity n m beta gamma y B Y S t i)).
    { intros i Hi.
      destruct (multirow_row_observables_regular n m beta gamma y B Y S t i Hb Hg HY HS (Hrow i Hi))
        as [HCV [_ [CV [_ [HBV _]]]]].
      exists CV; split; assumption. }
    assert (HR : forall i, In i (List.seq 0 (Datatypes.S m)) -> exists C,
      finite_joint_continuous (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) (gaussian_row_remainder n m beta gamma y B Y S t i) /\
      finite_polynomial_bound (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) C 2 (gaussian_row_remainder n m beta gamma y B Y S t i)).
    { intros i Hi.
      destruct (multirow_row_observables_regular n m beta gamma y B Y S t i Hb Hg HY HS (Hrow i Hi))
        as [_ [HCR [_ [CR [_ HBR]]]]].
      exists CR; split; assumption. }
    destruct (gaussian_finite_polynomial_sum (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) (List.seq 0 (Datatypes.S m))
      (fun i => gaussian_row_velocity n m beta gamma y B Y S t i) 2 HV)
      as [_ [_ [_ [HdomV HsumV]]]].
    destruct (gaussian_finite_polynomial_sum (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n))) (List.seq 0 (Datatypes.S m))
      (fun i => gaussian_row_remainder n m beta gamma y B Y S t i) 2 HR)
      as [_ [_ [_ [HdomR HsumR]]]].
    split; [exact HdomV|].
    split; [exact HdomR|].
    split; [exact HsumV|].
    split; [exact HsumR|].
    refine (eq_trans HsumV _).
    transitivity (finite_sum (fun i =>
      sqrt t / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n))) *
        gaussian_iterated_expectation (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))
          (fun xs => gaussian_row_remainder n m beta gamma y B Y S t i xs))
      (List.seq 0 (Datatypes.S m))).
    + apply multirow_finite_sum_ext; intros i Hi.
      destruct (multirow_row_observables_regular n m beta gamma y B Y S t i Hb Hg HY HS (Hrow i Hi))
        as [HCV [HCR [CV [CR [HBV HBR]]]]].
      exact (proj2 (proj2 (gaussian_row_full_stein_of_regular n m beta gamma y B Y S t i CV CR
        (Hrow i Hi) Hb Hg HY HS Ht Hsym HCV HBV HCR HBR))).
    + apply multirow_finite_sum_scale.
Qed.
