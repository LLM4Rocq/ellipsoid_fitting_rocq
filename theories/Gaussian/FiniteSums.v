(* Finite sums of functions of d Gaussian coordinates.
   - finite_joint_continuous_sum and finite_polynomial_bound_sum: a finite
     sum of jointly continuous functions, or of functions with polynomial
     bounds of degree p, has the same property.
   - gaussian_iterated_finite_sum: the iterated Gaussian expectation is
     linear on finite sums of integrable functions.
   - gaussian_finite_polynomial_sum: a finite sum of jointly continuous
     functions with polynomial bounds of degree p is jointly continuous,
     has such a bound, belongs to gaussian_list_domain, and its expectation
     is the sum of theirs.
   Each level of the iterated expectation is a Lebesgue integral over the
   line against the Gaussian kernel. *)

From Stdlib Require Import Reals List Lra.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.IteratedExpectationDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Joint.Definitions.
From EllipsoidFitting Require Import Gaussian.IteratedExpectation
  Analysis.CoordinateTopology Gaussian.CoordinateWeights
  Gaussian.CoordinatePolynomialContinuity Gaussian.CoordinatePolynomialDomain.
Import ListNotations.
Open Scope R_scope.

Lemma finite_joint_continuous_sum d I (F : nat -> list R -> R) :
  (forall i, In i I -> finite_joint_continuous d (F i)) ->
  finite_joint_continuous d (fun xs => finite_sum (fun i => F i xs) I).
Proof.
  induction I as [|i I IH]; intros HC; cbn [finite_sum].
  - apply finite_joint_continuous_constant.
  - apply finite_joint_continuous_add; [apply HC; simpl; auto|].
    apply IH; intros j Hj; apply HC; simpl; auto.
Qed.

Lemma finite_polynomial_bound_sum d I (F : nat -> list R -> R) p :
  (forall i, In i I -> exists C, finite_polynomial_bound d C p (F i)) ->
  exists C, finite_polynomial_bound d C p (fun xs => finite_sum (fun i => F i xs) I).
Proof.
  induction I as [|i I IH]; intros HB; cbn [finite_sum].
  - exists 0; split; [lra|]; intros xs HL; rewrite Rabs_R0, Rmult_0_l; lra.
  - destruct (HB i ltac:(simpl; auto)) as [C HC].
    destruct (IH ltac:(intros j Hj; apply HB; simpl; auto)) as [D HD].
    exists (C+D); apply finite_polynomial_bound_add; assumption.
Qed.

Theorem gaussian_iterated_finite_sum d I (F : nat -> list R -> R) :
  (forall i, In i I -> gaussian_iterated_integrable d (F i)) ->
  gaussian_iterated_integrable d (fun xs => finite_sum (fun i => F i xs) I) /\
  gaussian_iterated_expectation d (fun xs => finite_sum (fun i => F i xs) I) =
    finite_sum (fun i => gaussian_iterated_expectation d (F i)) I.
Proof.
  induction I as [|i I IH]; intros HF; cbn [finite_sum].
  - exact (gaussian_iterated_constant d 0).
  - destruct (IH ltac:(intros j Hj; apply HF; simpl; auto)) as [HI HE].
    destruct (gaussian_iterated_add d (F i) (fun xs => finite_sum (fun j => F j xs) I)
      (HF i ltac:(simpl; auto)) HI) as [HS HSum].
    split; [exact HS|rewrite HSum, HE; reflexivity].
Qed.

Theorem gaussian_finite_polynomial_sum d I (F : nat -> list R -> R) p :
  (forall i, In i I -> exists C,
    finite_joint_continuous d (F i) /\ finite_polynomial_bound d C p (F i)) ->
  exists C,
    finite_joint_continuous d (fun xs => finite_sum (fun i => F i xs) I) /\
    finite_polynomial_bound d C p (fun xs => finite_sum (fun i => F i xs) I) /\
    gaussian_list_domain d (fun xs => finite_sum (fun i => F i xs) I) /\
    gaussian_iterated_expectation d (fun xs => finite_sum (fun i => F i xs) I) =
      finite_sum (fun i => gaussian_iterated_expectation d (F i)) I.
Proof.
  intro HF.
  assert (HC : finite_joint_continuous d (fun xs => finite_sum (fun i => F i xs) I)).
  { apply finite_joint_continuous_sum; intros i Hi.
    destruct (HF i Hi) as [C [HC HB]]; exact HC. }
  destruct (finite_polynomial_bound_sum d I F p
    ltac:(intros i Hi; destruct (HF i Hi) as [C [HCi HBi]]; exists C; exact HBi)) as [C HB].
  exists C; split; [exact HC|]; split; [exact HB|]; split.
  - exact (gaussian_coordinate_polynomial_domain d _ C p HC HB).
  - apply (proj2 (gaussian_iterated_finite_sum d I F ltac:(
      intros i Hi; destruct (HF i Hi) as [D [HCi HBi]];
      exact (proj1 (gaussian_coordinate_polynomial_domain d (F i) D p HCi HBi))))).
Qed.
