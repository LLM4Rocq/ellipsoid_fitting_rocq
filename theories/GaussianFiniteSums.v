(* Port of theories/GaussianFiniteSums.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The proofs are the original ones, word for word. The
   changes are in the import lines only.
   - "From Coquelicot Require Import Coquelicot." is dropped: no statement or
     proof here names a Coquelicot notion. Tn and close_n, which
     finite_joint_continuous uses, come from the port of
     GaussianCoordinateDefinitions.
   - The original imported the bundle GaussianCoordinateProofs and named its
     inner modules GaussianProduct, GaussianCoordinateTopology,
     GaussianCoordinateWeights, GaussianCoordinatePolynomialContinuity and
     GaussianCoordinateSteinDomains through it. Here the standalone ported
     modules of the same names are imported directly, in the same order.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So the notations, the arithmetic on R, the lists (In) and
   the tactic syntax are Stdlib's, as in the original.

   The meaning of the statements follows the ported definitions they use.
   finite_sum (SoftDefinitions), finite_joint_continuous
   (GaussianCoordinateDefinitions) and finite_polynomial_bound
   (GaussianCoordinateWeightDefinitions) have their original texts, so
   finite_joint_continuous_sum and finite_polynomial_bound_sum say what they
   said. gaussian_iterated_integrable and gaussian_iterated_expectation
   (GaussianProductDefinitions), and through them gaussian_list_domain
   (JointDefinitions), now use at each level Lebesgue integrability over the
   line and the Lebesgue integral against the Gaussian kernel, in place of
   Coquelicot's improper Riemann integral (difference 4 of
   analysis/README.md). gaussian_iterated_finite_sum and
   gaussian_finite_polynomial_sum keep their text in that vocabulary and gain
   no hypothesis. For gaussian_finite_polynomial_sum every function
   integrated is continuous and bounded by a constant times a polynomial
   weight, hence absolutely integrable against the kernel, where the two
   meanings agree. gaussian_iterated_finite_sum is linearity of the iterated
   integral under its integrability hypothesis, in either meaning. This
   agreement is a mathematical argument and is not proved in Rocq. No
   statement is weakened. *)

From Stdlib Require Import Reals List Lra.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions JointDefinitions.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateTopology
  GaussianCoordinateWeights GaussianCoordinatePolynomialContinuity
  GaussianCoordinateSteinDomains.
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
