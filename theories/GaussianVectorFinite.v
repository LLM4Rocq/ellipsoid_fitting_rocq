From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  VectorCoordinateDefinitions GaussianProductDefinitions GaussianProduct
  GaussianVectorDefinitions GaussianVectorDomain GaussianVectorAlgebra.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Scaling and finite double sums for gaussian_vector_domain and
   gaussian_vector_expectation (GaussianVectorDefinitions).
   gaussian_vector_domain_scale: the domain is stable under scaling.
   gaussian_vector_coordinate_double_sum: the expectation of a double sum
   of integrable functions is the double sum of their expectations.
   gaussian_vector_polynomial_double_sum_domain: the same for continuous
   terms bounded by C * (1 + |x|) ^ p, with |x| the Euclidean norm, whose
   double sum then satisfies gaussian_vector_domain. Indices are compared
   with Stdlib's order le, written (a <= m)%coq_nat. *)

Lemma gaussian_vector_domain_scale n f c :
  gaussian_vector_domain n f -> gaussian_vector_domain n (fun x => c * f x).
Proof.
  intros [HI [HA _]]; apply gaussian_vector_domain_pullback.
  - exact (proj1 (gaussian_vector_scale n f c HI)).
  - apply gaussian_iterated_integrable_ext with
      (F := fun xs => Rabs c * Rabs (f (vector_of_list n xs))).
    + intros xs Hxs; rewrite Rabs_mult; reflexivity.
    + exact (proj1 (gaussian_iterated_scale (S n)
        (fun xs => Rabs (f (vector_of_list n xs))) (Rabs c) HA)).
Qed.

Lemma gaussian_vector_coordinate_double_sum n m k (F : nat -> nat -> vector n -> R) :
  (forall a b, (a <= m)%coq_nat -> (b <= k)%coq_nat -> gaussian_vector_integrable n (F a b)) ->
  gaussian_vector_integrable n (fun x => coordinate_sum m (fun a => coordinate_sum k (fun b => F a b x))) /\
  gaussian_vector_expectation n (fun x => coordinate_sum m (fun a => coordinate_sum k (fun b => F a b x))) =
    coordinate_sum m (fun a => coordinate_sum k (fun b => gaussian_vector_expectation n (F a b))).
Proof.
  intro HF.
  assert (Hinner : forall a, (a <= m)%coq_nat ->
    gaussian_vector_integrable n (fun x => coordinate_sum k (fun b => F a b x)) /\
    gaussian_vector_expectation n (fun x => coordinate_sum k (fun b => F a b x)) =
      coordinate_sum k (fun b => gaussian_vector_expectation n (F a b))).
  { intros a Ha; apply gaussian_vector_coordinate_sum; intros b Hb; apply HF; assumption. }
  destruct (gaussian_vector_coordinate_sum n m
    (fun a x => coordinate_sum k (fun b => F a b x))
    ltac:(intros a Ha; exact (proj1 (Hinner a Ha)))) as [HI HE].
  split; [exact HI|]; rewrite HE; apply coordinate_sum_ext; intros a Ha; apply Hinner; exact Ha.
Qed.

Theorem gaussian_vector_polynomial_double_sum_domain n m k p (F : nat -> nat -> vector n -> R) :
  (forall a b, (a <= m)%coq_nat -> (b <= k)%coq_nat -> forall x, {for x, continuous (F a b)}) ->
  (forall a b, (a <= m)%coq_nat -> (b <= k)%coq_nat -> exists C : R, 0 <= C /\
    forall x, Rabs (F a b x) <= C * (1 + (`|x|)%R)^p) ->
  gaussian_vector_domain n (fun x => coordinate_sum m (fun a => coordinate_sum k (fun b => F a b x))) /\
  gaussian_vector_expectation n (fun x => coordinate_sum m (fun a => coordinate_sum k (fun b => F a b x))) =
    coordinate_sum m (fun a => coordinate_sum k (fun b => gaussian_vector_expectation n (F a b))).
Proof.
  intros HC HB; split.
  - apply (proj1 (gaussian_vector_polynomial_sum_domain n m p
      (fun a x => coordinate_sum k (fun b => F a b x)) ltac:(
        intros a Ha; apply gaussian_vector_coordinate_sum_continuous;
        intros b Hb; apply HC; assumption) ltac:(
        intros a Ha; apply gaussian_vector_coordinate_sum_polynomial;
        intros b Hb; apply HB; assumption))).
  - apply (proj2 (gaussian_vector_coordinate_double_sum n m k F ltac:(
      intros a b Ha Hb; destruct (HB a b Ha Hb) as [C [HC0 Hbound]];
      exact (proj1 (gaussian_vector_polynomial_domain n (F a b) C p
        (HC a b Ha Hb) HC0 Hbound))))).
Qed.
