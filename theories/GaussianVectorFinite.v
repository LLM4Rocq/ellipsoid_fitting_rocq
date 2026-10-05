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

(* Port of the inner module GaussianVectorFinite of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/GaussianVectorFinite.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundle GaussianCoordinateProofs and named its
   inner module GaussianProduct through it. The port imports the standalone
   ported module GaussianProduct directly.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. The statements change form in three ways, none of which changes
   their meaning.

   1. Indices. With ssreflect loaded, (a <= m)%nat would be ssrnat's boolean
      leq. The statements write (a <= m)%coq_nat, which is Stdlib's Peano
      order le, as in the original. This concerns
      gaussian_vector_coordinate_double_sum and
      gaussian_vector_polynomial_double_sum_domain.

   2. Pointwise continuity. Coquelicot's continuous f x, continuity of f at
      the one point x, becomes MathComp's {for x, continuous f} (difference 5
      of analysis/README.md), in gaussian_vector_polynomial_double_sum_domain.
      This is the form of the hypothesis of the ported
      gaussian_vector_polynomial_domain and
      gaussian_vector_polynomial_sum_domain.

   3. Norms. Coquelicot's norm x becomes MathComp's (`|x|)%R, in
      gaussian_vector_polynomial_double_sum_domain. The vectors nest
      euclidean_product of MatrixEuclideanProduct, so this is still the
      Euclidean norm and the polynomial bounds C * (1 + norm x) ^ p keep
      their constants.

   gaussian_vector_domain_scale keeps its text. The meaning of
   gaussian_vector_integrable, gaussian_vector_expectation and
   gaussian_vector_domain follows the ported GaussianVectorDefinitions
   (difference 4 of analysis/README.md): at each level of the iterated
   expectation, Lebesgue integrability over the line against the Gaussian
   kernel, and Lebesgue integrals, in place of improper Riemann integrals.
   The lemmas below hold for this reading, by the ported GaussianProduct,
   GaussianVectorDomain and GaussianVectorAlgebra.

   The proofs are the original ones, with the index hypotheses written
   %coq_nat.

   Assumptions. gaussian_vector_domain_scale and
   gaussian_vector_coordinate_double_sum rest on the seven axioms of
   analysis/README.md only. gaussian_vector_polynomial_double_sum_domain
   also rests on Classical_Prop.classic, which it inherits from the ported
   gaussian_vector_polynomial_domain of GaussianVectorDomain. *)

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
