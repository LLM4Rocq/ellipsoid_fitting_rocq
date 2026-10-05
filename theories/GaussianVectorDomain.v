From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions VectorCoordinateDefinitions
  VectorCoordinates VectorCoordinateContinuity GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateSteinDomains GaussianVectorDefinitions GaussianVectorGrowth.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module GaussianVectorDomain of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/GaussianVectorDomain.v, from Coquelicot to
   MathComp-Analysis.

   The original imported the bundle GaussianCoordinateProofs and named its
   inner modules GaussianProduct, GaussianCoordinateWeights,
   GaussianCoordinateTopology, GaussianCoordinatePolynomialContinuity and
   GaussianCoordinateSteinDomains through it. The port imports these
   standalone modules directly.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. The statements change form in three ways, none of which changes
   their meaning.

   1. Pointwise continuity. Coquelicot's forall x, continuous f x becomes
      forall x, {for x, continuous f}, continuity at every point
      (difference 5 of analysis/README.md), in
      gaussian_vector_polynomial_domain, gaussian_vector_coordinate_domain and
      gaussian_vector_centered_product_domain. This is the hypothesis of the
      ported vector_continuous_joint and the form of the restated
      ellipsoid_gaussian_matrix challenge. The topology of vector n is the
      product topology, as in Coquelicot.

   2. Norms. Coquelicot's norm x becomes MathComp's (`|x|)%R in the same
      three statements. The vectors nest euclidean_product of
      MatrixEuclideanProduct, so this is still the Euclidean norm and the
      polynomial bounds C * (1 + norm x) ^ p keep their meaning.

   3. Indices. With ssreflect loaded, (i <= n)%nat would be ssrnat's boolean
      leq. The statements write (i <= n)%coq_nat, which is Stdlib's le, as in
      the original. In the proofs, nth is written List.nth.

   gaussian_vector_domain_pullback and gaussian_vector_domain_ext keep their
   text. The meaning of gaussian_vector_domain follows the ported
   GaussianVectorDefinitions (difference 4 of analysis/README.md): at each
   level of the iterated expectation, Lebesgue integrability over the line
   against the Gaussian kernel, in place of improper Riemann integrability.
   The polynomial domain theorems establish this Lebesgue reading, through
   the ported gaussian_coordinate_polynomial_domain. The proofs keep their
   steps; Stdlib's "rewrite ... by tac" is written with explicit arguments,
   since ssreflect's rewrite is loaded. *)

Lemma gaussian_vector_domain_pullback n f :
  gaussian_iterated_integrable (S n) (fun xs => f (vector_of_list n xs)) ->
  gaussian_iterated_absolutely_integrable (S n) (fun xs => f (vector_of_list n xs)) ->
  gaussian_vector_domain n f.
Proof.
  intros HI HA; split; [exact HI|].
  split; [exact HA|]; split;
    apply gaussian_iterated_has_expectation_correct; assumption.
Qed.

Lemma gaussian_vector_domain_ext n f g :
  (forall x, f x = g x) -> gaussian_vector_domain n f -> gaussian_vector_domain n g.
Proof.
  intros He [HI [HA _]]; apply gaussian_vector_domain_pullback.
  - apply gaussian_iterated_integrable_ext with (F := fun xs => f (vector_of_list n xs));
      [intros xs Hxs; apply He|exact HI].
  - apply gaussian_iterated_integrable_ext with (F := fun xs => Rabs (f (vector_of_list n xs)));
      [intros xs Hxs; rewrite He; reflexivity|exact HA].
Qed.

Theorem gaussian_vector_polynomial_domain n f C p :
  (forall x, {for x, continuous f}) -> 0 <= C ->
  (forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^p) ->
  gaussian_vector_domain n f.
Proof.
  intros HC HC0 HB.
  exact (gaussian_coordinate_polynomial_domain (S n)
    (fun xs => f (vector_of_list n xs)) C p
    (vector_continuous_joint n f HC)
    (vector_polynomial_bound_pullback n C p f HC0 HB)).
Qed.

Lemma gaussian_vector_coordinate_domain n i f C p :
  (i <= n)%coq_nat -> (forall x, {for x, continuous f}) -> 0 <= C ->
  (forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^p) ->
  gaussian_vector_domain n (fun x => vector_entry n x i * f x).
Proof.
  intros Hi HC HC0 HB.
  assert (HCF := vector_continuous_joint n f HC).
  assert (HBF := vector_polynomial_bound_pullback n C p f HC0 HB).
  pose proof (gaussian_coordinate_polynomial_domain (S n)
    (fun xs => List.nth i xs 0 * f (vector_of_list n xs)) C (S p)
    (finite_joint_continuous_times_coordinate (S n) _ i HCF ltac:(lia))
    (finite_polynomial_bound_times_coordinate (S n) C p _ i HBF ltac:(lia)))
    as [HI [HA _]].
  apply gaussian_vector_domain_pullback.
  - apply gaussian_iterated_integrable_ext with
      (F := fun xs => List.nth i xs 0 * f (vector_of_list n xs)); [|exact HI].
    intros xs Hxs; rewrite (vector_entry_of_list n xs i Hi); reflexivity.
  - apply gaussian_iterated_integrable_ext with
      (F := fun xs => Rabs (List.nth i xs 0 * f (vector_of_list n xs))); [|exact HA].
    intros xs Hxs; rewrite (vector_entry_of_list n xs i Hi); reflexivity.
Qed.

Theorem gaussian_vector_centered_product_domain n a b f C p :
  (a <= n)%coq_nat -> (b <= n)%coq_nat -> (forall x, {for x, continuous f}) -> 0 <= C ->
  (forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^p) ->
  gaussian_vector_domain n
    (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) * f x).
Proof.
  intros Ha Hb HC HC0 HB.
  pose proof (vector_continuous_joint n f HC) as HCF.
  pose proof (vector_polynomial_bound_pullback n C p f HC0 HB) as HBF.
  destruct (Nat.eq_dec a b) as [He|Hne].
  - subst b; rewrite Nat.eqb_refl.
    pose proof (gaussian_coordinate_polynomial_domain (S n)
      (fun xs => (List.nth a xs 0*List.nth a xs 0-1) * f (vector_of_list n xs)) C (S (S p))
      (finite_joint_continuous_times_centered_square (S n) _ a HCF ltac:(lia))
      (finite_polynomial_bound_times_centered_square (S n) C p _ a HBF ltac:(lia)))
      as [HI [HA _]].
    apply gaussian_vector_domain_pullback.
    + apply gaussian_iterated_integrable_ext with
        (F := fun xs => (List.nth a xs 0*List.nth a xs 0-1)*f (vector_of_list n xs)); [|exact HI].
      intros xs Hxs; rewrite (vector_entry_of_list n xs a Ha); reflexivity.
    + apply gaussian_iterated_integrable_ext with
        (F := fun xs => Rabs ((List.nth a xs 0*List.nth a xs 0-1)*f (vector_of_list n xs)));
        [|exact HA].
      intros xs Hxs; rewrite (vector_entry_of_list n xs a Ha); reflexivity.
  - assert (He : Nat.eqb a b = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite He.
    pose proof (gaussian_coordinate_polynomial_domain (S n)
      (fun xs => List.nth a xs 0*List.nth b xs 0 * f (vector_of_list n xs)) C (S (S p))
      (finite_joint_continuous_times_two_coordinates (S n) _ a b HCF ltac:(lia) ltac:(lia))
      (finite_polynomial_bound_times_two_coordinates (S n) C p _ a b HBF ltac:(lia) ltac:(lia)))
      as [HI [HA _]].
    apply gaussian_vector_domain_pullback.
    + apply gaussian_iterated_integrable_ext with
        (F := fun xs => List.nth a xs 0*List.nth b xs 0*f (vector_of_list n xs)); [|exact HI].
      intros xs Hxs.
      rewrite (vector_entry_of_list n xs a Ha) (vector_entry_of_list n xs b Hb); ring.
    + apply gaussian_iterated_integrable_ext with
        (F := fun xs => Rabs (List.nth a xs 0*List.nth b xs 0*f (vector_of_list n xs))); [|exact HA].
      intros xs Hxs.
      rewrite (vector_entry_of_list n xs a Ha) (vector_entry_of_list n xs b Hb); f_equal; ring.
Qed.
