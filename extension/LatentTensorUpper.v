(* A finite constant for the coordinate tensorization of the variance of
   the latent-sign law. Over the definitions of LatentTensorization,
   LatentSignScope, LatentSignDefinitions, PairedDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions: item T of
   phase 10, after section 7.3 of reviews/phase9-release-review.md.

   This file holds the statement only.

   Setting. As in LatentTensorization: 0 <= s <= 1, mu the uniform law on
   [-sqrt 3, sqrt 3] (any law with paired_uniform_spec), h = paired_kernel
   the rescaled Legendre polynomial P_4, and latent_tensorization s mu d T
   the tensorization inequality (12) with the constant T:
   Var f(X) <= T sum_(j < d) E Var(f(X) | X_k, k != j) for every bounded
   measurable f, for one point X of the latent-sign law.

   latent_tensor_constant s d is T_0 = 2 ((1 + s) / (1 - 3 s / 7))^d.
   latent_tensor_upper_statement: for every d, (12) holds with T_0.

   The route, which is not part of the statement. Write Q = mu^d and
   P = rho Q for the law of a point, rho = latent_sample_density s 1 d.
   On the box [-sqrt 3, sqrt 3]^d, which carries Q, -3/7 <= h <= 1 gives
   L = (1/2) (1 - 3 s / 7)^d <= rho <= U = (1 + s)^d, and L > 0 even at
   s = 1. Then Var_P f <= U Var_Q f, and the expected conditional variance
   of f given the coordinates other than j under P is at least L times the
   one under Q, since a conditional variance is the minimum over the
   constants a of the integral of (f - a)^2 against the conditional law.
   The Efron-Stein inequality for the product law Q gives T_0 = U / L.

   With latent_tensorization_statement, the best constant of (12) is at
   least 1 + (d - 1) s^2 / 9, and for a fixed s > 0 and every large d at
   least (c' / d) exp (c s^2 (d - 1)); with this statement it is at most
   T_0. So for every fixed s > 0 it lies between two exponentials in d; the
   statements do not identify the exponential rate.

   Choices, for the reviewer. The constant is explicit and the statement
   holds for every d, d = 0 included (both sides of (12) are then 0). It
   gives an upper bound only, with no claim of optimality.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability normal_distribution sequences trigo.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions.
From EllipsoidUniversality Require Import LatentSignScope.
From EllipsoidUniversality Require Import LatentTensorization.
Open Scope ring_scope.

(* The constant T_0 = 2 ((1 + s) / (1 - 3 s / 7))^d. *)
Definition latent_tensor_constant (s : R) (d : nat) :=
  2%:R * ((1 + s) / (1 - 3%:R * s / 7%:R)) ^+ d.

(* (12) with the constant T_0. *)
Definition latent_tensor_upper_statement : Prop :=
  forall (s : R) (mu : probability (measurableTypeR R) R) (d : nat),
    0 <= s <= 1 -> paired_uniform_spec mu ->
    latent_tensorization s mu d (latent_tensor_constant s d).
