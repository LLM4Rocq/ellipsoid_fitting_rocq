(* Two scope results for the latent-sign law (LatentSignDefinitions): one
   hidden sign couples all the coordinates of a point, the coupling does
   not decay with the dimension, and a convex 1-Lipschitz function of a
   point has a variance that grows with d. Over the definitions of
   LatentSignDefinitions, PairedDefinitions, UniversalityDefinitions and
   the frozen PaperMainDefinitions: the note
   notes/phase6-three-extensions.md, section 2, (10) and (11), in the form
   of section 4.5 of notes/three-extensions-plan.md.

   This file holds one definition and the statements.

   Setting. 0 <= s <= 1; mu is the uniform law on [-sqrt 3, sqrt 3] (any
   law with paired_uniform_spec); h = paired_kernel is the rescaled
   Legendre polynomial P_4 of PairedDefinitions, with int h dmu = 0 and
   int h^2 dmu = 1/9. A point x of R^d is a sample of one point
   (paper_main_sample 1 d), with coordinates x_j = List.nth j (tval x) 0
   for j < d. Under the latent-sign law a point has the density
   (prod_j (1 + s h(x_j)) + prod_j (1 - s h(x_j))) / 2 against the product
   of d copies of mu: latent_sample_density s 1 d, the frozen density of
   LatentSignDefinitions for a sample of one point.

   latent_point_expectation s mu d f is the expectation of f(x) for one
   point x of the latent-sign law: the integral of f times this density
   against the product of the d copies of mu (universality_sample_law
   (fun=> mu) 1 d). It is the real-valued integral of MathComp-Analysis;
   every f below is bounded on the support, hence integrable.

   latent_covariance_statement, the note's (10): for 0 <= s <= 1 and
   distinct coordinates j, k < d,
   1. x_j has the law mu: P(x_j in A) = mu(A) for every measurable A;
   2. E h(x_j) = 0;
   3. E h(x_j) h(x_k) = s^2 / 81, so Cov(h(x_j), h(x_k)) = s^2 / 81 for
      every d and every pair of distinct coordinates.

   latent_variance_statement, the note's (11): for d >= 1, the function
   F(x) = (|x_1| + ... + |x_d|) / sqrt d, convex and 1-Lipschitz, has
   variance E F^2 - (E F)^2 = 1/4 + (d - 1) s^2 / 768. For a fixed s > 0
   it grows linearly with d, so these laws satisfy no concentration
   inequality for convex 1-Lipschitz functions with a constant
   independent of d, while latent_sign_statement holds for them.

   latent_scope_statement is the conjunction of the two.

   Choices, for the reviewer. The statements are about the law of one
   point, through its density; the n points of a sample are i.i.d. with
   this law. s is fixed (any s in [0, 1]); the variance is written as
   E F^2 - (E F)^2.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions.
Open Scope ring_scope.

(* The expectation of f(x) for one point x of the latent-sign law: the
   integral of f times the density against the product of the d copies
   of mu. *)
Definition latent_point_expectation (s : R)
    (mu : probability (measurableTypeR R) R) (d : nat)
    (f : paper_main_sample 1 d -> R) : R :=
  \int[universality_sample_law (fun=> mu) 1 d]_x
     (f x * latent_sample_density s 1 d x).

(* (10): every coordinate has the law mu, h(x_j) is centered, and two
   distinct coordinates have E h(x_j) h(x_k) = s^2 / 81. *)
Definition latent_covariance_statement : Prop :=
  forall (s : R) (mu : probability (measurableTypeR R) R) (d j k : nat),
    0 <= s <= 1 -> paired_uniform_spec mu -> (j < d)%nat -> (k < d)%nat ->
    j <> k ->
    (forall A : set (measurableTypeR R), measurable A ->
       latent_point_expectation s mu d
         (fun x => \1_A (List.nth j (tval x) 0)) = fine (mu A)) /\
    latent_point_expectation s mu d
      (fun x => paired_kernel (List.nth j (tval x) 0)) = 0 /\
    latent_point_expectation s mu d
      (fun x => paired_kernel (List.nth j (tval x) 0) *
                paired_kernel (List.nth k (tval x) 0)) = s ^+ 2 / 81%:R.

(* (11): F(x) = (sum_j |x_j|) / sqrt d has variance
   1/4 + (d - 1) s^2 / 768. *)
Definition latent_variance_statement : Prop :=
  forall (s : R) (mu : probability (measurableTypeR R) R) (d : nat),
    0 <= s <= 1 -> paired_uniform_spec mu -> (0 < d)%nat ->
    let F := fun x : paper_main_sample 1 d =>
      (\sum_(j < d) `|List.nth j (tval x) 0|) / Num.sqrt d%:R in
    latent_point_expectation s mu d (fun x => F x ^+ 2) -
      latent_point_expectation s mu d F ^+ 2 =
    4%:R^-1 + (d%:R - 1) * s ^+ 2 / 768%:R.

Definition latent_scope_statement : Prop :=
  latent_covariance_statement /\ latent_variance_statement.
