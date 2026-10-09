(* The coordinate tensorization of the variance fails for the latent-sign
   law, with constants that grow with the dimension. Over the definitions
   of LatentSignScope, LatentSignDefinitions, PairedDefinitions,
   UniversalityDefinitions and the frozen PaperMainDefinitions: the note
   notes/phase6-three-extensions.md, section 2.3, (12) to (14), in the form
   of item R2 of notes/optional-items-plan.md.

   This file holds the definitions and the statement.

   Setting. As in LatentSignScope: 0 <= s <= 1, mu the uniform law on
   [-sqrt 3, sqrt 3] (any law with paired_uniform_spec), h = paired_kernel
   the rescaled Legendre polynomial P_4. A point x of R^d is a sample of
   one point (paper_main_sample 1 d), with coordinates
   x_j = List.nth j (tval x) 0 for j < d. Under the latent-sign law a point
   has the density rho(x) = latent_sample_density s 1 d x =
   (prod_j (1 + s h(x_j)) + prod_j (1 - s h(x_j))) / 2 against the product
   of d copies of mu, and latent_point_expectation s mu d f is E f(X)
   (LatentSignScope).

   1. Conditioning on the other coordinates. latent_replace d j x y is the
      point x with its coordinate j replaced by y. Given the coordinates
      X_k, k != j, the coordinate X_j has the density
      y |-> rho(x with x_j := y) / int rho(x with x_j := y') dmu(y')
      against mu, the conditional density of the law. The conditional
      expectation of g given the other coordinates, at the point x,
      latent_cond_expectation s mu d j g x, is the integral of g against
      it: int g(x with x_j := y) rho(x with x_j := y) dmu(y) divided by
      int rho(x with x_j := y) dmu(y). It does not depend on x_j. Where
      the denominator is 0 (a null set), it is 0, since x / 0 = 0 in
      MathComp. latent_cond_variance s mu d j f x is
      E[f^2 | X_k, k != j] - E[f | X_k, k != j]^2 at x, and
      latent_variance s mu d f is Var f(X) = E f(X)^2 - (E f(X))^2.
   2. The tensorization inequality (12) with the constant T:
      latent_tensorization s mu d T says that for every bounded measurable
      f, Var f(X) <= T sum_(j < d) E Var(f(X) | X_k, k != j).

   latent_tensorization_statement:
   1. for d >= 1 and every s in [0, 1], every constant T of (12) has
      T >= 1 + (d - 1) s^2 / 9 (from f = sum_j h(x_j));
   2. there are absolute constants c > 0 and c' > 0 such that, for every
      fixed s in (0, 1], every large d (depending on s) and every constant
      T of (12), T >= (c' / d) exp(c s^2 (d - 1)) (from
      f = 1{sum_j h(x_j) > 0}).
   So the constants of (12) grow with d whenever d s^2 is unbounded, and
   exponentially for fixed s > 0, although latent_sign_statement holds for
   these laws.

   Choices, for the reviewer. The conditional law is given by its density,
   which is the usual conditional density of a law with a density against
   a product law; (12) is asked for the bounded measurable functions, a
   class that contains the two test functions, so the statement bounds the
   best constant over that class. In part 2 the constants c and c' are
   chosen before s, and the dimension threshold after s.

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
Open Scope ring_scope.

(* 1. The point x with its coordinate j replaced by y. *)
Definition latent_replace (d j : nat) (x : paper_main_sample 1 d)
    (y : measurableTypeR R) : paper_main_sample 1 d :=
  [tuple if (k == j :> nat) then y else tnth x k | k < 1 * d].

(* The conditional expectation of g given the coordinates other than j, at
   the point x: the integral of g against the conditional density of the
   coordinate j. *)
Definition latent_cond_expectation (s : R)
    (mu : probability (measurableTypeR R) R) (d j : nat)
    (g : paper_main_sample 1 d -> R) (x : paper_main_sample 1 d) : R :=
  (\int[mu]_y (g (latent_replace d j x y) *
               latent_sample_density s 1 d (latent_replace d j x y))) /
  (\int[mu]_y latent_sample_density s 1 d (latent_replace d j x y)).

(* The conditional variance of f given the coordinates other than j. *)
Definition latent_cond_variance (s : R)
    (mu : probability (measurableTypeR R) R) (d j : nat)
    (f : paper_main_sample 1 d -> R) (x : paper_main_sample 1 d) : R :=
  latent_cond_expectation s mu d j (fun z => f z ^+ 2) x -
  latent_cond_expectation s mu d j f x ^+ 2.

(* The variance of f(X) for one point X of the latent-sign law. *)
Definition latent_variance (s : R) (mu : probability (measurableTypeR R) R)
    (d : nat) (f : paper_main_sample 1 d -> R) : R :=
  latent_point_expectation s mu d (fun x => f x ^+ 2) -
  latent_point_expectation s mu d f ^+ 2.

(* 2. (12) with the constant T, for every bounded measurable f. *)
Definition latent_tensorization (s : R)
    (mu : probability (measurableTypeR R) R) (d : nat) (T : R) : Prop :=
  forall f : paper_main_sample 1 d -> R,
    measurable_fun [set: paper_main_sample 1 d]
      (f : paper_main_sample 1 d -> measurableTypeR R) ->
    (exists M : R, forall x, `|f x| <= M) ->
    latent_variance s mu d f <=
    T * \sum_(j < d)
          latent_point_expectation s mu d (latent_cond_variance s mu d j f).

(* (13) and (14): lower bounds on every constant of (12). *)
Definition latent_tensorization_statement : Prop :=
  (forall (s : R) (mu : probability (measurableTypeR R) R) (d : nat) (T : R),
     0 <= s <= 1 -> paired_uniform_spec mu -> (0 < d)%nat ->
     latent_tensorization s mu d T ->
     1 + (d%:R - 1) * s ^+ 2 / 9%:R <= T) /\
  (exists c c' : R, 0 < c /\ 0 < c' /\
   forall (s : R) (mu : probability (measurableTypeR R) R),
     0 < s <= 1 -> paired_uniform_spec mu ->
     exists D : nat, forall (d : nat) (T : R), (D <= d)%nat ->
       latent_tensorization s mu d T ->
       c' / d%:R * expR (c * s ^+ 2 * (d%:R - 1)) <= T).
