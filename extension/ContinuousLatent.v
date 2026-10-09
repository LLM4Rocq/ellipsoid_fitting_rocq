(* A continuous latent mixture that is not close to any countable mixture
   of product laws: the counterexample (18) of
   notes/phase6-three-extensions.md, section 3.3, in the form of item R3 of
   notes/optional-items-plan.md. Over the definitions of RobustDefinitions
   (the point law of a countable mixture, the total variation distance) and
   the frozen PaperMainDefinitions.

   This file holds the definitions and the statement.

   The law. The latent parameter a is uniform on [1, 2]. Given a, the d
   coordinates of a point are independent, each equal to a with probability
   1 / (1 + a^2) and to -1/a with probability a^2 / (1 + a^2).
   1. cl_value a b and cl_weight a b: the two values of a coordinate and
      their probabilities, b = true for a and b = false for -1/a.
   2. cl_moment a k: the k-th moment of the component law,
      sum_b cl_weight a b * cl_value a b ^ k, a sum of two terms.
   3. cl_point_law d: the law of one point, on d.-tuple as in
      RobustDefinitions. For a set A of points, it is the integral over a
      in [1, 2], against Lebesgue measure, of the sum over the sign
      patterns v in {true, false}^d of prod_j cl_weight a v_j times the
      indicator that the point (cl_value a v_j)_j lies in A.

   continuous_latent_statement:
   1. for a in [1, 2], the component law has total mass 1, mean 0,
      variance 1 and fourth moment a^2 - 1 + a^-2, and its two values are
      at most 2 in absolute value;
   2. the average of the fourth moments over a uniform on [1, 2] is 11/6,
      so the coordinates have unconditional fourth moment 11/6;
   3. for d >= 2, cl_point_law d has total mass 1 and is at total variation
      distance 1 from the point law of every countable mixture of product
      laws (weights w s >= 0 of sum one, arbitrary probabilities mu s j on
      R as coordinate laws): the two laws are singular.
   So the components satisfy (M2), the mixture satisfies (M3) with
   kappa = 11/6, and yet no countable family is close to it in total
   variation: the transfer of RobustStatement does not reach this law.

   Choices, for the reviewer. The component facts are written with the
   explicit two-point sums rather than with integrals; part 3 uses no
   moment assumption on the mixtures, which makes it stronger.

   The arithmetic, the order and the numerals are MathComp's at Stdlib's
   R (ring_scope). *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct interval.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability normal_distribution sequences.
From GaussianAnalysis Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions.
Open Scope ring_scope.

(* 1. The two values of a coordinate given a, and their probabilities. *)
Definition cl_value (a : R) (b : bool) : R := if b then a else - a^-1.

Definition cl_weight (a : R) (b : bool) : R :=
  if b then (1 + a ^+ 2)^-1 else a ^+ 2 / (1 + a ^+ 2).

(* 2. The k-th moment of the component law. *)
Definition cl_moment (a : R) (k : nat) : R :=
  \sum_(b : bool) cl_weight a b * cl_value a b ^+ k.

(* 3. The law of one point: a uniform on [1, 2], then independent
   coordinates with the component law of a. *)
Definition cl_point_law (d : nat) (A : set (d.-tuple (measurableTypeR R))) :
    \bar R :=
  (\int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
     (\sum_(v : d.-tuple bool)
        (\prod_(j < d) cl_weight a (tnth v j))%:E *
        (\1_A [tuple (cl_value a (tnth v j) : measurableTypeR R) | j < d])%:E))%E.

(* (18): the components, the average fourth moment, and the singularity
   with respect to every countable mixture of product laws. *)
Definition continuous_latent_statement : Prop :=
  [/\ forall a : R, 1 <= a <= 2%:R ->
        [/\ cl_moment a 0 = 1, cl_moment a 1 = 0, cl_moment a 2 = 1,
            cl_moment a 4 = a ^+ 2 - 1 + a ^- 2 &
            forall b : bool, `|cl_value a b| <= 2%:R],
      \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
        ((a : R) ^+ 2 - 1 + (a : R) ^- 2) = 11%:R / 6%:R &
      forall d : nat, (2 <= d)%nat ->
        cl_point_law d setT = 1%E /\
        forall (w : nat -> R)
               (mu : nat -> nat -> probability (measurableTypeR R) R),
          (forall s : nat, 0 <= w s) -> (\sum_(s <oo) (w s)%:E = 1%:E)%E ->
          robust_tv d (cl_point_law d) (robust_point_law w mu d) = 1%E].
