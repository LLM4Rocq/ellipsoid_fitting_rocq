(* The glossary of the finite-mixture extension of the universality theorem
   of Koehler and Sohn ("Universality and sharp thresholds for ellipsoid
   fitting", arXiv 2608.27372, Theorem 1.2): exact fitting for i.i.d. points
   whose law is, at each dimension d, a finite mixture of product laws
   (the note notes/mixture-product-universality.md, assumptions (M1)-(M3);
   the plan notes/paired-law-plan-v2.md, section 4.1). Every definition is
   concrete and is meant to be read by the reviewer; the comment of
   MixtureStatement reads the statement. This module reuses the definitions
   of PaperMainDefinitions that do not depend on the law (the quadratic
   form, symmetry, the trace, the samples and their points) and those of
   UniversalityDefinitions (the moment functions of a coordinate law).

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope, as in PaperMainDefinitions and UniversalityDefinitions.
   tuple_prod mu n is the law of n independent coordinates with laws
   mu 0, ..., mu (n-1) (library, probability/lindeberg.v), the construction
   of universality_sample_law. 'E_mu[f] is the expectation of
   MathComp-Analysis, an extended real. ln is the logarithm of
   MathComp-Analysis.

   1. Component laws, (M2). A law mu on the line is a component law with
      subgaussian constant K when E X = 0, E X^2 = 1 and
      E exp (X^2 / K^2) <= 2: universality_coordinate_law without the
      condition on the fourth moment.
   2. Families of mixtures, (M1)-(M3). For every dimension d there are
      N d components, numbered 0, ..., N d - 1, with weights w d s >= 0 of
      sum one, and component s has independent coordinates, coordinate j
      (j < d) with law mu d s j; the law of a point is the mixture
      nu_d = sum_s w d s (mu d s 0 (x) ... (x) mu d s (d - 1)). N is an
      arbitrary function of d. mixture_family K N w mu asks (M1) and (M2)
      for every component (components of weight zero may be dropped, so
      this loses nothing); mixture_fourth_moment kappa N w mu asks (M3):
      under the mixture, every coordinate has fourth moment kappa.
   3. The sample. The n points are independent with law nu_d. Their law is
      written through labels: point i has a label s_i < N, the labels are
      independent with weights w, and given the labels the n * d
      coordinates are independent, coordinate j of point i with law
      mu s_i j. As in universality_sample_law and paper_main_point,
      coordinate k of the tuple is coordinate k mod d of point k / d.
      mixture_labelled_law is the law of the sample given the tuple s of
      labels, and mixture_probability the probability of a set of samples:
      the average over the label tuples, with the product weights, of
      their labelled laws. This is the n-fold product of nu_d, expanded by
      distributivity; with one component it is universality_sample_law.
   4. Exact interpolation of residuals (KS Theorem 1.9; the note, (M12)).
      With W_i = (x_i x_i^T - I) / sqrt d, so that
      <W_i, Delta> = (x_i^T Delta x_i - tr Delta) / sqrt d,
      mixture_interpolation n d C x says: every y in R^n is (<W_i, Delta>)_i
      up to a constant b, for a symmetric Delta whose operator norm,
      written through the quadratic form (|v^T Delta v| <= B v^T v for
      every v), is at most C (|y|_2 / d + (ln d)^4 |y|_oo / sqrt d). For y
      in the range of the centered map A_X this is A_X Delta = y.

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences exp.
From GaussianAnalysis Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. Component laws, (M2). *)

(* mu has mean 0, variance 1 and E exp (X^2 / K^2) <= 2. *)
Definition mixture_component_law (K : R)
    (mu : probability (measurableTypeR R) R) : Prop :=
  0 < K /\
  ('E_mu[universality_power 1])%E = 0%:E /\
  ('E_mu[universality_power 2])%E = 1%:E /\
  (('E_mu[universality_subgaussian_test K])%E <= (2%:R)%:E)%E.

(* 2. Families of mixtures. *)

(* (M1) and (M2): for every dimension d, N d components with weights
   w d s >= 0 of sum one, and coordinate laws mu d s j that are component
   laws with constant K, for s < N d and j < d. *)
Definition mixture_family (K : R) (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) : Prop :=
  forall d : nat,
    (forall s : nat, (s < N d)%N -> 0 <= w d s) /\
    \sum_(s < N d) w d s = 1 /\
    (forall s j : nat, (s < N d)%N -> (j < d)%N ->
       mixture_component_law K (mu d s j)).

(* (M3): under the mixture, every coordinate has fourth moment kappa. *)
Definition mixture_fourth_moment (kappa : R) (N : nat -> nat)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) : Prop :=
  forall d j : nat, (j < d)%N ->
    (\sum_(s < N d) (w d s)%:E * 'E_(mu d s j)[universality_power 4])%E =
    kappa%:E.

(* 3. The sample. *)

(* The label of point i in a tuple s of labels, as a natural number; 0
   past the end of the tuple. *)
Definition mixture_label {n N : nat} (s : n.-tuple 'I_N) (i : nat) : nat :=
  nth 0%N (map val s) i.

(* The law of a sample of n points of R^d given the labels s of the points:
   the n * d coordinates are independent, and coordinate k, which is
   coordinate k mod d of point k / d, has law mu (s_(k / d)) (k mod d). *)
Definition mixture_labelled_law (N : nat)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (n d : nat)
    (s : n.-tuple 'I_N) : probability (paper_main_sample n d) R :=
  tuple_prod (fun k => mu (mixture_label s (k %/ d)%N) (k %% d)%N) (n * d).

(* The probability of a set E of samples of n i.i.d. points whose law is
   the mixture with weights w and components mu: the labels s_1, ..., s_n
   are independent, each equal to t < N with probability w t, and given
   the labels the sample has the law mixture_labelled_law. An extended
   real; it is in [0, 1] for a measurable E when the weights are
   nonnegative of sum one. *)
Definition mixture_probability (N : nat) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (n d : nat)
    (E : set (paper_main_sample n d)) : \bar R :=
  (\sum_(s : n.-tuple 'I_N)
     (\prod_(i < n) w (tnth s i))%:E * mixture_labelled_law N mu n d s E)%E.

(* 4. Exact interpolation of residuals. *)

(* Every y in R^n is (<W_i, Delta>)_i up to a constant b, where
   <W_i, Delta> = (x_i^T Delta x_i - tr Delta) / sqrt d, for a symmetric
   Delta with |v^T Delta v| <= C (|y|_2 / d + (ln d)^4 |y|_oo / sqrt d) v^T v
   for every v. *)
Definition mixture_interpolation (n d : nat) (C : R)
    (x : paper_main_sample n d) : Prop :=
  forall y : 'I_n -> R, exists (Delta : 'M[R]_d) (b : R),
    [/\ paper_main_symmetric Delta,
        forall i : 'I_n,
          (paper_main_quadratic_form Delta (paper_main_point x i)
             - paper_main_trace Delta) / Num.sqrt d%:R = y i + b &
        forall v : 'cV[R]_d,
          `|paper_main_quadratic_form Delta v| <=
          C * (Num.sqrt (\sum_(i < n) y i ^+ 2) / d%:R
               + ln (d%:R : R) ^+ 4 / Num.sqrt d%:R
                 * \big[Num.max/0]_(i < n) `|y i|)
            * paper_main_quadratic_form 1%:M v].
