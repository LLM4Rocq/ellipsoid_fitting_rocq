(* The glossary of the countable-mixture extension of the finite-mixture
   theorem (MixtureStatement): exact fitting for i.i.d. points whose law
   is, at each dimension d, a mixture of countably many product laws
   (notes/phase6-three-extensions.md, section 3.1; the plan
   notes/three-extensions-plan.md, section 4.1). Every definition is
   concrete and is meant to be read by the reviewer; the comment of
   CountableMixtureStatement reads the statement. This module reuses the
   component laws of MixtureDefinitions, the moment functions of
   UniversalityDefinitions and the samples of PaperMainDefinitions, and
   follows MixtureDefinitions definition by definition, with natural
   numbers as labels.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope, as in MixtureDefinitions. tuple_prod mu n is the law of n
   independent coordinates with laws mu 0, ..., mu (n-1) (library,
   probability/lindeberg.v). 'E_mu[f] is the expectation of
   MathComp-Analysis, an extended real. \sum_(s <oo) a s is the series of
   MathComp-Analysis in the extended reals: the limit of the partial sums,
   for nonnegative terms their least upper bound. \esum_(s in S) a s is the
   sum of a family of extended reals indexed by a set S: for nonnegative
   terms, the least upper bound of the sums over the finite subsets of S,
   which does not depend on any order of S.

   1. Families of countable mixtures, (M1) and (M2). For every dimension d
      the components are numbered by all the natural numbers s, with
      weights w d s >= 0 of sum one, and component s has independent
      coordinates, coordinate j (j < d) with law mu d s j; the law of a
      point is the mixture nu_d = sum_s w d s (mu d s 0 (x) ... (x)
      mu d s (d - 1)). countable_mixture_family K w mu asks that every
      component law mu d s j be a component law with constant K
      (mixture_component_law of MixtureDefinitions: mean 0, variance 1,
      E exp (X^2 / K^2) <= 2), for every s, as mixture_family does for
      every s < N d.
   2. (M3). countable_fourth_moment kappa w mu: under the mixture, every
      coordinate has fourth moment kappa, the series of the weighted
      fourth moments of the components.
   3. The sample. The n points are independent with law nu_d. As in
      MixtureDefinitions, their law is written through labels: point i has
      a label s_i, a natural number, the labels are independent with
      weights w, and given the labels the n * d coordinates are
      independent, coordinate j of point i with law mu s_i j; coordinate k
      of the tuple is coordinate k mod d of point k / d, as in
      paper_main_point. countable_labelled_law is the law of the sample
      given the tuple s of labels (mixture_labelled_law with labels in nat),
      and countable_mixture_probability the probability of a set of
      samples: the sum, over all the tuples of labels, of their product
      weight times their labelled law. For nonnegative weights all the
      terms are nonnegative, so the sum is the ordinary sum of the family,
      in any order. With weights zero from N d on, it is
      mixture_probability (N d) (a lemma of the proof).

   The module contains definitions only: no lemma, no Axiom, no Parameter,
   no Admitted. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution sequences esum.
From GaussianAnalysis Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. Families of countable mixtures, (M1) and (M2). *)

(* For every dimension d, weights w d s >= 0 of sum one, s ranging over the
   natural numbers, and coordinate laws mu d s j that are component laws
   with constant K, for every s and every j < d. *)
Definition countable_mixture_family (K : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) : Prop :=
  forall d : nat,
    (forall s : nat, 0 <= w d s) /\
    (\sum_(s <oo) (w d s)%:E = 1%:E)%E /\
    (forall s j : nat, (j < d)%N -> mixture_component_law K (mu d s j)).

(* 2. (M3): under the mixture, every coordinate has fourth moment kappa. *)
Definition countable_fourth_moment (kappa : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) : Prop :=
  forall d j : nat, (j < d)%N ->
    (\sum_(s <oo) (w d s)%:E * 'E_(mu d s j)[universality_power 4])%E =
    kappa%:E.

(* 3. The sample. *)

(* The law of a sample of n points of R^d given the labels s of the points:
   the n * d coordinates are independent, and coordinate k, which is
   coordinate k mod d of point k / d, has law mu (s_(k / d)) (k mod d). *)
Definition countable_labelled_law
    (mu : nat -> nat -> probability (measurableTypeR R) R) (n d : nat)
    (s : n.-tuple nat) : probability (paper_main_sample n d) R :=
  tuple_prod (fun k => mu (nth 0%N s (k %/ d)%N) (k %% d)%N) (n * d).

(* The probability of a set E of samples of n i.i.d. points whose law is
   the countable mixture with weights w and components mu: the labels
   s_1, ..., s_n are independent, each equal to t with probability w t,
   and given the labels the sample has the law countable_labelled_law. An
   extended real; it is in [0, 1] for a measurable E when the weights are
   nonnegative of sum one. *)
Definition countable_mixture_probability (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (n d : nat)
    (E : set (paper_main_sample n d)) : \bar R :=
  (\esum_(s in [set: n.-tuple nat])
     (\prod_(i < n) w (tnth s i))%:E * countable_labelled_law mu n d s E)%E.
