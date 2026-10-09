(* The glossary of the robustness corollary of the mixture theorems: samples
   of i.i.d. points whose law is close in total variation to the point law
   of an admissible mixture family, and the contamination example that
   shows the scale (notes/phase6-three-extensions.md, section 3.2, (17);
   the plan notes/optional-items-plan.md, item R1). Every definition is
   concrete and is meant to be read by the reviewer; the comment of
   RobustStatement reads the statement. This module reuses the samples of
   PaperMainDefinitions and the families of MixtureDefinitions and
   CountableMixtureDefinitions.

   Vocabulary. Stdlib's R is the real field, read through MathComp's
   ring_scope. A point of R^d is a d-tuple of reals, d.-tuple
   (measurableTypeR R), with the product sigma-algebra of the tuples; a law
   of a point is a probability on it. tuple_prod mu n is the law of n
   independent coordinates with laws mu 0, ..., mu (n-1) (library,
   probability/lindeberg.v); here the coordinates may themselves be
   points. \esum_(s in S) a s is the sum of a family of extended reals; for
   nonnegative terms it is the least upper bound of the sums over the
   finite subsets of S. ereal_sup is the least upper bound of a set of
   extended reals. f @` A is the image of the set A under f.

   1. The law of one point of a countable mixture of product laws with
      weights w and component laws mu: robust_point_law w mu d
      = sum_s w s (mu s 0 (x) ... (x) mu s (d - 1)), the law nu_d of
      CountableMixtureDefinitions written on d.-tuple. A finite family is
      the countable one with weights zero from N on (finite_weights).
   2. The total variation distance of two set functions P and Q on the
      points: robust_tv d P Q, the least upper bound of |P A - Q A| over
      the measurable sets A of points. For two probabilities it lies in
      [0, 1].
   3. Samples of an arbitrary point law. A sample x of n points in R^d is
      the (n * d)-tuple of PaperMainDefinitions; point i has the
      coordinates x_(i d + j), j < d, as paper_main_point reads them
      (robust_points n d x lists the n points). The law of a sample of n
      i.i.d. points of law P is robust_sample_law n d P: the probability of
      a set A of samples is the probability, under n independent points of
      law P, that the list of the points is the list of the points of some
      sample in A. For the point law of a countable mixture family, the
      proof of RobustStatement does not identify this law with
      countable_mixture_probability: it compares the two through the
      truncation of the family (Countable/Robust.v, robust_transfer), and
      they differ by at most 2 n r_d on every measurable set of samples,
      where r_d is the tail mass of the truncation.
   4. Closeness at the scale of (17): robust_close w mu P says that
      d^2 times the total variation distance between P d and the point law
      of the family at dimension d tends to 0.
   5. The contamination of a finite family (N, w, mu) with parameter
      lambda, for samples of n points: N + 1 components, the components
      s < N with the weights (1 - lambda / n) w s and their laws, and the
      component N with the weight lambda / n, whose coordinates are 0
      (the Dirac law at 0). Its point law is
      (1 - lambda / n) nu_d + (lambda / n) delta_0, and its samples have the
      law mixture_probability (N + 1) of MixtureDefinitions.

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
From EllipsoidUniversality Require Import CountableMixtureDefinitions.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* 1. The law of one point of a countable mixture of product laws:
   sum_s w s (mu s 0 (x) ... (x) mu s (d - 1)). *)
Definition robust_point_law (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (d : nat)
    (A : set (d.-tuple (measurableTypeR R))) : \bar R :=
  (\esum_(s in [set: nat]) (w s)%:E * tuple_prod (mu s) d A)%E.

(* The weights of a finite family of N components, extended by zero. *)
Definition finite_weights (N : nat) (w : nat -> R) (s : nat) : R :=
  if (s < N)%N then w s else 0.

(* 2. The total variation distance: the least upper bound of |P A - Q A|
   over the measurable sets A of points. *)
Definition robust_tv (d : nat)
    (P Q : set (d.-tuple (measurableTypeR R)) -> \bar R) : \bar R :=
  ereal_sup [set `|(P A - Q A)%E|%E | A in
    [set A : set (d.-tuple (measurableTypeR R)) | measurable A]].

(* 3. The n points of a sample x of PaperMainDefinitions: point i has the
   coordinates x_(i d + j), j < d. *)
Definition robust_points (n d : nat) (x : paper_main_sample n d) :
    n.-tuple (d.-tuple (measurableTypeR R)) :=
  [tuple [tuple List.nth (i * d + j)%N (tval x) 0 | j < d] | i < n].

(* The law of a sample of n i.i.d. points of law P: the probability that n
   independent points of law P form the list of points of a sample in A. *)
Definition robust_sample_law (n d : nat)
    (P : probability (d.-tuple (measurableTypeR R)) R)
    (A : set (paper_main_sample n d)) : \bar R :=
  tuple_prod (fun=> P) n (robust_points n d @` A).

(* 4. The point laws P d are close to those of the countable family (w, mu)
   at the scale of (17): d^2 tv(P d, nu_d) tends to 0. *)
Definition robust_close (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (P : forall d : nat, probability (d.-tuple (measurableTypeR R)) R) :
    Prop :=
  paper_main_tends_to
    (fun d => ((d%:R ^+ 2)%:E *
               robust_tv d (P d) (robust_point_law (w d) (mu d) d))%E) 0.

(* 5. The contamination of a finite family of N components, for samples of
   n points: the weights (1 - lambda / n) w s for s < N, lambda / n for the
   component N, 0 beyond. *)
Definition contaminated_weights (lambda : R) (n N : nat) (w : nat -> R)
    (s : nat) : R :=
  if (s < N)%N then (1 - lambda / n%:R) * w s
  else if s == N then lambda / n%:R else 0.

(* The component laws: those of the family for s < N, and the Dirac law at
   0 for every coordinate of the component N (and beyond). *)
Definition contaminated_laws (N : nat)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (s j : nat) :
    probability (measurableTypeR R) R :=
  if (s < N)%N then mu s j else \d_(0 : measurableTypeR R).
